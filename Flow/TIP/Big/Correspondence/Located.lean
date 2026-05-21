import Flow.TIP.Big.CFG
import Flow.TIP.Big.Correspondence.Refinement
import Flow.TIP.Eval

/-!
# `BigLocatedAt` / `BigKontMatches` — Option A port to `BigCFG`

A mutual, env-aware pair of predicates that places a CEK state at a
`BigCFG` node, mirroring `Flow.Eval.Located.LocatedAt` /
`KontMatches` for the regular CFG.

## What changes from the regular version

* **No mid-expression disjunction at a single node.** The `buildExpr`
  refactor (commit `66d0f59`) gives every sub-expression its own
  `EEntry` / `EExit` pair, so each EEntry admits exactly the
  `⟨inr e, …⟩` shape for that specific `e`. The regular `LocatedAt`'s
  four `of_inr_*` constructors collapse into a single recursive family
  on EEntry, one branch per `Expr` constructor.
* **More edge "stuttering" between CEK shapes.** Almost every BigCFG
  edge corresponds to exactly one CEK step (sometimes zero — `Int n`
  edges and merge edges), so the constructors thread CFG edges
  pointwise.

## What does NOT change

* **The mutuality.** `BigKontMatches` still references downstream
  `BigLocatedAt` for the post-pop state at each frame — that is the
  whole point of Option A.
* The `K` stack still encodes future CFG transitions via its frames,
  so the frame constructors (`seqK`, `assignK`, …, `binOpLK`, …) keep
  their existing semantic shape.

## Roadblocks (see PR comment for the full report)

1. **No `BuildSpec` companion for the monadic builder.** The new
   builder is `StateM BigCFGBuilder`, so `of_buildSpec`-style induction
   on a `BuildSpec` inductive doesn't apply. Either reintroduce a
   `BuildSpec` companion (one constructor per `do` block) or prove all
   preservation lemmas against `BuilderM`. We need:
   - `freshNode` / `emitEdge` preservation of `nodeKind` / `hasEdge`
   - Monotonicity of `BigCFGBuilder.cfg` through `BuilderM.bind`
   - `BigSubCFG b.cfg ((buildStmt s).run b).snd.cfg` after every build
2. **`BigSubCFG` weakening machinery isn't usable.** Defined the type
   here but without (1) we can't build the `of_*` helpers that the
   regular CFG has (`of_addNode`, `of_addEdge`, `of_buildSpec`).
   Without these, `BigLocatedAt.weaken` (needed in `of_buildStmt`) is
   stuck. Punted.
3. **The recursive `at_EEntry_*` family is forced.** The original
   design tried a single `at_EEntry` constructor with just nodeKind +
   `BigKontMatches`, but that constructor is *unsatisfiable* at SEntry
   nodes — `ifKT/F` and `whileKT/F` require `nodeKind = .EExit`, so a
   `BigKontMatches (.IfK t f :: K) (SEntry …) E` has no inhabitant.
   Fix: make the SEntry constructors *embed* the inner `BigLocatedAt`
   at the matching `EEntry`, which transitively reaches the `EExit`
   where the frame actually pops. Done in the file. Cost: every
   `at_*_S` carries the entire downstream expression chain.
4. **Step cases needing chain lemmas remain stubbed.** Eleven of
   seventeen `Step` cases in `step_decorate` need auxiliary peel
   lemmas (`stepsN_seqMid_chain`, `stepsN_whileD_chain`,
   `stepsN_binOp{L,R,D}_chain`) and/or `evalExpr_det`. These mirror the
   regular file's helpers but need `sexitBridge` chains specialised
   to BigCFG's merge layout.
-/

namespace Flow.Eval.Big.Located

open Flow.Eval.Big.Refinement

/-! ## `BigSubCFG` — structural prefix relation on `BigCFG`s

Mirror of `SubCFG` for the regular CFG. Without `BuildSpec`-style
preservation lemmas it isn't immediately useful, but we'll need the
shape for `BigLocatedAt.weaken`. -/

def BigSubCFG (g₁ g₂ : BigCFG) : Prop :=
  (∃ ns, g₂.nodes = g₁.nodes ++ ns) ∧
  (∃ es, g₂.edges = g₁.edges ++ es)

namespace BigSubCFG

theorem refl (g : BigCFG) : BigSubCFG g g :=
  ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem trans {g₁ g₂ g₃ : BigCFG}
    (h₁ : BigSubCFG g₁ g₂) (h₂ : BigSubCFG g₂ g₃) : BigSubCFG g₁ g₃ := by
  obtain ⟨⟨ns₁, hn₁⟩, ⟨es₁, he₁⟩⟩ := h₁
  obtain ⟨⟨ns₂, hn₂⟩, ⟨es₂, he₂⟩⟩ := h₂
  refine ⟨⟨ns₁ ++ ns₂, ?_⟩, ⟨es₁ ++ es₂, ?_⟩⟩
  · simp [hn₂, hn₁, List.append_assoc]
  · simp [he₂, he₁, List.append_assoc]

theorem nodeKind {g₁ g₂ : BigCFG} (h : BigSubCFG g₁ g₂) {n : BigNodeID}
    (hn : n < g₁.nodes.length) : g₂.nodeKind n = g₁.nodeKind n := by
  obtain ⟨⟨ns, hns⟩, _⟩ := h
  simp [BigCFG.nodeKind, hns, List.getElem?_append_left, hn]

theorem hasEdge {g₁ g₂ : BigCFG} (h : BigSubCFG g₁ g₂)
    {src dst : BigNodeID} {k : EdgeKind} (he : g₁.hasEdge src dst k) :
    g₂.hasEdge src dst k := by
  obtain ⟨_, ⟨es, hes⟩⟩ := h
  simp only [BigCFG.hasEdge, hes, List.mem_append]
  exact Or.inl he

end BigSubCFG

/-! ## `BigLocatedAt` / `BigKontMatches` — mutual env-aware predicates -/

mutual

/-- The CEK state `σ` sits at node `n` of `g`. -/
inductive BigLocatedAt (g : BigCFG) : BigNodeID -> CEK -> Prop where
  -- ### Statement-side constructors
  /-- `SEntry .Skip`: about to execute `Skip`. -/
  | at_skip_S {n E K} :
      g.nodeKind n = some (.SEntry .Skip) ->
      BigKontMatches g K n E ->
      BigLocatedAt g n ⟨.inl .Skip, E, K⟩
  /-- `SEntry (Assign x e)`: about to execute the assignment. Embeds
      the recursive `BigLocatedAt` at the corresponding `EEntry e`,
      which (via its own `at_EEntry_*` constructor) carries the chain
      to the matching `EExit` and the `BigKontMatches.assignK` pop
      onto the `SExit`. -/
  | at_assign_S {n m_een x e E K} :
      g.nodeKind n = some (.SEntry (.Assign x e)) ->
      g.hasEdge n m_een .Normal ->
      BigLocatedAt g m_een ⟨.inr e, E, .AssignK x :: K⟩ ->
      BigLocatedAt g n ⟨.inl (.Assign x e), E, K⟩
  /-- `SEntry (Decl x e)`. -/
  | at_decl_S {n m_een x e E K} :
      g.nodeKind n = some (.SEntry (.Decl x e)) ->
      g.hasEdge n m_een .Normal ->
      BigLocatedAt g m_een ⟨.inr e, E, .DeclK x :: K⟩ ->
      BigLocatedAt g n ⟨.inl (.Decl x e), E, K⟩
  /-- `SEntry (If c t f)`. Embeds the inner `BigLocatedAt` at the
      `EEntry c`; the `IfK` frame is popped at the `EExit c`, which
      that inner predicate transitively reaches. -/
  | at_if_S {n m_een c t f E K} :
      g.nodeKind n = some (.SEntry (.If c t f)) ->
      g.hasEdge n m_een .Normal ->
      BigLocatedAt g m_een ⟨.inr c, E, .IfK t f :: K⟩ ->
      BigLocatedAt g n ⟨.inl (.If c t f), E, K⟩
  /-- `SEntry (While c b)`. -/
  | at_while_S {n m_een c b E K} :
      g.nodeKind n = some (.SEntry (.While c b)) ->
      g.hasEdge n m_een .Normal ->
      BigLocatedAt g m_een ⟨.inr c, E, .WhileK c b :: K⟩ ->
      BigLocatedAt g n ⟨.inl (.While c b), E, K⟩
  /-- Seq's entry shares with `s₁`'s entry; recursive frame. -/
  | at_seq {n s₁ s₂ E K} :
      BigLocatedAt g n ⟨.inl s₁, E, .SeqK s₂ :: K⟩ ->
      BigLocatedAt g n ⟨.inl (.Seq s₁ s₂), E, K⟩
  /-- `SExit`: just finished executing a statement. -/
  | at_SExit {n E K} :
      g.nodeKind n = some .SExit ->
      BigKontMatches g K n E ->
      BigLocatedAt g n ⟨.inl .Skip, E, K⟩

  -- ### Expression-side constructors
  -- One per `Expr` shape on `EEntry`; one uniform on `EExit`. Each
  -- `EEntry` constructor either base-cases (`Int`/`Var`) or recurses
  -- through its sub-expressions' EEntry, threading `BinOpLK`/`BinOpRK`
  -- frames onto `K`. Each packages the chain through to the
  -- corresponding `EExit` carrying the value of the expression.

  /-- `EEntry (.Int n)` — already a value; bridges directly to its
      `EExit` without a CEK step. -/
  | at_EEntry_Int {n m_ex n_ix E K} :
      g.nodeKind n = some (.EEntry (.Int n_ix)) ->
      g.hasEdge n m_ex .Normal ->
      BigLocatedAt g m_ex ⟨.inr (.Int n_ix), E, K⟩ ->
      BigLocatedAt g n ⟨.inr (.Int n_ix), E, K⟩
  /-- `EEntry (.Var x)` — `Step.Var` looks up `x` and lands at `EExit`
      with the looked-up value. -/
  | at_EEntry_Var {n m_ex x n_ix E K} :
      g.nodeKind n = some (.EEntry (.Var x)) ->
      g.hasEdge n m_ex .Normal ->
      E x = some (.Int n_ix) ->
      BigLocatedAt g m_ex ⟨.inr (.Int n_ix), E, K⟩ ->
      BigLocatedAt g n ⟨.inr (.Var x), E, K⟩
  /-- `EEntry (.BinOp o e₁ e₂)`. The constructor packages the entire
      sub-expression chain: enter `e₁` (pushing `BinOpLK`), reach
      `EExit(e₁)`, hop to `EEntry(e₂)` along `Step.BinOpR` (swapping
      `BinOpLK → BinOpRK`), reach `EExit(e₂)`, then `Step.BinOpD` lands
      at the outer `EExit` with the combined value. -/
  | at_EEntry_BinOp {n n_₁en n_₁ex n_₂en n_₂ex n_ex o e₁ e₂ E K n₁ n₂} :
      g.nodeKind n = some (.EEntry (.BinOp o e₁ e₂)) ->
      g.hasEdge n n_₁en .Normal ->
      BigLocatedAt g n_₁en ⟨.inr e₁, E, .BinOpLK o e₂ :: K⟩ ->
      g.nodeKind n_₁ex = some .EExit ->
      g.hasEdge n_₁ex n_₂en .Normal ->
      EvalExpr E e₁ (.Int n₁) ->
      BigLocatedAt g n_₂en ⟨.inr e₂, E, .BinOpRK (.Int n₁) o :: K⟩ ->
      g.nodeKind n_₂ex = some .EExit ->
      g.hasEdge n_₂ex n_ex .Normal ->
      EvalExpr E e₂ (.Int n₂) ->
      g.nodeKind n_ex = some .EExit ->
      BigLocatedAt g n_ex ⟨.inr (.Int (applyOp o n₁ n₂)), E, K⟩ ->
      BigLocatedAt g n ⟨.inr (.BinOp o e₁ e₂), E, K⟩
  /-- `EExit` — value computed; pop a `K` frame on outgoing edge. -/
  | at_EExit {n n_ix E K} :
      g.nodeKind n = some .EExit ->
      BigKontMatches g K n E ->
      BigLocatedAt g n ⟨.inr (.Int n_ix), E, K⟩

/-- `K`'s top frame, when popped at node `n` under env `E`, lands the
    CEK in a `BigLocatedAt` at some downstream node. -/
inductive BigKontMatches (g : BigCFG) : List Cont -> BigNodeID -> State -> Prop where
  | nil {n E} : BigKontMatches g [] n E
  /-- `.SeqK s₂` popped by `.SeqMid` — destination is `SEntry s₂`. -/
  | seqK {n m s₂ E K} :
      g.hasEdge n m .Normal ->
      BigLocatedAt g m ⟨.inl s₂, E, K⟩ ->
      BigKontMatches g (.SeqK s₂ :: K) n E
  /-- `.AssignK x` popped by `.AssignD` — destination is `SExit`. The
      writeback value `v` is universally quantified. -/
  | assignK {n m x v E K} :
      g.hasEdge n m .Normal ->
      g.nodeKind m = some .SExit ->
      BigKontMatches g K m (E.updated x v) ->
      BigKontMatches g (.AssignK x :: K) n E
  | declK {n m x v E K} :
      g.hasEdge n m .Normal ->
      g.nodeKind m = some .SExit ->
      BigKontMatches g K m (E.updated x v) ->
      BigKontMatches g (.DeclK x :: K) n E
  /-- `.IfK t f` popped by `.IfT` — destination is `SEntry t` via TBranch. -/
  | ifKT {n nT t f E K c v} :
      g.nodeKind n = some .EExit ->
      g.hasEdge n nT .TBranch ->
      BigLocatedAt g nT ⟨.inl t, E, K⟩ ->
      EvalExpr E c v ->
      v ≠ .Int 0 ->
      BigKontMatches g (.IfK t f :: K) n E
  | ifKF {n nF t f E K c} :
      g.nodeKind n = some .EExit ->
      g.hasEdge n nF .FBranch ->
      BigLocatedAt g nF ⟨.inl f, E, K⟩ ->
      EvalExpr E c (.Int 0) ->
      BigKontMatches g (.IfK t f :: K) n E
  /-- `.WhileK c b` popped by `.WhileT` / `.WhileF`. -/
  | whileKT {n nT c b E K v} :
      g.hasEdge n nT .TBranch ->
      BigLocatedAt g nT ⟨.inl b, E, .WhileBackK c b :: K⟩ ->
      EvalExpr E c v ->
      v ≠ .Int 0 ->
      BigKontMatches g (.WhileK c b :: K) n E
  | whileKF {n nF c b E K} :
      g.hasEdge n nF .FBranch ->
      BigLocatedAt g nF ⟨.inl .Skip, E, K⟩ ->
      EvalExpr E c (.Int 0) ->
      BigKontMatches g (.WhileK c b :: K) n E
  /-- `.WhileBackK c b` popped by `.WhileD` — destination is the same
      `SEntry (While c b)` re-entry. -/
  | whileBackK {n nc c b E K} :
      g.hasEdge n nc .Normal ->
      BigLocatedAt g nc ⟨.inl (.While c b), E, K⟩ ->
      BigKontMatches g (.WhileBackK c b :: K) n E
  /-- Two-step skip-bridge for the if-merge: at an `SExit` of a
      then/else arm, the merge `Normal` edge to the if's outer `SExit`
      preserves the kont stack. -/
  | sexitBridge {n m E K} :
      g.nodeKind n = some .SExit ->
      g.nodeKind m = some .SExit ->
      g.hasEdge n m .Normal ->
      BigKontMatches g K m E ->
      BigKontMatches g K n E
  /-- `.BinOpLK o e₂` popped by `.BinOpR` at an `EExit` of `e₁` —
      destination is the `EEntry` of `e₂`. The post-pop frame is
      `.BinOpRK v o` where `v` is the value at pop time. -/
  | binOpLK {n m o e₂ v E K} :
      g.nodeKind n = some .EExit ->
      g.hasEdge n m .Normal ->
      g.nodeKind m = some (.EEntry e₂) ->
      BigLocatedAt g m ⟨.inr e₂, E, .BinOpRK v o :: K⟩ ->
      BigKontMatches g (.BinOpLK o e₂ :: K) n E
  /-- `.BinOpRK (.Int n₁) o` popped by `.BinOpD` at an `EExit` of `e₂` —
      destination is the outer `EExit`. The frame carries `Val` but the
      only inhabited values are `.Int _`, so we narrow on the frame
      pattern. -/
  | binOpRK {n m n₁ o E K} :
      g.nodeKind n = some .EExit ->
      g.hasEdge n m .Normal ->
      g.nodeKind m = some .EExit ->
      (∀ n₂, BigLocatedAt g m ⟨.inr (.Int (applyOp o n₁ n₂)), E, K⟩) ->
      BigKontMatches g (.BinOpRK (.Int n₁) o :: K) n E

end

/-! ## `BigLocatedAt.bound` — every located state is within bounds -/

private lemma nodeKind_lt {g : BigCFG} {n : BigNodeID} {k : BigNodeKind}
    (h : g.nodeKind n = some k) : n < g.nodes.length := by
  unfold BigCFG.nodeKind at h
  false_or_by_contra
  rename_i hge
  grind

/-- Same dual-motive trick as the regular case: the `KontMatches`
    companion motive is `True`. -/
theorem BigLocatedAt.bound {g : BigCFG} {n : BigNodeID} {σ : CEK}
    (h : BigLocatedAt g n σ) : n < g.nodes.length := by
  induction h using BigLocatedAt.rec
    (motive_2 := fun _ _ _ _ => True) with
  | at_skip_S hk _ _                       => exact nodeKind_lt hk
  | at_assign_S hk _ _ _                   => exact nodeKind_lt hk
  | at_decl_S hk _ _ _                     => exact nodeKind_lt hk
  | at_if_S hk _ _ _                       => exact nodeKind_lt hk
  | at_while_S hk _ _ _                    => exact nodeKind_lt hk
  | at_seq _ ih                            => exact ih
  | at_SExit hk _ _                        => exact nodeKind_lt hk
  | at_EEntry_Int hk _ _ _                 => exact nodeKind_lt hk
  | at_EEntry_Var hk _ _ _ _               => exact nodeKind_lt hk
  | at_EEntry_BinOp hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact nodeKind_lt hk
  | at_EExit hk _ _                        => exact nodeKind_lt hk
  | _                                       => trivial

/-! ## `step_decorate` (mostly stubbed)

The single-step decoration theorem: for any `BigLocatedAt g n σ` and
any CEK `Step σ σ'`, there's a corresponding `BigStepsN` chain in `g`
landing at some downstream node where `σ'` is again `BigLocatedAt`.

Auxiliary lemmas needed (mirroring the regular case):

* `evalExpr_det` — copy from regular.
* `stepsN_seqMid_chain` / `stepsN_whileD_chain` — peel `BigKontMatches`
  chains through `sexitBridge`s and end in a `seqK` / `whileBackK`
  frame respectively. Generate `BigStepsN` for the bridges + a final
  `advance`. The BigCFG variant needs to bridge across multiple
  `sexitBridge`s for nested if-merges.
* A new `EEntry → … → EExit` chain lemma: from `BigLocatedAt g n_en
  ⟨inr e, …⟩` derived from `at_EEntry_*`, produce the `BigStepsN`
  through the sub-expression sub-graph to the matching `EExit`.
  Analogous to `stepsN_seqMid_chain`, but for expressions. Splice
  three sub-chains in the BinOp case (e₁ recursive, BinOpR, e₂
  recursive, BinOpD).

Proving below: just the structural CEK frames (`SeqEnter`) that don't
need any auxiliary chain lemmas. The rest is stubbed with `sorry`. -/

theorem step_decorate {g : BigCFG} {n : BigNodeID} {σ σ' : CEK}
    (hloc : BigLocatedAt g n σ) (hstep : Step σ σ') :
    ∃ (n' : BigNodeID) (h : n < g.nodes.length) (h' : n' < g.nodes.length),
      BigStepsN g h σ h' σ' ∧ BigLocatedAt g n' σ' := by
  have hn : n < g.nodes.length := hloc.bound
  cases hstep with
  | @SeqEnter s₁ s₂ E K =>
    -- σ = ⟨inl (Seq s₁ s₂), …⟩, σ' = ⟨inl s₁, …, .SeqK s₂ :: K⟩
    cases hloc with
    | at_seq hloc' =>
      refine ⟨n, hn, hn, ?_, hloc'⟩
      exact .single hn hn (.stutter hn .SeqEnter rfl)
  | @Assign x e E K =>
    -- σ = ⟨inl (Assign x e), …⟩, σ' = ⟨inr e, …, .AssignK x :: K⟩
    cases hloc with
    | at_assign_S _ hedge hinner =>
      have hm := hinner.bound
      refine ⟨_, hn, hm, ?_, hinner⟩
      exact .single hn hm (.advance hn hm .Assign hedge rfl)
  | @Decl x e E K =>
    cases hloc with
    | at_decl_S _ hedge hinner =>
      have hm := hinner.bound
      refine ⟨_, hn, hm, ?_, hinner⟩
      exact .single hn hm (.advance hn hm .Decl hedge rfl)
  | @IfC c t f E K =>
    cases hloc with
    | at_if_S _ hedge hinner =>
      have hm := hinner.bound
      refine ⟨_, hn, hm, ?_, hinner⟩
      exact .single hn hm (.advance hn hm .IfC hedge rfl)
  | @WhileC c b E K =>
    cases hloc with
    | at_while_S _ hedge hinner =>
      have hm := hinner.bound
      refine ⟨_, hn, hm, ?_, hinner⟩
      exact .single hn hm (.advance hn hm .WhileC hedge rfl)
  | @BinOpL o e₁ e₂ E K =>
    -- σ = ⟨inr (BinOp o e₁ e₂), …⟩, σ' = ⟨inr e₁, …, .BinOpLK o e₂ :: K⟩
    cases hloc with
    | at_EEntry_BinOp _ hedge hinner _ _ _ _ _ _ _ _ _ =>
      have hm := hinner.bound
      refine ⟨_, hn, hm, ?_, hinner⟩
      exact .single hn hm (.advance hn hm .BinOpL hedge rfl)
  -- Remaining cases (see comments above the theorem) all need
  -- additional case work that depends on auxiliary lemmas not yet
  -- ported. Stubbed.
  | AssignD => sorry
  | DeclD => sorry
  | @Var E x K n_step hxv =>
    -- σ = ⟨inr (Var x), …⟩, σ' = ⟨inr (.Int n_step), …⟩
    -- Roadblock: the `at_EEntry_Var` constructor binds the value as an
    -- anonymous `n_ix`. We need `n_step = n_ix` via two layers of
    -- injection on `E x = some (.Int _)`. Doable but cluttered; left
    -- stubbed.
    sorry
  | BinOpR => sorry
  | BinOpD => sorry
  | IfT _ => sorry
  | IfF => sorry
  | WhileT _ => sorry
  | WhileF => sorry
  | WhileD => sorry
  | SeqMid => sorry

/-! ## `cek_refines_cfg` — multi-step lift -/

theorem cek_refines_cfg {g : BigCFG} {n : BigNodeID} {σ σ' : CEK}
    (hloc : BigLocatedAt g n σ) (hsteps : Steps σ σ') :
    ∃ (n' : BigNodeID) (h : n < g.nodes.length) (h' : n' < g.nodes.length),
      BigStepsN g h σ h' σ' ∧ BigLocatedAt g n' σ' := by
  induction hsteps generalizing n with
  | refl =>
    exact ⟨n, hloc.bound, hloc.bound, .refl hloc.bound _, hloc⟩
  | step hstep _ ih =>
    obtain ⟨n₁, hn, h₁, hsn, hloc₁⟩ := step_decorate hloc hstep
    obtain ⟨n', _, h', hsns, hloc'⟩ := ih hloc₁
    exact ⟨n', hn, h', hsn.trans hsns, hloc'⟩

/-! ## `of_buildStmt` — entrypoint (stub)

Bridges the gap between the language-level `BigStep` and the
`BigLocatedAt` predicate. The regular `LocatedAt.of_buildSpec` inducts
on the `BuildSpec` inductive companion of the builder. For BigCFG
the builder is monadic (`BuilderM = StateM BigCFGBuilder`), so there
is no inductive companion to induct on yet — this is the largest
roadblock.

Options to discharge it:

* **Reintroduce a `BuildSpec` companion** mirroring the regular one
  but for the monadic builder. Each `do … return …` block in
  `BigCFGBuilder.buildStmt` / `buildExpr` becomes one constructor.
  Most of the proof would then transfer directly.
* **Reason about `BuilderM`'s state monad operations** with
  preservation lemmas (`freshNode_nodeKind`, `emitEdge_hasEdge`, …)
  and lift them through `bind`. This avoids the duplication but every
  small operation needs its own lemma, and the threading is fiddly.

Either way, this is downstream of having `BigSubCFG` machinery
(`of_freshNode`, `of_emitEdge`, monotonicity of `BigStep` builds). -/

theorem of_buildStmt
    {g : BigCFG} {b : BigCFGBuilder} {s : Stmt} {b' : BigCFGBuilder}
    {en ex : BigNodeID}
    (_hbuild : (BigCFGBuilder.buildStmt s).run b = ((en, ex), b'))
    (_hsub : BigSubCFG b'.cfg g)
    {E E' : State} (_hbig : BigStep s E E')
    {K_out : List Cont}
    (_hkm : BigKontMatches g K_out ex E') :
    BigLocatedAt g en ⟨.inl s, E, K_out⟩ :=
  sorry

end Flow.Eval.Big.Located
