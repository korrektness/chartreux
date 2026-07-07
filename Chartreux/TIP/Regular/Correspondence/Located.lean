import Chartreux.TIP.Regular.CFG
import Chartreux.TIP.Eval
import Chartreux.TIP.Regular.Correspondence.Refinement

namespace Chartreux.Eval.Located

open CFGBuilder
open Chartreux.Eval.Refinement

/-! ## Helpers for the expression-evaluation invariant -/

/-- A list of continuation frames that are entirely sub-expression
    `BinOp{L,R}K` frames — i.e. no statement-level frame appears. -/
inductive OnlyBinopFrames : List Cont -> Prop where
  | nil : OnlyBinopFrames []
  | binOpL {o : BinOp} {e₂ : Expr} {K : List Cont} :
      OnlyBinopFrames K -> OnlyBinopFrames (.BinOpLK o e₂ :: K)
  | binOpR {v : Val} {o : BinOp} {K : List Cont} :
      OnlyBinopFrames K -> OnlyBinopFrames (.BinOpRK v o :: K)

/-- `EvalCont E K v_in v_out`: a list of `BinOp{L,R}K` frames `K`,
    fed an inner value `v_in`, produces outer value `v_out` under `E`. -/
inductive EvalCont (E : State) : List Cont -> Val -> Val -> Prop where
  | nil {v : Val} : EvalCont E [] v v
  | binOpL {o : BinOp} {e₂ : Expr} {K : List Cont}
      {n₁ n₂ : Int} {v_out : Val} :
      EvalExpr E e₂ (.Int n₂) ->
      EvalCont E K (.Int (applyOp o n₁ n₂)) v_out ->
      EvalCont E (.BinOpLK o e₂ :: K) (.Int n₁) v_out
  | binOpR {n₁ : Int} {o : BinOp} {K : List Cont}
      {n₂ : Int} {v_out : Val} :
      EvalCont E K (.Int (applyOp o n₁ n₂)) v_out ->
      EvalCont E (.BinOpRK (.Int n₁) o :: K) (.Int n₂) v_out

/-- `Pending E e K_b v`: starting from `⟨inr e, E, K_b ++ rest⟩`, the
    expression-evaluation portion will yield value `v` before popping. -/
def Pending (E : State) (e : Expr) (K_b : List Cont) (v : Val) : Prop :=
  ∃ v_inner, EvalExpr E e v_inner ∧ EvalCont E K_b v_inner v

/-! ## Mutual env-aware predicates `LocatedAt` / `KontMatches` -/

mutual

/-- `LocatedAt g n σ`: the CEK state `σ` sits at node `n` of `g`. -/
inductive LocatedAt (g : CFG) : NodeID -> CEK -> Prop where
  /-- About to execute `Skip`. -/
  | at_skip {n E K} :
      g.nodeKind n = some .Skip ->
      KontMatches g K n E ->
      LocatedAt g n ⟨.inl .Skip, E, K⟩
  /-- About to execute `Assign x e`. The totality witness
      `EvalExpr E e v` is required so that `Step.Assign` can construct
      the post-state's `LocatedAt`. The post-mutation
      `KontMatches g K m (E.updated x v)` is embedded directly so that
      `v` is shared between the expression evaluation and the frame. -/
  | at_assign {n m x e v E K} :
      g.nodeKind n = some (.Assign x e) ->
      EvalExpr E e v ->
      g.hasEdge n m .Normal ->
      g.nodeKind m = some .Skip ->
      KontMatches g K m (E.updated x v) ->
      LocatedAt g n ⟨.inl (.Assign x e), E, K⟩
  /-- About to execute `Decl x e`. -/
  | at_decl {n m x e v E K} :
      g.nodeKind n = some (.Decl x e) ->
      EvalExpr E e v ->
      g.hasEdge n m .Normal ->
      g.nodeKind m = some .Skip ->
      KontMatches g K m (E.updated x v) ->
      LocatedAt g n ⟨.inl (.Decl x e), E, K⟩
  /-- About to execute `If c t f`. -/
  | at_if {n c t f v E K} :
      g.nodeKind n = some (.Cond c) ->
      EvalExpr E c v ->
      KontMatches g (.IfK t f :: K) n E ->
      LocatedAt g n ⟨.inl (.If c t f), E, K⟩
  /-- About to execute `While c b`. -/
  | at_while {n c b v E K} :
      g.nodeKind n = some (.Cond c) ->
      EvalExpr E c v ->
      KontMatches g (.WhileK c b :: K) n E ->
      LocatedAt g n ⟨.inl (.While c b), E, K⟩
  /-- About to execute `Seq s₁ s₂`. -/
  | at_seq {n s₁ s₂ E K} :
      LocatedAt g n ⟨.inl s₁, E, .SeqK s₂ :: K⟩ ->
      LocatedAt g n ⟨.inl (.Seq s₁ s₂), E, K⟩
  /-- Mid-expression evaluation, surrounding frame is `AssignK x`. -/
  | of_inr_assign {n m x e_orig e v_orig E K_b K_out} :
      g.nodeKind n = some (.Assign x e_orig) ->
      OnlyBinopFrames K_b ->
      EvalExpr E e_orig v_orig ->
      Pending E e K_b v_orig ->
      g.hasEdge n m .Normal ->
      g.nodeKind m = some .Skip ->
      KontMatches g K_out m (E.updated x v_orig) ->
      LocatedAt g n ⟨.inr e, E, K_b ++ .AssignK x :: K_out⟩
  /-- Mid-expression evaluation, surrounding frame is `DeclK x`. -/
  | of_inr_decl {n m x e_orig e v_orig E K_b K_out} :
      g.nodeKind n = some (.Decl x e_orig) ->
      OnlyBinopFrames K_b ->
      EvalExpr E e_orig v_orig ->
      Pending E e K_b v_orig ->
      g.hasEdge n m .Normal ->
      g.nodeKind m = some .Skip ->
      KontMatches g K_out m (E.updated x v_orig) ->
      LocatedAt g n ⟨.inr e, E, K_b ++ .DeclK x :: K_out⟩
  /-- Mid-expression evaluation, surrounding frame is `IfK t f`. -/
  | of_inr_if {n c_orig t f e v_orig E K_b K_out} :
      g.nodeKind n = some (.Cond c_orig) ->
      OnlyBinopFrames K_b ->
      EvalExpr E c_orig v_orig ->
      Pending E e K_b v_orig ->
      KontMatches g (.IfK t f :: K_out) n E ->
      LocatedAt g n ⟨.inr e, E, K_b ++ .IfK t f :: K_out⟩
  /-- Mid-expression evaluation, surrounding frame is `WhileK c b`. -/
  | of_inr_while {n c_orig b e v_orig E K_b K_out} :
      g.nodeKind n = some (.Cond c_orig) ->
      OnlyBinopFrames K_b ->
      EvalExpr E c_orig v_orig ->
      Pending E e K_b v_orig ->
      KontMatches g (.WhileK c_orig b :: K_out) n E ->
      LocatedAt g n ⟨.inr e, E, K_b ++ .WhileK c_orig b :: K_out⟩

/-- `KontMatches g K n E`: when control reaches node `n` under env `E`
    and stack `K`, the next pop lands in a `LocatedAt`-matched state.

    Frames whose post-pop state changes the env (`assignK`, `declK`) are
    universally quantified over the writeback value `v`. -/
inductive KontMatches (g : CFG) : List Cont -> NodeID -> State -> Prop where
  | nil {n E} : KontMatches g [] n E
  | seqK {n m s₂ E K} :
      g.hasEdge n m .Normal ->
      LocatedAt g m ⟨.inl s₂, E, K⟩ ->
      KontMatches g (.SeqK s₂ :: K) n E
  | assignK {n m x v E K} :
      g.hasEdge n m .Normal ->
      g.nodeKind m = some .Skip ->
      KontMatches g K m (E.updated x v) ->
      KontMatches g (.AssignK x :: K) n E
  | declK {n m x v E K} :
      g.hasEdge n m .Normal ->
      g.nodeKind m = some .Skip ->
      KontMatches g K m (E.updated x v) ->
      KontMatches g (.DeclK x :: K) n E
  | ifKT {n nT t f E K c v} :
      g.nodeKind n = some (.Cond c) ->
      g.hasEdge n nT .TBranch ->
      LocatedAt g nT ⟨.inl t, E, K⟩ ->
      EvalExpr E c v ->
      v ≠ .Int 0 ->
      KontMatches g (.IfK t f :: K) n E
  | ifKF {n nF t f E K c} :
      g.nodeKind n = some (.Cond c) ->
      g.hasEdge n nF .FBranch ->
      LocatedAt g nF ⟨.inl f, E, K⟩ ->
      EvalExpr E c (.Int 0) ->
      KontMatches g (.IfK t f :: K) n E
  | whileKT {n nT c b E K v} :
      g.hasEdge n nT .TBranch ->
      LocatedAt g nT ⟨.inl b, E, .WhileBackK c b :: K⟩ ->
      EvalExpr E c v ->
      v ≠ .Int 0 ->
      KontMatches g (.WhileK c b :: K) n E
  | whileKF {n nF c b E K} :
      g.hasEdge n nF .FBranch ->
      LocatedAt g nF ⟨.inl .Skip, E, K⟩ ->
      EvalExpr E c (.Int 0) ->
      KontMatches g (.WhileK c b :: K) n E
  | whileBackK {n nc c b E K} :
      g.hasEdge n nc .Normal ->
      LocatedAt g nc ⟨.inl (.While c b), E, K⟩ ->
      KontMatches g (.WhileBackK c b :: K) n E
  /-- Skip-bridge: at a `.Skip` node `n` with a `.Normal` edge to a
      `.Skip` node `m`, a kont matched at `m` lifts to a kont matched at
      `n` (under the same env and stack). Used by
      `LocatedAt.of_buildSpec` to bridge across the merge `Skip` node
      inserted by `BuildSpec.if_`/`while_`. The destination's
      `nodeKind = .Skip` premise gives a derivable `m < g.nodes.length`,
      enabling structural induction over chains of bridges. -/
  | skipBridge {n m E K} :
      g.nodeKind n = some .Skip ->
      g.nodeKind m = some .Skip ->
      g.hasEdge n m .Normal ->
      KontMatches g K m E ->
      KontMatches g K n E
  | binOpLK {n o e₂ E K} :
      KontMatches g K n E ->
      KontMatches g (.BinOpLK o e₂ :: K) n E
  | binOpRK {n v o E K} :
      KontMatches g K n E ->
      KontMatches g (.BinOpRK v o :: K) n E
end

/-! ## Bound lemma -/

private lemma nodeKind_lt {g : CFG} {n : NodeID} {k : NodeKind}
    (h : g.nodeKind n = some k) : n < g.nodes.length := by
  unfold CFG.nodeKind at h; grind

/-- Bound for `LocatedAt` proved via the *mutual* recursor of
    `LocatedAt`/`KontMatches`. Since the bound only depends on
    `LocatedAt`, the companion motive on `KontMatches` is the trivial
    `True` predicate — a dummy "always-true" branch — which lets us
    invoke the mutual induction principle without any side proof
    obligation on the `KontMatches` side, and avoids having to ship a
    `termination_by` measure for the recursive call in `at_seq`. -/
theorem LocatedAt.bound {g : CFG} {n : NodeID} {σ : CEK}
    (h : LocatedAt g n σ) : n < g.nodes.length := by
  induction h using LocatedAt.rec
    (motive_2 := fun _ _ _ _ => True) with
  | at_skip hk _ _                  => exact nodeKind_lt hk
  | at_assign hk _ _ _ _ _          => exact nodeKind_lt hk
  | at_decl hk _ _ _ _ _            => exact nodeKind_lt hk
  | at_if hk _ _ _                  => exact nodeKind_lt hk
  | at_while hk _ _ _               => exact nodeKind_lt hk
  | at_seq _ ih                     => exact ih
  | of_inr_assign hk _ _ _ _ _ _ _  => exact nodeKind_lt hk
  | of_inr_decl   hk _ _ _ _ _ _ _  => exact nodeKind_lt hk
  | of_inr_if     hk _ _ _ _ _      => exact nodeKind_lt hk
  | of_inr_while  hk _ _ _ _ _      => exact nodeKind_lt hk
  | _                               => trivial

/-! ## `step_decorate` -/

/-- `EvalExpr` is deterministic. -/
private lemma evalExpr_det {E : State} {e : Expr} {v₁ v₂ : Val}
    (h₁ : EvalExpr E e v₁) (h₂ : EvalExpr E e v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | int =>
    cases h₂ with | int => rfl
  | var hx =>
    cases h₂ with | var hy => rw [hx] at hy; cases hy; rfl
  | binop _ _ ih₁ ih₂ =>
    cases h₂ with
    | binop hb₁ hb₂ =>
      have e1 := ih₁ hb₁; have e2 := ih₂ hb₂
      cases e1; cases e2; rfl

/-- `Pending E (Int n) []` collapses to identity. -/
private lemma pending_int_nil {E : State} {n : Int} {v : Val}
    (h : Pending E (.Int n) [] v) : v = .Int n := by
  rcases h with ⟨vi, hev, hcont⟩
  cases hev
  cases hcont
  rfl

/-- Peel a chain of `KontMatches.skipBridge`s ending in a `seqK` frame:
    given a `Skip` node `n` with a kont stack `.SeqK s₂ :: K`, produce
    a `StepsN` chain (a sequence of `skipBridge`s ending in the
    `Step.SeqMid` `advance`) and the resulting `LocatedAt` for the
    seq-target. Proved by structural induction on `KontMatches` via the
    mutual recursor; non-matching `KontMatches` constructors and the
    companion `LocatedAt` arms collapse to a vacuous `True` motive,
    discharged by `trivial`. -/
private lemma stepsN_seqMid_chain
    {g : CFG} {n : NodeID} (hn : n < g.nodes.length)
    {E : State} {s₂ : Stmt} {K : List Cont}
    (hk : g.nodeKind n = some .Skip)
    (hkm : KontMatches g (.SeqK s₂ :: K) n E) :
    ∃ (m : NodeID) (h_m : m < g.nodes.length),
      StepsN g hn ⟨.inl .Skip, E, .SeqK s₂ :: K⟩ h_m
        ⟨.inl s₂, E, K⟩ ∧
      LocatedAt g m ⟨.inl s₂, E, K⟩ := by
  suffices h : ∀ (n' : NodeID) (E' : State) (K_full : List Cont)
      (_ : KontMatches g K_full n' E')
      (s₂' : Stmt) (K' : List Cont),
      K_full = .SeqK s₂' :: K' ->
      g.nodeKind n' = some .Skip ->
      ∀ (h_n' : n' < g.nodes.length),
        ∃ (m : NodeID) (h_m : m < g.nodes.length),
          StepsN g h_n' ⟨.inl .Skip, E', .SeqK s₂' :: K'⟩ h_m
              ⟨.inl s₂', E', K'⟩ ∧
          LocatedAt g m ⟨.inl s₂', E', K'⟩ from
    h n E _ hkm s₂ K rfl hk hn
  intro n' E' K_full hkm'
  induction hkm' using KontMatches.rec
    (motive_1 := fun _ _ _ => True) with
  | seqK hedge hloc =>
    intro s₂' K' h_eq hk_n' h_n'
    cases h_eq
    have h_m := hloc.bound
    refine ⟨_, h_m, ?_, hloc⟩
    exact .single h_n' h_m (.advance h_n' h_m .SeqMid hk_n' hedge rfl)
  | @skipBridge _ m_b _ _ hk_n_skip hk_m_skip hedge _ ih =>
    intro s₂' K' h_eq hk_n' h_n'
    have h_m_bound : m_b < g.nodes.length := nodeKind_lt hk_m_skip
    obtain ⟨m, h_m, hsteps_inner, hloc_m⟩ :=
      ih s₂' K' h_eq hk_m_skip h_m_bound
    refine ⟨m, h_m, ?_, hloc_m⟩
    exact .skipBridge h_n' h_m_bound h_m hk_n' hedge hsteps_inner
  | _ => grind
    
/-- Mirror of `stepsN_seqMid_chain` for the `WhileD` step: peel a
    chain of bridges ending in a `whileBackK` frame. -/
private lemma stepsN_whileD_chain
    {g : CFG} {n : NodeID} (hn : n < g.nodes.length)
    {E : State} {c : Expr} {b : Stmt} {K : List Cont}
    (hk : g.nodeKind n = some .Skip)
    (hkm : KontMatches g (.WhileBackK c b :: K) n E) :
    ∃ (m : NodeID) (h_m : m < g.nodes.length),
      StepsN g hn ⟨.inl .Skip, E, .WhileBackK c b :: K⟩ h_m
        ⟨.inl (.While c b), E, K⟩ ∧
      LocatedAt g m ⟨.inl (.While c b), E, K⟩ := by
  suffices h : ∀ (n' : NodeID) (E' : State) (K_full : List Cont)
      (_ : KontMatches g K_full n' E')
      (c' : Expr) (b' : Stmt) (K' : List Cont),
      K_full = .WhileBackK c' b' :: K' ->
      g.nodeKind n' = some .Skip ->
      ∀ (h_n' : n' < g.nodes.length),
        ∃ (m : NodeID) (h_m : m < g.nodes.length),
          StepsN g h_n' ⟨.inl .Skip, E', .WhileBackK c' b' :: K'⟩ h_m
              ⟨.inl (.While c' b'), E', K'⟩ ∧
          LocatedAt g m ⟨.inl (.While c' b'), E', K'⟩ from
    h n E _ hkm c b K rfl hk hn
  intro n' E' K_full hkm'
  induction hkm' using KontMatches.rec
    (motive_1 := fun _ _ _ => True) with
  | whileBackK hedge hloc =>
    intro c' b' K' h_eq hk_n' h_n'
    cases h_eq
    have h_m := hloc.bound
    refine ⟨_, h_m, ?_, hloc⟩
    exact .single h_n' h_m (.advance h_n' h_m .WhileD hk_n' hedge rfl)
  | @skipBridge _ m_b _ _ hk_n_skip hk_m_skip hedge _ ih =>
    intro c' b' K' h_eq hk_n' h_n'
    have h_m_bound : m_b < g.nodes.length := nodeKind_lt hk_m_skip
    obtain ⟨m, h_m, hsteps_inner, hloc_m⟩ :=
      ih c' b' K' h_eq hk_m_skip h_m_bound
    refine ⟨m, h_m, ?_, hloc_m⟩
    exact .skipBridge h_n' h_m_bound h_m hk_n' hedge hsteps_inner
  | _ => grind

/-- The main `step_decorate` theorem: every `Step σ σ'` from a state
    `LocatedAt g n σ` lifts to a decorated `StepsN` (a chain of `StepN`s,
    with optional `skipBridge` lifts across merge `Skip` nodes), together
    with a new `LocatedAt` for `σ'`. The chain has at most one
    underlying `Step` per CEK transition; bridges contribute zero. -/
theorem step_decorate {g : CFG} {n : NodeID} {σ σ' : CEK}
    (hloc : LocatedAt g n σ) (hstep : Step σ σ') :
    ∃ (n' : NodeID) (h : n < g.nodes.length) (h' : n' < g.nodes.length),
      StepsN g h σ h' σ' ∧ LocatedAt g n' σ' := by
  have hn : n < g.nodes.length := hloc.bound
  cases hstep with
  | @Decl x e E K =>
    -- ⟨inl (Decl x e), E, K⟩ -> ⟨inr e, E, DeclK x :: K⟩
    cases hloc with
    | at_decl hk hev hedge hskip hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn .Decl rfl)
      · exact .of_inr_decl (K_b := []) (e_orig := e) (v_orig := _)
          hk .nil hev ⟨_, hev, .nil⟩ hedge hskip hkm
  | @Assign x e E K =>
    cases hloc with
    | at_assign hk hev hedge hskip hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn .Assign rfl)
      · exact .of_inr_assign (K_b := []) (e_orig := e) (v_orig := _)
          hk .nil hev ⟨_, hev, .nil⟩ hedge hskip hkm
  | @DeclD nv E x K =>
    -- ⟨inr (Int nv), E, DeclK x :: K⟩ -> ⟨inl Skip, E.updated x (Int nv), K⟩
    -- Generalise the rigid `DeclK x :: K` in `hloc`'s index so dependent
    -- elimination of `cases hloc` unifies against a plain variable `K_full`.
    -- The list-shape obligation `K_b = []` is then discharged via
    -- `nil_of_declK` on the explicit equation `hKeq.symm`.
    generalize hKeq : (Cont.DeclK x :: K : List Cont) = K_full at hloc
    cases hloc with
    | @of_inr_decl _ _ _ _ _ _ _ K_b K_out hk hbf hev_orig hp hedge hskip hkm =>
      cases hbf with
      | nil =>
        simp only [List.nil_append] at hKeq
        cases hKeq
        have hv : (_ : Val) = .Int nv := pending_int_nil hp
        have hm : _ < g.nodes.length := nodeKind_lt hskip
        refine ⟨_, hn, hm, ?_, ?_⟩
        · refine .single hn hm (.mutate hn hm x _ (.Int nv) .DeclD (Or.inr hk) ?_ ⟨_, hedge⟩ rfl)
          have := hev_orig
          rw [hv] at this
          exact this
        · exact .at_skip hskip (hv ▸ hkm)
      | binOpL _
      | binOpR _ => simp at hKeq
    | @of_inr_assign _ _ _ _ _ _ _ _ _ _ hbf _ _ _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_if _ _ _ _ _ _ _ _ _ _ hbf _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_while _ _ _ _ _ _ _ _ _ hbf _ _ _ =>
      cases hbf <;> simp at hKeq
  | @AssignD nv E x K =>
    generalize hKeq : (Cont.AssignK x :: K : List Cont) = K_full at hloc
    cases hloc with
    | @of_inr_assign _ _ _ _ _ _ _ K_b K_out hk hbf hev_orig hp hedge hskip hkm =>
      cases hbf with
      | nil =>
        simp only [List.nil_append] at hKeq
        cases hKeq
        have hv : (_ : Val) = .Int nv := pending_int_nil hp
        have hm : _ < g.nodes.length := nodeKind_lt hskip
        refine ⟨_, hn, hm, ?_, ?_⟩
        · refine .single hn hm (.mutate hn hm x _ (.Int nv) .AssignD (Or.inl hk) ?_ ⟨_, hedge⟩ rfl)
          have := hev_orig
          rw [hv] at this
          exact this
        · exact .at_skip hskip (hv ▸ hkm)
      | binOpL _ => simp at hKeq
      | binOpR _ => simp at hKeq
    | @of_inr_decl _ _ _ _ _ _ _ _ _ _ hbf _ _ _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_if _ _ _ _ _ _ _ _ _ _ hbf _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_while _ _ _ _ _ _ _ _ _ hbf _ _ _ =>
      cases hbf <;> simp at hKeq
  | @Var E x nv K hxv =>
    -- ⟨inr (Var x), E, K⟩ -> ⟨inr (Int nv), E, K⟩, env unchanged
    cases hloc with
    | of_inr_assign hk hbf hev_orig hp hedge hskip hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn (.Var hxv) rfl)
      · refine .of_inr_assign hk hbf hev_orig ?_ hedge hskip hkm
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | var hxv' =>
          rw [hxv] at hxv'
          cases hxv'
          exact ⟨_, .int, hcont⟩
    | of_inr_decl hk hbf hev_orig hp hedge hskip hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn (.Var hxv) rfl)
      · refine .of_inr_decl hk hbf hev_orig ?_ hedge hskip hkm
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | var hxv' =>
          rw [hxv] at hxv'; cases hxv'
          exact ⟨_, .int, hcont⟩
    | of_inr_if hk hbf hev_orig hp hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn (.Var hxv) rfl)
      · refine .of_inr_if hk hbf hev_orig ?_ hkm
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | var hxv' => rw [hxv] at hxv'; cases hxv'; exact ⟨_, .int, hcont⟩
    | of_inr_while hk hbf hev_orig hp hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn (.Var hxv) rfl)
      · refine .of_inr_while hk hbf hev_orig ?_ hkm
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | var hxv' => rw [hxv] at hxv'; cases hxv'; exact ⟨_, .int, hcont⟩
  | @BinOpL o e₁ e₂ E K =>
    -- ⟨inr (BinOp o e₁ e₂), E, K⟩ -> ⟨inr e₁, E, BinOpLK o e₂ :: K⟩
    cases hloc with
    | of_inr_assign hk hbf hev_orig hp hedge hskip hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn .BinOpL rfl)
      · rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | binop hev1 hev2 =>
          rename_i n₁ n₂
          refine .of_inr_assign hk (.binOpL hbf) hev_orig
            ⟨.Int n₁, hev1, .binOpL hev2 hcont⟩ hedge hskip hkm
    | of_inr_decl hk hbf hev_orig hp hedge hskip hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn .BinOpL rfl)
      · rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | binop hev1 hev2 =>
          rename_i n₁ n₂
          refine .of_inr_decl hk (.binOpL hbf) hev_orig
            ⟨.Int n₁, hev1, .binOpL hev2 hcont⟩ hedge hskip hkm
    | of_inr_if hk hbf hev_orig hp hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn .BinOpL rfl)
      · rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | binop hev1 hev2 =>
          rename_i n₁ n₂
          refine .of_inr_if hk (.binOpL hbf) hev_orig
            ⟨.Int n₁, hev1, .binOpL hev2 hcont⟩ hkm
    | of_inr_while hk hbf hev_orig hp hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn .BinOpL rfl)
      · rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | binop hev1 hev2 =>
          rename_i n₁ n₂
          refine .of_inr_while hk (.binOpL hbf) hev_orig
            ⟨.Int n₁, hev1, .binOpL hev2 hcont⟩ hkm
  | @BinOpR n₁ E o e₂ K =>
    -- ⟨inr (Int n₁), E, BinOpLK o e₂ :: K⟩ -> ⟨inr e₂, E, BinOpRK (Int n₁) o :: K⟩
    -- σ.K = BinOpLK o e₂ :: K. In `of_inr_*`, σ.K = K_b ++ frame :: K_out where
    -- frame ≠ BinOpLK; with `OnlyBinopFrames K_b`, this forces
    -- K_b = .BinOpLK o e₂ :: K_b'.
    generalize hKeq : (Cont.BinOpLK o e₂ :: K : List Cont) = K_full at hloc
    cases hloc with
    | @of_inr_assign _ _ _ _ _ _ _ K_b K_out hk hbf hev_orig hp hedge hskip hkm =>
      cases hbf with
      | nil => simp at hKeq
      | binOpR _ => simp at hKeq
      | @binOpL o' e₂' K_b' hbf' =>
        simp only [List.cons_append] at hKeq
        cases hKeq
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | int =>
          cases hcont with
          | @binOpL _ _ _ _ n₂ _ hev2 hcont' =>
            refine ⟨n, hn, hn, ?_, ?_⟩
            · exact .single hn hn (.stutter hn .BinOpR rfl)
            · refine .of_inr_assign (K_b := .BinOpRK (.Int n₁) o :: K_b')
                hk (.binOpR hbf') hev_orig ?_ hedge hskip hkm
              exact ⟨.Int n₂, hev2, .binOpR hcont'⟩
    | @of_inr_decl _ _ _ _ _ _ _ K_b K_out hk hbf hev_orig hp hedge hskip hkm =>
      cases hbf with
      | nil => simp at hKeq
      | binOpR _ => simp at hKeq
      | @binOpL o' e₂' K_b' hbf' =>
        simp only [List.cons_append] at hKeq
        cases hKeq
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | int =>
          cases hcont with
          | @binOpL _ _ _ _ n₂ _ hev2 hcont' =>
            refine ⟨n, hn, hn, ?_, ?_⟩
            · exact .single hn hn (.stutter hn .BinOpR rfl)
            · refine .of_inr_decl (K_b := .BinOpRK (.Int n₁) o :: K_b')
                hk (.binOpR hbf') hev_orig ?_ hedge hskip hkm
              exact ⟨.Int n₂, hev2, .binOpR hcont'⟩
    | @of_inr_if _ _ _ _ _ _ _ K_b K_out hk hbf hev_orig hp hkm =>
      cases hbf with
      | nil => simp at hKeq
      | binOpR _ => simp at hKeq
      | @binOpL o' e₂' K_b' hbf' =>
        simp only [List.cons_append] at hKeq
        cases hKeq
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | int =>
          cases hcont with
          | @binOpL _ _ _ _ n₂ _ hev2 hcont' =>
            refine ⟨n, hn, hn, ?_, ?_⟩
            · exact .single hn hn (.stutter hn .BinOpR rfl)
            · refine .of_inr_if (K_b := .BinOpRK (.Int n₁) o :: K_b')
                hk (.binOpR hbf') hev_orig ?_ hkm
              exact ⟨.Int n₂, hev2, .binOpR hcont'⟩
    | @of_inr_while _ _ _ _ _ _ K_b K_out hk hbf hev_orig hp hkm =>
      cases hbf with
      | nil => simp at hKeq
      | binOpR _ => simp at hKeq
      | @binOpL o' e₂' K_b' hbf' =>
        simp only [List.cons_append] at hKeq
        cases hKeq
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | int =>
          cases hcont with
          | @binOpL _ _ _ _ n₂ _ hev2 hcont' =>
            refine ⟨n, hn, hn, ?_, ?_⟩
            · exact .single hn hn (.stutter hn .BinOpR rfl)
            · refine .of_inr_while (K_b := .BinOpRK (.Int n₁) o :: K_b')
                hk (.binOpR hbf') hev_orig ?_ hkm
              exact ⟨.Int n₂, hev2, .binOpR hcont'⟩
  | @BinOpD n₂ E n₁ o K =>
    -- ⟨inr (Int n₂), E, BinOpRK (Int n₁) o :: K⟩ -> ⟨inr (Int (applyOp o n₁ n₂)), E, K⟩
    -- K_b head = BinOpRK ⇒ peel; new K_b' is the tail.
    generalize hKeq : (Cont.BinOpRK (Val.Int n₁) o :: K : List Cont) = K_full at hloc
    cases hloc with
    | @of_inr_assign _ _ _ _ _ _ _ K_b K_out hk hbf hev_orig hp hedge hskip hkm =>
      cases hbf with
      | nil => simp at hKeq
      | binOpL _ => simp at hKeq
      | @binOpR v' o' K_b' hbf' =>
        simp only [List.cons_append] at hKeq
        cases hKeq
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | int =>
          cases hcont with
          | binOpR hcont' =>
            refine ⟨n, hn, hn, ?_, ?_⟩
            · exact .single hn hn (.stutter hn .BinOpD rfl)
            · refine .of_inr_assign hk hbf' hev_orig ?_ hedge hskip hkm
              exact ⟨_, .int, hcont'⟩
    | @of_inr_decl _ _ _ _ _ _ _ K_b K_out hk hbf hev_orig hp hedge hskip hkm =>
      cases hbf with
      | nil => simp at hKeq
      | binOpL _ => simp at hKeq
      | @binOpR v' o' K_b' hbf' =>
        simp only [List.cons_append] at hKeq
        cases hKeq
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | int =>
          cases hcont with
          | binOpR hcont' =>
            refine ⟨n, hn, hn, ?_, ?_⟩
            · exact .single hn hn (.stutter hn .BinOpD rfl)
            · refine .of_inr_decl hk hbf' hev_orig ?_ hedge hskip hkm
              exact ⟨_, .int, hcont'⟩
    | @of_inr_if _ _ _ _ _ _ _ K_b K_out hk hbf hev_orig hp hkm =>
      cases hbf with
      | nil => simp at hKeq
      | binOpL _ => simp at hKeq
      | @binOpR v' o' K_b' hbf' =>
        simp only [List.cons_append] at hKeq
        cases hKeq
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | int =>
          cases hcont with
          | binOpR hcont' =>
            refine ⟨n, hn, hn, ?_, ?_⟩
            · exact .single hn hn (.stutter hn .BinOpD rfl)
            · refine .of_inr_if hk hbf' hev_orig ?_ hkm
              exact ⟨_, .int, hcont'⟩
    | @of_inr_while _ _ _ _ _ _ K_b K_out hk hbf hev_orig hp hkm =>
      cases hbf with
      | nil => simp at hKeq
      | binOpL _ => simp at hKeq
      | @binOpR v' o' K_b' hbf' =>
        simp only [List.cons_append] at hKeq
        cases hKeq
        rcases hp with ⟨vi, hev, hcont⟩
        cases hev with
        | int =>
          cases hcont with
          | binOpR hcont' =>
            refine ⟨n, hn, hn, ?_, ?_⟩
            · exact .single hn hn (.stutter hn .BinOpD rfl)
            · refine .of_inr_while hk hbf' hev_orig ?_ hkm
              exact ⟨_, .int, hcont'⟩
  | @IfC c t f E K =>
    cases hloc with
    | at_if hk hev hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn .IfC rfl)
      · exact .of_inr_if (K_b := []) (c_orig := c) (v_orig := _)
          hk .nil hev ⟨_, hev, .nil⟩ hkm
  | @IfT nv E t f K hne =>
    generalize hKeq : (Cont.IfK t f :: K : List Cont) = K_full at hloc
    cases hloc with
    | @of_inr_if _ c_orig _ _ _ _ _ K_b K_out hk hbf hev_orig hp hkm =>
      cases hbf with
      | nil =>
        simp only [List.nil_append] at hKeq
        cases hKeq
        have hv : (_ : Val) = .Int nv := pending_int_nil hp
        cases hkm with
        | @ifKT _ nT _ _ _ _ _ _ _ hedgeT hT _ _ =>
          have hT_bound : nT < g.nodes.length := hT.bound
          refine ⟨nT, hn, hT_bound, ?_, hT⟩
          refine .single hn hT_bound (.branch hn hT_bound _ .TBranch (.Int nv) (.IfT hne)
            hk hedgeT ?_ ?_ rfl)
          · rw [hv] at hev_orig; exact hev_orig
          · simp [BranchTaken, hne]
        | @ifKF _ _ _ _ _ _ c_kont hkind _ _ hev_kont =>
          exfalso
          have heq_c : c_orig = c_kont := by
            have h := hk.symm.trans hkind
            cases h; rfl
          rw [hv] at hev_orig
          rw [heq_c] at hev_orig
          have hzero := evalExpr_det hev_orig hev_kont
          exact hne (by injection hzero)
        | @skipBridge _ _ _ _ hk_skip _ _ _ =>
          exfalso; rw [hk] at hk_skip; cases hk_skip
      | binOpL _ => simp at hKeq
      | binOpR _ => simp at hKeq
    | @of_inr_assign _ _ _ _ _ _ _ _ _ _ hbf _ _ _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_decl _ _ _ _ _ _ _ _ _ _ hbf _ _ _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_while _ _ _ _ _ _ _ _ _ hbf _ _ _ =>
      cases hbf <;> simp at hKeq
  | @IfF E t f K =>
    generalize hKeq : (Cont.IfK t f :: K : List Cont) = K_full at hloc
    cases hloc with
    | @of_inr_if _ c_orig _ _ _ _ _ K_b K_out hk hbf hev_orig hp hkm =>
      cases hbf with
      | nil =>
        simp only [List.nil_append] at hKeq
        cases hKeq
        have hv : (_ : Val) = .Int 0 := pending_int_nil hp
        cases hkm with
        | @ifKF _ nF _ _ _ _ _ _ hedgeF hF _ =>
          have hF_bound : nF < g.nodes.length := hF.bound
          refine ⟨nF, hn, hF_bound, ?_, hF⟩
          refine .single hn hF_bound (.branch hn hF_bound _ .FBranch (.Int 0) .IfF
            hk hedgeF ?_ ?_ rfl)
          · rw [hv] at hev_orig; exact hev_orig
          · simp [BranchTaken]
        | @ifKT _ _ _ _ _ _ c_kont _ hkind _ _ hev_kont hne_kont =>
          exfalso
          have heq_c : c_orig = c_kont := by
            have h := hk.symm.trans hkind
            cases h; rfl
          rw [hv] at hev_orig
          rw [heq_c] at hev_orig
          have hzero := evalExpr_det hev_orig hev_kont
          exact hne_kont hzero.symm
        | @skipBridge _ _ _ _ hk_skip _ _ _ =>
          exfalso; rw [hk] at hk_skip; cases hk_skip
      | binOpL _ => simp at hKeq
      | binOpR _ => simp at hKeq
    | @of_inr_assign _ _ _ _ _ _ _ _ _ _ hbf _ _ _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_decl _ _ _ _ _ _ _ _ _ _ hbf _ _ _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_while _ _ _ _ _ _ _ _ _ hbf _ _ _ =>
      cases hbf <;> simp at hKeq
  | @WhileC c b E K =>
    cases hloc with
    | at_while hk hev hkm =>
      refine ⟨n, hn, hn, ?_, ?_⟩
      · exact .single hn hn (.stutter hn .WhileC rfl)
      · exact .of_inr_while (K_b := []) (c_orig := c) (v_orig := _)
          hk .nil hev ⟨_, hev, .nil⟩ hkm
  | @WhileT nv E c b K hne =>
    generalize hKeq : (Cont.WhileK c b :: K : List Cont) = K_full at hloc
    cases hloc with
    | @of_inr_while _ _ _ _ _ _ _ _ hk hbf hev_orig hp hkm =>
      cases hbf with
      | nil =>
        simp only [List.nil_append] at hKeq
        cases hKeq
        have hv : (_ : Val) = .Int nv := pending_int_nil hp
        cases hkm with
        | @whileKT _ nT _ _ _ _ _ hedgeT hT _ _ =>
          have hT_bound : nT < g.nodes.length := hT.bound
          refine ⟨nT, hn, hT_bound, ?_, hT⟩
          refine .single hn hT_bound (.branch hn hT_bound _ .TBranch (.Int nv) (.WhileT hne)
            hk hedgeT ?_ ?_ rfl)
          · rw [hv] at hev_orig; exact hev_orig
          · simp [BranchTaken, hne]
        | @whileKF _ _ _ _ _ _ _ _ hev_kont =>
          exfalso
          rw [hv] at hev_orig
          have hzero := evalExpr_det hev_orig hev_kont
          exact hne (by injection hzero)
        | @skipBridge _ _ _ _ hk_skip _ _ _ =>
          exfalso; rw [hk] at hk_skip; cases hk_skip
      | binOpL _ => simp at hKeq
      | binOpR _ => simp at hKeq
    | @of_inr_assign _ _ _ _ _ _ _ _ _ _ hbf _ _ _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_decl _ _ _ _ _ _ _ _ _ _ hbf _ _ _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_if _ _ _ _ _ _ _ _ _ _ hbf _ _ _ =>
      cases hbf <;> simp at hKeq
  | @WhileF E c b K =>
    generalize hKeq : (Cont.WhileK c b :: K : List Cont) = K_full at hloc
    cases hloc with
    | @of_inr_while _ _ _ _ _ _ _ _ hk hbf hev_orig hp hkm =>
      cases hbf with
      | nil =>
        simp only [List.nil_append] at hKeq
        cases hKeq
        have hv : (_ : Val) = .Int 0 := pending_int_nil hp
        cases hkm with
        | @whileKF _ nF _ _ _ _ hedgeF hF _ =>
          have hF_bound : nF < g.nodes.length := hF.bound
          refine ⟨nF, hn, hF_bound, ?_, hF⟩
          refine .single hn hF_bound (.branch hn hF_bound _ .FBranch (.Int 0) .WhileF
            hk hedgeF ?_ ?_ rfl)
          · rw [hv] at hev_orig; exact hev_orig
          · simp [BranchTaken]
        | @whileKT _ _ _ _ _ _ _ _ _ hev_kont hne_kont =>
          exfalso
          rw [hv] at hev_orig
          have hzero := evalExpr_det hev_orig hev_kont
          exact hne_kont hzero.symm
        | @skipBridge _ _ _ _ hk_skip _ _ _ =>
          exfalso; rw [hk] at hk_skip; cases hk_skip
      | binOpL _ => simp at hKeq
      | binOpR _ => simp at hKeq
    | @of_inr_assign _ _ _ _ _ _ _ _ _ _ hbf _ _ _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_decl _ _ _ _ _ _ _ _ _ _ hbf _ _ _ _ _ =>
      cases hbf <;> simp at hKeq
    | @of_inr_if _ _ _ _ _ _ _ _ _ _ hbf _ _ _ =>
      cases hbf <;> simp at hKeq
  | @WhileD E c b K =>
    -- ⟨inl Skip, E, WhileBackK c b :: K⟩ -> ⟨inl (While c b), E, K⟩
    cases hloc with
    | at_skip hk hkm =>
      obtain ⟨m, h_m, hsteps, hloc'⟩ := stepsN_whileD_chain hn hk hkm
      exact ⟨m, hn, h_m, hsteps, hloc'⟩
  | @SeqEnter s₁ s₂ E K =>
    cases hloc with
    | at_seq hloc' =>
      refine ⟨n, hn, hn, ?_, hloc'⟩
      exact .single hn hn (.stutter hn .SeqEnter rfl)
  | @SeqMid E s₂ K =>
    cases hloc with
    | at_skip hk hkm =>
      obtain ⟨m, h_m, hsteps, hloc'⟩ := stepsN_seqMid_chain hn hk hkm
      exact ⟨m, hn, h_m, hsteps, hloc'⟩

/-! ## `cek_refines_cfg` — multi-step lift

`step_decorate` lifts a single `Step` from a `LocatedAt`-matched state to
a `StepN`. Iterating it along `Steps` yields the forward simulation
`cek_refines_cfg`: the entire CEK derivation `σ ⟶* σ'` reflects into a
decorated `StepsN` derivation in the CFG, terminating at some node `n'`
where the post-state `σ'` is again `LocatedAt`-matched.
-/

theorem cek_refines_cfg {g : CFG} {n : NodeID} {σ σ' : CEK}
    (hloc : LocatedAt g n σ) (hsteps : Steps σ σ') :
    ∃ (n' : NodeID) (h : n < g.nodes.length) (h' : n' < g.nodes.length),
      StepsN g h σ h' σ' ∧ LocatedAt g n' σ' := by
  induction hsteps generalizing n with
  | refl =>
    exact ⟨n, hloc.bound, hloc.bound, .refl hloc.bound _, hloc⟩
  | step hstep _ ih =>
    obtain ⟨n₁, hn, h₁, hsn, hloc₁⟩ := step_decorate hloc hstep
    obtain ⟨n', _, h', hsns, hloc'⟩ := ih hloc₁
    exact ⟨n', hn, h', hsn.trans hsns, hloc'⟩

/-! ## Monotonicity along `SubCFG`

If `g₁ ⊆ g₂` (in the `SubCFG` sense produced by every `BuildSpec`),
every `LocatedAt g₁ …` lifts to `LocatedAt g₂ …` and likewise for
`KontMatches`. Used by `LocatedAt.of_buildSpec` to compose IHs from
sub-builds — each sub-build's CFG is a structural prefix of the outer
build's CFG, so its `LocatedAt`/`KontMatches` witnesses transport. -/

/-- Weakening for `LocatedAt` along `SubCFG`, proved via the *mutual*
    recursor of `LocatedAt`/`KontMatches`. The companion motive on
    `KontMatches` is the corresponding `KontMatches`-weakening goal —
    a non-trivial "always solve the kont side too" branch — which lets
    us invoke the mutual induction principle in one shot and avoids
    having to ship a `termination_by` measure for the recursive calls
    across the mutual block (sizeOf is 0 on Props, so the previous
    `termination_by sizeOf h` could not decrease). Mirrors the trick
    used in `LocatedAt.bound`. -/
theorem LocatedAt.weaken {g₁ g₂ : CFG} (hsub : SubCFG g₁ g₂)
    {n : NodeID} {σ : CEK} (h : LocatedAt g₁ n σ) : LocatedAt g₂ n σ := by
  induction h using LocatedAt.rec
    (motive_2 := fun K n E _ => KontMatches g₂ K n E) with
  | at_skip hk _ ih_km =>
    exact .at_skip (hsub.nodeKind (nodeKind_lt hk) ▸ hk) ih_km
  | at_assign hk hev hedge hskip _ ih_km =>
    exact .at_assign (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hev
      (hsub.hasEdge hedge) (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | at_decl hk hev hedge hskip _ ih_km =>
    exact .at_decl (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hev
      (hsub.hasEdge hedge) (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | at_if hk hev _ ih_km =>
    exact .at_if (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hev ih_km
  | at_while hk hev _ ih_km =>
    exact .at_while (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hev ih_km
  | at_seq _ ih => exact .at_seq ih
  | of_inr_assign hk hbf hev hp hedge hskip _ ih_km =>
    exact .of_inr_assign (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hbf hev hp
      (hsub.hasEdge hedge) (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | of_inr_decl hk hbf hev hp hedge hskip _ ih_km =>
    exact .of_inr_decl (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hbf hev hp
      (hsub.hasEdge hedge) (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | of_inr_if hk hbf hev hp _ ih_km =>
    exact .of_inr_if (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hbf hev hp ih_km
  | of_inr_while hk hbf hev hp _ ih_km =>
    exact .of_inr_while (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hbf hev hp ih_km
  -- `KontMatches` companion arms (motive_2): each must produce the
  -- corresponding weakened `KontMatches g₂ …`.
  | nil => exact .nil
  | seqK hedge _ ih => exact .seqK (hsub.hasEdge hedge) ih
  | assignK hedge hskip _ ih_km =>
    exact .assignK (hsub.hasEdge hedge)
      (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | declK hedge hskip _ ih_km =>
    exact .declK (hsub.hasEdge hedge)
      (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | ifKT hkind hedgeT _ hev hne ihT =>
    exact .ifKT (hsub.nodeKind (nodeKind_lt hkind) ▸ hkind)
      (hsub.hasEdge hedgeT) ihT hev hne
  | ifKF hkind hedgeF _ hev ihF =>
    exact .ifKF (hsub.nodeKind (nodeKind_lt hkind) ▸ hkind)
      (hsub.hasEdge hedgeF) ihF hev
  | whileKT hedgeT _ hev hne ihT =>
    exact .whileKT (hsub.hasEdge hedgeT) ihT hev hne
  | whileKF hedgeF _ hev ihF =>
    exact .whileKF (hsub.hasEdge hedgeF) ihF hev
  | whileBackK hedge _ ih => exact .whileBackK (hsub.hasEdge hedge) ih
  | skipBridge hk hk_dst hedge _ ih_km =>
    exact .skipBridge (hsub.nodeKind (nodeKind_lt hk) ▸ hk)
      (hsub.nodeKind (nodeKind_lt hk_dst) ▸ hk_dst)
      (hsub.hasEdge hedge) ih_km
  | binOpLK _ ih => exact .binOpLK ih
  | binOpRK _ ih => exact .binOpRK ih

/-- Weakening for `KontMatches` along `SubCFG`, proved by the same
    dual-motive recursor trick (with `motive_1` doing the `LocatedAt`
    side). -/
theorem KontMatches.weaken {g₁ g₂ : CFG} (hsub : SubCFG g₁ g₂)
    {K : List Cont} {n : NodeID} {E : State}
    (h : KontMatches g₁ K n E) : KontMatches g₂ K n E := by
  induction h using KontMatches.rec
    (motive_1 := fun n σ _ => LocatedAt g₂ n σ) with
  | at_skip hk _ ih_km =>
    exact .at_skip (hsub.nodeKind (nodeKind_lt hk) ▸ hk) ih_km
  | at_assign hk hev hedge hskip _ ih_km =>
    exact .at_assign (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hev
      (hsub.hasEdge hedge) (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | at_decl hk hev hedge hskip _ ih_km =>
    exact .at_decl (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hev
      (hsub.hasEdge hedge) (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | at_if hk hev _ ih_km =>
    exact .at_if (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hev ih_km
  | at_while hk hev _ ih_km =>
    exact .at_while (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hev ih_km
  | at_seq _ ih => exact .at_seq ih
  | of_inr_assign hk hbf hev hp hedge hskip _ ih_km =>
    exact .of_inr_assign (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hbf hev hp
      (hsub.hasEdge hedge) (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | of_inr_decl hk hbf hev hp hedge hskip _ ih_km =>
    exact .of_inr_decl (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hbf hev hp
      (hsub.hasEdge hedge) (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | of_inr_if hk hbf hev hp _ ih_km =>
    exact .of_inr_if (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hbf hev hp ih_km
  | of_inr_while hk hbf hev hp _ ih_km =>
    exact .of_inr_while (hsub.nodeKind (nodeKind_lt hk) ▸ hk) hbf hev hp ih_km
  | nil => exact .nil
  | seqK hedge _ ih => exact .seqK (hsub.hasEdge hedge) ih
  | assignK hedge hskip _ ih_km =>
    exact .assignK (hsub.hasEdge hedge)
      (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | declK hedge hskip _ ih_km =>
    exact .declK (hsub.hasEdge hedge)
      (hsub.nodeKind (nodeKind_lt hskip) ▸ hskip) ih_km
  | ifKT hkind hedgeT _ hev hne ihT =>
    exact .ifKT (hsub.nodeKind (nodeKind_lt hkind) ▸ hkind)
      (hsub.hasEdge hedgeT) ihT hev hne
  | ifKF hkind hedgeF _ hev ihF =>
    exact .ifKF (hsub.nodeKind (nodeKind_lt hkind) ▸ hkind)
      (hsub.hasEdge hedgeF) ihF hev
  | whileKT hedgeT _ hev hne ihT =>
    exact .whileKT (hsub.hasEdge hedgeT) ihT hev hne
  | whileKF hedgeF _ hev ihF =>
    exact .whileKF (hsub.hasEdge hedgeF) ihF hev
  | whileBackK hedge _ ih => exact .whileBackK (hsub.hasEdge hedge) ih
  | skipBridge hk hk_dst hedge _ ih_km =>
    exact .skipBridge (hsub.nodeKind (nodeKind_lt hk) ▸ hk)
      (hsub.nodeKind (nodeKind_lt hk_dst) ▸ hk_dst)
      (hsub.hasEdge hedge) ih_km
  | binOpLK _ ih => exact .binOpLK ih
  | binOpRK _ ih => exact .binOpRK ih

/-! ## `LocatedAt.of_buildSpec`

The bridging entry-side lemma: for every CFG built by `BuildSpec b s b' en ex`,
every CEK execution that *terminates* (witnessed by `BigStep s E E'`)
starts from a `LocatedAt`-matched state at the entry node `en`, **provided
the outer continuation `K_out` is itself `KontMatches`-matched at the
exit node `ex` under the post-execution environment `E'`**.

Composing this with `cek_refines_cfg` yields a genuinely end-to-end
soundness statement: a post-fixpoint at the entry implies the analysis
fact along *every* CEK execution of the source program.

The proof is by induction on `BuildSpec`. The key generalisation:
the conclusion is universally quantified over the larger ambient CFG
`g`, of which `b'.cfg` is a prefix (witnessed by `SubCFG`). This lets
the `seq`/`if`/`while` cases compose IHs whose sub-builds live in
intermediate builders' CFGs. -/

namespace LocatedAt

theorem of_buildSpec
    {g : CFG} {b s b' en ex} (hwf : BuilderInv b)
    (hbs : BuildSpec b s b' en ex) (hsub : SubCFG b'.cfg g)
    {E E' : State} (hbig : BigStep s E E')
    {K_out : List Cont}
    (hkm : KontMatches g K_out ex E') :
    LocatedAt g en ⟨.inl s, E, K_out⟩ := by
  induction hbs generalizing K_out E E' with
  | skip b' =>
    cases hbig
    refine at_skip ?_ hkm
    unfold BuilderInv at hwf
    have := SubCFG.nodeKind (n := b'.nextID) hsub (by {
      simp [hwf]
    })
    grind [BuildSpec.skip_nodeKind b' hwf]
  | assign b' x e =>
    cases hbig
    case assign v heval =>
    refine at_assign ?_ heval ?_ ?_ hkm
    · have := BuildSpec.assign_kind_at_entry x e hwf
      have := SubCFG.nodeKind (n := b'.nextID) hsub (by {
        unfold BuilderInv at hwf
        simp [CFGBuilder.addNode, hwf]
      })
      grind
    · exact SubCFG.hasEdge hsub (BuildSpec.assign_normal_edge x e)
    · have := BuildSpec.assign_skip_kind_at_exit x e hwf
      have := SubCFG.nodeKind (n := b'.nextID + 1) hsub (by {
        unfold BuilderInv at hwf
        simp [CFGBuilder.addNode, hwf]
      })
      grind
  | decl b' x e =>
    cases hbig
    case decl v heval =>
    refine at_decl ?_ heval ?_ ?_ hkm
    · have := BuildSpec.decl_kind_at_entry x e hwf
      have := SubCFG.nodeKind (n := b'.nextID) hsub (by {
        unfold BuilderInv at hwf
        simp [CFGBuilder.addNode, hwf]
      })
      grind
    · exact SubCFG.hasEdge hsub (BuildSpec.assign_normal_edge x e)
    · have := BuildSpec.decl_skip_kind_at_exit x e hwf
      have := SubCFG.nodeKind (n := b'.nextID + 1) hsub (by {
        unfold BuilderInv at hwf
        simp [CFGBuilder.addNode, hwf]
      })
      grind
  | @seq b₁ b₂ b₃ s₁ s₂ en₁ ex₁ en₂ ex₂ h₁ h₂ ih₁ ih₂ =>
    cases hbig
    case seq E'' hE'' hE' =>
    refine at_seq ?_
    refine ih₁ hwf ?_ hE'' ?_
    · refine SubCFG.trans (SubCFG.of_buildSpec h₂) ?_
      refine SubCFG.trans ?_ hsub
      grind [SubCFG.of_addEdge]
    · apply KontMatches.seqK
      · refine SubCFG.hasEdge (dst := en₂)  hsub ?_
        apply BuildSpec.seq_normal_edge h₁ h₂
      · apply ih₂ (BuildSpec.preserves_WF h₁ hwf)
        · refine SubCFG.trans (SubCFG.of_addEdge b₃ ex₁ en₂ .Normal) hsub
        · exact hE'
        · exact hkm
  | @if_ b₁ b₂ b₃ c t f ent ext enf exf h₁ h₂ ih₁ ih₂ =>
    -- Common: builder well-formedness for the sub-builds and the
    -- ambient-`g` `nodeKind`/edge witnesses.
    have hwf_cond : BuilderInv (b₁.addNode (.Cond c)).fst := BuilderInv.addNode hwf _
    have hwf_b₂ : BuilderInv b₂ := BuildSpec.preserves_WF h₁ hwf_cond
    have hwf_b₃ : BuilderInv b₃ := BuildSpec.preserves_WF h₂ hwf_b₂
    -- nodeKind for the Cond node, lifted through each builder up to `g`.
    have hcond0 :
        ((b₁.addNode (.Cond c)).fst).cfg.nodeKind b₁.nextID = some (.Cond c) := by
      unfold BuilderInv at hwf
      simp [CFG.nodeKind, CFGBuilder.addNode, hwf]
    have hb₁ : b₁.nextID < ((b₁.addNode (.Cond c)).fst).cfg.nodes.length :=
      nodeKind_lt hcond0
    have hcond1 : b₂.cfg.nodeKind b₁.nextID = some (.Cond c) := by
      simpa [hcond0] using BuildSpec.preserves_nodeKind h₁ hb₁
    have hb₂ : b₁.nextID < b₂.cfg.nodes.length := nodeKind_lt hcond1
    have hcond2 : b₃.cfg.nodeKind b₁.nextID = some (.Cond c) := by
      simpa [hcond1] using BuildSpec.preserves_nodeKind h₂ hb₂
    have hb₃ : b₁.nextID < b₃.cfg.nodes.length := nodeKind_lt hcond2
    -- nodeKind for the Cond node in the *final* builder (after merge Skip
    -- and the four edges).
    have hcondF :
        (let b₃_1 := (b₃.addNode NodeKind.Skip).fst;
         (((b₃_1.addEdge b₁.nextID ent EdgeKind.TBranch).addEdge
             b₁.nextID enf EdgeKind.FBranch).addEdge
             ext b₃.nextID EdgeKind.Normal).addEdge
             exf b₃.nextID EdgeKind.Normal).cfg.nodeKind b₁.nextID
          = some (.Cond c) := by
      have := List.getElem?_append_left (l₂ := [NodeKind.Skip]) hb₃
      simpa [CFG.nodeKind, this] using hcond2
    have hboundF := nodeKind_lt hcondF
    have hCond_g : g.nodeKind b₁.nextID = some (.Cond c) := by
      simpa [hcondF] using SubCFG.nodeKind hsub hboundF
    -- Edges in `g`.
    have h_edges := BuildSpec.if_edges h₁ h₂
    have hET_g : g.hasEdge b₁.nextID ent .TBranch := SubCFG.hasEdge hsub h_edges.1
    have hEF_g : g.hasEdge b₁.nextID enf .FBranch := SubCFG.hasEdge hsub h_edges.2.1
    have hExt_merge_g : g.hasEdge ext b₃.nextID .Normal :=
      SubCFG.hasEdge hsub h_edges.2.2.1
    have hExf_merge_g : g.hasEdge exf b₃.nextID .Normal :=
      SubCFG.hasEdge hsub h_edges.2.2.2
    -- nodeKind = Skip for the merge node `b₃.nextID` in `g`.
    have hMerge_addNode :
        (b₃.addNode NodeKind.Skip).fst.cfg.nodeKind b₃.nextID = some .Skip := by
      unfold BuilderInv at hwf_b₃
      simp [CFG.nodeKind, CFGBuilder.addNode, hwf_b₃]
    have hMerge_F :
        (let b₃_1 := (b₃.addNode NodeKind.Skip).fst;
         (((b₃_1.addEdge b₁.nextID ent EdgeKind.TBranch).addEdge
             b₁.nextID enf EdgeKind.FBranch).addEdge
             ext b₃.nextID EdgeKind.Normal).addEdge
             exf b₃.nextID EdgeKind.Normal).cfg.nodeKind b₃.nextID
          = some .Skip := by
      simpa [CFG.nodeKind] using hMerge_addNode
    have hMergeBound := nodeKind_lt hMerge_F
    have hMerge_g : g.nodeKind b₃.nextID = some .Skip := by
      simpa [hMerge_F] using SubCFG.nodeKind hsub hMergeBound
    -- nodeKind = Skip for the t-branch's exit `ext` and f-branch's `exf`.
    have hExt_b₂ : b₂.cfg.nodeKind ext = some .Skip :=
      BuildSpec.exit_nodeKind_skip h₁ hwf_cond
    have hExt_b₃ : b₃.cfg.nodeKind ext = some .Skip := by
      have h_ext_lt : ext < b₂.cfg.nodes.length := nodeKind_lt hExt_b₂
      simpa [hExt_b₂] using BuildSpec.preserves_nodeKind h₂ h_ext_lt
    have hExf_b₃ : b₃.cfg.nodeKind exf = some .Skip :=
      BuildSpec.exit_nodeKind_skip h₂ hwf_b₂
    have hExt_g : g.nodeKind ext = some .Skip := by
      have h_ext_lt : ext < b₃.cfg.nodes.length := nodeKind_lt hExt_b₃
      have h_ext_addNode :
          (b₃.addNode NodeKind.Skip).fst.cfg.nodeKind ext = some .Skip := by
        have := List.getElem?_append_left (l₂ := [NodeKind.Skip]) h_ext_lt
        simpa [CFG.nodeKind, this] using hExt_b₃
      have h_ext_F :
          (let b₃_1 := (b₃.addNode NodeKind.Skip).fst;
           (((b₃_1.addEdge b₁.nextID ent EdgeKind.TBranch).addEdge
               b₁.nextID enf EdgeKind.FBranch).addEdge
               ext b₃.nextID EdgeKind.Normal).addEdge
               exf b₃.nextID EdgeKind.Normal).cfg.nodeKind ext
            = some .Skip := by
        simpa [CFG.nodeKind] using h_ext_addNode
      simpa [h_ext_F] using SubCFG.nodeKind hsub (nodeKind_lt h_ext_F)
    have hExf_g : g.nodeKind exf = some .Skip := by
      have h_exf_lt : exf < b₃.cfg.nodes.length := nodeKind_lt hExf_b₃
      have h_exf_addNode :
          (b₃.addNode NodeKind.Skip).fst.cfg.nodeKind exf = some .Skip := by
        have := List.getElem?_append_left (l₂ := [NodeKind.Skip]) h_exf_lt
        simpa [CFG.nodeKind, this] using hExf_b₃
      have h_exf_F :
          (let b₃_1 := (b₃.addNode NodeKind.Skip).fst;
           (((b₃_1.addEdge b₁.nextID ent EdgeKind.TBranch).addEdge
               b₁.nextID enf EdgeKind.FBranch).addEdge
               ext b₃.nextID EdgeKind.Normal).addEdge
               exf b₃.nextID EdgeKind.Normal).cfg.nodeKind exf
            = some .Skip := by
        simpa [CFG.nodeKind] using h_exf_addNode
      simpa [h_exf_F] using SubCFG.nodeKind hsub (nodeKind_lt h_exf_F)
    -- SubCFG chains: b₂.cfg ⊆ g and b₃.cfg ⊆ g.
    have hsub_b₃_g : SubCFG b₃.cfg g := by
      have h1 : SubCFG b₃.cfg (b₃.addNode .Skip).fst.cfg :=
        SubCFG.of_addNode b₃ .Skip
      let bM := (b₃.addNode .Skip).fst
      have h2 : SubCFG bM.cfg (bM.addEdge b₁.nextID ent .TBranch).cfg :=
        SubCFG.of_addEdge bM b₁.nextID ent .TBranch
      let bE1 := bM.addEdge b₁.nextID ent .TBranch
      have h3 : SubCFG bE1.cfg (bE1.addEdge b₁.nextID enf .FBranch).cfg :=
        SubCFG.of_addEdge bE1 b₁.nextID enf .FBranch
      let bE2 := bE1.addEdge b₁.nextID enf .FBranch
      have h4 : SubCFG bE2.cfg (bE2.addEdge ext b₃.nextID .Normal).cfg :=
        SubCFG.of_addEdge bE2 ext b₃.nextID .Normal
      let bE3 := bE2.addEdge ext b₃.nextID .Normal
      have h5 : SubCFG bE3.cfg (bE3.addEdge exf b₃.nextID .Normal).cfg :=
        SubCFG.of_addEdge bE3 exf b₃.nextID .Normal
      exact SubCFG.trans h1 (SubCFG.trans h2 (SubCFG.trans h3
        (SubCFG.trans h4 (SubCFG.trans h5 hsub))))
    have hsub_b₂_g : SubCFG b₂.cfg g :=
      SubCFG.trans (SubCFG.of_buildSpec h₂) hsub_b₃_g
    -- Now case-split on BigStep.
    cases hbig
    case ifT n hn heval hbig =>
      have hne_val : (Val.Int n) ≠ Val.Int 0 := fun h => hn (by injection h)
      refine at_if hCond_g heval ?_
      refine .ifKT hCond_g hET_g ?_ heval hne_val
      -- Need LocatedAt g ent ⟨inl t, E, K_out⟩.
      refine ih₁ hwf_cond hsub_b₂_g hbig ?_
      -- Need KontMatches g K_out ext E'. Bridge from merge node b₃.nextID.
      exact .skipBridge hExt_g hMerge_g hExt_merge_g hkm
    case ifF heval hbig =>
      refine at_if hCond_g heval ?_
      refine .ifKF hCond_g hEF_g ?_ heval
      refine ih₂ hwf_b₂ hsub_b₃_g hbig ?_
      exact .skipBridge hExf_g hMerge_g hExf_merge_g hkm
  | @while_ b₁ b₂ c body en_b ex_b h_b ih_b =>
    have hwf_cond : BuilderInv (b₁.addNode (.Cond c)).fst := BuilderInv.addNode hwf _
    have hwf_b₂ : BuilderInv b₂ := BuildSpec.preserves_WF h_b hwf_cond
    have hcond0 :
        ((b₁.addNode (.Cond c)).fst).cfg.nodeKind b₁.nextID = some (.Cond c) := by
      unfold BuilderInv at hwf
      simp [CFG.nodeKind, CFGBuilder.addNode, hwf]
    have hb₁ : b₁.nextID < ((b₁.addNode (.Cond c)).fst).cfg.nodes.length :=
      nodeKind_lt hcond0
    have hcond1 : b₂.cfg.nodeKind b₁.nextID = some (.Cond c) := by
      simpa [hcond0] using BuildSpec.preserves_nodeKind h_b hb₁
    have hb₂ : b₁.nextID < b₂.cfg.nodes.length := nodeKind_lt hcond1
    -- nodeKind in the final builder (after merge .Skip and 3 edges).
    have hcondF :
        (let b₂_1 := (b₂.addNode NodeKind.Skip).fst;
         ((b₂_1.addEdge b₁.nextID en_b EdgeKind.TBranch).addEdge
             ex_b b₁.nextID EdgeKind.Normal).addEdge
             b₁.nextID b₂.nextID EdgeKind.FBranch).cfg.nodeKind b₁.nextID
          = some (.Cond c) := by
      have := List.getElem?_append_left (l₂ := [NodeKind.Skip]) hb₂
      simpa [CFG.nodeKind, this] using hcond1
    have hboundF := nodeKind_lt hcondF
    have hCond_g : g.nodeKind b₁.nextID = some (.Cond c) := by
      simpa [hcondF] using SubCFG.nodeKind hsub hboundF
    have h_edges := BuildSpec.while_edges h_b
    have hET_g : g.hasEdge b₁.nextID en_b .TBranch := SubCFG.hasEdge hsub h_edges.1
    have hEN_g : g.hasEdge ex_b b₁.nextID .Normal := SubCFG.hasEdge hsub h_edges.2.1
    have hEF_g : g.hasEdge b₁.nextID b₂.nextID .FBranch :=
      SubCFG.hasEdge hsub h_edges.2.2
    -- nodeKind .Skip for the loop's F-target `b₂.nextID` in `g`.
    have hSkip_addNode :
        (b₂.addNode NodeKind.Skip).fst.cfg.nodeKind b₂.nextID = some .Skip := by
      unfold BuilderInv at hwf_b₂
      simp [CFG.nodeKind, CFGBuilder.addNode, hwf_b₂]
    have hSkip_F :
        (let b₂_1 := (b₂.addNode NodeKind.Skip).fst;
         ((b₂_1.addEdge b₁.nextID en_b EdgeKind.TBranch).addEdge
             ex_b b₁.nextID EdgeKind.Normal).addEdge
             b₁.nextID b₂.nextID EdgeKind.FBranch).cfg.nodeKind b₂.nextID
          = some .Skip := by
      simpa [CFG.nodeKind] using hSkip_addNode
    have hSkip_g : g.nodeKind b₂.nextID = some .Skip := by
      simpa [hSkip_F] using SubCFG.nodeKind hsub (nodeKind_lt hSkip_F)
    have hsub_b₂_g : SubCFG b₂.cfg g := by
      have h1 : SubCFG b₂.cfg (b₂.addNode .Skip).fst.cfg :=
        SubCFG.of_addNode b₂ .Skip
      let bM := (b₂.addNode .Skip).fst
      have h2 : SubCFG bM.cfg (bM.addEdge b₁.nextID en_b .TBranch).cfg :=
        SubCFG.of_addEdge bM b₁.nextID en_b .TBranch
      let bE1 := bM.addEdge b₁.nextID en_b .TBranch
      have h3 : SubCFG bE1.cfg (bE1.addEdge ex_b b₁.nextID .Normal).cfg :=
        SubCFG.of_addEdge bE1 ex_b b₁.nextID .Normal
      let bE2 := bE1.addEdge ex_b b₁.nextID .Normal
      have h4 : SubCFG bE2.cfg (bE2.addEdge b₁.nextID b₂.nextID .FBranch).cfg :=
        SubCFG.of_addEdge bE2 b₁.nextID b₂.nextID .FBranch
      exact SubCFG.trans h1 (SubCFG.trans h2 (SubCFG.trans h3
        (SubCFG.trans h4 hsub)))
    revert hkm
    generalize h_w_eq : (Stmt.While c body) = w_stmt at hbig
    rw [<- h_w_eq]
    induction hbig with
    | skip => cases h_w_eq
    | assign _ => cases h_w_eq
    | decl _ => cases h_w_eq
    | seq _ _ => cases h_w_eq
    | ifT _ _ _ => cases h_w_eq
    | ifF _ _ => cases h_w_eq
    | @whileT E_in E_mid E_out c' body' n hev_w hne_w hbig_b _ ih_b' ih_w =>
      cases h_w_eq
      intro hkm
      have hne_val : (Val.Int n) ≠ Val.Int 0 := fun h => hne_w (by injection h)
      refine at_while hCond_g hev_w ?_
      refine .whileKT hET_g ?_ hev_w hne_val
      refine ih_b hwf_cond hsub_b₂_g hbig_b ?_
      refine .whileBackK hEN_g ?_
      exact ih_w rfl hkm
    | whileF hev_w =>
      cases h_w_eq
      intro hkm
      refine at_while hCond_g hev_w ?_
      refine .whileKF hEF_g ?_ hev_w
      exact at_skip hSkip_g hkm

end LocatedAt

end Chartreux.Eval.Located
