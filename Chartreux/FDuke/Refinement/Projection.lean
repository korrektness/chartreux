import Chartreux.FDuke.Refinement.Summary

-- temporary
set_option linter.style.longLine false

/-!
# κ-rewrite correctness: the refinement chain

Correctness proof for the κ-shaped structural CFG emitted by `kappaEdges`.
Call returns are resolved from retained `CallGadget` metadata, while the
callee effect is replayed as an admitted chain through the caller's inline
copy. `CFG.kappa` is the structural identity view used by analyses.

The *projection* direction — every ground-truth CEK run, viewed from one
caller CFG, is an `LSteps` run under the denotational `fdukeLangSem` — is
`cek_projection`.  It is now *proved* by reduction to the strengthened
balanced invariant `balanced_project`, whose induction (over run length,
generalised over all CFGs of the family) is fully carried out here.  Both
interprocedural step cases — `balanced_project_invoke` and
`balanced_project_call` — are proved, the latter by splitting the run
(`call_body_decompose`) into the callee body run and caller tail, projecting
the tail with the induction hypothesis, projecting the callee body with the
focused crux `call_step_bpgoal`, and composing with `BPGoal.trans`.
`call_step_bpgoal` is discharged by exact gadget provenance, bounded
standalone-to-inline transport, and the callee's counting verdict.  Everything
else — the reflexive case, the three intra-procedural cases, the two
impossible return cases, and the interprocedural `invoke` case
(`balanced_project_invoke`, proved via `invoke_body_decompose` and the
strengthened `CloWF`/`KontWF` invariant) — is discharged, along with the
supporting CFG-locality (`stepsOver_same_cfg`), node-bound
(`stepsOver_inbounds`), exit-identification (`succ_nil_eq_exit`),
ghost-counter shift (`cnt_shift`), chain composition (`BPGoal.trans`,
`LamChain.key_end`), and edge plumbing.  The remaining crux still requires the
standalone→inline transport / counting-verdict machinery described in
`PLUMBING.md`.
-/

open Chartreux.Analysis Chartreux.Analysis.Generic

namespace FDuke.Refinement

open FDuke.Counting

-- # The plain-state `LangSem` on the κ-graph

/-- The store-only language semantics on the κ-graph of a caller CFG: every
    edge is structural, and a loud step is a `KappaStep` (an `IntraStep`, or
    the store-identity step of a `Call` node); bookkeeping is a stutter. -/
instance kappaLangSem (cfg : WFCFG) :
    LangSem NodeID Edge State cfg.kappa.analysis where
  LStep e σ σ' := KappaStep cfg.val e.val.src σ σ'
  LStutter _ σ σ' := σ = σ'
  IsInit c := c = State.empty

/-- Forget the ghost invocation counter from a counted κ-graph run.  This is
    the sole bridge from the counted transport stack to its store-only view:
    all standalone-to-inline transport is kept counted so the concrete number
    of lambda invocations remains available to the projection proof. -/
theorem lsteps_forget_count (cfg : WFCFG) {n n' : NodeID} {c c' : CntState}
    (hrun : LSteps (ls := countingLangSem cfg) cfg.kappa.analysis n c n' c') :
    LSteps (ls := kappaLangSem cfg) cfg.kappa.analysis n c.1 n' c'.1 := by
  induction hrun with
  | refl n c => exact .refl _ _
  | @step e n_src n'' c c₁ c' hstep htail hsrc ih =>
    rcases hstep with ⟨hκ, _⟩
    exact LSteps.step (g := cfg.kappa.analysis) (e := e) hκ ih hsrc
  | stut hstut htail ih =>
    exact .stut (congrArg Prod.fst hstut) ih

-- # Reading a verdict back on a concrete count

/-- κ = 1: a callee passing the `once` check invoked exactly once. -/
theorem count_of_once {S : Cnt} {k : Nat}
    (hv : CountVerdict .once S) (hk : S (Counting.abs k)) : k = 1 := by
  simp only [CountVerdict, Fin.isValue, ω] at hv
  obtain ⟨hz, ht, ho⟩ := hv
  cases k with
  | zero => grind [abs]
  | succ k =>
  cases k with
  | zero => grind
  | succ k => simp at hk; grind

/-- κ = +: a callee passing the `atLeast` check invoked at least once. -/
theorem count_of_atLeast {S : Cnt} {k : Nat}
    (hv : CountVerdict .atLeast S) (hk : S (Counting.abs k)) : 1 ≤ k := by
  match k with
  | 0 =>
    grind [abs, CountVerdict]
  | k + 1 => omega

/-- κ = ?: a callee passing the `atMost` check invoked at most once. -/
theorem count_of_atMost {S : Cnt} {k : Nat}
    (hv : CountVerdict .atMost S) (hk : S (Counting.abs k)) : k ≤ 1 := by
  match k with
  | 0 | 1 => omega
  | k + 2 =>
    simp [CountVerdict] at hk hv
    grind

-- # The denotational summary step

/-- The κ-admitted invocation counts: the body-iteration counts a κ contract
    allows. This is the count-side face of the gadget shapes emitted by
    `kappaEdges`: `1` crosses the inline copy exactly once (no bypass, no
    back-edge), `+` at least once (back-edge), `?` at most once (bypass),
    ε anything (`L*`: bypass *and* back-edge). -/
def κAdmits : InvKind → Nat → Prop
  | .none,    _ => True
  | .once,    k => k = 1
  | .atLeast, k => 1 ≤ k
  | .atMost,  k => k ≤ 1

/-- One inline body run: a store-only run of the *caller's own* κ-graph from
    the inline copy's entry `enL` to its exit `exL`, *followed by* `exL`'s own
    loud action. The trailing `KappaStep` is part of the unit because an
    `LSteps` run ends *at* `exL` without performing its action — that action
    fires when leaving `exL` across a gadget edge (`exL → r` to exit the
    site, `exL → enL` along a back-edge), which is exactly how `chain_replay`
    discharges it. This is the unit the summary step iterates — no standalone
    lam CFG, no CEK environments: the lambda body has exactly one relevant
    copy, the inlined one. -/
def InlineBodyRun (cfg : WFCFG) (enL exL : NodeID) (σ σ' : State) : Prop :=
  ∃ σm, LSteps (ls := kappaLangSem cfg) cfg.kappa.analysis enL σ exL σm ∧
    KappaStep cfg.val exL σm σ'

/-- Store-only specialization of the shared indexed body-run chain. -/
abbrev InlineChain (cfg : WFCFG) (enL exL : NodeID) :=
  IndexedChain (InlineBodyRun cfg enL exL)

/-- The counted form of `InlineBodyRun`.  It keeps the ghost invocation
    counter through both the body path and the action at the inline exit. -/
def CntInlineBodyRun (cfg : WFCFG) (enL exL : NodeID)
    (c c' : CntState) : Prop :=
  ∃ cm, LSteps (ls := countingLangSem cfg) cfg.kappa.analysis enL c exL cm ∧
    CntStep cfg.val exL cm c'

/-- Counted specialization of the shared indexed body-run chain. -/
abbrev CntInlineChain (cfg : WFCFG) (enL exL : NodeID) :=
  IndexedChain (CntInlineBodyRun cfg enL exL)

/-- Forgetting ghost counts maps a counted inline chain to the existing
    store-only chain without changing its number of body iterations. -/
theorem CntInlineChain.forget_count {cfg : WFCFG} {enL exL : NodeID}
    {k : Nat} {c c' : CntState}
    (hchain : CntInlineChain cfg enL exL k c c') :
    InlineChain cfg enL exL k c.1 c'.1 := by
  apply IndexedChain.map Prod.fst (h := hchain)
  rintro c₁ c₂ ⟨cm, hrun, hstep⟩
  exact ⟨cm.1, lsteps_forget_count cfg hrun, hstep.1⟩

/-- The FDuke `LStep` on the structural graph. -/
def fdukeLStep (cfg : WFCFG) (e : Edge) (σ σ' : State) : Prop :=
  KappaStep cfg.val e.src σ σ'

/-- Compatibility semantics for the now-structural execution graph. -/
instance fdukeLangSem (cfg : WFCFG) :
    LangSem NodeID Edge State cfg.analysis where
  LStep e σ σ' := fdukeLStep cfg e.val σ σ'
  LStutter _ σ σ' := σ = σ'
  IsInit c := c = State.empty

-- # Family-wide checkedness (required by the projection)

/-- Every function of the family passes the counting analysis for its declared
    κ. The projection obligation (`cek_projection`) needs this *family-wide*
    hypothesis: a callee's body may contain nested `call` sites, and its own
    summary refines to a κ-admitted inline chain only if the *nested* callees
    honour their own κ. Without it the obligation is **false** — e.g. a callee
    `f` whose body is `call g { invoke }` with `g` declared `κ = 1` but
    actually invoking twice: the real run invokes `f`'s lambda twice
    (`k = 2`), yet a `κ = 1` verdict for `f` would only admit `k = 1`. -/
def FamilyChecked (fam : CFGFamily) : Prop :=
  ∀ q ∈ fam.funCFGs,
    ∃ rdf : NodeID → Cnt,
      PostFixpoint q.2.2.kappa.analysis (countingDFA q.2.2.val) rdf ∧
      (countingDFA q.2.2.val).entry ⊑ rdf q.2.2.kappa.analysis.entry ∧
      CountVerdict q.2.1 (rdf q.2.2.val.exit)

-- # Equivariance transfer of store steps

/-- The store-only intra-step relation depends only on a node's *kind*, and
    `NodeKind.shiftLam` (the node map that relates a standalone lambda
    fragment to its inlined copy — see `lowerStmt_equivariant`) touches only
    `.Call` nodes, which carry no `IntraStep`. Hence two nodes whose kinds
    agree up to `shiftLam δL` (the standalone node `n₁` and the inline node
    `n₂ = n₁ + δ`) have *identical* intra-step behaviour. -/
theorem intraStep_shiftLam_iff (cfg₁ cfg₂ : CFG) (n₁ n₂ : NodeID) (δL : Nat)
    {σ σ' : State}
    (h : cfg₂.nodeKind n₂ = (cfg₁.nodeKind n₁).map (NodeKind.shiftLam δL)) :
    IntraStep cfg₁ n₁ σ σ' ↔ IntraStep cfg₂ n₂ σ σ' := by
  unfold IntraStep
  rcases hk : cfg₁.nodeKind n₁ with _ | k
  · simp [hk] at h; simp [h]
  · cases k <;> simp [hk] at h <;> simp [h, NodeKind.shiftLam]

/-- The κ-graph loud step `KappaStep` (the `LStep` of `kappaLangSem`) is
    likewise invariant under `shiftLam δL`: it is an `IntraStep` (invariant
    by `intraStep_shiftLam_iff`) or the store-identity step of a `.Call`
    node, and `shiftLam` maps `.Call` nodes to `.Call` nodes (only their
    lambda id moves), so the "is a call" side is preserved too. -/
theorem kappaStep_shiftLam_iff (cfg₁ cfg₂ : CFG) (n₁ n₂ : NodeID) (δL : Nat)
    {σ σ' : State}
    (h : cfg₂.nodeKind n₂ = (cfg₁.nodeKind n₁).map (NodeKind.shiftLam δL)) :
    KappaStep cfg₁ n₁ σ σ' ↔ KappaStep cfg₂ n₂ σ σ' := by
  unfold KappaStep
  rw [intraStep_shiftLam_iff cfg₁ cfg₂ n₁ n₂ δL h]
  rcases hk : cfg₁.nodeKind n₁ with _ | k
  · simp [hk] at h; simp [h]
  · cases k <;> simp [hk] at h <;> simp [h, NodeKind.shiftLam]

/-- The ghost-counter step is invariant under the same shifted-node
    correspondence as `KappaStep`: `shiftLam` preserves whether a node is an
    `Invoke`, so it preserves the counter update as well as the store step. -/
theorem cntStep_shiftLam_iff (cfg₁ cfg₂ : CFG) (n₁ n₂ : NodeID) (δL : Nat)
    {c c' : CntState}
    (h : cfg₂.nodeKind n₂ = (cfg₁.nodeKind n₁).map (NodeKind.shiftLam δL)) :
    CntStep cfg₁ n₁ c c' ↔ CntStep cfg₂ n₂ c c' := by
  unfold CntStep
  rw [kappaStep_shiftLam_iff cfg₁ cfg₂ n₁ n₂ δL h]
  constructor <;> intro hc
  · rcases hc with ⟨hκ, hcnt⟩
    refine ⟨hκ, ?_⟩
    rcases hk : cfg₁.nodeKind n₁ with _ | k
    · grind
    · cases k <;> grind [NodeKind.shiftLam]
  · rcases hc with ⟨hκ, hcnt⟩
    refine ⟨hκ, ?_⟩
    rcases hk : cfg₁.nodeKind n₁ with _ | k
    · grind
    · cases k <;> grind [NodeKind.shiftLam]

/-- Transport a store-only κ-graph run along a uniform node-id shift.  The
    hypotheses intentionally speak directly about the two κ graphs, so this
    lemma can be instantiated from any fragment provenance, in particular
    `Program.lowerStmt_equivariant`. -/
theorem kappa_lsteps_shift (cfg₁ cfg₂ : WFCFG) (δ δL : Nat)
    (hedges : ∀ e ∈ cfg₁.kappa.analysis.edges,
      Edge.shift δ e ∈ cfg₂.kappa.analysis.edges)
    (hnodes : ∀ n k, cfg₁.val.nodeKind n = some k →
      cfg₂.val.nodeKind (n + δ) = some (NodeKind.shiftLam δL k))
    {n n' : NodeID} {σ σ' : State}
    (hrun : LSteps (ls := kappaLangSem cfg₁) cfg₁.kappa.analysis n σ n' σ') :
    LSteps (ls := kappaLangSem cfg₂) cfg₂.kappa.analysis
      (n + δ) σ (n' + δ) σ' := by
  induction hrun with
  | refl n σ => exact .refl _ _
  | @step e n_src n'' σ σ₁ σ' hstep htail hsrc ih =>
    change KappaStep cfg₁.val e.val.src σ σ₁ at hstep
    change e.val.src = n_src at hsrc
    rw [hsrc] at hstep
    let e' : EdgeOf cfg₂.kappa.analysis :=
      ⟨Edge.shift δ e.val, hedges e.val e.property⟩
    rcases hk : cfg₁.val.nodeKind n_src with _ | k
    · simp [KappaStep, IntraStep, hk] at hstep
    have hstep' : KappaStep cfg₂.val (n_src + δ) σ σ₁ :=
      (kappaStep_shiftLam_iff cfg₁.val cfg₂.val n_src (n_src + δ) δL
        (by simpa [hk] using hnodes n_src k hk)).mp
        (by simpa [kappaLangSem, hsrc] using hstep)
    have hsrc' : cfg₂.kappa.analysis.srcOf e' = n_src + δ := by
      change e.val.src + δ = n_src + δ
      exact congrArg (· + δ) hsrc
    have hstep'' : (kappaLangSem cfg₂).LStep e' σ σ₁ := by
      change KappaStep cfg₂.val e'.val.src σ σ₁
      change e'.val.src = n_src + δ at hsrc'
      rw [hsrc']
      exact hstep'
    exact LSteps.step (g := cfg₂.kappa.analysis) (e := e') hstep''
      (by simpa [e', Edge.shift] using ih)
      hsrc'
  | stut hstut htail ih =>
    exact .stut hstut ih

/-- The counted analogue of `kappa_lsteps_shift`; it preserves both the store
    and the ghost invocation count exactly. -/
theorem counting_lsteps_shift (cfg₁ cfg₂ : WFCFG) (δ δL : Nat)
    (hedges : ∀ e ∈ cfg₁.kappa.analysis.edges,
      Edge.shift δ e ∈ cfg₂.kappa.analysis.edges)
    (hnodes : ∀ n k, cfg₁.val.nodeKind n = some k →
      cfg₂.val.nodeKind (n + δ) = some (NodeKind.shiftLam δL k))
    {n n' : NodeID} {c c' : CntState}
    (hrun : LSteps (ls := countingLangSem cfg₁) cfg₁.kappa.analysis n c n' c') :
    LSteps (ls := countingLangSem cfg₂) cfg₂.kappa.analysis
      (n + δ) c (n' + δ) c' := by
  induction hrun with
  | refl n c => exact .refl _ _
  | @step e n_src n'' c c₁ c' hstep htail hsrc ih =>
    change CntStep cfg₁.val e.val.src c c₁ at hstep
    change e.val.src = n_src at hsrc
    rw [hsrc] at hstep
    let e' : EdgeOf cfg₂.kappa.analysis :=
      ⟨Edge.shift δ e.val, hedges e.val e.property⟩
    rcases hk : cfg₁.val.nodeKind n_src with _ | k
    · simp [CntStep, KappaStep, IntraStep, hk] at hstep
    have hstep' : CntStep cfg₂.val (n_src + δ) c c₁ :=
      (cntStep_shiftLam_iff cfg₁.val cfg₂.val n_src (n_src + δ) δL
        (by simpa [hk] using hnodes n_src k hk)).mp
        (by simpa [countingLangSem, hsrc] using hstep)
    have hsrc' : cfg₂.kappa.analysis.srcOf e' = n_src + δ := by
      change e.val.src + δ = n_src + δ
      exact congrArg (· + δ) hsrc
    have hstep'' : (countingLangSem cfg₂).LStep e' c c₁ := by
      change CntStep cfg₂.val e'.val.src c c₁
      change e'.val.src = n_src + δ at hsrc'
      rw [hsrc']
      exact hstep'
    exact LSteps.step (g := cfg₂.kappa.analysis) (e := e') hstep''
      (by simpa [e', Edge.shift] using ih)
      hsrc'
  | stut hstut htail ih =>
    exact .stut hstut ih

/-- Transport a counted run of a call body's standalone lowering into the
    shifted inline copy certified for the call gadget.  The ghost counter is
    preserved, so later chain assembly can read the concrete number of
    invocations directly from the transported run. -/
theorem lsteps_inline_cnt (cfg : WFCFG) (Φ : FunEnv) (site : CallGadget)
    (hfragment : cfg.val.HasInlineBodyFragment Φ site)
    {n n' : NodeID} {c c' : CntState}
    (hrun : LSteps (ls := countingLangSem (site.body.wfcfgFrom Φ (site.lamID + 1)))
      (site.body.wfcfgFrom Φ (site.lamID + 1)).kappa.analysis n c n' c') :
    LSteps (ls := countingLangSem cfg) cfg.kappa.analysis
      (n + site.enL) c (n' + site.enL) c' := by
  apply counting_lsteps_shift (site.body.wfcfgFrom Φ (site.lamID + 1)) cfg site.enL 0
  · intro e he
    apply CFG.kappa_edges_mem.mpr
    exact hfragment.1 e (CFG.kappa_edges_mem.mp he)
  · intro n k hn
    rw [hfragment.2 n k (by simpa using hn)]
    cases k <;> rfl
  · exact hrun

/-- Close a counted κ-graph run by firing the pending action at its exit
    across a plain edge.  This is the counted counterpart of the elementary
    hop used by `chain_replay`. -/
theorem lsteps_from_exit_cnt (cfg : WFCFG) {en ex r : NodeID}
    {c cm c' : CntState}
    (hrun : LSteps (ls := countingLangSem cfg) cfg.kappa.analysis en c ex cm)
    (hstep : CntStep cfg.val ex cm c')
    (hedge : (⟨ex, r, .plain⟩ : Edge) ∈ cfg.val.edges) :
    LSteps (ls := countingLangSem cfg) cfg.kappa.analysis en c r c' := by
  have hmem : (⟨ex, r, .plain⟩ : Edge) ∈ cfg.kappa.analysis.edges :=
    CFG.kappa_edges_mem.mpr hedge
  exact LSteps.trans _ hrun
    (LSteps.single cfg.kappa.analysis (e := ⟨⟨ex, r, .plain⟩, hmem⟩) hstep)

/-- Package a counted run reaching a body's exit together with its pending
    exit action.  Keeping this elimination separate lets the balanced
    decomposition construct inline links without ever dropping the ghost
    invocation count. -/
theorem lsteps_split_exit_cnt (cfg : WFCFG) {en ex : NodeID}
    {c cm c' : CntState}
    (hrun : LSteps (ls := countingLangSem cfg) cfg.kappa.analysis en c ex cm)
    (hstep : CntStep cfg.val ex cm c') :
    CntInlineBodyRun cfg en ex c c' :=
  ⟨cm, hrun, hstep⟩

/-- Transport one standalone counted body run and its pending exit action to
    the corresponding inline fragment. -/
theorem cnt_link_transport (cfg : WFCFG) (Φ : FunEnv) (site : CallGadget)
    (hfragment : cfg.val.HasInlineBodyFragment Φ site)
    {n n' : NodeID} {c cm c' : CntState}
    (hrun : LSteps (ls := countingLangSem (site.body.wfcfgFrom Φ (site.lamID + 1)))
      (site.body.wfcfgFrom Φ (site.lamID + 1)).kappa.analysis n c n' cm)
    (hstep : CntStep (site.body.wfcfgFrom Φ (site.lamID + 1)).val n' cm c') :
    CntInlineBodyRun cfg (n + site.enL) (n' + site.enL) c c' := by
  refine ⟨cm, lsteps_inline_cnt cfg Φ site hfragment hrun, ?_⟩
  apply (cntStep_shiftLam_iff
    (site.body.wfcfgFrom Φ (site.lamID + 1)).val cfg.val n'
    (n' + site.enL) 0 ?_).mp
  · exact hstep
  · rcases hk : (site.body.wfcfgFrom Φ (site.lamID + 1)).val.nodeKind n' with _ | k
    · simp [CntStep, KappaStep, IntraStep, hk] at hstep
    · rw [hfragment.2 n' k hk]
      cases k <;> rfl

/-
A counted run which starts and ends at a node with no outgoing κ-edge
    cannot change its state.
-/
theorem counting_lsteps_sink_eq (cfg : WFCFG) (n : NodeID)
    (hsink : ∀ e ∈ cfg.kappa.analysis.edges, e.src ≠ n)
    {c c' : CntState}
    (hrun : LSteps (ls := countingLangSem cfg) cfg.kappa.analysis n c n c') :
    c = c' := by
  contrapose! hrun;
  have h_no_edges : ∀ {n' : NodeID} {c' : CntState},
      LSteps (ls := countingLangSem cfg) cfg.kappa.analysis n c n' c' → n' = n → c' = c := by
    intros n' c' hrun hn' ; induction hrun <;> simp_all +decide only [ne_eq, not_false_eq_true,
      implies_true, forall_const] ;
    · rename_i e _ _ _ _ _ _ _ h ih
      have := hsink e e.prop
      unfold AnalysisCFG.srcOf at h
      exact False.elim (this h)
    · cases ‹LangSem.LStutter cfg.kappa.analysis _ _ _› ; aesop;
  exact fun h => hrun <| h_no_edges h rfl ▸ rfl

/-- Split the unique final edge of a counted run into a sink. -/
theorem counting_lsteps_unique_sink_last (cfg : WFCFG) {en src sink : NodeID}
    (hne : en ≠ sink)
    (hsink : ∀ e ∈ cfg.kappa.analysis.edges, e.src ≠ sink)
    (hin : ∀ e ∈ cfg.kappa.analysis.edges, e.dst = sink → e.src = src)
    {c c' : CntState}
    (hrun : LSteps (ls := countingLangSem cfg) cfg.kappa.analysis en c sink c') :
    ∃ cm,
      LSteps (ls := countingLangSem cfg) cfg.kappa.analysis en c src cm ∧
      CntStep cfg.val src cm c' := by
  induction hrun with
  | refl => exact False.elim (hne rfl)
  | @step e n n' c c₁ c' hstep htail hsrc ih =>
      by_cases hd : cfg.kappa.analysis.dstOf e = n'
      · have ht : c₁ = c' :=
          counting_lsteps_sink_eq cfg n' hsink (hd ▸ htail)
        have hes : e.val.src = src := hin e.val e.property hd
        have hn : n = src := hsrc.symm.trans hes
        subst ht
        subst hn
        refine ⟨c, .refl _ _, ?_⟩
        change CntStep cfg.val e.val.src c c₁ at hstep
        rw [← hsrc]
        exact hstep
      · obtain ⟨cm, hp, hs⟩ := ih hd hsink hin
        exact ⟨cm, .step hstep hp hsrc, hs⟩
  | @stut n n' c c₁ c' hstut htail ih =>
      have hc : c = c₁ := hstut
      subst hc
      exact ih hne hsink hin

-- temporary
set_option linter.flexible false in
/-
The appended `Skip` is a fresh sink whose unique incoming edge is from
    the original body exit.
-/
theorem seq_skip_terminal_shape (Φ : FunEnv) (startLam : Nat) (body : Stmt) :
    let g := body.wfcfgFrom Φ startLam
    let gs := (body ;; Stmt.Skip).wfcfgFrom Φ startLam
    gs.val.entry ≠ gs.val.exit ∧
    (∀ e ∈ gs.kappa.analysis.edges, e.src ≠ gs.val.exit) ∧
    (∀ e ∈ gs.kappa.analysis.edges, e.dst = gs.val.exit → e.src = g.val.exit) := by
  refine ⟨ ?_, ?_, ?_ ⟩ <;> simp +decide only [AnalysisCFG.edges, ne_eq];
  · unfold Stmt.wfcfgFrom; simp +decide only [cfgFrom_seq_skip_shape] ;
    exact Nat.ne_of_lt (Stmt.wfcfgFrom Φ startLam body).prop.1;
  · intro e he
    change e ∈ ((body ;; Stmt.Skip).cfgFrom Φ startLam).edges at he
    change e.src ≠ ((body ;; Stmt.Skip).cfgFrom Φ startLam).exit
    rw [cfgFrom_seq_skip_shape] at he ⊢
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact Nat.ne_of_lt ((body.wfcfgFrom Φ startLam).prop.2.1 e he)
    · exact Nat.ne_of_lt (body.wfcfgFrom Φ startLam).prop.2.2.2.2
  · intro e he hdest
    have hstruct := CFG.kappa_edges_mem.mp he
    change e ∈ ((body ;; Stmt.Skip).cfgFrom Φ startLam).edges at hstruct
    change e.dst = ((body ;; Stmt.Skip).cfgFrom Φ startLam).exit at hdest
    change e.src = (body.cfgFrom Φ startLam).exit
    rw [cfgFrom_seq_skip_shape] at hstruct
    simp only [List.mem_append, List.mem_singleton] at hstruct
    rcases hstruct with he | rfl
    · have hlt := (body.wfcfgFrom Φ startLam).prop.2.2.1 e he
      have hdest' : e.dst = (body.cfgFrom Φ startLam).nodes.length := by
        simpa [cfgFrom_seq_skip_shape] using hdest
      exact False.elim ((Nat.ne_of_lt hlt) hdest')
    · rfl

/-
A run starting at a sink can only finish at that same node.
-/
theorem counting_lsteps_sink_target (cfg : WFCFG) (sink : NodeID)
    (hsink : ∀ e ∈ cfg.kappa.analysis.edges, e.src ≠ sink)
    {n : NodeID} {c c' : CntState}
    (hrun : LSteps (ls := countingLangSem cfg) cfg.kappa.analysis sink c n c') :
    n = sink := by
  rcases hrun with ( _ | ⟨ _, _, hrun ⟩ )
  · simp
  · contrapose! hsink; aesop;
  · rename_i h₁ h₂
    induction h₂ <;>
      simp_all +decide only [LangSem.LStutter, ne_eq, not_false_eq_true, implies_true, forall_const]
    rename_i e _ _ _ _ _ _ _ h
    have := hsink e e.prop
    unfold AnalysisCFG.srcOf at h
    exact False.elim (this h)

/-
Transport a counted run out of a graph with one fresh sink back to the
    original graph.
-/
theorem counting_lsteps_remove_sink (cfg₁ cfg₂ : WFCFG) (sink : NodeID)
    (hsink : ∀ e ∈ cfg₂.kappa.analysis.edges, e.src ≠ sink)
    (hedges : ∀ e ∈ cfg₂.kappa.analysis.edges, e.dst ≠ sink →
      e ∈ cfg₁.kappa.analysis.edges)
    (hsteps : ∀ {n : NodeID}, n ≠ sink → ∀ {c c' : CntState},
      CntStep cfg₂.val n c c' → CntStep cfg₁.val n c c')
    {en target : NodeID} (htarget : target ≠ sink) {c c' : CntState}
    (hrun : LSteps (ls := countingLangSem cfg₂) cfg₂.kappa.analysis en c target c') :
    LSteps (ls := countingLangSem cfg₁) cfg₁.kappa.analysis en c target c' := by
  induction hrun;
  · constructor;
  · rename_i e n n' σ σ' σ'' hstep hrun hsrc ih;
    have hdst : e.val.dst ≠ sink := by
      intro hd
      have hrun' : LSteps (ls := countingLangSem cfg₂) cfg₂.kappa.analysis
          sink σ' n' σ'' := by
        change e.val.dst = sink at hd
        rw [← hd]
        exact hrun
      have heq := counting_lsteps_sink_target cfg₂ sink hsink hrun'
      exact htarget heq
    convert LSteps.step (e := ⟨e.val, hedges e.val e.property hdst⟩) ?_
      (ih htarget) using 1
    rotate_left
    · exact n
    · exact σ
    · cases e
      aesop
    · simp only [AnalysisCFG.srcOf] at ⊢ hsrc
      grind
  · cases ‹LangSem.LStutter cfg₂.kappa.analysis _ _ _›
    aesop (simp_config := { singlePass := true })

/-
A counted loud step can only fire at a node present in the CFG.
-/
theorem cntStep_nodeKind_exists {g : CFG} {n : NodeID} {c c' : CntState}
    (h : CntStep g n c c') : ∃ k, g.nodeKind n = some k := by
  rcases h with ⟨ h₁, h₂ ⟩;
  cases h₁;
  · cases ‹IntraStep g n c.1 c'.1› <;> tauto;
  · grind

/-
Every nonterminal node of `body ;; Skip` belongs to the original body.
-/
theorem seq_skip_nonterminal_lt (Φ : FunEnv) (startLam : Nat) (body : Stmt)
    {n : NodeID}
    (hn : n ≠ ((body ;; Stmt.Skip).wfcfgFrom Φ startLam).val.exit)
    {c c' : CntState}
    (h : CntStep ((body ;; Stmt.Skip).wfcfgFrom Φ startLam).val n c c') :
    n < (body.wfcfgFrom Φ startLam).val.nodes.length := by
  obtain ⟨ k, hk ⟩ := cntStep_nodeKind_exists h;
  have := @cfgFrom_seq_skip_shape Φ startLam body;
  simp_all +decide [ CFG.nodeKind ];
  simp_all +decide [ Stmt.wfcfgFrom ];
  grind

/-
The pending action at an original body node is unchanged by appending the
    terminal `Skip`.
-/
theorem seq_skip_cntStep_iff (Φ : FunEnv) (startLam : Nat) (body : Stmt)
    {n : NodeID} (hn : n < (body.wfcfgFrom Φ startLam).val.nodes.length)
    {c c' : CntState} :
    CntStep ((body ;; Stmt.Skip).wfcfgFrom Φ startLam).val n c c' ↔
      CntStep (body.wfcfgFrom Φ startLam).val n c c' := by
  obtain ⟨g, hg⟩ : ∃ g : WFCFG, g.val = (body ;; Stmt.Skip).wfcfgFrom Φ startLam := by
    grind;
  have := cfgFrom_seq_skip_shape Φ startLam body;
  convert cntStep_shiftLam_iff _ _ _ _ 0 _;
  unfold Stmt.wfcfgFrom at *; simp_all +decide only [CFG.nodeKind, getElem?_pos] ;
  rw [ List.getElem?_append ] ; simp +decide only [hn, ↓reduceIte, getElem?_pos, Option.map_some,
    Option.some.injEq];
  unfold NodeKind.shiftLam; aesop;


/-- Before the administrative edge is taken, a run in `body ;; Skip` is
    exactly a run in the original body CFG. -/
theorem seq_skip_prefix_to_body (Φ : FunEnv) (startLam : Nat) (body : Stmt)
    {c cm : CntState}
    (hrun : LSteps
      (ls := countingLangSem ((body ;; Stmt.Skip).wfcfgFrom Φ startLam))
      ((body ;; Stmt.Skip).wfcfgFrom Φ startLam).kappa.analysis
      ((body ;; Stmt.Skip).wfcfgFrom Φ startLam).val.entry c
      (body.wfcfgFrom Φ startLam).val.exit cm) :
    LSteps (ls := countingLangSem (body.wfcfgFrom Φ startLam))
      (body.wfcfgFrom Φ startLam).kappa.analysis
      (body.wfcfgFrom Φ startLam).val.entry c
      (body.wfcfgFrom Φ startLam).val.exit cm := by
  let g := body.wfcfgFrom Φ startLam
  let gs := (body ;; Stmt.Skip).wfcfgFrom Φ startLam
  have hshape := seq_skip_terminal_shape Φ startLam body
  have htarget : g.val.exit ≠ gs.val.exit := by
    change (body.cfgFrom Φ startLam).exit ≠
      ((body ;; Stmt.Skip).cfgFrom Φ startLam).exit
    rw [cfgFrom_seq_skip_shape]
    exact Nat.ne_of_lt (body.wfcfgFrom Φ startLam).prop.2.2.2.2
  have hedges : ∀ e ∈ gs.kappa.analysis.edges, e.dst ≠ gs.val.exit →
      e ∈ g.kappa.analysis.edges := by
    intro e he hdst
    apply CFG.kappa_edges_mem.mpr
    have he := CFG.kappa_edges_mem.mp he
    change e ∈ (body.cfgFrom Φ startLam).edges
    change e ∈ ((body ;; Stmt.Skip).cfgFrom Φ startLam).edges at he
    change e.dst ≠ ((body ;; Stmt.Skip).cfgFrom Φ startLam).exit at hdst
    rw [cfgFrom_seq_skip_shape] at he hdst
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · exact he
    · subst he
      exact False.elim (hdst rfl)
  have hsteps : ∀ {n : NodeID}, n ≠ gs.val.exit → ∀ {c c' : CntState},
      CntStep gs.val n c c' → CntStep g.val n c c' := by
    intro n hn c₀ c₁ hs
    dsimp [g, gs] at hs ⊢
    exact (seq_skip_cntStep_iff Φ startLam body
      (seq_skip_nonterminal_lt Φ startLam body hn hs)).mp hs
  have hrun' : LSteps (ls := countingLangSem gs) gs.kappa.analysis
      g.val.entry c g.val.exit cm := by
    dsimp [g, gs]
    convert hrun using 1
  exact counting_lsteps_remove_sink g gs gs.val.exit
    hshape.2.1 hedges hsteps htarget hrun'

/-- A counted run of the registered standalone body followed by its terminal
    administrative `Skip` reaches that terminal only by first reaching the
    original body's exit and firing the body's pending exit action. -/
theorem standalone_seq_skip_exit_decompose (Φ : FunEnv) (startLam : Nat)
    (body : Stmt) {c c' : CntState}
    (hrun : LSteps
      (ls := countingLangSem ((body ;; Stmt.Skip).wfcfgFrom Φ startLam))
      ((body ;; Stmt.Skip).wfcfgFrom Φ startLam).kappa.analysis
      ((body ;; Stmt.Skip).wfcfgFrom Φ startLam).val.entry c
      ((body ;; Stmt.Skip).wfcfgFrom Φ startLam).val.exit c') :
    ∃ cm,
      LSteps (ls := countingLangSem (body.wfcfgFrom Φ startLam))
        (body.wfcfgFrom Φ startLam).kappa.analysis
        (body.wfcfgFrom Φ startLam).val.entry c
        (body.wfcfgFrom Φ startLam).val.exit cm ∧
      CntStep (body.wfcfgFrom Φ startLam).val
        (body.wfcfgFrom Φ startLam).val.exit cm c' := by
  let g := body.wfcfgFrom Φ startLam
  let gs := (body ;; Stmt.Skip).wfcfgFrom Φ startLam
  have hshape := seq_skip_terminal_shape Φ startLam body
  obtain ⟨cm, hp, hs⟩ := counting_lsteps_unique_sink_last gs
    hshape.1 hshape.2.1 hshape.2.2 hrun
  refine ⟨cm, ?_, ?_⟩
  · exact seq_skip_prefix_to_body Φ startLam body hp
  · apply (seq_skip_cntStep_iff Φ startLam body
      (body.wfcfgFrom Φ startLam).prop.2.2.2.2).mp
    exact hs

/-- Replay a nonempty counted inline chain through the caller's κ graph.
    Unlike its store-only projection, this retains the precise invocation
    counter accumulated by each inline body. -/
theorem cnt_chain_replay (cfg : WFCFG) {enL exL r : NodeID}
    (hout : (⟨exL, r, .plain⟩ : Edge) ∈ cfg.val.edges)
    {k : Nat} {c c' : CntState} (hchain : CntInlineChain cfg enL exL k c c')
    (hback : 2 ≤ k → (⟨exL, enL, .plain⟩ : Edge) ∈ cfg.val.edges)
    (hk : 1 ≤ k) :
    LSteps (ls := countingLangSem cfg) cfg.kappa.analysis enL c r c' := by
  revert hback hk
  induction hchain with
  | zero => intro _ hk; omega
  | @succ k c c₁ c'' hlink hrest ih =>
    intro hback _
    obtain ⟨cm, hrun, hstep⟩ := hlink
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · cases hrest
      exact lsteps_from_exit_cnt cfg hrun hstep hout
    · have hb := hback (by omega)
      have hmem : (⟨exL, enL, .plain⟩ : Edge) ∈ cfg.kappa.analysis.edges :=
        CFG.kappa_edges_mem.mpr hb
      have htail := ih (fun _ => hback (by omega)) hpos
      exact LSteps.trans _ hrun
        (LSteps.step (g := cfg.kappa.analysis)
          (e := ⟨⟨exL, enL, .plain⟩, hmem⟩) hstep htail rfl)

-- # Closure-environment algebra for balanced projection

/-- The balanced body execution underlying one concrete lambda invocation.
    The ambient continuation is retained explicitly: it is the evidence which
    `StepsOver.first_return` exposes before `Step.retInv` restores the caller.
    Unlike the old closure-only chain, this record keeps the whole body run,
    including nested calls and invokes, available to the projection induction.
-/
structure LamBodyRun (fam : CFGFamily) (clo : Clo)
    (ρ' : Option Clo) (σ' : State) where
  nr : NodeRef
  σf : State
  K : Kont
  k : Nat
  run : StepsOver fam (.inv nr (some clo) σf :: K) k
    ⟨clo.enL, clo.σ, clo.ρ, .inv nr (some clo) σf :: K⟩
    ⟨clo.exL, σ', ρ', .inv nr (some clo) σf :: K⟩

/-- The immutable lambda-body identity of a closure trace.  The captured
    environment and store may evolve after every invocation, but all links in
    a trace must belong to this one body. -/
structure LamKey where
  enL : NodeRef
  exL : NodeRef

/-- A sequence of completed invocations of one evolving closure.  Each link
    retains the CEK body run that changes the closure's captured environment,
    so a caller projection can turn the links into counted inline runs rather
    than having to recover them from closure values after the fact. -/
inductive LamChain (fam : CFGFamily) (key : LamKey) :
    Option Clo → Option Clo → Prop where
  | refl (ρ) : LamChain fam key ρ ρ
  | invoke {clo ρ' σ' ρ''} :
      clo.enL = key.enL →
      clo.exL = key.exL →
      LamBodyRun fam clo ρ' σ' →
      LamChain fam key (some ⟨clo.enL, clo.exL, ρ', σ'⟩) ρ'' →
      LamChain fam key (some clo) ρ''

/-- A lambda-body run whose length is strictly below the enclosing induction budget. -/
structure BoundedLamBodyRun (fam : CFGFamily) (N : Nat) (clo : Clo)
    (ρ' : Option Clo) (σ' : State) extends LamBodyRun fam clo ρ' σ' where
  lt_bound : toLamBodyRun.k < N
  wf_parent : CloWF fam clo.ρ
  wf_kont : KontWF fam toLamBodyRun.K

/-- A proof-specific lambda chain retaining a strict induction bound on every body. -/
inductive BoundedLamChain (fam : CFGFamily) (N : Nat) (key : LamKey) :
    Option Clo → Option Clo → Type where
  | refl (ρ) : BoundedLamChain fam N key ρ ρ
  | invoke {clo ρ' σ' ρ''} :
      clo.enL = key.enL →
      clo.exL = key.exL →
      BoundedLamBodyRun fam N clo ρ' σ' →
      BoundedLamChain fam N key
        (some ⟨clo.enL, clo.exL, ρ', σ'⟩) ρ'' →
      BoundedLamChain fam N key (some clo) ρ''

protected theorem BoundedLamChain.erase {fam : CFGFamily} {N : Nat} {key : LamKey}
    {ρ ρ' : Option Clo} :
    BoundedLamChain fam N key ρ ρ' → LamChain fam key ρ ρ' := by
  intro h
  induction h with
  | refl => exact .refl _
  | _ hen hex body tail ih => exact .invoke hen hex body.toLamBodyRun ih

inductive BoundedLamChain.Count {fam : CFGFamily} {N : Nat} {key : LamKey} :
    {ρ ρ' : Option Clo} → BoundedLamChain fam N key ρ ρ' → Nat → Prop where
  | refl (ρ) : BoundedLamChain.Count (.refl ρ) 0
  | invoke {clo ρ' σ' ρ''} {body : BoundedLamBodyRun fam N clo ρ' σ'}
      {hen : clo.enL = key.enL} {hex : clo.exL = key.exL}
      {tail : BoundedLamChain fam N key (some ⟨clo.enL, clo.exL, ρ', σ'⟩) ρ''} {k} :
      BoundedLamChain.Count tail k →
      BoundedLamChain.Count (.invoke hen hex body tail) (k + 1)

protected theorem BoundedLamChain.key_end {fam : CFGFamily} {N : Nat} {key : LamKey}
    {ρ ρ' : Option Clo} (h : BoundedLamChain fam N key ρ ρ')
    (hρ : ∀ clo, ρ = some clo → clo.enL = key.enL ∧ clo.exL = key.exL) :
    ∀ clo, ρ' = some clo → clo.enL = key.enL ∧ clo.exL = key.exL := by
  induction h with
  | refl => exact hρ
  | _ hen hex body tail ih =>
    exact ih (by rintro clo' ⟨⟩; exact ⟨hen, hex⟩)

protected noncomputable def BoundedLamChain.trans {fam : CFGFamily} {N : Nat} {key : LamKey}
    {ρ₁ ρ₂ ρ₃ : Option Clo} :
    BoundedLamChain fam N key ρ₁ ρ₂ → BoundedLamChain fam N key ρ₂ ρ₃ →
    BoundedLamChain fam N key ρ₁ ρ₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | _ hen hex body tail ih => exact .invoke hen hex body (ih h₂)

protected theorem BoundedLamChain.Count.trans {fam : CFGFamily} {N : Nat}
    {key : LamKey} {ρ₁ ρ₂ ρ₃ : Option Clo}
    {h₁ : BoundedLamChain fam N key ρ₁ ρ₂}
    {h₂ : BoundedLamChain fam N key ρ₂ ρ₃} {k₁ k₂ : Nat} :
    BoundedLamChain.Count h₁ k₁ → BoundedLamChain.Count h₂ k₂ →
    BoundedLamChain.Count (h₁.trans h₂) (k₁ + k₂) := by
  intro hc₁ hc₂
  induction hc₁ with
  | refl => simpa using hc₂
  | _ hc ih =>
    convert BoundedLamChain.Count.invoke (ih hc₂) using 1; omega

theorem BoundedLamChain.Count.unique {fam : CFGFamily} {N : Nat} {key : LamKey}
    {ρ ρ' : Option Clo} {h : BoundedLamChain fam N key ρ ρ'} {q₁ q₂ : Nat}
    (hc₁ : BoundedLamChain.Count h q₁) (hc₂ : BoundedLamChain.Count h q₂) :
    q₁ = q₂ := by
  induction hc₁ generalizing q₂ with
  | refl => cases hc₂; rfl
  | «invoke» htail ih =>
      cases hc₂
      rename_i htail₂
      exact congrArg (· + 1) (ih htail₂)

theorem BoundedLamChain.Count.mono {fam : CFGFamily} {N M : Nat} {key : LamKey}
    {ρ ρ' : Option Clo} {h : BoundedLamChain fam N key ρ ρ'} {q : Nat}
    (hNM : N ≤ M) (hc : BoundedLamChain.Count h q) :
    ∃ h' : BoundedLamChain fam M key ρ ρ', BoundedLamChain.Count h' q := by
  induction hc;
  · exact ⟨ BoundedLamChain.refl _, BoundedLamChain.Count.refl _ ⟩;
  · rename_i h₁ h₂ h₃ h₄ h₅ h₆;
    obtain ⟨ h', h₇ ⟩ := h₆;
    rename_i clo ρ' σ' ρ'' body;
    let bodyM : BoundedLamBodyRun fam M clo ρ' σ' :=
      ⟨body.toLamBodyRun, Nat.lt_of_lt_of_le body.lt_bound hNM,
        body.wf_parent, body.wf_kont⟩
    exact ⟨BoundedLamChain.invoke h₁ h₂ bodyM h',
      BoundedLamChain.Count.invoke (body := bodyM) (hen := h₁) (hex := h₂) h₇⟩

/-- The number of completed invocations recorded by a trace.  This is kept
    separate from the ghost counter: the latter counts `Invoke` nodes in a
    CFG run, while this index is exactly the number of body iterations needed
    by a call site's inline gadget.  It is a proposition rather than a
    computable extractor because `LamChain` itself is proof-valued. -/
inductive LamChain.Count {fam : CFGFamily} {key : LamKey} :
    {ρ ρ' : Option Clo} → LamChain fam key ρ ρ' → Nat → Prop where
  | refl (ρ) : LamChain.Count (.refl ρ) 0
  | invoke {clo ρ' σ' ρ''} {hbody : LamBodyRun fam clo ρ' σ'}
      {hen : clo.enL = key.enL} {hex : clo.exL = key.exL}
      {htail : LamChain fam key (some ⟨clo.enL, clo.exL, ρ', σ'⟩) ρ''} {k} :
      LamChain.Count htail k → LamChain.Count (.invoke hen hex hbody htail) (k + 1)

/-- Package the balanced prefix ending at a lambda exit.  In the invocation
    branch of `balanced_project`, this is instantiated with the prefix
    supplied by `StepsOver.first_return` immediately before `retInv`. -/
def LamBodyRun.ofStepsOver {fam : CFGFamily} {clo : Clo} {ρ' : Option Clo}
    {σ' σf : State} {nr : NodeRef} {K : Kont} {k : Nat}
    (hrun : StepsOver fam (.inv nr (some clo) σf :: K) k
      ⟨clo.enL, clo.σ, clo.ρ, .inv nr (some clo) σf :: K⟩
      ⟨clo.exL, σ', ρ', .inv nr (some clo) σf :: K⟩) :
    LamBodyRun fam clo ρ' σ' :=
  ⟨nr, σf, K, k, hrun⟩

/-- One completed lambda body advances its closure to the environment and
    store left at its exit. -/
theorem LamChain.single {fam : CFGFamily} {key : LamKey} {clo : Clo}
    {ρ' : Option Clo} {σ' : State} (hen : clo.enL = key.enL)
    (hex : clo.exL = key.exL) (hbody : LamBodyRun fam clo ρ' σ') :
    LamChain fam key (some clo) (some ⟨clo.enL, clo.exL, ρ', σ'⟩) :=
  .invoke hen hex hbody (.refl _)

/-- The ambient closure evolves by zero or more completed, run-indexed lambda
    invocations.  Store evolution remains in the counted κ shadow, while each
    `LamBodyRun` supplies the CEK evidence needed to assemble that shadow. -/
abbrev AmbientEvolve (fam : CFGFamily) (key : LamKey) :
    Option Clo → Option Clo → Prop :=
  LamChain fam key

theorem LamChain.trans {fam : CFGFamily} {key : LamKey} {ρ₁ ρ₂ ρ₃ : Option Clo} :
    LamChain fam key ρ₁ ρ₂ → LamChain fam key ρ₂ ρ₃ → LamChain fam key ρ₁ ρ₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | _ hen hex hbody htail ih => exact .invoke hen hex hbody (ih h₂)

theorem LamChain.Count.trans {fam : CFGFamily} {key : LamKey} {ρ₁ ρ₂ ρ₃ : Option Clo}
    {h₁ : LamChain fam key ρ₁ ρ₂} {h₂ : LamChain fam key ρ₂ ρ₃} {k₁ k₂} :
    LamChain.Count h₁ k₁ → LamChain.Count h₂ k₂ →
      LamChain.Count (h₁.trans h₂) (k₁ + k₂) := by
  intro hc₁ hc₂
  induction hc₁ with
  | refl => simpa using hc₂
  | _ hcount ih =>
    convert LamChain.Count.invoke (ih hc₂) using 1 <;> omega

/-- The lambda key is preserved along an ambient chain: if the source closure
    carries `key` (or is `none`), so does the target. -/
theorem LamChain.key_end {fam : CFGFamily} {key : LamKey} {ρ ρ' : Option Clo}
    (h : LamChain fam key ρ ρ')
    (hρ : ∀ clo, ρ = some clo → clo.enL = key.enL ∧ clo.exL = key.exL) :
    ∀ clo, ρ' = some clo → clo.enL = key.enL ∧ clo.exL = key.exL := by
  induction h with
  | refl ρ => exact hρ
  | _ hen hex hbody htail ih =>
    exact ih (by rintro clo' ⟨⟩; exact ⟨hen, hex⟩)

/-- Every finite invocation trace has a body-iteration count.  The count is
    intentionally proof-indexed, but this eliminator lets the projection
    induction recover the exact number required by a call gadget without
    exposing a noncomputable traversal of `LamChain`. -/
theorem LamChain.exists_count {fam : CFGFamily} {key : LamKey} {ρ ρ' : Option Clo}
    (hchain : LamChain fam key ρ ρ') :
    ∃ k, LamChain.Count hchain k := by
  induction hchain with
  | refl => exact ⟨0, .refl _⟩
  | _ hen hex hbody htail ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .invoke (hen := hen) (hex := hex) (hbody := hbody) hk⟩

/-- Assemble a counted inline chain by prefixing a certified body link.  This
    packages the constructor in the orientation used by `LamChain`: a newly
    exposed invocation runs before the already accumulated tail. -/
theorem CntInlineChain.cons {cfg : WFCFG} {enL exL : NodeID}
    {k : Nat} {c c₁ c' : CntState}
    (hlink : CntInlineBodyRun cfg enL exL c c₁)
    (htail : CntInlineChain cfg enL exL k c₁ c') :
    CntInlineChain cfg enL exL (k + 1) c c' :=
  .succ hlink htail

/-- Concatenate two counted inline chains while preserving both the threaded
    state and the total number of body iterations.  This is the counted
    counterpart of composing completed invocation traces across a return. -/
theorem CntInlineChain.append {cfg : WFCFG} {enL exL : NodeID}
    {k₁ k₂ : Nat} {c₁ c₂ c₃ : CntState}
    (h₁ : CntInlineChain cfg enL exL k₁ c₁ c₂)
    (h₂ : CntInlineChain cfg enL exL k₂ c₂ c₃) :
    CntInlineChain cfg enL exL (k₁ + k₂) c₁ c₃ :=
  IndexedChain.trans h₁ h₂

/-- Project a run-indexed closure trace to a counted inline chain once each
    retained lambda-body execution has been transported to the caller's inline
    fragment.  This is deliberately parametric in the body projection: the
    balanced induction supplies that projection recursively, while this lemma
    owns the purely compositional chain assembly. -/
theorem LamChain.toCntInline {fam : CFGFamily} {cfg : WFCFG}
    {key : LamKey} {ρ ρ' : Option Clo} {c : CntState}
    (hchain : LamChain fam key ρ ρ')
    (hbody : ∀ {clo : Clo} {ρ' : Option Clo} {σ' : State} {c : CntState},
      clo.enL = key.enL → clo.exL = key.exL →
      LamBodyRun fam clo ρ' σ' → ∃ c', CntInlineBodyRun cfg key.enL.2 key.exL.2 c c') :
    ∃ k c', CntInlineChain cfg key.enL.2 key.exL.2 k c c' := by
  induction hchain generalizing c with
  | refl => exact ⟨0, c, .zero⟩
  | _ hen hex hrun htail ih =>
    obtain ⟨c₁, hlink⟩ := hbody (c := c) hen hex hrun
    obtain ⟨k, c', hrest⟩ := ih (c := c₁)
    exact ⟨k + 1, c', hrest.cons hlink⟩

theorem LamChain.mono {fam : CFGFamily} {key : LamKey} {ρ₁ ρ₂ : Option Clo}
    (h : LamChain fam key ρ₁ ρ₂) : AmbientEvolve fam key ρ₁ ρ₂ := by
  exact h

theorem AmbientEvolve.rfl (fam : CFGFamily) (key : LamKey) (ρ : Option Clo) :
    AmbientEvolve fam key ρ ρ :=
  .refl _

theorem AmbientEvolve.trans {fam : CFGFamily} {key : LamKey} {ρ₁ ρ₂ ρ₃ : Option Clo} :
    AmbientEvolve fam key ρ₁ ρ₂ → AmbientEvolve fam key ρ₂ ρ₃ →
      AmbientEvolve fam key ρ₁ ρ₃ := by
  intro h₁ h₂
  exact LamChain.trans h₁ h₂

theorem AmbientEvolve.mono {fam : CFGFamily} {key : LamKey} {ρ₁ ρ₂ : Option Clo}
    (h : LamChain fam key ρ₁ ρ₂) : AmbientEvolve fam key ρ₁ ρ₂ :=
  h.mono

-- # Generated-family standalone components

/-- A generated call-gadget certificate resolves its lambda identifier to the
standalone CFG obtained by lowering the recorded body followed by the terminal
`Skip`.  This exposes the certificate-level result in the ordinary family
interface used by CEK projection. -/
theorem Program.family_gadget_standalone_wfcfg (p : Program) {ref : CFGRef}
    {source : CertifiedGeneratedCFG}
    (hresolve : p.generatedFamily.cfgAt? ref = some source)
    {site : CallGadget} (hsite : site ∈ source.generated.callGadgets) :
    p.family.cfgAt? (.lam site.lamID) =
      some ((site.body ;; Stmt.Skip).wfcfgFrom p.phi (site.lamID + 1)) := by
  rw [p.family_cfgAt?_iff_generatedFamily]
  refine ⟨(site.body ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (site.lamID + 1), ?_, rfl⟩
  exact p.generatedFamily_gadget_standalone hresolve hsite

/-- The standalone component selected by a generated gadget retains the body
and lambda-id offset from the gadget record. -/
theorem Program.generatedFamily_gadget_standalone_source (p : Program) {ref : CFGRef}
    {source : CertifiedGeneratedCFG}
    (hresolve : p.generatedFamily.cfgAt? ref = some source)
    {site : CallGadget} (hsite : site ∈ source.generated.callGadgets) :
    ∃ component, p.generatedFamily.cfgAt? (.lam site.lamID) = some component ∧
      component.source = (site.body ;; Stmt.Skip) ∧ component.startLam = site.lamID + 1 := by
  refine ⟨(site.body ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (site.lamID + 1),
    p.generatedFamily_gadget_standalone hresolve hsite, rfl, rfl⟩


/-- Lowering a standalone fragment from an empty CFG gives a complete shifted
edge copy in any lowering of the same statement from an offset builder state.
This is the edge half of the standalone-to-inline correspondence; a concrete
gadget instantiation supplies the caller's pre-inline builder state. -/
theorem lowerStmt_empty_fragment_edges (Φ : FunEnv) (s : Stmt) (b : BState)
    (δ δL : Nat) (hid : b.nextID = δ) (hlam : b.nextLam = δL) :
    let b₀ : BState := { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := 0 }
    let (_, b₀') := (lowerStmt Φ s).run b₀
    let (_, b') := (lowerStmt Φ s).run b
    ∀ e ∈ b₀'.cfg.edges, Edge.shift δ e ∈ b'.cfg.edges := by
  dsimp
  have h := lowerStmt_equivariant Φ s
    { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := 0 } b δ δL
    (by simpa using hid) (by simpa using hlam)
  obtain ⟨-, -, -, -, -, ⟨es₀, es, he₀, he, hshift⟩⟩ := h
  intro e hmem
  rw [he₀] at hmem
  simp only [List.nil_append] at hmem
  rw [he, hshift]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨e, hmem, rfl⟩)

-- # κ-gadget shape facts

/-- A κ admitting the count `0` provides the bypass `en → r` in its gadget
    (only `?` and ε admit zero, and both shapes carry the bypass). -/
theorem κAdmits_zero_bypass {κ : InvKind} (en enL exL r : NodeID)
    (h : κAdmits κ 0) :
    (⟨en, r, .plain⟩ : Edge) ∈ kappaEdges κ en enL exL r := by
  cases κ with
  | none => simp [kappaEdges]
  | once => exact absurd h (by simp [κAdmits])
  | atLeast => exact absurd h (by simp [κAdmits])
  | atMost => simp [kappaEdges]

/-- A κ admitting a count `≥ 2` provides the back-edge `exL → enL` in its
    gadget (only `+` and ε admit two or more, and both shapes carry it). -/
theorem κAdmits_two_back {κ : InvKind} (en enL exL r : NodeID)
    {k : Nat} (h : κAdmits κ k) (hk : 2 ≤ k) :
    (⟨exL, enL, .plain⟩ : Edge) ∈ kappaEdges κ en enL exL r := by
  cases κ with
  | none => simp [kappaEdges]
  | once => simp [κAdmits] at h; omega
  | atLeast => simp [kappaEdges]
  | atMost => simp [κAdmits] at h; omega

/-- Reading a per-κ verdict back on a concrete count, uniformly: a callee
    passing the check for κ was invoked a κ-admitted number of times. -/
theorem κAdmits_of_verdict {κ : InvKind} {S : Cnt} {k : Nat}
    (hv : CountVerdict κ S) (hk : S (abs k)) : κAdmits κ k := by
  cases κ with
  | none => trivial
  | once => exact count_of_once hv hk
  | atLeast => exact count_of_atLeast hv hk
  | atMost => exact count_of_atMost hv hk

/-
Replay an admitted counted inline chain from the call node through its
    complete gadget to the return node.
-/
theorem cnt_call_chain_replay (cfg : WFCFG) {f : String} {ℓ : Nat}
    {κ : InvKind} {en enL exL r : NodeID}
    (hkind : cfg.val.nodeKind en = some (.Call f ℓ))
    (hgadget : ∀ e ∈ kappaEdges κ en enL exL r, e ∈ cfg.val.edges)
    {k : Nat} (hadmit : κAdmits κ k)
    {c c' : CntState} (hchain : CntInlineChain cfg enL exL k c c') :
    LSteps (ls := countingLangSem cfg) cfg.kappa.analysis en c r c' := by
  have hcall : CntStep cfg.val en c c := by
    refine ⟨Or.inr ⟨⟨f, ℓ, hkind⟩, rfl⟩, ?_⟩
    simp [hkind]
  cases k with
  | zero =>
      cases hchain
      have hedge : (⟨en, r, .plain⟩ : Edge) ∈ cfg.val.edges :=
        hgadget _ (κAdmits_zero_bypass en enL exL r hadmit)
      have hmem : (⟨en, r, .plain⟩ : Edge) ∈ cfg.kappa.analysis.edges :=
        CFG.kappa_edges_mem.mpr hedge
      exact LSteps.single cfg.kappa.analysis
        (e := ⟨⟨en, r, .plain⟩, hmem⟩) hcall
  | succ k =>
      have hedgeIn : (⟨en, enL, .plain⟩ : Edge) ∈ cfg.val.edges :=
        hgadget _ (kappaEdges_en_enL κ en enL exL r)
      have hmemIn : (⟨en, enL, .plain⟩ : Edge) ∈ cfg.kappa.analysis.edges :=
        CFG.kappa_edges_mem.mpr hedgeIn
      have hinit : LSteps (ls := countingLangSem cfg) cfg.kappa.analysis
          en c enL c :=
        LSteps.single cfg.kappa.analysis
          (e := ⟨⟨en, enL, .plain⟩, hmemIn⟩) hcall
      have htail : LSteps (ls := countingLangSem cfg) cfg.kappa.analysis
          enL c r c' :=
        cnt_chain_replay cfg
          (hgadget _ (kappaEdges_exL_r κ en enL exL r)) hchain
          (fun hk => hgadget _ (κAdmits_two_back en enL exL r hadmit hk))
          (by omega)
      exact LSteps.trans _ hinit htail


-- # Assembly: single κ-gadget hops and chain replay

/-- The store-identity hop of a `Call` node across one of its κ-gadget
    structural edges (`en → enL` to enter the inline copy, or the `?`/ε bypass
    `en → r`): a single loud `KappaStep` on the κ-graph. -/
theorem call_identity_lstep (cfg : WFCFG) {f : String} {ℓ : Nat}
    {en d : NodeID} (hkind : cfg.val.nodeKind en = some (.Call f ℓ))
    (hedge : (⟨en, d, .plain⟩ : Edge) ∈ cfg.val.edges) (σ : State) :
    LSteps (ls := kappaLangSem cfg) cfg.kappa.analysis en σ d σ := by
  have hmem : (⟨en, d, .plain⟩ : Edge) ∈ cfg.kappa.analysis.edges :=
    CFG.kappa_edges_mem.mpr hedge
  exact LSteps.single cfg.kappa.analysis (e := ⟨⟨en, d, .plain⟩, hmem⟩)
    (Or.inr ⟨⟨f, ℓ, hkind⟩, rfl⟩)

/-- **Chain replay.** A nonempty inline chain replays on the κ-graph from the
    copy's entry `enL` to the return node `r`: each link's run reaches `exL`,
    whose pending action fires while crossing a gadget edge — the back-edge
    `exL → enL` for every link but the last (needed only when there are at
    least two links, hence the conditional hypothesis `hback`; κ = 1 sites
    have no back-edge but also never need one), and `exL → r` for the
    last. -/
theorem chain_replay (cfg : WFCFG) {enL exL r : NodeID}
    (hout : (⟨exL, r, .plain⟩ : Edge) ∈ cfg.val.edges)
    {k : Nat} {σ σ' : State} (hchain : InlineChain cfg enL exL k σ σ')
    (hback : 2 ≤ k → (⟨exL, enL, .plain⟩ : Edge) ∈ cfg.val.edges)
    (hk : 1 ≤ k) :
    LSteps (ls := kappaLangSem cfg) cfg.kappa.analysis enL σ r σ' := by
  revert hback hk
  induction hchain with
  | zero => intro _ hk; omega
  | @succ k σ σ₁ σ'' hlink hrest ih =>
    intro hback _
    obtain ⟨σm, hrun, hstep⟩ := hlink
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · -- last link: the pending `exL` action fires across `exL → r`
      cases hrest
      have hmem : (⟨exL, r, .plain⟩ : Edge) ∈ cfg.kappa.analysis.edges :=
        CFG.kappa_edges_mem.mpr hout
      exact LSteps.trans _ hrun
        (LSteps.single cfg.kappa.analysis (e := ⟨⟨exL, r, .plain⟩, hmem⟩) hstep)
    · -- interior link: the pending action fires across the back-edge
      have hb := hback (by omega)
      have hmem : (⟨exL, enL, .plain⟩ : Edge) ∈ cfg.kappa.analysis.edges :=
        CFG.kappa_edges_mem.mpr hb
      have htail := ih (fun _ => hback (by omega)) hpos
      exact LSteps.trans _ hrun
        (LSteps.step (g := cfg.kappa.analysis)
          (e := ⟨⟨exL, enL, .plain⟩, hmem⟩) hstep htail rfl)

-- # The projection obligation

/-- The projection conclusion of `balanced_project`, packaged so the step
    cases can be stated and proved as focused helper lemmas. -/
def BPGoal (p : Program) (N : Nat) (cfg : WFCFG) (key : LamKey)
    (n : NodeID) (σ : State) (ρ : Option Clo)
    (n' : NodeID) (σ' : State) (ρ' : Option Clo) : Prop :=
  ∃ (hρ : BoundedLamChain p.family N key ρ ρ') (q : Nat) (c' : CntState),
    BoundedLamChain.Count hρ q ∧
    LSteps (ls := countingLangSem cfg) cfg.kappa.analysis n (σ, 0) n' c' ∧
    c' = (σ', q) ∧
    LSteps (ls := fdukeLangSem cfg) cfg.analysis n σ n' σ'

/-- The strong-induction hypothesis of `balanced_project`, abstracted so the
    step-case helper lemmas can consume it for strictly shorter sub-runs on
    *any* CFG of the family (nested calls and invokes leave `self`). -/
def BPIH (p : Program) (N : Nat) : Prop :=
  ∀ m, m < N → ∀ {self : CFGRef} (cfg : WFCFG),
    p.family.cfgAt? self = some cfg →
    ∀ (key : LamKey) (K : Kont) {n n' : NodeID} {σ σ' : State}
      {ρ ρ' : Option Clo},
      StepsOver p.family K m ⟨(self, n), σ, ρ, K⟩ ⟨(self, n'), σ', ρ', K⟩ →
      (∀ clo, ρ = some clo → clo.enL = key.enL ∧ clo.exL = key.exL) →
      CloWF p.family ρ → KontWF p.family K →
      BPGoal p N cfg key n σ ρ n' σ' ρ'

/-- The ghost counter of a counting κ-graph run may be shifted by a constant:
    `CntStep` only ever compares counters up to an additive offset. -/
theorem cnt_shift (cfg : WFCFG) (d : Nat) {n n' : NodeID} {c c' : CntState}
    (h : LSteps (ls := countingLangSem cfg) cfg.kappa.analysis n c n' c') :
    LSteps (ls := countingLangSem cfg) cfg.kappa.analysis
      n (c.1, c.2 + d) n' (c'.1, c'.2 + d) := by
  induction h with
  | refl => exact .refl _ _
  | @step e a b s₀ s₁ s₂ hstep htail hsrc ih =>
    refine LSteps.step (g := cfg.kappa.analysis) (e := e) ?_ ih hsrc
    obtain ⟨hκ, hcnt⟩ := hstep
    exact ⟨hκ, by simp only [hcnt]; split <;> omega⟩
  | @stut a b s₀ s₁ s₂ hstut htail ih =>
    refine LSteps.stut ?_ ih
    have : s₀ = s₁ := hstut
    subst this
    rfl

theorem CntInlineChain.count_shift {cfg : WFCFG} {enL exL : NodeID}
    {k d : Nat} {c c' : CntState}
    (h : CntInlineChain cfg enL exL k c c') :
    CntInlineChain cfg enL exL k (c.1, c.2 + d) (c'.1, c'.2 + d) := by
  induction h with
  | zero => exact .zero
  | succ hlink htail ih =>
      rcases hlink with ⟨cm, hrun, hstep⟩
      refine .succ ⟨(cm.1, cm.2 + d), ?_, ?_⟩ ih
      · exact cnt_shift cfg d hrun
      · obtain ⟨hk, hc⟩ := hstep
        exact ⟨hk, by simp only [hc]; split <;> omega⟩

/-
Equivariance identifies the standalone endpoints of a freshly lowered call
    body with the endpoints recorded in its inline gadget.
-/
theorem lowerStmt_call_body_endpoints (Φ : FunEnv) (f : String) (body : Stmt)
    (b : BState) (enL exL : NodeID) (bb : BState)
    (hbody : StateT.run (lowerStmt Φ body)
      { cfg := { nodes := b.cfg.nodes ++ [.Call f b.nextLam], edges := b.cfg.edges,
                 entry := b.cfg.entry, exit := b.cfg.exit },
        nextID := b.nextID + 1, nextLam := b.nextLam + 1,
        callGadgets := b.callGadgets } = ((enL, exL), bb)) :
    (body.wfcfgFrom Φ (b.nextLam + 1)).val.entry + enL = enL ∧
    (body.wfcfgFrom Φ (b.nextLam + 1)).val.exit + enL = exL := by
  unfold Stmt.wfcfgFrom; simp +decide only [Stmt.cfgFrom, Nat.add_eq_right];
  convert lowerStmt_equivariant Φ body _ _ ( b.nextID + 1 ) 0 _ _;
  rotate_left;
  · exact ⟨ ⟨ [ ], [ ], 0, 0 ⟩, 0, b.nextLam + 1, [ ] ⟩;
  · exact ⟨
      ⟨ b.cfg.nodes ++ [ NodeKind.Call f b.nextLam ], b.cfg.edges, b.cfg.entry, b.cfg.exit ⟩,
      b.nextID + 1, b.nextLam + 1, b.callGadgets ⟩;
  · simp;
  · rfl;
  · cases h : StateT.run ( lowerStmt Φ body ) { cfg := { nodes := [], edges := [], entry := 0, exit := 0 }, nextID := 0, nextLam := b.nextLam + 1 } ; simp_all +decide only;
    have := lowerStmt_equivariant Φ body { cfg := { nodes := [], edges := [], entry := 0, exit := 0 }, nextID := 0, nextLam := b.nextLam + 1 } { cfg := { nodes := b.cfg.nodes ++ [ NodeKind.Call f b.nextLam ], edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit }, nextID := b.nextID + 1, nextLam := b.nextLam + 1, callGadgets := b.callGadgets } ( b.nextID + 1 ) 0 ; simp_all +decide;
    have := lowerStmt_entry_eq_nextID Φ body { cfg := { nodes := [], edges := [], entry := 0, exit := 0 }, nextID := 0, nextLam := b.nextLam + 1 } ; aesop;

/-- Every retained gadget agrees with the call-node metadata in its builder. -/
def CallMetadataValid (Φ : FunEnv) (b : BState) : Prop :=
  ∀ site ∈ b.callGadgets,
    b.cfg.nodeKind site.en = some (.Call site.f site.lamID) ∧
      site.kappa = callKind Φ site.f

/-
Appending nodes preserves metadata for all already-recorded gadgets.
-/
theorem CallMetadataValid.mono {Φ : FunEnv} {b b' : BState}
    (h : CallMetadataValid Φ b) (hg : b'.callGadgets = b.callGadgets)
    {ns : List NodeKind} (hn : b'.cfg.nodes = b.cfg.nodes ++ ns) :
    CallMetadataValid Φ b' := by
  intro site hsite; specialize h site; simp_all +decide only [forall_const, and_true] ;
  unfold CFG.nodeKind at *; simp_all +decide [ List.getElem?_append ] ;
  grind

/-
The atomic builder operations which do not record a gadget preserve its
    metadata invariant.
-/
theorem callMetadata_addNode (Φ : FunEnv) (b : BState) (k : NodeKind)
    (h : CallMetadataValid Φ b) :
    CallMetadataValid Φ ((Builder.addNode k).run b).2 := by
  exact CallMetadataValid.mono h rfl rfl

theorem callMetadata_addEdge (Φ : FunEnv) (b : BState) (src dst : NodeID)
    (h : CallMetadataValid Φ b) :
    CallMetadataValid Φ ((Builder.addEdge src dst).run b).2 := by
  apply CallMetadataValid.mono h rfl (ns := [])
  simp

/-
Recording a gadget preserves metadata when its call-node fact already
    holds in the current graph.
-/
theorem callMetadata_addGadget (Φ : FunEnv) (b : BState) (site : CallGadget)
    (h : CallMetadataValid Φ b)
    (hsite : b.cfg.nodeKind site.en = some (.Call site.f site.lamID) ∧
      site.kappa = callKind Φ site.f) :
    CallMetadataValid Φ ((Builder.addCallGadget site).run b).2 := by
  intro site' hsite'; simp_all +decide [ CallMetadataValid ] ;
  cases hsite' <;> simp_all +decide [ CFG.nodeKind ]

-- temporary
set_option linter.flexible false in
/-
The call constructor preserves metadata, including for its freshly
    recorded outer gadget.
-/
theorem lowerStmt_call_preserves_callMetadata (Φ : FunEnv) (f : String)
    (body : Stmt)
    (ih : ∀ (b : BState), b.nextID = b.cfg.nodes.length →
      CallMetadataValid Φ b → CallMetadataValid Φ ((lowerStmt Φ body).run b).2) :
    ∀ (b : BState), b.nextID = b.cfg.nodes.length → CallMetadataValid Φ b →
      CallMetadataValid Φ ((lowerStmt Φ (.Call f body)).run b).2 := by
  intros b hb h metadata;
  revert metadata;
  unfold lowerStmt;
  cases h : StateT.run ( lowerStmt Φ body ) { cfg := { nodes := b.cfg.nodes ++ [ NodeKind.Call f b.nextLam ], edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit }, nextID := b.nextID + 1, nextLam := b.nextLam + 1, callGadgets := b.callGadgets } ; simp_all +decide only ;
  have := ih { cfg := { nodes := b.cfg.nodes ++ [ NodeKind.Call f b.nextLam ], edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit }, nextID := b.cfg.nodes.length + 1, nextLam := b.nextLam + 1, callGadgets := b.callGadgets } ?_ ?_ <;> simp_all +decide [ CallMetadataValid ];
  · simp +decide [ Bind.bind ] at *;
    simp +decide [ Functor.map ] at *;
    rintro metadata ( h | rfl ) <;> simp_all +decide [ CFG.nodeKind ];
    · grind;
    · have := lowerStmt_spec Φ body { cfg := { nodes := b.cfg.nodes ++ [ NodeKind.Call f b.nextLam ], edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit }, nextID := b.cfg.nodes.length + 1, nextLam := b.nextLam + 1, callGadgets := b.callGadgets } ; simp_all +decide only ;
      grind +revert;
  · intro site hsite; specialize ‹∀ site ∈ b.callGadgets, b.cfg.nodeKind site.en = some ( NodeKind.Call site.f site.lamID ) ∧ site.kappa = callKind Φ site.f› site hsite; simp_all +decide [ CFG.nodeKind ] ;
    grind

/-
Sequential composition preserves metadata when both substatements do.
-/
theorem lowerStmt_seq_preserves_callMetadata (Φ : FunEnv) (s₁ s₂ : Stmt)
    (ih₁ : ∀ (b : BState), b.nextID = b.cfg.nodes.length →
      CallMetadataValid Φ b → CallMetadataValid Φ ((lowerStmt Φ s₁).run b).2)
    (ih₂ : ∀ (b : BState), b.nextID = b.cfg.nodes.length →
      CallMetadataValid Φ b → CallMetadataValid Φ ((lowerStmt Φ s₂).run b).2) :
    ∀ (b : BState), b.nextID = b.cfg.nodes.length → CallMetadataValid Φ b →
      CallMetadataValid Φ ((lowerStmt Φ (s₁ ;; s₂)).run b).2 := by
  intro b hb hmetadata
  obtain ⟨a, b₁, hrun⟩ := lowerStmt_spec Φ s₁ b hb;
  exact ih₂ _ a ( ih₁ _ hb hmetadata )

-- temporary
set_option linter.flexible false in
/-
Conditional composition preserves metadata when both branches do.
-/
theorem lowerStmt_if_preserves_callMetadata (Φ : FunEnv) (c : FExpr) (t f : Stmt)
    (iht : ∀ (b : BState), b.nextID = b.cfg.nodes.length →
      CallMetadataValid Φ b → CallMetadataValid Φ ((lowerStmt Φ t).run b).2)
    (ihf : ∀ (b : BState), b.nextID = b.cfg.nodes.length →
      CallMetadataValid Φ b → CallMetadataValid Φ ((lowerStmt Φ f).run b).2) :
    ∀ (b : BState), b.nextID = b.cfg.nodes.length → CallMetadataValid Φ b →
      CallMetadataValid Φ ((lowerStmt Φ (.If c t f)).run b).2 := by
  intro b hb h metadata;
  unfold lowerStmt;
  simp +decide [ Builder.addNode, Builder.addEdge ] at *;
  cases h : StateT.run ( lowerStmt Φ t ) { cfg := { nodes := b.cfg.nodes ++ [ NodeKind.Skip, NodeKind.Assume c, NodeKind.Assume ( @! c ) ], edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit }, nextID := b.nextID + 1 + 1 + 1, nextLam := b.nextLam, callGadgets := b.callGadgets } ; simp_all +decide;
  have := iht { cfg := { nodes := b.cfg.nodes ++ [ NodeKind.Skip, NodeKind.Assume c, NodeKind.Assume ( @! c ) ], edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit }, nextID := b.cfg.nodes.length + 1 + 1 + 1, nextLam := b.nextLam, callGadgets := b.callGadgets } ?_ ?_ <;> simp_all +decide [ CallMetadataValid ];
  · simp +decide [ Bind.bind, Functor.map ] at *;
    intro hmetadata;
    convert ihf _ _ _ _ hmetadata using 1;
    · unfold CFG.nodeKind; simp +decide [ List.getElem?_append ] ;
      grind;
    · have := lowerStmt_spec Φ t { cfg := { nodes := b.cfg.nodes ++ [ NodeKind.Skip, NodeKind.Assume c, NodeKind.Assume ( @! c ) ], edges := b.cfg.edges, entry := b.cfg.entry, exit := b.cfg.exit }, nextID := b.cfg.nodes.length + 1 + 1 + 1, nextLam := b.nextLam, callGadgets := b.callGadgets } ; simp_all +decide;
    · exact this;
  · intro site hsite; specialize ‹∀ site ∈ b.callGadgets, b.cfg.nodeKind site.en = some ( NodeKind.Call site.f site.lamID ) ∧ site.kappa = callKind Φ site.f› site hsite; simp_all +decide [ CFG.nodeKind ] ;
    grind

/-
Loop lowering preserves metadata when its body does.
-/
theorem lowerStmt_while_preserves_callMetadata (Φ : FunEnv) (c : FExpr) (body : Stmt)
    (ih : ∀ (b : BState), b.nextID = b.cfg.nodes.length →
      CallMetadataValid Φ b → CallMetadataValid Φ ((lowerStmt Φ body).run b).2) :
    ∀ (b : BState), b.nextID = b.cfg.nodes.length → CallMetadataValid Φ b →
      CallMetadataValid Φ ((lowerStmt Φ (.While c body)).run b).2 := by
  unfold lowerStmt;
  simp +decide only [Builder.addNode, bind_pure_comp, Builder.addEdge, bind_assoc, bind_map_left,
    LawfulMonadStateOf.set_bind_get_bind, List.append_assoc, List.cons_append, List.nil_append,
    LawfulMonadStateOf.set_bind_set_bind, StateT.run_bind, StateT.run_get, StateT.run_set,
    StateT.run_modify, StateT.run_map, map_pure, pure_bind] at *;
  intro b hb h metadata
  specialize ih {
    cfg := {
      nodes := b.cfg.nodes ++ [ NodeKind.Skip, NodeKind.Assume c, NodeKind.Assume ( @! c ) ],
      edges := b.cfg.edges,
      entry := b.cfg.entry,
      exit := b.cfg.exit
    },
    nextID := b.cfg.nodes.length + 1 + 1 + 1,
    nextLam := b.nextLam,
    callGadgets := b.callGadgets } ?_ ?_ <;> simp_all +decide only [CallMetadataValid,
      List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, and_true]
  · intro site hsite; specialize h site hsite; unfold CFG.nodeKind at *; simp_all +decide only [
      List.getElem?_append, getElem?_pos, ite_eq_left_iff, Nat.not_lt] ;
    grind;
  · convert ih metadata using 1

/-
Statement lowering preserves exact call-site metadata.
-/
theorem lowerStmt_preserves_callMetadata (Φ : FunEnv) (s : Stmt) :
    ∀ (b : BState), b.nextID = b.cfg.nodes.length → CallMetadataValid Φ b →
      CallMetadataValid Φ ((lowerStmt Φ s).run b).2 := by
  induction s using Stmt.recOn with
  | Skip => exact fun _ _ h => CallMetadataValid.mono h rfl rfl
  | Decl => exact fun _ _ h => CallMetadataValid.mono h rfl rfl
  | Assign => exact fun _ _ h => CallMetadataValid.mono h rfl rfl
  | If c t e t_ih e_ih =>
      exact lowerStmt_if_preserves_callMetadata Φ c t e t_ih e_ih
  | While c b b_ih =>
      exact lowerStmt_while_preserves_callMetadata Φ c b b_ih
  | Seq s₁ s₂ s₁_ih s₂_ih =>
      exact lowerStmt_seq_preserves_callMetadata Φ s₁ s₂ s₁_ih s₂_ih
  | Invoke => exact fun _ _ h => CallMetadataValid.mono h rfl rfl
  | Call f body body_ih =>
      exact lowerStmt_call_preserves_callMetadata Φ f body body_ih

/-
Every call gadget retained by a generated statement records the exact
    call node and declared invocation kind from which it was emitted.
-/
theorem Stmt.generatedCFGFrom_gadget_metadata (Φ : FunEnv)
    (startLam : Nat) (s : Stmt) {site : CallGadget}
    (hsite : site ∈ (s.generatedCFGFrom Φ startLam).callGadgets) :
    (s.generatedCFGFrom Φ startLam).cfg.nodeKind site.en =
        some (.Call site.f site.lamID) ∧
      site.kappa = callKind Φ site.f := by
  exact lowerStmt_preserves_callMetadata Φ s
    { cfg := { nodes := [], edges := [], entry := 0, exit := 0 },
      nextID := 0, nextLam := startLam }
    rfl (by simp [CallMetadataValid]) site hsite

/-
Resolving a function component recovers its declaration tuple in the
    family list, including the invocation kind checked for that component.
-/
theorem CFGFamily.fn_mem_of_cfgAt {fam : CFGFamily} {f : String} {F : WFCFG}
    (hF : fam.cfgAt? (.fn f) = some F) :
    ∃ κ, (f, κ, F) ∈ fam.funCFGs := by
  simp [CFGFamily.cfgAt?, CFGFamily.view, CFGFamilyView.cfgAt?] at hF
  grind +suggestions

/-
Folding function declarations preserves the source order of names and
    invocation kinds.
-/
theorem family_fold_name_kind (p : Program) (xs : FunEnv) :
    ∀ (acc : List (String × InvKind × WFCFG) × List (Nat × Stmt) × Nat),
      (xs.foldl (fun acc fb =>
        let (funs, lams, c) := acc
        let (f, κ, body) := fb
        let wrapped := body ;; Stmt.Skip
        let (bl, c') := (collectLams wrapped).run c
        (funs ++ [(f, κ, wrapped.wfcfgFrom p.phi c)], lams ++ bl, c')) acc).1.map
          (fun q => (q.1, q.2.1)) =
        acc.1.map (fun q => (q.1, q.2.1)) ++ xs.map (fun q => (q.1, q.2.1)) := by
  induction xs <;> grind

/-
The first matching name in the name/kind projection agrees with
    `FunEnv.lookup`.
-/
theorem find_name_kind_eq_callKind (Φ : FunEnv) (f : String) {κ : InvKind}
    (h : (Φ.map (fun q => (q.1, q.2.1))).find? (fun q => q.1 = f) =
      some (f, κ)) :
    callKind Φ f = κ := by
  induction Φ <;> simp_all +decide [ callKind ]; grind [FunEnv.lookup]

/-
Resolving a generated function component recovers the invocation kind
    selected by the source environment's lookup.
-/
theorem Program.family_fn_kind (p : Program) {f : String} {F : WFCFG}
    (hF : p.family.cfgAt? (.fn f) = some F) :
    (f, callKind p.phi f, F) ∈ p.family.funCFGs := by
  -- By definition of `p.family`, we know that if `p.family.cfgAt? (.fn f) = some F`,
  -- then `F` must be one of the function entries in `p.family.funCFGs`.
  specialize hF;
  simp [CFGFamily.cfgAt?, CFGFamily.view, CFGFamilyView.cfgAt?] at hF
  have := List.find?_eq_some_iff_append.mp hF.choose_spec.choose_spec; simp_all +decide ;
  have h_lookup :
      (p.family.funCFGs.map (fun q => (q.1, q.2.1))) = (p.phi.map (fun q => (q.1, q.2.1))) := by
    convert family_fold_name_kind p p.phi _ using 1;
  have h_lookup : (f, hF.choose_spec.choose) ∈ p.phi.map (fun q => (q.1, q.2.1)) := by
    grind;
  have h_lookup : callKind p.phi f = hF.choose_spec.choose := by
    apply find_name_kind_eq_callKind;
    grind +suggestions;
  grind

/-
Every call gadget newly recorded while lowering a statement has inline
    endpoints equal to its standalone body endpoints shifted by the inline
    entry.  The statement is builder-relative so sequential and branching
    recursive calls can thread their accumulated gadget lists.
-/
theorem lowerStmt_new_gadget_body_endpoints (Φ : FunEnv) (s : Stmt) :
    ∀ (b : BState) (site : CallGadget),
      site ∈ ((lowerStmt Φ s).run b).2.callGadgets →
      site ∈ b.callGadgets ∨
        ((site.body.wfcfgFrom Φ (site.lamID + 1)).val.entry + site.enL = site.enL ∧
         (site.body.wfcfgFrom Φ (site.lamID + 1)).val.exit + site.enL = site.exL) := by
  intro b site hsite;
  revert hsite;
  induction s generalizing b;
  all_goals simp +decide only [Nat.add_eq_right, lowerStmt, bind_pure_comp, StateT.run_bind,
    addCallNodeWithLam_run, addNode_run, StateT.run_map, addCallGadget_run,
    CallGadget.edges_mk] at *;
  all_goals simp_all +decide only [bind, true_or, implies_true, Functor.map, List.mem_append,
    List.append_assoc, List.cons_append, List.nil_append, addEdge_run, List.mem_cons,
    List.not_mem_nil, or_false];
  · grind;
  · grind;
  · grind;
  · rename_i h₁ h₂;
    intro hsite
    cases hsite;
    · grind;
    · rename_i f h
      let a : BState := {
          cfg := {
            nodes := b.cfg.nodes ++ [NodeKind.Call f b.nextLam],
            edges := b.cfg.edges,
            entry := b.cfg.entry,
            exit := b.cfg.exit
          },
          nextID := b.nextID + 1, nextLam := b.nextLam + 1,
          callGadgets := b.callGadgets }
      rcases hrun : StateT.run (lowerStmt Φ h₁) a with ⟨⟨enL, exL⟩, bb⟩
      have hends :=
        lowerStmt_call_body_endpoints Φ f h₁ b site.enL site.exL
          (StateT.run (lowerStmt Φ h₁) a |>.2)
      right
      grind
/-
The standalone body's endpoints shift exactly to the endpoints recorded
    by a generated call gadget.
-/
theorem Stmt.generatedCFGFrom_gadget_body_endpoints (Φ : FunEnv)
    (startLam : Nat) (s : Stmt) {site : CallGadget}
    (hsite : site ∈ (s.generatedCFGFrom Φ startLam).callGadgets) :
    (site.body.wfcfgFrom Φ (site.lamID + 1)).val.entry + site.enL = site.enL ∧
    (site.body.wfcfgFrom Φ (site.lamID + 1)).val.exit + site.enL = site.exL := by
  have := lowerStmt_new_gadget_body_endpoints Φ s {
    cfg := { nodes := [], edges := [], entry := 0, exit := 0 }, nextID := 0, nextLam := startLam
    } site hsite
  aesop

/-
Every component resolved from a program's generated family is the lowering
    of its recorded source with the program environment and recorded offset.
-/
theorem Program.generatedFamily_component_generated (p : Program) {ref : CFGRef}
    {component : CertifiedGeneratedCFG}
    (hresolve : p.generatedFamily.cfgAt? ref = some component) :
    component.phi = p.phi ∧
    component.generated = component.source.generatedCFGFrom p.phi component.startLam := by
  have hcomponent :=
    GeneratedCFGFamily.Program.generatedFamily_component_canonical p hresolve
  exact ⟨hcomponent ▸ rfl, hcomponent ▸ rfl⟩

/-
A gadget in a resolved generated component retains exact call-node and
    invocation-kind metadata in the erased caller CFG.
-/
theorem Program.family_gadget_metadata (p : Program) {ref : CFGRef}
    {cfg : WFCFG} (hcfg : p.family.cfgAt? ref = some cfg)
    {comp : CertifiedGeneratedCFG}
    (hresolve : p.generatedFamily.cfgAt? ref = some comp)
    {site : CallGadget} (hsite : site ∈ comp.generated.callGadgets) :
    cfg.val.nodeKind site.en = some (.Call site.f site.lamID) ∧
      site.kappa = callKind p.phi site.f := by
  have hcfg_eq : cfg = comp.wfcfg := by
    obtain ⟨ comp', hcomp', hcfg' ⟩ := ( p.family_cfgAt?_iff_generatedFamily ref cfg ).mp hcfg
    aesop
  have := Program.generatedFamily_component_generated p hresolve
  simp_all +decide only
  convert Stmt.generatedCFGFrom_gadget_metadata p.phi comp.startLam comp.source hsite using 1;
  rw [ ← this.2, CertifiedGeneratedCFG.wfcfg ]

theorem Program.family_gadget_body_endpoints (p : Program) {ref : CFGRef}
    {component : CertifiedGeneratedCFG}
    (hresolve : p.generatedFamily.cfgAt? ref = some component)
    {site : CallGadget} (hsite : site ∈ component.generated.callGadgets) :
    (site.body.wfcfgFrom p.phi (site.lamID + 1)).val.entry + site.enL = site.enL ∧
    (site.body.wfcfgFrom p.phi (site.lamID + 1)).val.exit + site.enL = site.exL := by
  have hcanonical := Program.generatedFamily_component_generated p hresolve
  rw [hcanonical.2] at hsite
  exact Stmt.generatedCFGFrom_gadget_body_endpoints
    p.phi component.startLam component.source hsite

/-- Result of turning a bounded callback chain obtained inside a callee into
    the caller-local inline chain.  The two counts are intentionally distinct:
    `callbackCount` indexes executions of the site's callback body, while
    `outerCount` counts invocations performed by those body executions and is
    therefore the count attached to the evolved outer chain. -/
def CallInlineProjection (p : Program) (N : Nat) (cfg : WFCFG)
    (outerKey : LamKey) (site : CallGadget) (outerρ outerρ' : Option Clo)
    (σ σ' : State) (callbackCount : Nat) : Prop :=
  ∃ (outerChain : BoundedLamChain p.family N outerKey outerρ outerρ')
    (outerCount : Nat) (cEnd : CntState),
    BoundedLamChain.Count outerChain outerCount ∧
    CntInlineChain cfg site.enL site.exL callbackCount (σ, 0) cEnd ∧
    cEnd = (σ', outerCount)

/-- Recursively project every retained callback-body execution through the
    registered standalone lambda CFG and transport it into this call site's
    inline fragment.  Bounds are retained so each recursive body projection is
    justified by `BPIH`. -/
theorem bounded_chain_to_inline (p : Program) {N : Nat} (ih : BPIH p N)
    {self : CFGRef} (cfg : WFCFG) (hcfg : p.family.cfgAt? self = some cfg)
    (outerKey : LamKey) (K : Kont) (site : CallGadget)
    {component : CertifiedGeneratedCFG}
    (hcomponent : p.generatedFamily.cfgAt? self = some component)
    (hsite : site ∈ component.generated.callGadgets)
    (hfragment : cfg.val.HasInlineBodyFragment p.phi site)
    {L : WFCFG} (hL : p.family.cfgAt? (.lam site.lamID) = some L)
    {outerρ outerρ' : Option Clo} {σ σ' : State}
    {hchain : BoundedLamChain p.family N
      ⟨(.lam site.lamID, L.val.entry), (.lam site.lamID, L.val.exit)⟩
      (some ⟨(.lam site.lamID, L.val.entry),
        (.lam site.lamID, L.val.exit), outerρ, σ⟩)
      (some ⟨(.lam site.lamID, L.val.entry),
        (.lam site.lamID, L.val.exit), outerρ', σ'⟩)}
    {callbackCount : Nat} (hcount : BoundedLamChain.Count hchain callbackCount)
    (houter : ∀ clo, outerρ = some clo →
      clo.enL = outerKey.enL ∧ clo.exL = outerKey.exL)
    (_ : CloWF p.family outerρ) (hwfK : KontWF p.family K) :
    CallInlineProjection p N cfg outerKey site outerρ outerρ' σ σ' callbackCount := by
  cases hchain with
  | refl =>
      cases hcount
      exact ⟨.refl outerρ, 0, (σ, 0), .refl outerρ, .zero, rfl⟩
  | @«invoke» clo ρ₁ σ₁ ρ₂ hen hex body tail =>
      cases hcount
      rename_i k hcountTail
      have hbodyProj := ih body.k body.lt_bound L hL outerKey
        (.inv body.nr
          (some ⟨(.lam site.lamID, L.val.entry),
            (.lam site.lamID, L.val.exit), outerρ, σ⟩) body.σf :: body.K)
        body.run houter body.wf_parent
        (.cons (CloWF.some hL body.wf_parent) body.wf_kont)
      obtain ⟨hbodyChain, qBody, cBody, hbodyCount, hcntBody,
        hcBody, _⟩ := hbodyProj
      subst cBody
      have hstand := Program.family_gadget_standalone_wfcfg p hcomponent hsite
      have hLeq : L = (site.body ;; Stmt.Skip).wfcfgFrom p.phi
          (site.lamID + 1) := by
        rw [hstand] at hL
        exact (Option.some.inj hL).symm
      subst L
      obtain ⟨cm, hprefix, hexit⟩ :=
        standalone_seq_skip_exit_decompose p.phi (site.lamID + 1)
          site.body hcntBody
      have hlink := cnt_link_transport cfg p.phi site hfragment hprefix hexit
      have hwfEnd := body.run.toSteps.wf
        (show ConfWF p.family
          ⟨(.lam site.lamID, (site.body ;; Stmt.Skip).wfcfgFrom p.phi
              (site.lamID + 1) |>.val.entry), σ, outerρ,
            .inv body.nr
              (some ⟨(.lam site.lamID,
                  (site.body ;; Stmt.Skip).wfcfgFrom p.phi
                    (site.lamID + 1) |>.val.entry),
                (.lam site.lamID,
                  (site.body ;; Stmt.Skip).wfcfgFrom p.phi
                    (site.lamID + 1) |>.val.exit), outerρ, σ⟩)
              body.σf :: body.K⟩ from
          ⟨body.wf_parent,
            .cons (CloWF.some hL body.wf_parent) body.wf_kont⟩)
      have hwfρ₁ : CloWF p.family ρ₁ := hwfEnd.1
      have houter₁ := hbodyChain.key_end houter
      obtain ⟨htailChain, qTail, cTail, htailCount, hinlineTail,
        hcTail⟩ := bounded_chain_to_inline p ih cfg hcfg outerKey K site
          hcomponent hsite hfragment hL hcountTail houter₁ hwfρ₁ hwfK
      subst cTail
      refine ⟨hbodyChain.trans htailChain, qBody + qTail,
        (σ', qBody + qTail), hbodyCount.trans htailCount, ?_, rfl⟩
      have hshiftedTail := hinlineTail.count_shift (d := qBody)
      have hends := Program.family_gadget_body_endpoints p
        (ref := self) hcomponent hsite
      have hlink' : CntInlineBodyRun cfg site.enL site.exL
          (σ, 0) (σ₁, qBody) := by
        simpa [hends.1, hends.2] using hlink
      simp only [Nat.zero_add] at hshiftedTail
      have hcombined := hshiftedTail.cons hlink'
      simpa only [Nat.add_comm] using hcombined

/-- Unfold a family successor of a located node into the caller CFG edge that
    produces it. -/
theorem succ_mem_iff {fam : CFGFamily} {self : CFGRef} {cfg : WFCFG}
    (hcfg : fam.cfgAt? self = some cfg) {n : NodeID} {nr : NodeRef} :
    nr ∈ fam.succ (self, n) ↔
      ∃ e ∈ cfg.val.edges, e.src = n ∧ nr = (self, e.dst) := by
  unfold CFGFamily.succ
  rw [hcfg]
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨he, hsrc⟩, rfl⟩
    exact ⟨e, he, hsrc, rfl⟩
  · rintro ⟨e, he, hsrc, rfl⟩
    exact ⟨e, ⟨he, hsrc⟩, rfl⟩

/-- Prepend one intra-procedural `.plain` edge to a projection: the store
    takes an `IntraStep`, the node is not an `Invoke` (so the ghost counter is
    untouched), and the edge is present in the caller CFG. -/
theorem bp_prepend_intra (p : Program) {N : Nat} (cfg : WFCFG) (key : LamKey)
    {n m n' : NodeID} {σ σ₁ σ' : State} {ρ ρ' : Option Clo}
    (hedge : (⟨n, m, .plain⟩ : Edge) ∈ cfg.val.edges)
    (hintra : IntraStep cfg.val n σ σ₁)
    (hninv : cfg.val.nodeKind n ≠ some .Invoke)
    (htail : BPGoal p N cfg key m σ₁ ρ n' σ' ρ') :
    BPGoal p N cfg key n σ ρ n' σ' ρ' := by
  obtain ⟨hρ, q, c', hcount, hcnt, hc'eq, hfduke⟩ := htail
  have hmem : (⟨n, m, .plain⟩ : Edge) ∈ cfg.analysis.edges := hedge
  have hmemκ : (⟨n, m, .plain⟩ : Edge) ∈ cfg.kappa.analysis.edges :=
    CFG.kappa_edges_mem.mpr hedge
  refine ⟨hρ, q, c', hcount, ?_, hc'eq, ?_⟩
  · refine LSteps.step (g := cfg.kappa.analysis) (e := ⟨⟨n, m, .plain⟩, hmemκ⟩)
      ?_ hcnt rfl
    exact ⟨Or.inl hintra, by simp [hninv]⟩
  · exact LSteps.step (g := cfg.analysis) (e := ⟨⟨n, m, .plain⟩, hmem⟩)
      (Or.inl hintra) hfduke rfl

/-- Every ordinary successor of a located node lives in the same CFG. -/
theorem succ_fst {fam : CFGFamily} {nr x : NodeRef} (hx : x ∈ fam.succ nr) :
    x.1 = nr.1 := by
  unfold CFGFamily.succ at hx
  cases hc : fam.cfgAt? nr.1 with
  | none => rw [hc] at hx; simp at hx
  | some cfg =>
    rw [hc] at hx
    simp only [List.mem_map, List.mem_filter] at hx
    obtain ⟨e, _, rfl⟩ := hx
    rfl


/-- Compose two consecutive balanced projections: the ambient chains chain up
    (`LamChain.trans`/`LamChain.Count.trans`), the counting κ shadows compose
    with the first segment's final count shifted onto the second (`cnt_shift`),
    and the store-only `fduke` runs concatenate. -/
theorem BPGoal.trans {p : Program} {N : Nat} {cfg : WFCFG} {key : LamKey}
    {n m n' : NodeID} {σ τ σ' : State} {ρ μ ρ' : Option Clo}
    (h₁ : BPGoal p N cfg key n σ ρ m τ μ)
    (h₂ : BPGoal p N cfg key m τ μ n' σ' ρ') :
    BPGoal p N cfg key n σ ρ n' σ' ρ' := by
  obtain ⟨hρ₁, q₁, c₁, hcount₁, hcnt₁, hc₁eq, hfd₁⟩ := h₁
  obtain ⟨hρ₂, q₂, c₂, hcount₂, hcnt₂, hc₂eq, hfd₂⟩ := h₂
  subst hc₁eq; subst hc₂eq
  refine ⟨hρ₁.trans hρ₂, q₁ + q₂, (σ', q₁ + q₂),
    hcount₁.trans hcount₂, ?_, rfl, LSteps.trans _ hfd₁ hfd₂⟩
  refine LSteps.trans _ hcnt₁ ?_
  have h := cnt_shift cfg q₁ hcnt₂
  have e1 : (0 : Nat) + q₁ = q₁ := by omega
  have e2 : q₂ + q₁ = q₁ + q₂ := by omega
  simpa only [e1, e2] using h

/-- A balanced run that starts and ends with the ambient stack exactly `G`
    never leaves the CFG it starts in: the located CFG-ref at the two `G`-level
    endpoints agrees.  Only `call`/`invoke` (push) and `ret-call`/`ret-inv`
    (pop) change the CFG-ref, and they are balanced, so at `G`-level the
    CFG-ref is constant. -/
theorem stepsOver_same_cfg {fam : CFGFamily} {G : Kont} :
    ∀ (k : Nat) {c c' : Conf}, StepsOver fam G k c c' → c.K = G → c'.K = G →
      c'.n.1 = c.n.1 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro c c' h hc hc'
    cases h with
    | refl _ => rfl
    | @step k' cc c₁ ce hsuf hstep hrest =>
      have hk' : k' < k' + 1 := Nat.lt_succ_self k'
      cases hstep with
      | @assign a nr x e v σ₀ ρ₀ K₀ hkind heval hs =>
        have := ih k' hk' hrest hc hc'
        rw [this]; exact succ_fst hs
      | @assume a nr m0 cnd σ₀ ρ₀ K₀ hkind heval hne hs =>
        have := ih k' hk' hrest hc hc'
        rw [this]; exact succ_fst hs
      | @skip a nr σ₀ ρ₀ K₀ hkind hs =>
        have := ih k' hk' hrest hc hc'
        rw [this]; exact succ_fst hs
      | @«call» a nr f ℓ F L σ₀ ρ₀ K₀ hkind hF hL hs =>
        -- pushes `.call nr ρ₀`; find the first return to `G`
        subst hc
        have hstrict : (Frame.call nr ρ₀ :: K₀) ≠ K₀ := by
          intro heq; simpa using congrArg List.length heq
        obtain ⟨F', ka, kb, cp, cq, hpref, hpop, hqK, htail, hklen⟩ :=
          hrest.first_return hstrict
        have hcpK : cp.K = F' :: K₀ := hpref.suffix.2
        have hsufF : F' :: K₀ <:+ (Frame.call nr ρ₀ :: K₀) := hpref.suffix.1
        have hFeq : F' = Frame.call nr ρ₀ := by
          have heq := List.IsSuffix.eq_of_length hsufF (by simp)
          simpa [List.cons.injEq] using heq
        subst hFeq
        have hcqn : cq.n = nr := by
          cases hpop with
          | @retCall a2 nr2 enL2 exL2 rho2 rhoc2 s2 sc2 K2 hnil =>
            have h2 := hcpK
            simp only [List.cons.injEq, Frame.call.injEq] at h2
            exact h2.1.1
          | @retInv a2 nr2 enL2 exL2 rho2 rhod2 s2 sd2 sf2 K2 hnil =>
            exact absurd hcpK (by simp)
          | @assign a2 nr2 x2 e2 v2 s2 r2 K2 hk2 he2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @assume a2 nr2 m2 cc2 s2 r2 K2 hk2 he2 hne2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @skip a2 nr2 s2 r2 K2 hk2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @«call» a2 nr2 f2 l2 F2 L2 s2 r2 K2 hk2 hF2 hL2 hs2 =>
            exfalso
            have l1 := congrArg List.length hcpK
            have l2 := congrArg List.length hqK
            simp at l1 l2
            omega
          | @«invoke» a2 nr2 enL2 exL2 L2 rd2 sd2 s2 r2 K2 hk2 hr2 hL2 hs2 =>
            exfalso
            have l1 := congrArg List.length hcpK
            have l2 := congrArg List.length hqK
            simp at l1 l2
            omega
        have hqn1 : cq.n.1 = a.1 := by rw [hcqn]; exact succSummary_fst hs
        have hkb : kb < k' + 1 := by omega
        have := ih kb hkb htail hqK hc'
        rw [this, hqn1]
      | @«invoke» a nr enL exL L ρd σd σ₀ ρ₀ K₀ hkind hρeq hL hs =>
        subst hc
        have hstrict : (Frame.inv nr ρ₀ σ₀ :: K₀) ≠ K₀ := by
          intro heq; simpa using congrArg List.length heq
        obtain ⟨F', ka, kb, cp, cq, hpref, hpop, hqK, htail, hklen⟩ :=
          hrest.first_return hstrict
        have hcpK : cp.K = F' :: K₀ := hpref.suffix.2
        have hsufF : F' :: K₀ <:+ (Frame.inv nr ρ₀ σ₀ :: K₀) := hpref.suffix.1
        have hFeq : F' = Frame.inv nr ρ₀ σ₀ := by
          have heq := List.IsSuffix.eq_of_length hsufF (by simp)
          simpa [List.cons.injEq] using heq
        subst hFeq
        have hcqn : cq.n = nr := by
          cases hpop with
          | @retInv a2 nr2 enL2 exL2 rho2 rhod2 s2 sd2 sf2 K2 hnil =>
            have h2 := hcpK
            simp only [List.cons.injEq, Frame.inv.injEq] at h2
            exact h2.1.1
          | @retCall a2 nr2 enL2 exL2 rho2 rhoc2 s2 sc2 K2 hnil =>
            exact absurd hcpK (by simp)
          | @assign a2 nr2 x2 e2 v2 s2 r2 K2 hk2 he2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @assume a2 nr2 m2 cc2 s2 r2 K2 hk2 he2 hne2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @skip a2 nr2 s2 r2 K2 hk2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @«call» a2 nr2 f2 l2 F2 L2 s2 r2 K2 hk2 hF2 hL2 hs2 =>
            exfalso
            have l1 := congrArg List.length hcpK
            have l2 := congrArg List.length hqK
            simp at l1 l2
            omega
          | @«invoke» a2 nr2 enL2 exL2 L2 rd2 sd2 s2 r2 K2 hk2 hr2 hL2 hs2 =>
            exfalso
            have l1 := congrArg List.length hcpK
            have l2 := congrArg List.length hqK
            simp at l1 l2
            omega
        have hqn1 : cq.n.1 = a.1 := by rw [hcqn]; exact succ_fst hs
        have hkb : kb < k' + 1 := by omega
        have := ih kb hkb htail hqK hc'
        rw [this, hqn1]
      | @retInv a nr enL exL ρ'₀ ρd σ₀ σd σf K₀ hnil =>
        exfalso
        have hsuf2 : G <:+ K₀ := hrest.suffix.1
        have hle := hsuf2.length_le
        have hGlen : G.length = K₀.length + 1 := by
          have hG : G = Frame.inv nr (some (Clo.mk enL exL ρd σd)) σf :: K₀ := hc.symm
          rw [hG]; simp
        omega
      | @retCall a nr enL exL ρ'₀ ρc σ₀ σc K₀ hnil =>
        exfalso
        have hsuf2 : G <:+ K₀ := hrest.suffix.1
        have hle := hsuf2.length_le
        have hGlen : G.length = K₀.length + 1 := by
          have hG : G = Frame.call nr ρ'₀ :: K₀ := hc.symm
          rw [hG]; simp
        omega

/-- In a well-formed CFG, a located node that is in bounds and has no ordinary
    successors is the CFG's exit node. -/
theorem succ_nil_eq_exit {fam : CFGFamily} {ref : CFGRef} {L : WFCFG}
    (hL : fam.cfgAt? ref = some L) {m : NodeID}
    (hlt : m < L.val.nodes.length) (hnil : fam.succ (ref, m) = []) :
    m = L.val.exit := by
  by_contra hne
  obtain ⟨n', hn'⟩ := L.prop.2.2.2.1 m hlt hne
  have hmem : (ref, n') ∈ fam.succ (ref, m) :=
    (succ_mem_iff hL).mpr ⟨⟨m, n', .plain⟩, hn', rfl, rfl⟩
  rw [hnil] at hmem
  exact absurd hmem (by simp)


/-- A balanced run that starts and ends with ambient stack exactly `G` keeps
    its located node within the bounds of the (single) CFG it lives in.  This
    complements `stepsOver_same_cfg`: the CFG-ref is constant, and here the
    node id stays `< nodes.length`. -/
theorem stepsOver_inbounds {fam : CFGFamily} {G : Kont} :
    ∀ (k : Nat) {c c' : Conf}, StepsOver fam G k c c' → c.K = G → c'.K = G →
      ∀ (Lo : WFCFG), fam.cfgAt? c.n.1 = some Lo →
      c.n.2 < Lo.val.nodes.length →
      c'.n.2 < Lo.val.nodes.length := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro c c' h hc hc' Lo hcfg hlt
    cases h with
    | refl _ => exact hlt
    | @step k' cc c₁ ce hsuffix hstep hrest =>
      have hk' : k' < k' + 1 := Nat.lt_succ_self k'
      cases hstep with
      | @assign a nr x e v σ₀ ρ₀ K₀ hkind heval hs =>
        have hb : nr.2 < Lo.val.nodes.length := by
          obtain ⟨ed, hed, hesrc, hnr⟩ := (succ_mem_iff hcfg).mp hs
          rw [hnr]; exact Lo.prop.2.2.1 ed hed
        have hcfg' : fam.cfgAt? nr.1 = some Lo := by rw [succ_fst hs]; exact hcfg
        exact ih k' hk' hrest hc hc' Lo hcfg' hb
      | @assume a nr m0 cnd σ₀ ρ₀ K₀ hkind heval hne hs =>
        have hb : nr.2 < Lo.val.nodes.length := by
          obtain ⟨ed, hed, hesrc, hnr⟩ := (succ_mem_iff hcfg).mp hs
          rw [hnr]; exact Lo.prop.2.2.1 ed hed
        have hcfg' : fam.cfgAt? nr.1 = some Lo := by rw [succ_fst hs]; exact hcfg
        exact ih k' hk' hrest hc hc' Lo hcfg' hb
      | @skip a nr σ₀ ρ₀ K₀ hkind hs =>
        have hb : nr.2 < Lo.val.nodes.length := by
          obtain ⟨ed, hed, hesrc, hnr⟩ := (succ_mem_iff hcfg).mp hs
          rw [hnr]; exact Lo.prop.2.2.1 ed hed
        have hcfg' : fam.cfgAt? nr.1 = some Lo := by rw [succ_fst hs]; exact hcfg
        exact ih k' hk' hrest hc hc' Lo hcfg' hb
      | @«call» a nr f ℓ F L σ₀ ρ₀ K₀ hkind hF hL hs =>
        subst hc
        have hstrict : (Frame.call nr ρ₀ :: K₀) ≠ K₀ := by
          intro heq; simpa using congrArg List.length heq
        obtain ⟨F', ka, kb, cp, cq, hpref, hpop, hqK, htail, hklen⟩ :=
          hrest.first_return hstrict
        have hcpK : cp.K = F' :: K₀ := hpref.suffix.2
        have hsufF : F' :: K₀ <:+ (Frame.call nr ρ₀ :: K₀) := hpref.suffix.1
        have hFeq : F' = Frame.call nr ρ₀ := by
          have heq := List.IsSuffix.eq_of_length hsufF (by simp)
          simpa [List.cons.injEq] using heq
        subst hFeq
        have hcqn : cq.n = nr := by
          cases hpop with
          | @retCall a2 nr2 enL2 exL2 rho2 rhoc2 s2 sc2 K2 hnil =>
            have h2 := hcpK
            simp only [List.cons.injEq, Frame.call.injEq] at h2
            exact h2.1.1
          | @retInv a2 nr2 enL2 exL2 rho2 rhod2 s2 sd2 sf2 K2 hnil =>
            exact absurd hcpK (by simp)
          | @assign a2 nr2 x2 e2 v2 s2 r2 K2 hk2 he2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @assume a2 nr2 m2 cc2 s2 r2 K2 hk2 he2 hne2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @skip a2 nr2 s2 r2 K2 hk2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @«call» a2 nr2 f2 l2 F2 L2 s2 r2 K2 hk2 hF2 hL2 hs2 =>
            exfalso
            have l1 := congrArg List.length hcpK
            have l2 := congrArg List.length hqK
            simp at l1 l2
            omega
          | @«invoke» a2 nr2 enL2 exL2 L2 rd2 sd2 s2 r2 K2 hk2 hr2 hL2 hs2 =>
            exfalso
            have l1 := congrArg List.length hcpK
            have l2 := congrArg List.length hqK
            simp at l1 l2
            omega
        have hb : cq.n.2 < Lo.val.nodes.length := by
          rw [hcqn]
          obtain ⟨site, _, hedge, hnr⟩ := (succSummary_mem_iff hcfg).mp hs
          rw [hnr]; exact Lo.prop.2.2.1 _ hedge
        have hcfgq : fam.cfgAt? cq.n.1 = some Lo := by
          rw [hcqn, succSummary_fst hs]; exact hcfg
        have hkb : kb < k' + 1 := by omega
        exact ih kb hkb htail hqK hc' Lo hcfgq hb
      | @«invoke» a nr enL exL L ρd σd σ₀ ρ₀ K₀ hkind hρeq hL hs =>
        subst hc
        have hstrict : (Frame.inv nr ρ₀ σ₀ :: K₀) ≠ K₀ := by
          intro heq; simpa using congrArg List.length heq
        obtain ⟨F', ka, kb, cp, cq, hpref, hpop, hqK, htail, hklen⟩ :=
          hrest.first_return hstrict
        have hcpK : cp.K = F' :: K₀ := hpref.suffix.2
        have hsufF : F' :: K₀ <:+ (Frame.inv nr ρ₀ σ₀ :: K₀) := hpref.suffix.1
        have hFeq : F' = Frame.inv nr ρ₀ σ₀ := by
          have heq := List.IsSuffix.eq_of_length hsufF (by simp)
          simpa [List.cons.injEq] using heq
        subst hFeq
        have hcqn : cq.n = nr := by
          cases hpop with
          | @retInv a2 nr2 enL2 exL2 rho2 rhod2 s2 sd2 sf2 K2 hnil =>
            have h2 := hcpK
            simp only [List.cons.injEq, Frame.inv.injEq] at h2
            exact h2.1.1
          | @retCall a2 nr2 enL2 exL2 rho2 rhoc2 s2 sc2 K2 hnil =>
            exact absurd hcpK (by simp)
          | @assign a2 nr2 x2 e2 v2 s2 r2 K2 hk2 he2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @assume a2 nr2 m2 cc2 s2 r2 K2 hk2 he2 hne2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @skip a2 nr2 s2 r2 K2 hk2 hs2 =>
            exact absurd hcpK (by rw [hqK]; simp)
          | @«call» a2 nr2 f2 l2 F2 L2 s2 r2 K2 hk2 hF2 hL2 hs2 =>
            exfalso
            have l1 := congrArg List.length hcpK
            have l2 := congrArg List.length hqK
            simp at l1 l2
            omega
          | @«invoke» a2 nr2 enL2 exL2 L2 rd2 sd2 s2 r2 K2 hk2 hr2 hL2 hs2 =>
            exfalso
            have l1 := congrArg List.length hcpK
            have l2 := congrArg List.length hqK
            simp at l1 l2
            omega
        have hb : cq.n.2 < Lo.val.nodes.length := by
          rw [hcqn]
          obtain ⟨ed, hed, hesrc, hnr⟩ := (succ_mem_iff hcfg).mp hs
          rw [hnr]; exact Lo.prop.2.2.1 ed hed
        have hcfgq : fam.cfgAt? cq.n.1 = some Lo := by
          rw [hcqn, succ_fst hs]; exact hcfg
        have hkb : kb < k' + 1 := by omega
        exact ih kb hkb htail hqK hc' Lo hcfgq hb
      | @retInv a nr enL exL ρ'₀ ρd σ₀ σd σf K₀ hnil =>
        exfalso
        have hsuf2 : G <:+ K₀ := hrest.suffix.1
        have hle := hsuf2.length_le
        have hGlen : G.length = K₀.length + 1 := by
          have hG : G = Frame.inv nr (some (Clo.mk enL exL ρd σd)) σf :: K₀ := hc.symm
          rw [hG]; simp
        omega
      | @retCall a nr enL exL ρ'₀ ρc σ₀ σc K₀ hnil =>
        exfalso
        have hsuf2 : G <:+ K₀ := hrest.suffix.1
        have hle := hsuf2.length_le
        have hGlen : G.length = K₀.length + 1 := by
          have hG : G = Frame.call nr ρ'₀ :: K₀ := hc.symm
          rw [hG]; simp
        omega

/-- Invert a well-formed non-empty closure: it delimits a registered lambda
    CFG, so its entry/exit are that CFG's entry/exit and its captured
    environment is itself well-formed. -/
theorem cloWF_some_inv {fam : CFGFamily} {enL exL : NodeRef} {ρd : Option Clo}
    {σd : State} (h : CloWF fam (some (.mk enL exL ρd σd))) :
    ∃ ℓ L, fam.cfgAt? (.lam ℓ) = some L ∧
      enL = (.lam ℓ, L.val.entry) ∧ exL = (.lam ℓ, L.val.exit) ∧
      CloWF fam ρd := by
  cases h with
  | some hlam hρd => exact ⟨_, _, hlam, rfl, rfl, hρd⟩

-- temporary
set_option linter.flexible false in
/-
Surgery for the invoke case: a balanced run that begins in a lambda body
    (the configuration right after an `invoke` push) splits into the completed
    body run — which necessarily ends at the lambda's exit — and the tail that
    resumes the invoker after the matching `ret-inv`.
-/
theorem invoke_body_decompose (p : Program) {L : WFCFG} {ℓ : Nat}
    {enL exL : NodeRef} {ρd : Option Clo} {σd : State}
    (hlam : p.family.cfgAt? (.lam ℓ) = some L)
    (henL : enL = (.lam ℓ, L.val.entry)) (hexL : exL = (.lam ℓ, L.val.exit))
    {nr : NodeRef} {σ : State} {K : Kont} {k' : Nat}
    {self : CFGRef} {n' : NodeID} {σ' : State} {ρ' : Option Clo}
    (hrest : StepsOver p.family K k'
      ⟨enL, σd, ρd, .inv nr (some (.mk enL exL ρd σd)) σ :: K⟩
      ⟨(self, n'), σ', ρ', K⟩) :
    ∃ (kb : Nat) (σ_b : State) (ρ_b : Option Clo) (kt : Nat),
      StepsOver p.family (.inv nr (some (.mk enL exL ρd σd)) σ :: K) kb
        ⟨enL, σd, ρd, .inv nr (some (.mk enL exL ρd σd)) σ :: K⟩
        ⟨exL, σ_b, ρ_b, .inv nr (some (.mk enL exL ρd σd)) σ :: K⟩ ∧
      StepsOver p.family K kt
        ⟨nr, σ, some (.mk enL exL ρ_b σ_b), K⟩ ⟨(self, n'), σ', ρ', K⟩ ∧
      kt < k' + 1 ∧ kb < k' + 1 := by
  obtain ⟨ka, kb, cp, cq, hpref, hpop, hqK, htail, hklen⟩ : ∃ ka kb cp cq, StepsOver p.family (Frame.inv nr (some ⟨enL, exL, ρd, σd⟩) σ :: K) ka ⟨enL, σd, ρd, Frame.inv nr (some ⟨enL, exL, ρd, σd⟩) σ :: K⟩ cp ∧ Step p.family cp cq ∧ cq.K = K ∧ StepsOver p.family K kb cq ⟨(self, n'), σ', ρ', K⟩ ∧ k' = ka + 1 + kb := by
    have := hrest.first_return (by aesop)
    obtain ⟨ F, k₁, k₂, c₁, c₂, h₁, h₂, h₃, h₄, h₅ ⟩ := this
    use k₁, k₂, c₁, c₂
    simp_all +decide only [ and_self, and_true ]
    have := h₁.suffix
    simp_all +decide only [ List.IsSuffix ]
    obtain ⟨ t, ht ⟩ := this.1; replace ht := congr_arg List.reverse ht
    simp_all +decide [ List.reverse_append ] ;
  rcases hpop with ( _ | _ | _ | _ | _ | hpop );
  all_goals have := hpref.suffix; simp_all +decide [ Prod.ext_iff ] ;
  · replace hqK := congr_arg List.length hqK ; simp +arith +decide at hqK;
  · replace hqK := congr_arg List.length hqK ; simp +arith +decide at hqK;
  · rename_i n nr' enL' exL' ρ' ρd' σ' σd' σf' K';
    have h_eq : n = exL := by
      have h_eq : n.1 = .lam ℓ := by
        convert stepsOver_same_cfg _ hpref rfl _ using 1;
        · exact henL.1.symm;
        · grind;
      have h_eq : n.2 < L.val.nodes.length := by
        have := stepsOver_inbounds ka hpref; simp_all +decide [ Prod.ext_iff ] ;
        exact this ( L.prop.1 );
      grind +suggestions;
    grind +splitIndPred

/-- The invoke step case of `balanced_project`: a complete closure invocation
    (`invoke … ret-inv`) is store-identity for the invoker, appends one link to
    the ambient-closure `LamChain` (bumping the ghost count by one), and
    replays as one κ-graph invoke hop in the caller's shadow. -/
theorem balanced_project_invoke (p : Program)
    {N : Nat} (ih : BPIH p N)
    {self : CFGRef} (cfg : WFCFG) (hcfg : p.family.cfgAt? self = some cfg)
    (key : LamKey) (K : Kont) {n n' : NodeID} {σ σ' : State}
    {ρ ρ' : Option Clo} {k' : Nat} (hk' : k' < N)
    {enL exL : NodeRef} {ρd : Option Clo} {σd : State}
    {nr : NodeRef}
    (hkind : p.family.kind (self, n) = some .Invoke)
    (hρeq : ρ = some (.mk enL exL ρd σd))
    (hsucc : nr ∈ p.family.succ (self, n))
    (hrest : StepsOver p.family K k'
      ⟨enL, σd, ρd, .inv nr ρ σ :: K⟩ ⟨(self, n'), σ', ρ', K⟩)
    (hkey : ∀ clo, ρ = some clo → clo.enL = key.enL ∧ clo.exL = key.exL)
    (hwfρ : CloWF p.family ρ) (hwfK : KontWF p.family K) :
    BPGoal p N cfg key n σ ρ n' σ' ρ' := by
  subst hρeq
  -- Node-kind and outgoing-edge facts for the caller's invoke node.
  have hnk : cfg.val.nodeKind n = some .Invoke := by
    have := hkind; simp only [CFGFamily.kind, hcfg] at this; simpa using this
  obtain ⟨ed, hed, hesrc, hnrEq⟩ := (succ_mem_iff hcfg).mp hsucc
  have hplain : ed.kind = .plain := by cases ed.kind; rfl
  have hedge : (⟨n, ed.dst, .plain⟩ : Edge) ∈ cfg.val.edges := by
    have hee : ed = ⟨n, ed.dst, .plain⟩ := by cases ed; simp_all
    rwa [← hee]
  -- Closure inversion, then body/tail decomposition of the run.
  obtain ⟨ℓ, Lc, hlam, henL, hexL, hρd⟩ := cloWF_some_inv hwfρ
  obtain ⟨kb, σ_b, ρ_b, kt, hbody, htail, hktlt, hkblt⟩ :=
    invoke_body_decompose p hlam henL hexL hrest
  have hnrself : nr = (self, ed.dst) := hnrEq
  -- Well-formedness of the closure produced at `ret-inv`.
  have hwfEntry : ConfWF p.family
      ⟨enL, σd, ρd, .inv nr (some (.mk enL exL ρd σd)) σ :: K⟩ :=
    ⟨hρd, .cons hwfρ hwfK⟩
  have hwfEnd : ConfWF p.family
      ⟨exL, σ_b, ρ_b, .inv nr (some (.mk enL exL ρd σd)) σ :: K⟩ :=
    hbody.toSteps.wf hwfEntry
  have hρb : CloWF p.family ρ_b := hwfEnd.1
  have hρc : CloWF p.family (some (.mk enL exL ρ_b σ_b)) := by
    rw [henL, hexL]; exact CloWF.some hlam hρb
  have hkk := hkey _ rfl
  have hkeyc : ∀ clo, (some (.mk enL exL ρ_b σ_b) : Option Clo) = some clo →
      clo.enL = key.enL ∧ clo.exL = key.exL := by
    rintro clo heq; injection heq with h; subst h; exact hkk
  -- Apply the induction hypothesis to the (strictly shorter) tail.
  have htail' : StepsOver p.family K kt
      ⟨(self, ed.dst), σ, some (.mk enL exL ρ_b σ_b), K⟩
      ⟨(self, n'), σ', ρ', K⟩ := by rw [← hnrself]; exact htail
  obtain ⟨hchainT, qT, cT, hcountT, hcntT, hcTeq, hfdukeT⟩ :=
    ih kt (by omega) cfg hcfg key K htail' hkeyc hρc hwfK
  subst hcTeq
  -- Ambient closure evolves by this invocation prepended to the tail chain.
  have hbodyLam : BoundedLamBodyRun p.family N (.mk enL exL ρd σd) ρ_b σ_b := {
    nr := nr
    σf := σ
    K := K
    k := kb
    run := hbody
    lt_bound := by omega
    wf_parent := hρd
    wf_kont := hwfK }
  -- Counting κ-graph run: the invoke node bumps the ghost counter by one.
  have hmemκ : (⟨n, ed.dst, .plain⟩ : Edge) ∈ cfg.kappa.analysis.edges :=
    CFG.kappa_edges_mem.mpr hedge
  have hstepCnt : CntStep cfg.val n (σ, 0) (σ, 1) :=
    ⟨Or.inl (Or.inr (Or.inr (Or.inr ⟨hnk, rfl⟩))), by simp [hnk]⟩
  have hcntWhole : LSteps (ls := countingLangSem cfg) cfg.kappa.analysis
      n (σ, 0) n' (σ', qT + 1) := by
    refine LSteps.step (g := cfg.kappa.analysis)
      (e := ⟨⟨n, ed.dst, .plain⟩, hmemκ⟩) hstepCnt ?_ rfl
    simpa using cnt_shift cfg 1 hcntT
  -- Store-only structural run: the invoke node is store-identity.
  have hmem : (⟨n, ed.dst, .plain⟩ : Edge) ∈ cfg.analysis.edges := hedge
  have hfdukeWhole : LSteps (ls := fdukeLangSem cfg) cfg.analysis n σ n' σ' := by
    refine LSteps.step (g := cfg.analysis)
      (e := ⟨⟨n, ed.dst, .plain⟩, hmem⟩) ?_ hfdukeT rfl
    change fdukeLStep cfg ⟨n, ed.dst, .plain⟩ σ σ
    simp only [fdukeLStep]
    exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hnk, rfl⟩)))
  exact ⟨_, qT + 1, (σ', qT + 1),
    BoundedLamChain.Count.invoke (hen := hkk.1) (hex := hkk.2) (body := hbodyLam) hcountT,
    hcntWhole, rfl, hfdukeWhole⟩

/-
Surgery for the call case: a balanced run that begins by entering a callee
    function `f` (the configuration right after a `call` push) splits into the
    completed callee run — which necessarily ends at `f`'s exit, carrying the
    threaded closure that `ret-call` returns — and the tail that resumes the
    caller.
-/
theorem call_body_decompose (p : Program) {F : WFCFG} {f : String}
    {clo0 : Clo} {nr : NodeRef} {ρ : Option Clo} {K : Kont} {k' : Nat}
    {self : CFGRef} {n' : NodeID} {σ' : State} {ρ' : Option Clo}
    (hF : p.family.cfgAt? (.fn f) = some F)
    (hrest : StepsOver p.family K k'
      ⟨(.fn f, F.val.entry), State.empty, some clo0, .call nr ρ :: K⟩
      ⟨(self, n'), σ', ρ', K⟩) :
    ∃ (kb : Nat) (σc_body : State) (enL' exL' : NodeRef) (ρc : Option Clo)
      (σc : State) (kt : Nat),
      StepsOver p.family (.call nr ρ :: K) kb
        ⟨(.fn f, F.val.entry), State.empty, some clo0, .call nr ρ :: K⟩
        ⟨(.fn f, F.val.exit), σc_body, some (.mk enL' exL' ρc σc),
          .call nr ρ :: K⟩ ∧
      StepsOver p.family K kt ⟨nr, σc, ρc, K⟩ ⟨(self, n'), σ', ρ', K⟩ ∧
      kt < k' + 1 ∧ kb < k' + 1 := by
  apply Classical.byContradiction
  intro h_no_kb;
  obtain ⟨F', ka, kb, cp, cq, hpref, hpop, hqK, htail, hklen⟩ := hrest.first_return (by
    intro heq; simpa using congrArg List.length heq)
  have hcpK : cp.K = F' :: K := by
    exact hpref.suffix.2.symm ▸ rfl
  have hFeq : F' = Frame.call nr ρ := by
    have := hpref.suffix.1; simp_all +decide only [exists_and_left, Prod.exists, not_exists,
      not_and, Nat.not_lt, List.IsSuffix] ;
    obtain ⟨ t, ht ⟩ := this
    replace ht := congr_arg List.reverse ht
    simp_all +decide [ List.reverse_append ]
  subst hFeq
  generalize_proofs at *;
  rcases hpop with ( _ | _ | _ | _ | _ ) <;> simp_all +decide only;
  all_goals try { have := congr_arg List.length hqK; simp +arith +decide at this };
  · cases hcpK;
  · rename_i n nr enL exL ρ' ρc σ σc K' hnil;
    have hcp_n : n.1 = CFGRef.fn f := by
      have := stepsOver_same_cfg ka hpref rfl ( by aesop ) ; aesop;
    generalize_proofs at *;
    have hcp_n : n.2 = F.val.exit := by
      apply succ_nil_eq_exit hF;
      · have := hpref.suffix.2;
        apply stepsOver_inbounds ka hpref this this F hF (by
        exact F.prop.1);
      · grind
    generalize_proofs at *;
    grind +splitIndPred

/-- The heart of the call case: a completed function call projects onto the
    caller's structural gadget path from `n` to `nr.2`. Its ambient effect is
    the chain of invocations performed while running the callee, and its κ
    shadow is the counted inline chain admitted by the callee's verdict.

    This isolates the standalone→inline transport / counting-verdict machinery
    from the surrounding tail plumbing; `balanced_project_call` obtains it and
    composes with the induction hypothesis on the tail via `BPGoal.trans`. -/
theorem call_step_bpgoal (p : Program) (hchecked : FamilyChecked p.family)
    {N : Nat} (ih : BPIH p N)
    {self : CFGRef} (cfg : WFCFG) (hcfg : p.family.cfgAt? self = some cfg)
    (key : LamKey) (K : Kont) {n : NodeID} {σ : State} {ρ : Option Clo}
    {f : String} {ℓ : Nat} {F L : WFCFG} {nr : NodeRef}
    {kb : Nat} (hkbN : kb < N)
    {σc_body σc : State} {enL' exL' : NodeRef} {ρc : Option Clo}
    (hkind : p.family.kind (self, n) = some (.Call f ℓ))
    (hF : p.family.cfgAt? (.fn f) = some F)
    (hL : p.family.cfgAt? (.lam ℓ) = some L)
    (hsucc : nr ∈ p.family.succSummary (self, n))
    (hbody : StepsOver p.family (.call nr ρ :: K) kb
      ⟨(.fn f, F.val.entry), State.empty,
        some (.mk (.lam ℓ, L.val.entry) (.lam ℓ, L.val.exit) ρ σ),
        .call nr ρ :: K⟩
      ⟨(.fn f, F.val.exit), σc_body, some (.mk enL' exL' ρc σc),
        .call nr ρ :: K⟩)
    (hkey : ∀ clo, ρ = some clo → clo.enL = key.enL ∧ clo.exL = key.exL)
    (hwfρ : CloWF p.family ρ) (hwfK : KontWF p.family K) :
    BPGoal p N cfg key n σ ρ nr.2 σc ρc := by
  -- Step 1: project the callee body run with the callback lambda's own key,
  -- via the induction hypothesis at the callee CFG `F`.
  have hkeyL : ∀ clo,
      (some (.mk (.lam ℓ, L.val.entry) (.lam ℓ, L.val.exit) ρ σ) : Option Clo)
        = some clo →
      clo.enL = (⟨(.lam ℓ, L.val.entry), (.lam ℓ, L.val.exit)⟩ : LamKey).enL ∧
      clo.exL = (⟨(.lam ℓ, L.val.entry), (.lam ℓ, L.val.exit)⟩ : LamKey).exL := by
    rintro clo ⟨⟩; exact ⟨rfl, rfl⟩
  have hcallee : BPGoal p N F ⟨(.lam ℓ, L.val.entry), (.lam ℓ, L.val.exit)⟩
      F.val.entry State.empty
      (some (.mk (.lam ℓ, L.val.entry) (.lam ℓ, L.val.exit) ρ σ))
      F.val.exit σc_body (some (.mk enL' exL' ρc σc)) :=
    ih kb hkbN F hF ⟨(.lam ℓ, L.val.entry), (.lam ℓ, L.val.exit)⟩
      (.call nr ρ :: K) hbody hkeyL (CloWF.some hL hwfρ) (.cons hwfρ hwfK)
  obtain ⟨hcb, callbackCount, cCallee, hcbCount, hcntCallee,
    hcCallee, _⟩ := hcallee
  subst cCallee
  obtain ⟨site, hlookup, _, hnr⟩ := (succSummary_mem_iff hcfg).mp hsucc
  have hret : site.ret = nr.2 := by rw [hnr]
  rw [Program.family_gadgetAt?_eq_generatedFamily] at hlookup
  obtain ⟨component, hcomponent, hsite, hen⟩ :=
    GeneratedCFGFamily.gadgetAt?_resolved hlookup
  obtain ⟨component', hcomponent', hwfcfg⟩ :=
    (p.family_cfgAt?_iff_generatedFamily self cfg).mp hcfg
  have hcomponentEq : component = component' := by
    rw [hcomponent] at hcomponent'
    exact Option.some.inj hcomponent'
  subst component'
  have hmeta := Program.family_gadget_metadata p hcfg hcomponent hsite
  have hkindCfg : cfg.val.nodeKind n = some (.Call f ℓ) := by
    have := hkind
    simp only [CFGFamily.kind, hcfg] at this
    exact this
  rw [hen, hkindCfg] at hmeta
  have hf : site.f = f := by
    injection Option.some.inj hmeta.1 with hf' _
    exact hf'.symm
  have hlam : site.lamID = ℓ := by
    injection Option.some.inj hmeta.1 with _ hlam'
    exact hlam'.symm
  subst hf
  subst hlam
  have hcanonical := Program.generatedFamily_component_generated p hcomponent
  have hfragment : cfg.val.HasInlineBodyFragment p.phi site := by
    rw [← hwfcfg, ← hcanonical.1]
    exact component.inline_body_fragment hsite
  have hcbEnd := hcb.key_end hkeyL
  have hcallbackEndpoints := hcbEnd _ rfl
  have henL' : enL' = (.lam site.lamID, L.val.entry) := by
    simpa using hcallbackEndpoints.1
  have hexL' : exL' = (.lam site.lamID, L.val.exit) := by
    simpa using hcallbackEndpoints.2
  subst enL'
  subst exL'
  obtain ⟨outerChain, outerCount, cEnd, houterCount, hinline, hcEnd⟩ :=
    bounded_chain_to_inline p ih cfg hcfg key K site hcomponent hsite hfragment
      hL hcbCount hkey hwfρ hwfK
  subst cEnd
  have hfunmem := Program.family_fn_kind p hF
  obtain ⟨rd, hpf, hentry, hverdict⟩ := hchecked _ hfunmem
  have hreach : Reachable F.kappa.analysis F.val.exit
      (σc_body, callbackCount) (fun c => c.1 = State.empty /\ c.2 = 0) :=
    ⟨(State.empty, 0), ⟨rfl, rfl⟩, hcntCallee⟩
  have habs : (rd F.val.exit) (abs callbackCount) :=
    counting_correct F hpf hentry hreach
  have hadmit : κAdmits site.kappa callbackCount := by
    rw [hmeta.2]
    exact κAdmits_of_verdict hverdict habs
  have hgadget : ∀ e ∈ kappaEdges site.kappa n site.enL site.exL nr.2,
      e ∈ cfg.val.edges := by
    intro ed hed
    rw [← hen, ← hret] at hed
    rw [← hwfcfg]
    exact component.gadget_present hsite hed
  have hcntCaller : LSteps (ls := countingLangSem cfg) cfg.kappa.analysis
      n (σ, 0) nr.2 (σc, outerCount) :=
    cnt_call_chain_replay cfg hkindCfg hgadget hadmit hinline
  have hfduke : LSteps (ls := fdukeLangSem cfg) cfg.analysis
      n σ nr.2 σc := by
    simpa [fdukeLStep, CFG.kappa] using lsteps_forget_count cfg hcntCaller
  exact ⟨outerChain, outerCount, (σc, outerCount), houterCount,
    hcntCaller, rfl, hfduke⟩

/-- The call step case of `balanced_project`: a complete function call
    (`call … ret-call`) follows its site's structural gadget path, whose inline
    chain length is the κ-admitted invocation count read from the callee's
    counting verdict. It splits (via
    `call_body_decompose`) into the callee body run — projected by
    `call_step_bpgoal` — and the caller tail — projected by the induction
    hypothesis — composed with `BPGoal.trans`. -/
theorem balanced_project_call (p : Program) (hchecked : FamilyChecked p.family)
    {N : Nat} (ih : BPIH p N)
    {self : CFGRef} (cfg : WFCFG) (hcfg : p.family.cfgAt? self = some cfg)
    (key : LamKey) (K : Kont) {n n' : NodeID} {σ σ' : State}
    {ρ ρ' : Option Clo} {k' : Nat} (hk' : k' < N)
    {f : String} {ℓ : Nat} {F L : WFCFG} {nr : NodeRef}
    (hkind : p.family.kind (self, n) = some (.Call f ℓ))
    (hF : p.family.cfgAt? (.fn f) = some F)
    (hL : p.family.cfgAt? (.lam ℓ) = some L)
    (hsucc : nr ∈ p.family.succSummary (self, n))
    (hrest : StepsOver p.family K k'
      ⟨(.fn f, F.val.entry), State.empty,
        some (.mk (.lam ℓ, L.val.entry) (.lam ℓ, L.val.exit) ρ σ),
        .call nr ρ :: K⟩ ⟨(self, n'), σ', ρ', K⟩)
    (hkey : ∀ clo, ρ = some clo → clo.enL = key.enL ∧ clo.exL = key.exL)
    (hwfρ : CloWF p.family ρ) (hwfK : KontWF p.family K) :
    BPGoal p N cfg key n σ ρ n' σ' ρ' := by
  -- CEK surgery: split off the completed callee run and the caller tail.
  obtain ⟨kb, σc_body, enL', exL', ρc, σc, kt, hbody, htail, hktlt, hkblt⟩ :=
    call_body_decompose p hF hrest
  -- Well-formedness of the closure `ret-call` restores.
  have hwfEntry : ConfWF p.family
      ⟨(.fn f, F.val.entry), State.empty,
        some (.mk (.lam ℓ, L.val.entry) (.lam ℓ, L.val.exit) ρ σ),
        .call nr ρ :: K⟩ :=
    ⟨CloWF.some hL hwfρ, .cons hwfρ hwfK⟩
  have hwfEnd := hbody.toSteps.wf hwfEntry
  obtain ⟨_, _, _, _, _, hwfρc⟩ := cloWF_some_inv hwfEnd.1
  -- Project the call portion `n → nr.2` onto its structural gadget path.
  have hcall : BPGoal p N cfg key n σ ρ nr.2 σc ρc :=
    call_step_bpgoal p hchecked ih cfg hcfg key K (show kb < N by omega)
      hkind hF hL hsucc hbody hkey hwfρ hwfK
  -- The ambient key is preserved into `ρc`, so the IH applies to the tail.
  have hkeyc : ∀ clo, ρc = some clo → clo.enL = key.enL ∧ clo.exL = key.exL := by
    obtain ⟨hρcall, _⟩ := hcall
    exact hρcall.key_end hkey
  have hnrself : nr = (self, nr.2) := by
    have h1 := succSummary_fst hsucc
    cases nr; simp_all
  have htail' : StepsOver p.family K kt
      ⟨(self, nr.2), σc, ρc, K⟩ ⟨(self, n'), σ', ρ', K⟩ := by
    rw [← hnrself]; exact htail
  have htailG : BPGoal p N cfg key nr.2 σc ρc n' σ' ρ' :=
    ih kt (show kt < N by omega) cfg hcfg key K htail' hkeyc hwfρc hwfK
  exact hcall.trans htailG

/-- The balanced induction invariant behind `cek_projection`.  Besides the
    denotational projection, it retains a fixed-body trace of ambient closure
    evolution and its exact ghost-counted κ shadow.  The call case uses the
    trace to assemble the certified inline body chain for its summary step. -/
theorem balanced_project (p : Program) (hchecked : FamilyChecked p.family) :
    ∀ (k : Nat) {self : CFGRef} (cfg : WFCFG),
      p.family.cfgAt? self = some cfg →
      ∀ (key : LamKey) (K : Kont) {n n' : NodeID}
        {σ σ' : State} {ρ ρ' : Option Clo},
        StepsOver p.family K k
          ⟨(self, n), σ, ρ, K⟩ ⟨(self, n'), σ', ρ', K⟩ →
        (∀ clo, ρ = some clo → clo.enL = key.enL ∧ clo.exL = key.exL) →
        CloWF p.family ρ → KontWF p.family K →
        ∃ (hρ : BoundedLamChain p.family k key ρ ρ') (q : Nat) (c' : CntState),
          BoundedLamChain.Count hρ q ∧
          LSteps (ls := countingLangSem cfg) cfg.kappa.analysis n (σ, 0) n' c' ∧
          c' = (σ', q) ∧
          LSteps (ls := fdukeLangSem cfg) cfg.analysis n σ n' σ' := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro self cfg hcfg key K n n' σ σ' ρ ρ' h hkey hwfρ hwfK
    have IH : BPIH p k := by
      intro m hm _ cfg₁ hcfg₁ key₁ K₁ _ _ _ _ _ _ hrun₁ hkey₁ hwfρ₁ hwfK₁
      obtain ⟨hρm, q, c', hcountm, hcnt, heq, hfd⟩ :=
        ih m hm cfg₁ hcfg₁ key₁ K₁ hrun₁ hkey₁ hwfρ₁ hwfK₁
      obtain ⟨hρk, hcountk⟩ := hcountm.mono (Nat.le_of_lt hm)
      exact ⟨hρk, q, c', hcountk, hcnt, heq, hfd⟩
    cases h with
    | refl hK =>
      exact ⟨BoundedLamChain.refl ρ, 0, (σ, 0), .refl ρ, .refl _ _, rfl, .refl _ _⟩
    | @step k' c c₁ c'' hsuffix hstep hrest =>
      -- `k = k' + 1`; the intermediate config `c₁` follows from the first step.
      have hk' : k' < k' + 1 := Nat.lt_succ_self k'
      cases hstep with
      | @assign n₀ nr x e v σ₀ ρ₀ K₀ hkind heval hs =>
        -- intra step: a plain edge out of the (non-invoke) assign node
        obtain ⟨ed, hed, hsrc, hnr⟩ := (succ_mem_iff hcfg).mp hs
        have hnk : cfg.val.nodeKind n = some (.Assign x e) := by
          have := hkind; simp only [CFGFamily.kind, hcfg] at this; simpa using this
        subst hnr
        have hedge : (⟨n, ed.dst, .plain⟩ : Edge) ∈ cfg.val.edges := by
          have : ed = ⟨n, ed.dst, .plain⟩ := by
            cases ed; simp_all
          rwa [← this]
        refine bp_prepend_intra p cfg key (σ₁ := σ.updated x v) hedge ?_
          (by rw [hnk]; simp) ?_
        · exact Or.inl ⟨x, e, v, hnk, heval, rfl⟩
        · exact IH k' hk' cfg hcfg key K hrest hkey hwfρ hwfK
      | @assume n₀ nr m0 cnd σ₀ ρ₀ K₀ hkind heval hne hs =>
        obtain ⟨ed, hed, hsrc, hnr⟩ := (succ_mem_iff hcfg).mp hs
        have hnk : cfg.val.nodeKind n = some (.Assume cnd) := by
          have := hkind; simp only [CFGFamily.kind, hcfg] at this; simpa using this
        subst hnr
        have hedge : (⟨n, ed.dst, .plain⟩ : Edge) ∈ cfg.val.edges := by
          have : ed = ⟨n, ed.dst, .plain⟩ := by cases ed; simp_all
          rwa [← this]
        refine bp_prepend_intra p cfg key (σ₁ := σ) hedge ?_
          (by rw [hnk]; simp) ?_
        · exact Or.inr (Or.inl ⟨cnd, m0, hnk, heval, hne, rfl⟩)
        · exact IH k' hk' cfg hcfg key K hrest hkey hwfρ hwfK
      | @skip n₀ nr σ₀ ρ₀ K₀ hkind hs =>
        obtain ⟨ed, hed, hsrc, hnr⟩ := (succ_mem_iff hcfg).mp hs
        have hnk : cfg.val.nodeKind n = some .Skip := by
          have := hkind; simp only [CFGFamily.kind, hcfg] at this; simpa using this
        subst hnr
        have hedge : (⟨n, ed.dst, .plain⟩ : Edge) ∈ cfg.val.edges := by
          have : ed = ⟨n, ed.dst, .plain⟩ := by cases ed; simp_all
          rwa [← this]
        refine bp_prepend_intra p cfg key (σ₁ := σ) hedge ?_
          (by rw [hnk]; simp) ?_
        · exact Or.inr (Or.inr (Or.inl ⟨hnk, rfl⟩))
        · exact IH k' hk' cfg hcfg key K hrest hkey hwfρ hwfK
      | @«call» n₀ nr f ℓ F L σ₀ ρ₀ K₀ hkind hF hL hs =>
        exact balanced_project_call p hchecked IH cfg hcfg key K hk'
          hkind hF hL hs hrest hkey hwfρ hwfK
      | @«invoke» n₀ nr enL exL L ρd σd σ₀ ρ₀ K₀ hkind hρeq hL hs =>
        exact balanced_project_invoke p IH cfg hcfg key K hk'
          hkind hρeq hs hrest hkey hwfρ hwfK
      | @retInv n₀ nr enL exL ρ'₀ ρd σ₀ σd σf K₀ hnil =>
        -- impossible: the return pops below `K`, contradicting balancedness
        have hsuf := (hrest.suffix).1
        simp only at hsuf
        exact absurd hsuf.length_le (by simp)
      | @retCall n₀ nr enL exL ρ'₀ ρc σ₀ σc K₀ hnil =>
        have hsuf := (hrest.suffix).1
        simp only at hsuf
        exact absurd hsuf.length_le (by simp)

/-- **The projection theorem — proved.** In a checked family, every
    ground-truth CEK run located in one caller CFG projects onto its structural
    graph. Each complete `call … ret-call` round trip follows the retained
    gadget with inline-chain length pinned by the callee's counting verdict.

    This is discharged by reduction to `balanced_project`; the two remaining
    interprocedural obligations live in `balanced_project_call` and
    `balanced_project_invoke`. -/
theorem cek_projection (p : Program) (hchecked : FamilyChecked p.family)
    {self : CFGRef} (cfg : WFCFG) (hcfg : p.family.cfgAt? self = some cfg)
    {n n' : NodeID} {σ σ' : State} {ρ' : Option Clo}
    (h : Steps p.family ⟨(self, n), σ, none, []⟩ ⟨(self, n'), σ', ρ', []⟩) :
    LSteps (ls := fdukeLangSem cfg) cfg.analysis n σ n' σ' := by
  obtain ⟨k, hover⟩ := h.toStepsOver_nil rfl
  obtain ⟨-, -, -, -, -, -, hfduke⟩ :=
    balanced_project p hchecked k cfg hcfg ⟨(self, n), (self, n)⟩ [] hover
      (by rintro clo ⟨⟩) CloWF.none KontWF.nil
  exact hfduke

-- # Top-level: κ-rewrite correctness

/-- **κ-rewrite correctness — proved, `sorry`-free.** Any post-fixpoint `rd`
    of an analysis `A` on the structural κ-graph is correct for reachable
    states under `fdukeLangSem`. The two graph views are definitionally the
    same, so reachability transports edge by edge. -/
theorem kappa_rewrite_correct_core (cfg : WFCFG)
    {A : DFA NodeID Edge} [Max A.L]
    (S : DFASemantics (ls := kappaLangSem cfg) cfg.kappa.analysis A)
    (mono_absorb : ∀ {ℓ ℓ' : A.L} {σ : State},
      ℓ ⊑ ℓ' → S.Coh ℓ σ → S.Coh ℓ' σ)
    {rd : NodeID → A.L}
    (hpf : PostFixpoint cfg.kappa.analysis A rd)
    (hentry : A.entry ⊑ rd cfg.kappa.analysis.entry)
    {n : NodeID} {σ : State}
    (hreach : Reachable (ls := fdukeLangSem cfg) cfg.analysis n σ (fdukeLangSem cfg).IsInit) :
    S.Coh (rd n) σ := by
  refine reachable_corr cfg.kappa.analysis S mono_absorb hpf hentry ?_
  refine reachable_of_simulates (ls₁ := fdukeLangSem cfg)
    (ls₂ := kappaLangSem cfg) rfl (fun _ _ _ h => h) ?_ hreach
  intro e σ₀ σ₁ hstep
  have hmem : e.val ∈ cfg.kappa.analysis.edges :=
    CFG.kappa_edges_mem.mpr e.prop
  exact LSteps.single cfg.kappa.analysis (e := ⟨e.val, hmem⟩) hstep

/-
`#print axioms` record:
  * `kappa_rewrite_correct` and the whole refinement direction
    (`chain_replay`, `call_identity_lstep`) —
    no `sorryAx` (only `propext`/`Classical.choice`/`Quot.sound`).
  * `cek_projection` reduces to `balanced_project`, whose reflexive, three
    intra-procedural, both impossible-return, and the interprocedural
    *invoke* step cases are proved.  The invoke case is discharged by the
    strengthened balanced invariant (now threading `CloWF`/`KontWF`) via the
    supporting lemmas `stepsOver_same_cfg` (CFG-locality), `stepsOver_inbounds`
    (node bounds), `succ_nil_eq_exit` (a successor-less in-bounds node is the
    exit), `cloWF_some_inv`, `invoke_body_decompose`, `cnt_shift`,
    `succ_mem_iff`, `succSummary_mem_iff`, `succ_fst`, `succSummary_fst` and
    `bp_prepend_intra`.
  * The *call* step `balanced_project_call` is proved using
    `call_body_decompose` (CEK surgery) to split the run into the callee body
    and caller tail.  `call_step_bpgoal` projects the completed call by combining
    exact gadget metadata, standalone-to-inline counted transport, and the
    callee's checked counting verdict; `BPGoal.trans` then composes it with the
    projected tail.
-/

end FDuke.Refinement
