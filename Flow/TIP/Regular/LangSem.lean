import Flow.TIP.Regular.CFG
import Flow.TIP.Eval
import Flow.TIP.Regular.Correspondence.Refinement
import Flow.Analysis.Lattice
import Flow.Analysis.Generic
import Flow.Analysis.WorklistProofs

/-!
# TIP bridge into the generic framework

Provides the `forCFG` adapter from TIP's `CFG` to the abstract `AnalysisCFG NodeID Edge`,
and a family of `LangSem NodeID Edge CEK` instances (one per TIP `CFG`) that wires
TIP's `StepN` / `StepsN` / `IsInitial` to the language-agnostic interface.
-/

namespace Flow.TIP

open Flow.Analysis Flow.Analysis.Generic Flow.Eval.Refinement

/-! ## Adapter: `CFG` ↪ `AnalysisCFG NodeID Edge` -/

def inEdges (g : CFG) (n : NodeID) : List Edge :=
  g.edges.filter (fun e => e.dst = n)

@[reducible]
def forCFG (g : CFG)
    (hsrc : ∀ e ∈ g.edges, e.src < g.nodes.length)
    (hdst : ∀ e ∈ g.edges, e.dst < g.nodes.length) :
    AnalysisCFG NodeID Edge where
  nodes := List.range g.nodes.length
  edges := g.edges
  entry := g.entry
  exit  := g.exit
  srcOf e := e.src
  dstOf e := e.dst
  inEdges n := inEdges g n
  inEdges_src_mem := by
    intro n e he
    have hin : e ∈ g.edges := (List.mem_filter.mp he).1
    exact List.mem_range.mpr (hsrc e hin)
  edges_mem_inEdges := by
    intro e he
    simp [inEdges, List.mem_filter, he]
  dstOf_mem := by
    intro e he
    exact List.mem_range.mpr (hdst e he)

@[reducible]
def forCFG_of_wf (g : CFG) (h : g.WellFormed) : AnalysisCFG NodeID Edge :=
  forCFG g h.2.1 h.2.2.1

/-! ## TIP `LangSem`, parameterised by the underlying TIP `CFG`

Because the abstract `AnalysisCFG NodeID Edge` doesn't carry
`nodeKind`, we cannot express TIP's per-constructor transitions
purely through `AnalysisCFG`. We therefore parameterise the language
semantics by the original `cfg : CFG` and synthesise a `LangSem`
*value* that the framework consumes via `letI`. -/

/-- The edge-consuming TIP transitions, parameterised by the
    underlying `cfg`. Captures `StepN.mutate`, `StepN.branch`,
    `StepN.advance` and `StepsN.skipBridge` — i.e. every TIP step
    that advances the program counter along a CFG edge. We only
    keep the witnesses each client analysis needs (kind + env
    relation), not the full `Step` derivation. -/
def tipLStep (cfg : CFG) (G : AnalysisCFG NodeID Edge)
    (e : Edge) (σ σ' : State) : Prop :=
  e ∈ G.edges ∧ G.srcOf e = e.src ∧ G.dstOf e = e.dst ∧
  ((∃ x e' v,
      NodeAssigns cfg e.src x e' ∧ EvalExpr σ e' v ∧
      σ'= σ.updated x v) ∨
   (∃ c v,
      NodeBranches cfg e.src c ∧ EvalExpr σ c v ∧
      BranchTaken e.kind v ∧ σ'= σ) ∨
   (cfg.nodeKind e.src = some .Skip ∧ e.kind = .Normal ∧ σ'= σ))

/-- A non-edge-consuming TIP transition: a CEK step that does not
    advance the program counter (TIP's `StepN.stutter`). We only
    keep the env-preservation witness. -/
def tipLStutter (σ σ' : State) : Prop :=
  σ' = σ

/-- A `LangSem` instance for a fixed TIP CFG. -/
@[reducible]
def tipLangSem (cfg : CFG) : LangSem NodeID Edge State where
  LStep G e σ σ'    := tipLStep cfg G e σ σ'
  LStutter _ _ σ σ' := tipLStutter σ σ'
  LStep_edge_mem    := by grind [tipLStep]

/-! ## Bridge: TIP's `StepsN` -> generic `LSteps` -/

/-- For a CFG `cfg` and its adapter `G = forCFG cfg _`, every
    `StepsN cfg h σ h' σ'` lifts to a generic `LSteps G n σ n' σ'`
    in the language semantics `tipLangSem cfg`.

    Edge well-formedness for the adapter is assumed so that abstract
    `srcOf`/`dstOf` agree with TIP's `e.src`/`e.dst`. -/
theorem stepsN_to_lsteps {cfg : CFG} {G : AnalysisCFG NodeID Edge}
    (hedges : G.edges = cfg.edges)
    (hsrc : ∀ e, G.srcOf e = e.src) (hdst : ∀ e, G.dstOf e = e.dst)
    {n n' : Nat} {h : n < cfg.nodes.length} {h' : n' < cfg.nodes.length}
    {σ σ' : CEK} (hsteps : StepsN cfg h σ h' σ') :
    letI : LangSem NodeID Edge State := tipLangSem cfg
    LSteps G n σ.E n' σ'.E := by
  letI : LangSem NodeID Edge State := tipLangSem cfg
  induction hsteps with
  | refl _ _ => exact LSteps.refl _ _
  | @step n n₁ n' _hn _hn₁ _hn' _σ _σ₁ _σ' hsn _hssn ih =>
    cases hsn with
    | stutter _hn _hstep hE =>
      exact LSteps.stut (show tipLStutter _ _ from hE) ih
    | mutate _hn _hn' x e' v _hstep hassign heval _hedge hE =>
      obtain ⟨k, hedge_cfg⟩ := _hedge
      let edge : Edge := ⟨n, n₁, k⟩
      have hmem_G : edge ∈ G.edges := hedges ▸ hedge_cfg
      have hLStep : tipLStep cfg G edge _ _ :=
        ⟨hmem_G, hsrc edge, hdst edge,
          Or.inl ⟨x, e', v, hassign, heval, hE⟩⟩
      refine LSteps.step (g := G) (e := edge) hLStep ?_ (hsrc edge)
      have hd : G.dstOf edge = n₁ := hdst edge
      rw [hd]; exact ih
    | branch _hn _hn' c k v _hstep hbr hedge heval hbt hE =>
      let edge : Edge := ⟨n, n₁, k⟩
      have hmem_G : edge ∈ G.edges := hedges ▸ hedge
      have hLStep : tipLStep cfg G edge _ _ :=
        ⟨hmem_G, hsrc edge, hdst edge,
          Or.inr (Or.inl ⟨c, v, hbr, heval, hbt, hE⟩)⟩
      refine LSteps.step (g := G) (e := edge) hLStep ?_ (hsrc edge)
      have hd : G.dstOf edge = n₁ := hdst edge
      rw [hd]; exact ih
    | advance _hn _hn' _hstep hskip hedge hE =>
      let edge : Edge := ⟨n, n₁, .Normal⟩
      have hmem_G : edge ∈ G.edges := hedges ▸ hedge
      have hLStep : tipLStep cfg G edge _ _ :=
        ⟨hmem_G, hsrc edge, hdst edge,
          Or.inr (Or.inr ⟨hskip, rfl, hE⟩)⟩
      refine LSteps.step (g := G) (e := edge) hLStep ?_ (hsrc edge)
      have hd : G.dstOf edge = n₁ := hdst edge
      rw [hd]; exact ih
  | @skipBridge n n₁ n' _hn _hn₁ _hn' σ _σ' hskip hedge _hssn ih =>
    let edge : Edge := ⟨n, n₁, .Normal⟩
    have hmem_G : edge ∈ G.edges := hedges ▸ hedge
    have hLStep : tipLStep cfg G edge σ.E σ.E :=
      ⟨hmem_G, hsrc edge, hdst edge,
        Or.inr (Or.inr ⟨hskip, rfl, rfl⟩)⟩
    refine LSteps.step (g := G) (e := edge) hLStep ?_ (hsrc edge)
    have hd : G.dstOf edge = n₁ := hdst edge
    rw [hd]; exact ih

end Flow.TIP
