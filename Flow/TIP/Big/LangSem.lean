import Flow.TIP.Big.CFG
import Flow.TIP.Big.Correspondence.Refinement
import Flow.TIP.Eval
import Flow.TIP.Regular.Correspondence.Refinement
import Flow.Analysis.Lattice
import Flow.Analysis.Generic

/-!
# Big-TIP bridge into the generic framework

Mirrors `Flow.TIP.LangSem` for the regular CFG. Provides:
* `Flow.TIP.Big.forBigCFG` — adapter from `BigCFG` to
  `AnalysisCFG BigNodeID Edge`;
* `Flow.TIP.Big.tipBigLangSem` — a family of `LangSem BigNodeID Edge CEK`
  values, one per `BigCFG`;
* `Flow.TIP.Big.bigStepsN_to_lsteps` — refinement of `BigStepsN` into the
  language-agnostic `LSteps`.

The shape is intentionally identical to the regular bridge: stutters
become `LSteps.stut`; `mutate` / `branch` / `advance` / `skipBridge`
become `LSteps.step` with the appropriate disjunct of `tipBigLStep`.
The extra "judicious stuttering" lives entirely inside `BigStepsN`; the
bridge here just plumbs the data through.
-/

namespace Flow.TIP.Big

open Flow.Analysis Flow.Analysis.Generic Flow.Eval.Big.Refinement
open Flow.Eval.Refinement (BranchTaken)

/-! ## Adapter: `BigCFG` ↪ `AnalysisCFG BigNodeID Edge` -/

def inEdges (g : BigCFG) (n : BigNodeID) : List Edge :=
  g.edges.filter (fun e => e.dst = n)

def forBigCFG (g : BigCFG)
    (hsrc : ∀ e ∈ g.edges, e.src < g.nodes.length)
    (hdst : ∀ e ∈ g.edges, e.dst < g.nodes.length) :
    AnalysisCFG BigNodeID Edge where
  nodes := List.range g.nodes.length
  edges := g.edges
  entry := g.entry
  exit  := g.exit
  srcOf e := e.src
  dstOf e := e.dst
  succ := g.succ
  pred := g.pred
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

/-! ## TIP `LangSem` for the big CFG

The disjuncts mirror the regular `tipLStep`:
* (a) writeback (`BigNodeWritesback`);
* (b) branch (`BigNodeBranches`);
* (c) env-preserving advance / `skipBridge` along a `Normal` edge.

Disjunct (c) collapses `advance` and `skipBridge` together at the
`LangSem` boundary: both end up as `e.kind = .Normal ∧ σ'.E = σ.E`. The
distinction (one-CEK-step vs zero-CEK-steps) is private to `BigStepsN`
and is only needed when *proving* refinement; downstream `LangSem`
consumers do not see it. -/
def tipBigLStep (cfg : BigCFG) (G : AnalysisCFG BigNodeID Edge)
    (e : Edge) (σ σ' : CEK) : Prop :=
  e ∈ G.edges ∧ G.srcOf e = e.src ∧ G.dstOf e = e.dst ∧
  ((∃ x e' v,
      BigNodeWritesback cfg e.src x e' ∧ EvalExpr σ.E e' v ∧
      σ'.E = σ.E.updated x v) ∨
   (∃ c v,
      BigNodeBranches cfg e.src c ∧ EvalExpr σ.E c v ∧
      BranchTaken e.kind v ∧ σ'.E = σ.E) ∨
   (e.kind = .Normal ∧ σ'.E = σ.E))

def tipBigLStutter (_cfg : BigCFG) (_G : AnalysisCFG BigNodeID Edge)
    (_n : BigNodeID) (σ σ' : CEK) : Prop :=
  σ'.E = σ.E

def tipBigLangSem (cfg : BigCFG) : LangSem BigNodeID Edge CEK where
  LStep G e σ σ'      := tipBigLStep cfg G e σ σ'
  LStutter G n σ σ'   := tipBigLStutter cfg G n σ σ'
  IsInitial _G σ      := σ.E = State.empty ∧ σ.K = []
  LStep_edge_mem := by
    intro _G _e _σ _σ' h; exact h.1

/-! ## Bridge: `BigStepsN` → generic `LSteps` -/

/-- For a `BigCFG` `cfg` and its adapter `G = forBigCFG cfg _`, every
    `BigStepsN cfg h σ h' σ'` lifts to a generic `LSteps G n σ n' σ'`
    in the language semantics `tipBigLangSem cfg`. -/
theorem bigStepsN_to_lsteps {cfg : BigCFG} {G : AnalysisCFG BigNodeID Edge}
    (hedges : G.edges = cfg.edges)
    (hsrc : ∀ e, G.srcOf e = e.src) (hdst : ∀ e, G.dstOf e = e.dst)
    {n n' : Nat} {h : n < cfg.nodes.length} {h' : n' < cfg.nodes.length}
    {σ σ' : CEK} (hsteps : BigStepsN cfg h σ h' σ') :
    letI : LangSem BigNodeID Edge CEK := tipBigLangSem cfg
    LSteps G n σ n' σ' := by
  letI : LangSem BigNodeID Edge CEK := tipBigLangSem cfg
  induction hsteps with
  | refl _ _ => exact LSteps.refl _ _
  | @step n n₁ n' _hn _hn₁ _hn' _σ _σ₁ _σ' hsn _hssn ih =>
    cases hsn with
    | stutter _hn _hstep hE =>
      exact LSteps.stut (show tipBigLStutter cfg G n _ _ from hE) ih
    | mutate _hn _hn' x e' v _hstep hwb heval hedge hE =>
      let edge : Edge := ⟨n, n₁, .Normal⟩
      have hmem_G : edge ∈ G.edges := hedges ▸ hedge
      have hLStep : tipBigLStep cfg G edge _ _ :=
        ⟨hmem_G, hsrc edge, hdst edge,
          Or.inl ⟨x, e', v, hwb, heval, hE⟩⟩
      refine LSteps.step (g := G) (e := edge) hLStep ?_ (hsrc edge)
      have hd : G.dstOf edge = n₁ := hdst edge
      rw [hd]; exact ih
    | branch _hn _hn' c k v _hstep hbr hedge heval hbt hE =>
      let edge : Edge := ⟨n, n₁, k⟩
      have hmem_G : edge ∈ G.edges := hedges ▸ hedge
      have hLStep : tipBigLStep cfg G edge _ _ :=
        ⟨hmem_G, hsrc edge, hdst edge,
          Or.inr (Or.inl ⟨c, v, hbr, heval, hbt, hE⟩)⟩
      refine LSteps.step (g := G) (e := edge) hLStep ?_ (hsrc edge)
      have hd : G.dstOf edge = n₁ := hdst edge
      rw [hd]; exact ih
    | advance _hn _hn' _hstep hedge hE =>
      let edge : Edge := ⟨n, n₁, .Normal⟩
      have hmem_G : edge ∈ G.edges := hedges ▸ hedge
      have hLStep : tipBigLStep cfg G edge _ _ :=
        ⟨hmem_G, hsrc edge, hdst edge,
          Or.inr (Or.inr ⟨rfl, hE⟩)⟩
      refine LSteps.step (g := G) (e := edge) hLStep ?_ (hsrc edge)
      have hd : G.dstOf edge = n₁ := hdst edge
      rw [hd]; exact ih
  | @skipBridge n n₁ n' _hn _hn₁ _hn' σ _σ' hedge _hssn ih =>
    let edge : Edge := ⟨n, n₁, .Normal⟩
    have hmem_G : edge ∈ G.edges := hedges ▸ hedge
    have hLStep : tipBigLStep cfg G edge σ σ :=
      ⟨hmem_G, hsrc edge, hdst edge,
        Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    refine LSteps.step (g := G) (e := edge) hLStep ?_ (hsrc edge)
    have hd : G.dstOf edge = n₁ := hdst edge
    rw [hd]; exact ih

end Flow.TIP.Big
