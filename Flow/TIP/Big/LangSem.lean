import Flow.TIP.Big.CFG
import Flow.TIP.Big.Correspondence.Refinement
import Flow.TIP.Eval
import Flow.Analysis.Lattice
import Flow.Analysis.Generic
import Flow.Analysis.WorklistProofs

namespace Flow.TIP.Big

open Flow.Analysis Flow.Analysis.Generic Flow.Eval.Big.Refinement

/-! ## Adapter: `CFG` ↪ `AnalysisCFG NodeID Edge` -/

def inEdges (g : BigCFG) (n : NodeID) : List Edge :=
  g.edges.filter (fun e => e.dst = n)

def forCFG (g : BigCFG)
    (hsrc : ∀ e ∈ g.edges, e.src < g.nodes.length)
    (hdst : ∀ e ∈ g.edges, e.dst < g.nodes.length) :
    AnalysisCFG NodeID Edge where
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

def forCFG_of_wf (g : BigCFG) (h : g.WellFormed) : AnalysisCFG NodeID Edge :=
  forCFG g h.2.1 h.2.2.1

def BigLStep (g : BigCFG) (G : AnalysisCFG BigNodeID Edge)
    (e : Edge) (σ σ' : CEK) : Prop :=
  e ∈ G.edges ∧ G.srcOf e = e.src ∧ G.dstOf e = e.dst ∧
  ((∃ x e' v,
      BigNodeWritesback g e.src x e' ∧ EvalExpr σ.E e' v ∧
      σ'.E = σ.E.updated x v) ∨
   (∃ c v,
      BigNodeBranches g e.src c ∧ EvalExpr σ.E c v ∧
      BranchTaken e.kind v ∧ σ'.E = σ.E) ∨
   (e.kind = .Normal ∧ σ'.E = σ.E))

def BigLStutter (_ : BigCFG) (_ : AnalysisCFG BigNodeID Edge)
    (_ : BigNodeID) (σ σ' : CEK) : Prop :=
  σ'.E = σ.E

instance bigLangSem (g : BigCFG) : LangSem BigNodeID Edge CEK where
  LStep G e σ σ' := BigLStep g G e σ σ'
  LStutter G n σ σ' := BigLStutter g G n σ σ'
  LStep_edge_mem h := by exact h.1
  IsInitial _ σ := σ.IsInitial

theorem bigStepsN_to_lsteps {g : BigCFG} {G : AnalysisCFG BigNodeID Edge}
    (hedges : G.edges = g.edges)
    (hsrc : ∀ e, G.srcOf e = e.src) (hdst : ∀ e, G.dstOf e = e.dst)
    {n n' : Nat} {h : n < g.nodes.length} {h' : n' < g.nodes.length}
    {σ σ' : CEK} (hsteps : BigStepsN g h σ h' σ') :
    letI := bigLangSem g
    LSteps G n σ n' σ' := by
  letI inst := bigLangSem g
  induction hsteps with
  | refl => constructor
  | @step n n₁ n' h h₁ h' σ σ₁ σ' hsn _ ih =>
    cases hsn with
    | stutter _ hstep heq =>
      apply LSteps.stut _ ih
      exact ((fun a ↦ heq) ∘ fun a ↦ g) g
    | advance
    | mutate =>
      let edge : Edge := ⟨n, n₁, .Normal⟩
      refine LSteps.step ?_ (by simpa [hdst edge, edge]) (hsrc edge)
      constructor
      · simpa [hedges]
      · refine ⟨hsrc edge, hdst edge, ?_⟩; grind
    | branch _ _ c k v hstep hbranches hedge heval htaken heq =>
      let edge : Edge := ⟨n, n₁, k⟩
      refine LSteps.step ?_ (by simpa [hdst edge, edge]) (hsrc edge)
      constructor
      · simpa [hedges]
      · grind
  | @skipBridge n n₁ n' h h₁ h' σ σ' hedge hstepsn hstepsl  =>
    let edge : Edge := ⟨n, n₁, .Normal⟩
    refine LSteps.step ?_ (by simpa [hdst edge, edge]) (hsrc edge)
    constructor
    · simpa [hedges]
    · grind

end Big
end TIP
end Flow
