import Flow.Analysis.Lattice

/-!
# Forward worklist dataflow algorithm

Abstract, forward worklist algorithm for dataflow analysis.
-/

namespace Flow.Analysis

variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]
variable {A : Type}

/-- transfer-function monotonicity properties for the dataflow framework. -/
class TransferMono
    {A : Type} [Max A]
    {Node Edge : Type}
    (nodeTransfer : Node -> A -> A)
    (edgeTransfer : Edge -> A -> A) where
  node_mono : ∀ n, mono_f (nodeTransfer n)
  edge_mono : ∀ e, mono_f (edgeTransfer e)


/-- computes the join of the results of applying an edge transfer function
    to all incoming edges of a given node `n` in `g`. -/
def joinPredEdges [Bot A] [Max A]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> A -> A)
    (outF : StateN g A) (n : NodeOf g) : A :=
  ((g.inEdges n.val).attach).foldl (fun acc ⟨e, he⟩ =>
    let srcNode : NodeOf g := ⟨g.srcOf e, g.inEdges_src_mem n.val e he⟩
    acc ⊔ edgeTransfer e (outF srcNode)
  ) ⊥

/-- main forward worklist algorithm. -/
def worklistForward
    [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> A -> A)
    (edgeTransfer : Edge -> A -> A) (entryInit : A)
    (outF : StateN g A := fun _ => ⊥)
    (wl : List (NodeOf g) := g.nodes_mem) : StateN g A :=
  match wl with
  | [] => outF
  | n :: rest =>
      let newIn :=
        if n.val = g.entry then entryInit else joinPredEdges g edgeTransfer outF n
      let newOut := outF n ⊔ nodeTransfer n.val newIn
      if newOut = outF n then
        worklistForward g nodeTransfer edgeTransfer entryInit outF rest
      else
        let outF' := StateN.update outF n newOut
        let wl' := rest ++ g.succOf n
        worklistForward g nodeTransfer edgeTransfer entryInit outF' wl'
termination_by (StateN.height g outF, wl.length)
decreasing_by
  · refine Prod.Lex.right (StateN.height g outF) ?_
    grind
  · refine Prod.Lex.left (rest ++ g.succOf n).length (n :: rest).length ?_
    apply StateN.height_update_decreases g outF n (outF n ⊔ nodeTransfer n.val newIn)
    exact FiniteHeight.height_join _ _ ‹newOut ≠ outF n›

def expectedIn [Bot A] [Max A]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> A -> A)
    (entryInit : A) (outF : StateN g A) (n : NodeOf g) : A :=
  if n.val = g.entry then entryInit else joinPredEdges g edgeTransfer outF n

/-- run the dataflow analysis to a fixpoint, returning the per-node
    entry and exit facts. -/
def runDataflow
    [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> A -> A) (edgeTransfer : Edge -> A -> A)
    (entryInit : A) : StateN g A × StateN g A :=
  let finalOut : StateN g A :=
    worklistForward g nodeTransfer edgeTransfer entryInit
  let finalIn : StateN g A := fun n => expectedIn g edgeTransfer entryInit finalOut n
  ⟨finalIn, finalOut⟩

end Flow.Analysis
