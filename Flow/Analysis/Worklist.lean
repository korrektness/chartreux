import Flow.Analysis.Lattice
import Flow.Analysis.CFG

/-!
# Forward worklist dataflow algorithm

Abstract, forward worklist algorithm for dataflow analysis.
-/

namespace Flow.Analysis

variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]
variable {L : Type}

/-- transfer-function monotonicity properties for the dataflow framework. -/
class TransferMono [Max L]
    (nodeTransfer : Node -> L -> L)
    (edgeTransfer : Edge -> L -> L) where
  node_mono : ∀ n, mono_f (nodeTransfer n)
  edge_mono : ∀ e, mono_f (edgeTransfer e)


/-- computes the join of the results of applying an edge transfer function
    to all incoming edges of a given node `n` in `g`. -/
def joinPredEdges [Bot L] [Max L]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> L -> L)
    (outF : StateN g L) (n : NodeOf g) : L :=
  ((g.inEdges n.val).attach).foldl (fun acc ⟨e, he⟩ =>
    let srcNode : NodeOf g := ⟨g.srcOf e, g.inEdges_src_mem n.val e he⟩
    acc ⊔ edgeTransfer e (outF srcNode)
  ) ⊥

def expectedIn [Bot L] [Max L]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> L -> L)
    (entryInit : L) (outF : StateN g L) (n : NodeOf g) : L :=
  let join := joinPredEdges g edgeTransfer outF n
  if n.val = g.entry then entryInit ⊔ join else join

/-- main forward worklist algorithm. -/
def worklistForward
    [Bot L] [Max L] [DecidableEq L] [FiniteHeight L]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> L -> L)
    (edgeTransfer : Edge -> L -> L) (entryInit : L)
    (outF : StateN g L := StateN.empty)
    (wl : List (NodeOf g) := g.nodes_mem) : StateN g L :=
  match wl with
  | [] => outF
  | n :: rest =>
      let newIn := expectedIn g edgeTransfer entryInit outF n
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

/-- run the dataflow analysis to a fixpoint, returning the per-node
    entry and exit facts. -/
def runDataflow
    [Bot L] [Max L] [DecidableEq L] [FiniteHeight L]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> L -> L) (edgeTransfer : Edge -> L -> L)
    (entryInit : L) : StateN g L × StateN g L :=
  let finalOut : StateN g L :=
    worklistForward g nodeTransfer edgeTransfer entryInit
  let finalIn : StateN g L := fun n => expectedIn g edgeTransfer entryInit finalOut n
  ⟨finalIn, finalOut⟩

end Flow.Analysis
