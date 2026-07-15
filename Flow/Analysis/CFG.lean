import Flow.Analysis.Lattice

variable {L : Type} [Max L] [Bot L]
variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]

section Dataflow

class AnalysisCFG (Node Edge : Type) [DecidableEq Node] [DecidableEq Edge] where
  nodes : List Node
  edges : List Edge
  entry : Node
  srcOf : Edge -> Node
  dstOf : Edge -> Node
  srcOf_mem :
    ∀ e ∈ edges, srcOf e ∈ nodes
  dstOf_mem :
    ∀ e ∈ edges, dstOf e ∈ nodes
  entry_mem : entry ∈ nodes

abbrev NodeOf (g : AnalysisCFG Node Edge) := {n // n ∈ g.nodes}
abbrev EdgeOf (g : AnalysisCFG Node Edge) := {e // e ∈ g.edges}

namespace AnalysisCFG
/-- All in-edges of a node -/
def inEdges (g : AnalysisCFG Node Edge) (n : Node) : List Edge :=
  g.edges.filter (g.dstOf · = n)

def inEdges_src_mem (g : AnalysisCFG Node Edge) :
    ∀ n e, e ∈ inEdges g n -> g.srcOf e ∈ g.nodes := by grind [inEdges, g.srcOf_mem]
def edges_mem_inEdges (g : AnalysisCFG Node Edge) :
    ∀ e, e ∈ g.edges -> e ∈ g.inEdges (g.dstOf e) := by grind [inEdges, g.dstOf_mem]

/-- the list of all nodes in `g`, packaged as `NodeOf g`. -/
def nodes_mem (g : AnalysisCFG Node Edge) : List (NodeOf g) :=
  g.nodes.attach

/-- successors of a node, packaged as `NodeOf g`. -/
def succOf (g : AnalysisCFG Node Edge) (n : NodeOf g) : List (NodeOf g) :=
  g.nodes.attach.filter (fun m => (g.inEdges m.val).any (fun e => g.srcOf e = n.val))
end AnalysisCFG

/-- analysis result: finite map from nodes of `g` to element of the analysis Lattice. -/
abbrev StateN (g : AnalysisCFG Node Edge) (L : Type) := NodeOf g -> L

namespace StateN

def empty {g : AnalysisCFG Node Edge} : StateN g L := fun _ => ⊥
def update {g : AnalysisCFG Node Edge} (f : StateN g L)
    (n : NodeOf g) (v : L) : StateN g L :=
  fun m => if m = n then v else f m

omit [Bot L] in
private theorem gmap_height_update_eq [FiniteHeight L]
    {g : AnalysisCFG Node Edge}
    (nodes : List (NodeOf g)) (outF : StateN g L) (node : NodeOf g) (newOut : L) :
    (nodes.map (fun x => FiniteHeight.remainingHeight (StateN.update outF node newOut x))) =
       (nodes.map (fun x => if x = node then FiniteHeight.remainingHeight newOut
        else FiniteHeight.remainingHeight (outF x))) := by
  congr 1; ext x; simp [StateN.update]; split <;> rfl

omit [Bot L] in
private theorem gmap_update_sum_lt [FiniteHeight L]
    {g : AnalysisCFG Node Edge}
    (nodes : List (NodeOf g)) (outF : StateN g L) (node : NodeOf g) (newOut : L)
    (hn : node ∈ nodes)
    (hlt : FiniteHeight.remainingHeight newOut < FiniteHeight.remainingHeight (outF node)) :
    (nodes.map (fun x => FiniteHeight.remainingHeight (StateN.update outF node newOut x))).sum
    < (nodes.map (fun x => FiniteHeight.remainingHeight (outF x))).sum := by
  rw [gmap_height_update_eq]
  exact Utils.sum_map_update_lt nodes
    (fun x => FiniteHeight.remainingHeight (outF x)) node
    (FiniteHeight.remainingHeight newOut) hn hlt

/- pointwise instances of max/bot/le -/
instance {g : AnalysisCFG Node Edge} : Max (StateN g L) where
  max f g := fun n => f n ⊔ g n

instance {g : AnalysisCFG Node Edge} : Bot (StateN g L) where
  bot := empty

def le {g : AnalysisCFG Node Edge} (f₁ f₂ : StateN g L) : Prop :=
  ∀ n, (f₁ n) ⊑ (f₂ n)

omit [Bot L] in
/-- height of a `StateN`, termination condition for the worklist algorithm. -/
def height [fh : FiniteHeight L] (g : AnalysisCFG Node Edge) (f : StateN g L) : Nat :=
    (g.nodes.attach.map (fun x => fh.remainingHeight (f x))).sum

omit [Bot L] in
theorem height_update_decreases [FiniteHeight L]
    (g : AnalysisCFG Node Edge) (outF : StateN g L) (node : NodeOf g) (newOut : L)
    (hlt : FiniteHeight.remainingHeight newOut < FiniteHeight.remainingHeight (outF node)) :
    StateN.height g (StateN.update outF node newOut) < StateN.height g outF := by
  have hn : node ∈ g.nodes.attach := List.mem_attach _ _
  have h_lt := gmap_update_sum_lt g.nodes.attach outF node newOut hn hlt
  unfold StateN.height
  omega

theorem le_trans {g : AnalysisCFG Node Edge} [FiniteHeight L]
    [LatticeLike L]
    (f1 f2 f3 : StateN g L) (h12 : StateN.le f1 f2) (h23 : StateN.le f2 f3) :
    StateN.le f1 f3 := by
  exact fun n => join_ge_trans _ _ _ (h12 n) (h23 n)

theorem le_update_join {g : AnalysisCFG Node Edge} [FiniteHeight L]
    [ll : LatticeLike L]
    (outF : StateN g L) (n : NodeOf g) (v : L) :
    StateN.le outF (outF.update n (outF n ⊔ v)) := by
  intro m; simp only [StateN.update]
  split
  · rename_i h; subst h
    rw [<-ll.join_assoc, ll.join_idem]
  · exact ll.join_idem _

end StateN
end Dataflow
