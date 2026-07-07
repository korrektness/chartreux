import Chartreux.Analysis.Lattice
import Mathlib.Order.Notation

variable {A : Type} [Max A] [Bot A]
variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]

section Dataflow

class AnalysisCFG (Node Edge : Type) [DecidableEq Node] [DecidableEq Edge] where
  nodes : List Node
  edges : List Edge
  entry : Node
  srcOf : Edge -> Node
  dstOf : Edge -> Node
  inEdges : Node -> List Edge
  inEdges_src_mem :
    ∀ n e, e ∈ inEdges n -> srcOf e ∈ nodes
  edges_mem_inEdges :
    ∀ e, e ∈ edges -> e ∈ inEdges (dstOf e)
  dstOf_mem :
    ∀ e, e ∈ edges -> dstOf e ∈ nodes
  entry_mem : entry ∈ nodes

abbrev NodeOf (g : AnalysisCFG Node Edge) := {n // n ∈ g.nodes}
abbrev EdgeOf (g : AnalysisCFG Node Edge) := {e // e ∈ g.edges}

namespace AnalysisCFG
/-- the list of all nodes in `g`, packaged as `NodeOf g`. -/
def nodes_mem (g : AnalysisCFG Node Edge) : List (NodeOf g) :=
  g.nodes.attach

/-- successors of a node, packaged as `NodeOf g`. -/
def succOf (g : AnalysisCFG Node Edge) (n : NodeOf g) : List (NodeOf g) :=
  g.nodes.attach.filter (fun m => (g.inEdges m.val).any (fun e => g.srcOf e = n.val))
end AnalysisCFG

/-- analysis result: finite map from nodes of `g` to element of the analysis Lattice. -/
abbrev StateN (g : AnalysisCFG Node Edge) (A : Type) := NodeOf g -> A

namespace StateN

def empty {g : AnalysisCFG Node Edge} : StateN g A := fun _ => ⊥
def update {g : AnalysisCFG Node Edge} (f : StateN g A)
    (n : NodeOf g) (v : A) : StateN g A :=
  fun m => if m = n then v else f m

omit [Bot A] in
private lemma gmap_height_update_eq [FiniteHeight A]
    {g : AnalysisCFG Node Edge}
    (nodes : List (NodeOf g)) (outF : StateN g A) (node : NodeOf g) (newOut : A) :
    (nodes.map (fun x => FiniteHeight.remainingHeight (StateN.update outF node newOut x))) =
       (nodes.map (fun x => if x = node then FiniteHeight.remainingHeight newOut
        else FiniteHeight.remainingHeight (outF x))) := by
  congr 1; ext x; simp [StateN.update]; split <;> rfl

omit [Bot A] in
private lemma gmap_update_sum_lt [FiniteHeight A]
    {g : AnalysisCFG Node Edge}
    (nodes : List (NodeOf g)) (outF : StateN g A) (node : NodeOf g) (newOut : A)
    (hn : node ∈ nodes)
    (hlt : FiniteHeight.remainingHeight newOut < FiniteHeight.remainingHeight (outF node)) :
    (nodes.map (fun x => FiniteHeight.remainingHeight (StateN.update outF node newOut x))).sum
    < (nodes.map (fun x => FiniteHeight.remainingHeight (outF x))).sum := by
  rw [gmap_height_update_eq]
  exact Utils.sum_map_update_lt nodes
    (fun x => FiniteHeight.remainingHeight (outF x)) node
    (FiniteHeight.remainingHeight newOut) hn hlt

/- pointwise instances of max/bot/le -/
instance {g : AnalysisCFG Node Edge} : Max (StateN g A) where
  max f g := fun n => f n ⊔ g n

instance {g : AnalysisCFG Node Edge} : Bot (StateN g A) where
  bot := empty

def le {g : AnalysisCFG Node Edge} (f₁ f₂ : StateN g A) : Prop :=
  ∀ n, (f₁ n) ⊑ (f₂ n)

omit [Bot A] in
/-- height of a `StateN`, termination condition for the worklist algorithm. -/
def height [fh : FiniteHeight A] (g : AnalysisCFG Node Edge) (f : StateN g A) : Nat :=
    (g.nodes.attach.map (fun x => fh.remainingHeight (f x))).sum

omit [Bot A] in
theorem height_update_decreases [FiniteHeight A]
    (g : AnalysisCFG Node Edge) (outF : StateN g A) (node : NodeOf g) (newOut : A)
    (hlt : FiniteHeight.remainingHeight newOut < FiniteHeight.remainingHeight (outF node)) :
    StateN.height g (StateN.update outF node newOut) < StateN.height g outF := by
  have hn : node ∈ g.nodes.attach := List.mem_attach _ _
  have h_lt := gmap_update_sum_lt g.nodes.attach outF node newOut hn hlt
  unfold StateN.height
  omega

lemma le_trans {g : AnalysisCFG Node Edge} [FiniteHeight A]
    [LatticeLike A]
    (f1 f2 f3 : StateN g A) (h12 : StateN.le f1 f2) (h23 : StateN.le f2 f3) :
    StateN.le f1 f3 :=
  fun n => join_ge_trans _ _ _ (h12 n) (h23 n)

lemma le_update_join {g : AnalysisCFG Node Edge} [FiniteHeight A]
    [ll : LatticeLike A]
    (outF : StateN g A) (n : NodeOf g) (v : A) :
    StateN.le outF (outF.update n (outF n ⊔ v)) := by
  intro m; simp only [StateN.update]
  split
  · rename_i h; subst h
    rw [<-ll.join_assoc, ll.join_idem]
  · exact ll.join_idem _

end StateN
end Dataflow
