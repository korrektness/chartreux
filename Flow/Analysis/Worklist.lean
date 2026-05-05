import Flow.Analysis.Lattice

/-!
# Forward worklist dataflow algorithm

Maximally general port of `readings/Analysis.ref` lifted to the abstract
`class CFG (Node Edge : Type)`.  The language-specific `LBaseSpec` section
of the reference is intentionally dropped: this file is purely about the
monotone framework.

The names mirror the reference (`gfactLe`, `gfactHeight`,
`joinPredEdgesOf`, `worklistForwardEdgeOf`, `expectedInOf`, `runDataflowOf`)
with the `…Of` suffix dropped, since here `g`-indexing is the only mode
considered.
-/

namespace Flow.Analysis

variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]
variable {A : Type}

/-- transfer-function monotonicity properties for the dataflow framework.
    Split out from `LatticeLike` so that the lattice structure on `A` and
    the analysis-specific transfer functions can be supplied independently. -/
class TransferMono
    {A : Type} [Max A]
    {Node Edge : Type}
    (nodeTransfer : Node -> A -> A)
    (edgeTransfer : Edge -> A -> A) where
  node_mono : ∀ n, mono_f (nodeTransfer n)
  edge_mono : ∀ e, mono_f (edgeTransfer e)

/-! ## `Bot` and `≤` for `StateN` -/

/-- pointwise bottom of `StateN`. -/
instance {g : AnalysisCFG Node Edge} [Bot A] : Bot (StateN g A) where
  bot := fun _ => ⊥

/-- definition of `f₁ ≤ f₂` for `StateN`. Mirrors the reference's `gfactLe`. -/
def StateN.le {g : AnalysisCFG Node Edge} [Max A] (f₁ f₂ : StateN g A) : Prop :=
  ∀ n, (f₁ n) ⊔ (f₂ n) = (f₁ n)

/-! ## Utility lemmas on list-sums under update -/

namespace Utils

private lemma sum_map_update_le {B : Type} [DecidableEq B]
      (l : List B) (f : B -> Nat) (n : B) (nv : Nat) (hle : f n ≤ nv) :
    (l.map f).sum ≤ (l.map (fun x => if x = n then nv else f x)).sum := by
  induction l with
  | nil => grind
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases h' : h = n
    case pos => simpa [h'] using Nat.add_le_add hle ih
    case neg => simpa [h'] using ih

private lemma sum_map_update_lt {B : Type} [DecidableEq B]
      (l : List B) (f : B -> Nat) (n : B) (nv : Nat)
      (hin : n ∈ l) (hlt : f n < nv) :
    (l.map f).sum < (l.map (fun x => if x = n then nv else f x)).sum := by
  induction l with
  | nil => cases hin
  | cons h t ih =>
    by_cases hc : h = n
    case pos =>
      simp only [hc, List.map_cons, List.sum_cons, ↓reduceIte]
      refine Nat.add_lt_add_of_lt_of_le hlt ?_
      exact sum_map_update_le t f n nv (by grind)
    case neg => grind

end Utils

/-! ## Termination measure on `StateN` -/

/-- height of a `StateN`. Used as a termination measure for the worklist
    algorithm. Matches the reference's `gfactHeight`. -/
def StateN.height [Max A] [fh : FiniteHeight A]
    (g : AnalysisCFG Node Edge) (f : StateN g A) : Nat :=
  fh.maxHeight * g.nodes.length
    - (g.nodes.attach.map (fun x => fh.height (f x))).sum

lemma StateN.sum_height_le_max [Max A] [fh : FiniteHeight A]
    {g : AnalysisCFG Node Edge} (l : List (NodeOf g)) (f : StateN g A) :
    (l.map (fun x => fh.height (f x))).sum ≤ fh.maxHeight * l.length := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc
      _ ≤ fh.maxHeight + (t.map (fun x ↦ fh.height (f x))).sum := by
        simp [fh.maxHeight_ub]
      _ ≤ fh.maxHeight + fh.maxHeight * t.length := by
        simp [ih]
      _ ≤ fh.maxHeight * (t.length + 1) := by
        grind

private lemma gmap_height_update_eq [Max A] [FiniteHeight A]
    {g : AnalysisCFG Node Edge}
    (nodes : List (NodeOf g)) (outF : StateN g A) (node : NodeOf g) (newOut : A) :
    Eq (nodes.map (fun x => FiniteHeight.height (StateN.update outF node newOut x)))
       (nodes.map (fun x => if x = node then FiniteHeight.height newOut
        else FiniteHeight.height (outF x))) := by
  congr 1; ext x; simp [StateN.update]; split <;> rfl

private lemma gmap_update_sum_lt [Max A] [FiniteHeight A]
    {g : AnalysisCFG Node Edge}
    (nodes : List (NodeOf g)) (outF : StateN g A) (node : NodeOf g) (newOut : A)
    (hn : node ∈ nodes)
    (hlt : FiniteHeight.height (outF node) < FiniteHeight.height newOut) :
    (nodes.map (fun x => FiniteHeight.height (outF x))).sum
    < (nodes.map (fun x => FiniteHeight.height (StateN.update outF node newOut x))).sum := by
  rw [gmap_height_update_eq]
  exact Utils.sum_map_update_lt nodes
    (fun x => FiniteHeight.height (outF x)) node (FiniteHeight.height newOut) hn hlt

/-- if you replace a node's fact with one of larger height, the resulting
    `StateN.height` strictly decreases. Mirrors `gfactHeight_decreases`. -/
private theorem StateN.height_update_decreases [Max A] [FiniteHeight A]
    (g : AnalysisCFG Node Edge) (outF : StateN g A) (node : NodeOf g) (newOut : A)
    (hlt : FiniteHeight.height (outF node) < FiniteHeight.height newOut) :
    StateN.height g (StateN.update outF node newOut) < StateN.height g outF := by
  have hn : node ∈ g.nodes.attach := List.mem_attach _ _
  have h_le := StateN.sum_height_le_max g.nodes.attach (StateN.update outF node newOut)
  have h_lt := gmap_update_sum_lt g.nodes.attach outF node newOut hn hlt
  unfold StateN.height
  have h_len : g.nodes.length = g.nodes.attach.length := by simp
  rw [h_len]
  omega

/-! ## Forward worklist algorithm -/

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
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> A -> A) (edgeTransfer : Edge -> A -> A)
    (entryInit : A) (outF : StateN g A := fun _ => ⊥)
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

/-- the input fact `Analysis∘` for a node `n`: the `entryInit` if `n` is the
    entry of the graph, otherwise the join of all incoming edge facts. -/
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
