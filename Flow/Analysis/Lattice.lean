import Flow.Analysis.Utils
import Mathlib.Order.Notation

variable {A : Type} [Max A] [Bot A]

section Basics
infix:90 " ⊑ " => fun x y => x ⊔ y = y

/-- a function is monotone if it maintains ordering of inputs. -/
def mono_f (f : A -> A) : Prop :=
  ∀ x y, x ⊑ y -> f x ⊑ f y

/-- encoding of the finite height requirement on lattices to ensure termination
    of Kildall's algorithm. -/
class FiniteHeight (A : Type) [Max A] where
  height : A -> Nat
  maxHeight : Nat
  maxHeight_ub : ∀ a, height a ≤ maxHeight
  height_join : ∀ a b, a ⊔ b ≠ a -> height a < height (a ⊔ b)

namespace FiniteHeight

omit [Bot A] in theorem height_le_of_join [FiniteHeight A] (a b : A) :
    height a ≤ height (a ⊔ b) := by
  by_cases h : a ⊔ b = a
  · rw [h]; apply Nat.le_refl
  · refine Nat.le_of_lt (height_join a b h)

end FiniteHeight

/-- a type is `LatticeLike` if it has `FiniteHeight`, a bottom element `⊥`,
    and its join operation satisfies the properties of lattices. -/
class LatticeLike (A : Type) [Max A] [Bot A] [FiniteHeight A] where
  join_comm : ∀ a b : A, a ⊔ b = b ⊔ a
  join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
  join_idem : ∀ a : A, a ⊔ a = a
  bot_le : ∀ a : A, a ⊔ ⊥ = a

lemma join_ge_trans [FiniteHeight A] [ll : LatticeLike A]
    (a b c : A) (hab : a ⊑ b) (hbc : b ⊑ c) :
    a ⊑ c := by
  calc a ⊔ c = a ⊔ (b ⊔ c) := by rw [hbc]
    _ = (a ⊔ b) ⊔ c := (ll.join_assoc a b c).symm
    _ = b ⊔ c := by rw [hab]
    _ = c := hbc

instance JoinLeRefl [FiniteHeight A] [LatticeLike A] : Std.Refl (α := A) (· ⊑ ·) where
  refl := LatticeLike.join_idem

variable {n : Nat}

-- ## domains
-- the goal of this section is to show that the type of a finite map from
-- integers to lattice elements forms itself a lattice.

/-- a domain is a finite map from integers to lattice elements. -/
abbrev Domain (n : Nat) (A : Type) := Fin n -> A

/-- its bottom element is the function that maps every variable to the
    bottom element of `A`. -/
instance : Bot (Domain n A) where
  bot := fun _ => ⊥

/-- the lub is computed pointwise. -/
instance : Max (Domain n A) where
  max ρ₁ ρ₂ := fun i => ρ₁ i ⊔ ρ₂ i

namespace Domain

-- function application distributes over lub
omit [Bot A] in lemma max_app {x y : Domain n A} {i : Fin n} :
  (x ⊔ y) i = x i ⊔ y i := by rfl

-- domain variable manipulation
def getVar (ρ : Domain n A) (x : Nat) : A :=
  if h : x < n then ρ ⟨x, h⟩ else ⊥
def setVar (ρ : Domain n A) (x : Nat) (v : A) : Domain n A :=
  fun i => if i.val = x then v else ρ i

def pushBinding (ρ : Domain n A) (v : A) : Domain n A :=
  fun i =>
    if i.val = 0 then v
    else if h : i.val - 1 < n then ρ ⟨i.val - 1, h⟩
    else ⊥
def popBinding (ρ : Domain n A) (k : Nat) : Domain n A :=
  fun i =>
    if h : i.val + k < n then ρ ⟨i.val + k, h⟩
    else ⊥

-- decidable equality instances
@[simp]
private def domainBEq [DecidableEq A] (ρ₁ ρ₂ : Domain n A) : Bool :=
  List.finRange n |> (·.all (fun i => ρ₁ i = ρ₂ i))

omit [Max A] [Bot A] in
private theorem domainBEq_iff [DecidableEq A] (ρ₁ ρ₂ : Domain n A) :
    domainBEq ρ₁ ρ₂ = true <-> ρ₁ = ρ₂ := by
  grind [domainBEq]

/-- if A has a decidable equality instance, so does Domain n A -/
instance [DecidableEq A] : DecidableEq (Domain n A) := fun ρ₁ ρ₂ =>
  if h : domainBEq ρ₁ ρ₂ then
    isTrue ((domainBEq_iff ρ₁ ρ₂).mp h)
  else
    isFalse (fun h' => h ((domainBEq_iff ρ₁ ρ₂).mpr h'))

@[simp]
def domHeight [fh : FiniteHeight A] (ρ : Domain n A) : Nat :=
  (List.finRange n |>.map fun i => fh.height (ρ i)) |>.sum

/-- If `A` is a `FiniteHeight` type, the finite map `Domain n A` is also
    `FiniteHeight`. -/
instance [fh : FiniteHeight A] : FiniteHeight (Domain n A) where
  height := domHeight
  maxHeight := n * fh.maxHeight
  maxHeight_ub ρ := by
    induction n with
    | zero => simp
    | succ n ih =>
      have := FiniteHeight.maxHeight_ub (ρ 0)
      simp only [Nat.add_one_mul, Nat.add_comm, ge_iff_le, domHeight,
        List.finRange_succ, List.map_cons, List.map_map]
      exact Nat.add_le_add this (ih fun i ↦ ρ i.succ)
  height_join ρ₁ ρ₂ h := by
    have ⟨i, hi₁, hi₂⟩ : ∃ i, i ∈ List.finRange n ∧ ρ₁ i ⊔ ρ₂ i ≠ ρ₁ i := by
      false_or_by_contra; apply h
      case h h' =>
      funext i
      simp only [List.mem_finRange, ne_eq, true_and, not_exists, Classical.not_not] at h'
      exact h' i
    suffices ∀ (l : List (Fin n)), i ∈ l ->
        (l.map (fun j => FiniteHeight.height (ρ₁ j))).sum <
        (l.map (fun j => FiniteHeight.height ((ρ₁ ⊔ ρ₂) j))).sum from this _ hi₁
    intro l hmem
    have hsum_le : ∀ (l : List (Fin n)),
        (l.map (fun j => FiniteHeight.height (ρ₁ j))).sum ≤
        (l.map (fun j => FiniteHeight.height ((ρ₁ ⊔ ρ₂) j))).sum := by
      intro l; induction l with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.map_cons, List.sum_cons]
        refine Nat.add_le_add ?_ ih
        exact FiniteHeight.height_le_of_join _ _
    induction l with
    | nil => cases hmem
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      cases List.mem_cons.mp hmem
      case inl heq =>
        subst heq
        apply Nat.add_lt_add_of_lt_of_le
        · exact fh.height_join _ _ hi₂
        · exact hsum_le _
      case inr htl =>
        refine Nat.add_lt_add_of_le_of_lt ?_ (ih htl)
        exact FiniteHeight.height_le_of_join _ _

/-- If `A` is a `LatticeLike` type, the finite map `Domain n A` is also
    `LatticeLike`. -/
instance {n : Nat} [FiniteHeight A]
    [ll : LatticeLike A] : LatticeLike (Domain n A) where
  join_comm a b := by funext i; exact ll.join_comm (a i) (b i)
  join_assoc a b c := by funext i; exact ll.join_assoc (a i) (b i) (c i)
  join_idem a := by funext i; exact ll.join_idem (a i)
  bot_le a := by funext i; exact ll.bot_le (a i)

end Domain
end Basics

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

variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]

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
    (nodes.map (fun x => FiniteHeight.height (StateN.update outF node newOut x))) =
       (nodes.map (fun x => if x = node then FiniteHeight.height newOut
        else FiniteHeight.height (outF x))) := by
  congr 1; ext x; simp [StateN.update]; split <;> rfl

omit [Bot A] in
private lemma gmap_update_sum_lt [FiniteHeight A]
    {g : AnalysisCFG Node Edge}
    (nodes : List (NodeOf g)) (outF : StateN g A) (node : NodeOf g) (newOut : A)
    (hn : node ∈ nodes)
    (hlt : FiniteHeight.height (outF node) < FiniteHeight.height newOut) :
    (nodes.map (fun x => FiniteHeight.height (outF x))).sum
    < (nodes.map (fun x => FiniteHeight.height (StateN.update outF node newOut x))).sum := by
  rw [gmap_height_update_eq]
  exact Utils.sum_map_update_lt nodes
    (fun x => FiniteHeight.height (outF x)) node (FiniteHeight.height newOut) hn hlt

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
  fh.maxHeight * g.nodes.length
    - (g.nodes.attach.map (fun x => fh.height (f x))).sum

omit [Bot A] in lemma sum_height_le_max [fh : FiniteHeight A]
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

omit [Bot A] in
theorem height_update_decreases [FiniteHeight A]
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
