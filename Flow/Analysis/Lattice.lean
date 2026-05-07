import Mathlib.Order.Notation

variable {A : Type} [Max A] [Bot A]

section Basics

-- lattice theory
infix:90 "⊑" => fun x y => x ⊔ y = x

class FiniteHeight (A : Type) [Max A] where
  height : A -> Nat
  maxHeight : Nat
  maxHeight_ub : ∀ a, height a ≤ maxHeight
  height_join : ∀ a b, ¬(a ⊑ b) -> height a < height (a ⊔ b)

namespace FiniteHeight

omit [Bot A] in theorem height_le_of_join [FiniteHeight A] (a b : A) :
    height a ≤ height (a ⊔ b) := by
  by_cases h : a ⊔ b = a
  · rw [h]; apply Nat.le_refl
  · refine Nat.le_of_lt (height_join a b h)

end FiniteHeight

def mono_f {A : Type} [Max A] (f : A -> A) : Prop :=
  ∀ x y, x ⊑ y -> f x ⊑ f y

class LatticeLike
    (A : Type) [Max A] [Bot A] [FiniteHeight A] where
  -- regular lattice structure
  join_comm : ∀ a b : A, a ⊔ b = b ⊔ a
  join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
  join_idem : ∀ a : A, a ⊔ a = a
  bot_le : ∀ a : A, a ⊔ ⊥ = a

-- extension to multivariate case
variable {n : Nat}

abbrev Domain (n : Nat) (A : Type) := Fin n -> A
instance : Bot (Domain n A) where
  bot := fun _ => ⊥
instance : Max (Domain n A) where
  max ρ₁ ρ₂ := fun i => ρ₁ i ⊔ ρ₂ i

namespace Domain
omit [Bot A] in lemma max_app {x y : Domain n A} :
    ∀ i, (x ⊔ y) i = x i ⊔ y i := by
  intros i; rfl

-- operations on domains
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

-- finite height instance

@[simp]
def domHeight [fh : FiniteHeight A] (ρ : Domain n A) : Nat :=
  (List.finRange n |>.map fun i => fh.height (ρ i)) |>.sum

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

end Domain

instance instLatticeLikeDomain
    {n : Nat} {A : Type} [Max A] [Bot A] [FiniteHeight A] [ll : LatticeLike A] :
    LatticeLike (Domain n A) where
  join_comm a b := by funext i; exact ll.join_comm (a i) (b i)
  join_assoc a b c := by funext i; exact ll.join_assoc (a i) (b i) (c i)
  join_idem a := by funext i; exact ll.join_idem (a i)
  bot_le a := by funext i; exact ll.bot_le (a i)

end Basics

section Dataflow

class AnalysisCFG (Node Edge : Type) [DecidableEq Node] [DecidableEq Edge] where
  nodes : List Node
  edges : List Edge
  entry : Node
  exit  : Node
  srcOf : Edge -> Node
  dstOf : Edge -> Node
  succ  : Node -> List Node
  pred  : Node -> List Node
  inEdges : Node -> List Edge
  -- well-formedness:
  inEdges_src_mem :
    ∀ n e, e ∈ inEdges n -> srcOf e ∈ nodes

variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]

abbrev NodeOf (g : AnalysisCFG Node Edge) := {n // n ∈ g.nodes}

/-- the list of all nodes in `g`, packaged as `NodeOf g`. Mirrors the
    reference's `g.nodes_mem`. -/
def AnalysisCFG.nodes_mem (g : AnalysisCFG Node Edge) : List (NodeOf g) :=
  g.nodes.attach

/-- successors of a node, packaged as `NodeOf g`. Successors are derived
    from the predecessor edges of each candidate node so that we get the
    `NodeOf g` membership proof for free via `inEdges_src_mem`. -/
def AnalysisCFG.succOf (g : AnalysisCFG Node Edge) (n : NodeOf g) : List (NodeOf g) :=
  g.nodes.attach.filter (fun m => (g.inEdges m.val).any (fun e => g.srcOf e = n.val))

abbrev StateN (g : AnalysisCFG Node Edge) (A : Type) := NodeOf g -> A
def StateN.empty {g : AnalysisCFG Node Edge} : StateN g A := fun _ => ⊥
def StateN.update {g : AnalysisCFG Node Edge} (f : StateN g A)
    (n : NodeOf g) (v : A) : StateN g A :=
  fun m => if m = n then v else f m

instance {g : AnalysisCFG Node Edge} : Max (StateN g A) where
  max f g := fun n => f n ⊔ g n

end Dataflow
