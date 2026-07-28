import Chartreux.Analysis.Utils

class Bot (α : Type) where
  bot : α
notation "⊥" => Bot.bot

variable {L : Type} [Max L] [Bot L]

section Basics
infix:90 " ⊔ " => Max.max
infix:90 " ⊑ " => fun x y => x ⊔ y = y

/-- a function is monotone if it maintains ordering of inputs. -/
def mono_f (f : L -> L) : Prop :=
  ∀ x y, x ⊑ y -> f x ⊑ f y

/-- encoding of the finite height requirement on lattices to ensure termination
    of Kildall's algorithm. -/
class FiniteHeight (L : Type) [Max L] where
  remainingHeight : L -> Nat
  height_join : ∀ a b, a ⊔ b ≠ a -> remainingHeight (a ⊔ b) < remainingHeight a

namespace FiniteHeight

omit [Bot L] in
theorem height_le_of_join [FiniteHeight L] (a b : L) :
    remainingHeight (a ⊔ b) ≤ remainingHeight a := by
  by_cases h : a ⊔ b = a
  · rw [h]; apply Nat.le_refl
  · refine Nat.le_of_lt (height_join a b h)

end FiniteHeight

class SemiLattice (L : Type) [Max L] where
  join_comm : ∀ a b : L, a ⊔ b = b ⊔ a
  join_assoc : ∀ a b c : L, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
  join_idem : ∀ a : L, a ⊔ a = a

class Bounded (L : Type) [Max L] [Bot L] where
  bot_le : ∀ a : L, ⊥ ⊑ a

omit [Bot L]
theorem join_ge_trans [FiniteHeight L] [ll : SemiLattice L]
    (a b c : L) (hab : a ⊑ b) (hbc : b ⊑ c) :
    a ⊑ c := by
  calc a ⊔ c = a ⊔ (b ⊔ c) := by rw [hbc]
    _ = (a ⊔ b) ⊔ c := (ll.join_assoc a b c).symm
    _ = b ⊔ c := by rw [hab]
    _ = c := hbc

instance JoinLeRefl [FiniteHeight L] [SemiLattice L] : Std.Refl (α := L) (· ⊑ ·) where
  refl := SemiLattice.join_idem

-- ## domains
-- the goal of this section is to show that the type of a finite map from
-- integers to lattice elements forms itself a lattice.
section Domain

variable {n : Nat}

/-- a domain is a finite map from integers to lattice elements. -/
abbrev Domain (n : Nat) (A : Type) := Fin n -> A

/-- its bottom element is the function that maps every variable to the
    bottom element of `A`. -/
instance : Bot (Domain n L) where
  bot := fun _ => ⊥

/-- the lub is computed pointwise. -/
instance : Max (Domain n L) where
  max ρ₁ ρ₂ := fun i => ρ₁ i ⊔ ρ₂ i

-- decidable equality instances
@[simp]
private def domainBEq [DecidableEq L] (ρ₁ ρ₂ : Domain n L) : Bool :=
  List.finRange n |> (·.all (fun i => ρ₁ i = ρ₂ i))

omit [Max L] [Bot L] in
private theorem domainBEq_iff [DecidableEq L] (ρ₁ ρ₂ : Domain n L) :
    domainBEq ρ₁ ρ₂ = true <-> ρ₁ = ρ₂ := by
  grind [domainBEq]

/-- if A has a decidable equality instance, so does Domain n A -/
instance [DecidableEq L] : DecidableEq (Domain n L) := fun ρ₁ ρ₂ =>
  if h : domainBEq ρ₁ ρ₂ then
    isTrue ((domainBEq_iff ρ₁ ρ₂).mp h)
  else
    isFalse (fun h' => h ((domainBEq_iff ρ₁ ρ₂).mpr h'))

@[simp]
def domRemainingHeight [fh : FiniteHeight L] (ρ : Domain n L) : Nat :=
  (List.finRange n |>.map fun i => fh.remainingHeight (ρ i)) |>.sum

/-- If `A` is a `FiniteHeight` type, the finite map `Domain n A` is also
    `FiniteHeight`. -/
instance [fh : FiniteHeight L] : FiniteHeight (Domain n L) where
  remainingHeight := domRemainingHeight
  height_join ρ₁ ρ₂ h := by
    have ⟨i, hi₁, hi₂⟩ : ∃ i, i ∈ List.finRange n ∧ ρ₁ i ⊔ ρ₂ i ≠ ρ₁ i := by
      false_or_by_contra; apply h
      case h h' =>
      funext i
      simp only [List.mem_finRange, ne_eq, true_and, not_exists, Classical.not_not] at h'
      exact h' i
    suffices ∀ (l : List (Fin n)), i ∈ l ->
        (l.map (fun j => FiniteHeight.remainingHeight ((ρ₁ ⊔ ρ₂) j))).sum <
        (l.map (fun j => FiniteHeight.remainingHeight (ρ₁ j))).sum from this _ hi₁
    intro l hmem
    have hsum_le : ∀ (l : List (Fin n)),
        (l.map (fun j => FiniteHeight.remainingHeight ((ρ₁ ⊔ ρ₂) j))).sum ≤
        (l.map (fun j => FiniteHeight.remainingHeight (ρ₁ j))).sum := by
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

/-- If `A` is a `SemiLattice` type, the finite map `Domain n A` is also
    `SemiLattice`. -/
instance [ll : SemiLattice L] : SemiLattice (Domain n L) where
  join_comm a b := by funext i; exact ll.join_comm (a i) (b i)
  join_assoc a b c := by funext i; exact ll.join_assoc (a i) (b i) (c i)
  join_idem a := by funext i; exact ll.join_idem (a i)

instance [Bounded L] : Bounded (Domain n L) where
  bot_le a := by funext i; exact Bounded.bot_le (a i)

namespace Domain
-- function application distributes over lub
omit [Bot L] in
theorem max_app {x y : Domain n L} {i : Fin n} :
  (x ⊔ y) i = x i ⊔ y i := by rfl

omit [Bot L] in
theorem ord_distr {x y : Domain n L} {i : Fin n} (h : x ⊑ y) : x i ⊑ y i := by
  simp only
  rw [<-max_app, h]
end Domain

end Domain

-- A pointwise product lattice L₁ × L₂
section Product

variable {L₁ L₂ : Type} [Max L₁] [Max L₂] [Bot L₁] [Bot L₂]
variable [fh₁ : FiniteHeight L₁] [fh₂ : FiniteHeight L₂]
variable [sl₁ : SemiLattice L₁] [sl₂ : SemiLattice L₂]
variable [b₁ : Bounded L₁] [b₂ : Bounded L₂]

instance : Max (L₁ × L₂) where
  max
  | (a₁, b₁), (a₂, b₂) => (max a₁ a₂, max b₁ b₂)

instance : Bot (L₁ × L₂) where
  bot := (⊥, ⊥)

instance : FiniteHeight (L₁ × L₂) where
  remainingHeight
  | (a, b) => FiniteHeight.remainingHeight a + FiniteHeight.remainingHeight b
  height_join := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hmax
    simp only [max, ne_eq, Prod.mk.injEq, not_and] at *
    have ne : a₁ ⊔ a₂ ≠ a₁ ∨ b₁ ⊔ b₂ ≠ b₁ := by grind
    cases ne with
    | inl h => grind [fh₁.height_join _ _ h, fh₂.height_le_of_join b₁ b₂]
    | inr h => grind [fh₂.height_join _ _ h, fh₁.height_le_of_join a₁ a₂]

instance : SemiLattice (L₁ × L₂) where
  join_comm := by simp [max]; grind [sl₁.join_comm, sl₂.join_comm]
  join_assoc := by simp [max]; grind [sl₁.join_assoc, sl₂.join_assoc]
  join_idem := by simp [max]; grind [sl₁.join_idem, sl₂.join_idem]

instance : Bounded (L₁ × L₂) where
  bot_le := by simp [max]; grind [b₁.bot_le, b₂.bot_le]

end Product

-- A optional lattice `Option L`
section Option

variable [fh : FiniteHeight L] [sl : SemiLattice L]

instance : Max (Option L) where
  max
  | a, .none => a
  | .none, b => b
  | .some a, .some b => .some (max a b)

instance : Bot (Option L) where
  bot := none

/-- Finite height of bounded lattices -/
instance [Bounded L] : FiniteHeight (Option L) where
  remainingHeight
  | .none => FiniteHeight.remainingHeight ⊥ + 1
  | .some a => FiniteHeight.remainingHeight a
  height_join := by
    intro a b hmax
    cases a <;> cases b <;>
      simp only [max, ne_eq, not_true_eq_false, Option.some.injEq] at * <;> expose_names
    · have h_bot : ⊥ ⊑ val := Bounded.bot_le val
      have h_le := fh.height_le_of_join ⊥ val
      rw [h_bot] at h_le
      omega
    · apply fh.height_join
      assumption

/-- Finite height of lattices with known max height -/
instance
  (maxHeight : Nat)
  (max_height_le : ∀ a : L, FiniteHeight.remainingHeight a ≤ maxHeight)
    : FiniteHeight (Option L) where
  remainingHeight
  | .none => maxHeight + 1
  | .some a => FiniteHeight.remainingHeight a
  height_join := by
    intro a b hmax
    cases a <;> cases b <;>
      simp only [max, ne_eq, not_true_eq_false, Option.some.injEq] at * <;> expose_names
    · exact Nat.lt_succ_of_le (max_height_le val)
    · apply fh.height_join
      assumption

instance : SemiLattice (Option L) where
  join_comm := by simp [max]; grind [sl.join_comm]
  join_assoc := by simp [max]; grind [sl.join_assoc]
  join_idem := by simp [max]; grind [sl.join_idem]

instance : Bounded (Option L) where
  bot_le := by intro a; cases a <;> simp [max]; rfl

end Option

-- A boolean lattice with `false` as bottom
section Bool

instance : Max Bool where
  max := Bool.or

instance : Bot Bool where
  bot := false

instance : FiniteHeight Bool where
  remainingHeight a := if a then 0 else 1
  height_join := by simp! [max]

instance : SemiLattice Bool where
  join_comm := by simp [max]
  join_assoc := by simp [max]
  join_idem := by simp [max]

instance : Bounded Bool where
  bot_le := by simp [max]

end Bool

-- A powerset lattice
section Powerset

-- Powerset represented as a set characteristic function.
-- This induces a join to be the set union and order to be the subset relation.
abbrev Powerset (n : Nat) := Domain n Bool

end Powerset
end Basics
