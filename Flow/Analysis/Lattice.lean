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
  remainingHeight : A -> Nat
  height_join : ∀ a b, a ⊔ b ≠ a -> remainingHeight (a ⊔ b) < remainingHeight a

namespace FiniteHeight

omit [Bot A] in
theorem height_le_of_join [FiniteHeight A] (a b : A) :
    remainingHeight (a ⊔ b) ≤ remainingHeight a := by
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
  bot_le : ∀ a : A, ⊥ ⊑ a

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
omit [Bot A] in
lemma max_app {x y : Domain n A} {i : Fin n} :
  (x ⊔ y) i = x i ⊔ y i := by rfl

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
def domRemainingHeight [fh : FiniteHeight A] (ρ : Domain n A) : Nat :=
  (List.finRange n |>.map fun i => fh.remainingHeight (ρ i)) |>.sum

/-- If `A` is a `FiniteHeight` type, the finite map `Domain n A` is also
    `FiniteHeight`. -/
instance [fh : FiniteHeight A] : FiniteHeight (Domain n A) where
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

/-- If `A` is a `LatticeLike` type, the finite map `Domain n A` is also
    `LatticeLike`. -/
instance {n : Nat} [FiniteHeight A]
    [ll : LatticeLike A] : LatticeLike (Domain n A) where
  join_comm a b := by funext i; exact ll.join_comm (a i) (b i)
  join_assoc a b c := by funext i; exact ll.join_assoc (a i) (b i) (c i)
  join_idem a := by funext i; exact ll.join_idem (a i)
  bot_le a := by funext i; exact ll.bot_le (a i)

end Domain

-- A pointwise product lattice L₁ × L₂
section Product

variable {L₁ L₂ : Type} [Max L₁] [Max L₂] [Bot L₁] [Bot L₂]
variable [fh₁ : FiniteHeight L₁] [fh₂ : FiniteHeight L₂]
variable [ll₁ : LatticeLike L₁] [ll₂ : LatticeLike L₂]

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

instance : LatticeLike (L₁ × L₂) where
  join_comm := by simp [max]; grind [ll₁.join_comm, ll₂.join_comm]
  join_assoc := by simp [max]; grind [ll₁.join_assoc, ll₂.join_assoc]
  join_idem := by simp [max]; grind [ll₁.join_idem, ll₂.join_idem]
  bot_le := by simp [max]; grind [ll₁.bot_le, ll₂.bot_le]

end Product

-- A optional lattice `Option L`
section Option

variable {L : Type} [Max L] [Bot L]
variable [fh : FiniteHeight L] [ll : LatticeLike L]

instance : Max (Option L) where
  max
  | a, .none => a
  | .none, b => b
  | .some a, .some b => .some (max a b)

instance : Bot (Option L) where
  bot := none

instance : FiniteHeight (Option L) where
  remainingHeight
  | .none => FiniteHeight.remainingHeight ⊥ + 1
  | .some a => FiniteHeight.remainingHeight a
  height_join := by
    intro a b hmax
    cases a <;> cases b <;>
      simp only [max, ne_eq, not_true_eq_false, Option.some.injEq] at * <;> expose_names
    · have h_bot : ⊥ ⊑ val := ll.bot_le val
      have h_le := fh.height_le_of_join ⊥ val
      rw [h_bot] at h_le
      omega
    · apply fh.height_join
      assumption

instance : LatticeLike (Option L) where
  join_comm := by simp [max]; grind [ll.join_comm]
  join_assoc := by simp [max]; grind [ll.join_assoc]
  join_idem := by simp [max]; grind [ll.join_idem]
  bot_le := by intro a; cases a <;> simp [max]; rfl

end Option

-- `Fin n` has no bottom element so it is not `LatticeLike`,
-- but we can make `Option.none` the bottom element of `Option (Fin n)`.
section OptionFin

variable (n : ℕ)

instance : Max (Option (Fin n)) where
  max
  | none, x => x
  | x, none => x
  | some i, some j => some (if i.val ≤ j.val then j else i)

instance : Bot (Option (Fin n)) where
  bot := none

instance : FiniteHeight (Option (Fin n)) where
  remainingHeight
  | none => n
  | some i => n - 1 - i
  height_join := by
    intro x y hmax
    cases x with
    | none =>
      cases y with
      | none => contradiction
      | some j =>
        simp only [max] at *
        omega
    | some i =>
      cases y with
      | none =>
        simp [max] at hmax
      | some j =>
        simp [max] at *
        split_ifs <;> omega

instance : LatticeLike (Option (Fin n)) where
  join_comm := by
    intro x y
    cases x <;> cases y <;> simp only [max]
    split_ifs <;> congr <;> omega
  join_assoc := by
    intro x y z
    cases x <;> cases y <;> cases z <;> simp only [max]
    split_ifs <;> congr <;> omega
  join_idem := by
    intro x
    cases x <;> simp only [max]
    split_ifs <;> rfl
  bot_le := by
    intro x
    cases x <;> rfl

end OptionFin

end Basics
