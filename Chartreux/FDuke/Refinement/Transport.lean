import Chartreux.FDuke.Counting

open Chartreux.Analysis Chartreux.Analysis.Generic

namespace FDuke.Refinement

/-- A chain of exactly `k` executions of a common body-run relation. -/
inductive IndexedChain {α : Type} (BodyRun : α → α → Prop) :
    Nat → α → α → Prop where
  | zero {a} : IndexedChain BodyRun 0 a a
  | succ {k a b c} :
      BodyRun a b → IndexedChain BodyRun k b c →
      IndexedChain BodyRun (k + 1) a c

namespace IndexedChain

theorem trans {α : Type} {BodyRun : α → α → Prop} {k₁ k₂ : Nat}
    {a b c : α} (h₁ : IndexedChain BodyRun k₁ a b)
    (h₂ : IndexedChain BodyRun k₂ b c) :
    IndexedChain BodyRun (k₁ + k₂) a c := by
  induction h₁ with
  | zero => simpa using h₂
  | succ hrun _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        IndexedChain.succ hrun (ih h₂)

theorem map {α β : Type} {BodyRun : α → α → Prop}
    {BodyRun' : β → β → Prop} (f : α → β)
    (hmap : ∀ {a b}, BodyRun a b → BodyRun' (f a) (f b))
    {k : Nat} {a b : α} (h : IndexedChain BodyRun k a b) :
    IndexedChain BodyRun' k (f a) (f b) := by
  induction h with
  | zero => exact .zero
  | succ hrun _ ih => exact .succ (hmap hrun) ih

end IndexedChain

end FDuke.Refinement
