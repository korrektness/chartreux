import Mathlib.Tactic.Lemma
import Mathlib.Data.List.Nodup

namespace Utils

lemma sum_map_update_le {B : Type} [DecidableEq B]
      (l : List B) (f : B -> Nat) (n : B) (nv : Nat) (hle : f n ≤ nv) :
    (l.map f).sum ≤ (l.map (fun x => if x = n then nv else f x)).sum := by
  induction l with
  | nil => grind
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases h' : h = n
    case pos => simpa [h'] using Nat.add_le_add hle ih
    case neg => simpa [h'] using ih

lemma sum_map_update_lt {B : Type} [DecidableEq B]
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

theorem List.eraseDups_nodup {α} [BEq α] [LawfulBEq α] :
    ∀ l : List α, l.eraseDups.Nodup
  | [] => by exact List.nodup_nil
  | h :: t => by
    rw [List.eraseDups_cons]
    refine List.Nodup.cons ?_ (List.eraseDups_nodup _)
    intro hmem
    rw [List.mem_eraseDups, List.mem_filter] at hmem
    grind
termination_by l => l.length
decreasing_by grind [List.length_filter_le]

end Utils
