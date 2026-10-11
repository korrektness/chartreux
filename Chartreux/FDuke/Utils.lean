section Utils
namespace List

variable {α : Type} (x : α) (l : List α)
variable [DecidableEq α]

theorem finIdxOf?_nodup (hnd : l.Nodup)
    (i j : Fin l.length) (hi : l.finIdxOf? x = some i) (hneq : j ≠ i) :
    x ≠ l.get j := by
  intro h_eq
  have hget := List.finIdxOf?_eq_some_iff.mp hi |>.left
  subst h_eq
  rw [List.get_eq_getElem] at *
  have := (List.getElem_inj hnd).1 hget
  grind

end List
end Utils
