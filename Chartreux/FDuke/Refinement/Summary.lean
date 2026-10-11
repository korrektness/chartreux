import Chartreux.FDuke.Refinement.Transport

namespace FDuke.Refinement

/-- Every gadget-derived call successor remains in the caller component. -/
theorem succSummary_fst {fam : CFGFamily} {nr x : NodeRef}
    (hx : x ∈ fam.succSummary nr) : x.1 = nr.1 := by
  unfold CFGFamily.succSummary at hx
  cases hg : fam.gadgetAt? nr.1 nr.2 <;>
    cases hc : fam.cfgAt? nr.1 <;> simp_all

/-- Unfold a family call successor into retained metadata and its certified
structural return edge. -/
theorem succSummary_mem_iff {fam : CFGFamily} {self : CFGRef} {cfg : WFCFG}
    (hcfg : fam.cfgAt? self = some cfg) {n : NodeID} {nr : NodeRef} :
    nr ∈ fam.succSummary (self, n) ↔
      ∃ site, fam.gadgetAt? self n = some site ∧
        (⟨site.exL, site.ret, .plain⟩ : Edge) ∈ cfg.val.edges ∧
        nr = (self, site.ret) := by
  unfold CFGFamily.succSummary
  rw [hcfg]
  cases hg : fam.gadgetAt? self n with
  | none => simp
  | some site =>
      by_cases hedge : (⟨site.exL, site.ret, .plain⟩ : Edge) ∈ cfg.val.edges <;>
        simp [hedge]

end FDuke.Refinement
