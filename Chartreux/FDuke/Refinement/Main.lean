import Chartreux.FDuke.Refinement.Projection

open Chartreux.Analysis Chartreux.Analysis.Generic

namespace FDuke.Refinement

/-- Public compatibility wrapper for structural κ-graph correctness. -/
theorem kappa_rewrite_correct (cfg : WFCFG)
    {A : DFA NodeID Edge} [Max A.L]
    (S : DFASemantics (ls := kappaLangSem cfg) cfg.kappa.analysis A)
    (mono_absorb : ∀ {ℓ ℓ' : A.L} {σ : State},
      ℓ ⊑ ℓ' → S.Coh ℓ σ → S.Coh ℓ' σ)
    {rd : NodeID → A.L}
    (hpf : PostFixpoint cfg.kappa.analysis A rd)
    (hentry : A.entry ⊑ rd cfg.kappa.analysis.entry)
    {n : NodeID} {σ : State}
    (hreach : Reachable (ls := fdukeLangSem cfg) cfg.analysis n σ
      (fdukeLangSem cfg).IsInit) :
    S.Coh (rd n) σ :=
  kappa_rewrite_correct_core cfg S mono_absorb hpf hentry hreach

end FDuke.Refinement
