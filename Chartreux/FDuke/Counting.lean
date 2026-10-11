import Chartreux.FDuke.Semantics
import Chartreux.Analysis.WorklistProofs

/-!
# Counting analysis

Checks that a function body respects its declared contract.
-/

open Chartreux.Analysis Chartreux.Analysis.Generic

namespace FDuke.Counting

-- ## Powerset Lattice 

/-- Abstract invocation counts -/
abbrev CntElem := Fin 3

@[simp]
def ω : CntElem := 2

@[simp]
def abs : Nat -> CntElem
| 0 => 0
| 1 => 1
| _ => ω

abbrev Cnt := Powerset 3

def absSet : Nat -> Cnt
| k => fun i => i = abs k

@[simp]
def incr (s : Cnt) : Cnt :=
  fun i =>
    match i with
    | 0 => false
    | 1 => s 0
    | 2 => s 1 || s ω

theorem abs_incr {k : Nat} {s : Cnt} (h : s (abs k)) : (incr s) (abs (k + 1)) := by
  cases k with
  | zero => simpa using h
  | succ k =>
  cases k with
  | zero => simpa using Or.intro_left _ h
  | succ k => simpa using Or.intro_right _ h

theorem incr_mono : mono_f incr := by
  intro x y hst
  have hpt : ∀ i, x i ⊔ y i = y i := fun i => congr_fun hst i
  funext i
  simp only [Domain.max_app, incr, Fin.isValue, ω, Bool.max_eq_or, Bool.or_eq_right_iff_imp]
  intros h
  split <;> simp only [Fin.isValue, Bool.or_eq_true, Bool.false_eq_true] at h
  · simpa [h] using hpt 0
  · cases h with
    | inl h => simpa [h] using Or.intro_left _ (hpt 1)
    | inr h => simpa [h] using Or.intro_right _ (hpt 2)

/-- Node transfer: `incr` at `Invoke` nodes, identity everywhere else. -/
def cntTransfer (cfg : CFG) (n : NodeID) (s : Cnt) : Cnt :=
  if cfg.nodeKind n = some .Invoke then incr s else s

/-- Edge transfer: the identity. -/
def cntEdgeTransfer : Edge → Cnt → Cnt := fun _ s => s

theorem cntTransfer_mono (cfg : CFG) (n : NodeID) :
    mono_f (cntTransfer cfg n) := by
  intro s t hst
  unfold cntTransfer
  split
  · exact incr_mono s t hst
  · exact hst

instance instTransferMonoCnt (cfg : CFG) :
    TransferMono (cntTransfer cfg) cntEdgeTransfer where
  node_mono := cntTransfer_mono cfg
  edge_mono _ _ _ h := h

@[reducible]
def countingDFA (cfg : CFG) : DFA NodeID Edge where
  L := Cnt
  nodeTransfer := cntTransfer cfg
  edgeTransfer := cntEdgeTransfer
  entry := fun i => i == 0

-- ## The ghost-counter semantics

/-- Ghost-counter states: a store paired with the number of `invoke`s. -/
abbrev CntState := State × Nat

/-- Stepping: ordinary step through the semantics, + additional logging on
    amount of invocations triggered. -/
def CntStep (cfg : CFG) (n : NodeID) (c c' : CntState) : Prop :=
  KappaStep cfg n c.1 c'.1 ∧
  c'.2 = if cfg.nodeKind n = some .Invoke then c.2 + 1 else c.2

/-- LangSem over the previous step semantics. -/
instance countingLangSem (cfg : WFCFG) :
    LangSem NodeID Edge CntState cfg.kappa.analysis where
  LStep e c c' := CntStep cfg.val e.val.src c c'
  LStutter _ c c' := c = c'
  IsInit c := c.1 = State.empty ∧ c.2 = 0

/-- Coherence: the current state of the counter is coherent with `s`. -/
def cntCoh (s : Cnt) (c : CntState) : Prop := s (abs c.2) = true

@[simp] theorem countingDFA_transferAlong (cfg : WFCFG)
    (e : EdgeOf cfg.kappa.analysis) (s : Cnt) :
    (countingDFA cfg.val).transferAlong cfg.kappa.analysis e s =
      cntTransfer cfg.val e.val.src s := rfl

/-- Proofs of preservation of coherence. -/
def countingSemantics (cfg : WFCFG) :
    DFASemantics (ls := countingLangSem cfg)
      cfg.kappa.analysis (countingDFA cfg.val) where
  Coh := cntCoh
  preserve_entry := by
    intro c hinit
    simp [LangSem.IsInit] at hinit
    simp [cntCoh, hinit]
  preserve_step := by
    intro e c c' s hstep hcorr
    obtain ⟨-, hcnt⟩ := hstep
    simp only [countingDFA_transferAlong, cntTransfer]
    by_cases hk : cfg.val.nodeKind e.val.src = some .Invoke <;>
      simp only [hk, if_true, if_false] at hcnt ⊢
    · rw [cntCoh, hcnt]
      exact abs_incr hcorr
    · rw [cntCoh, hcnt]
      exact hcorr
  preserve_stutter := by
    intro _ c c' s h hcorr
    subst h
    exact hcorr

theorem cnt_mono_absorb {s t : Cnt} {c : CntState}
    (h : s ⊑ t) (hcorr : cntCoh s c) : cntCoh t c := by
  unfold cntCoh at *
  have hpt := congr_fun h (abs c.snd) ▸ Domain.max_app
  rw [hpt, hcorr]
  simp

/-- Generic worklist solver interface. -/
@[reducible]
def analysis (cfg : WFCFG) :
    Chartreux.Analysis (ls := countingLangSem cfg) NodeID Edge CntState :=
  { dfa          := countingDFA cfg.val
    botL         := (inferInstance : Bot Cnt)
    maxL         := _
    decEqL       := (inferInstance : DecidableEq Cnt)
    fhL          := (inferInstance : FiniteHeight Cnt)
    llL          := (inferInstance : SemiLattice Cnt)
    semantics    := countingSemantics cfg
    mono_absorb  := cnt_mono_absorb
    edge_mono    := fun _ _ _ h => h }

def analyzeCFG (cfg : WFCFG) : Chartreux.AnalysisResult (analysis cfg) :=
  Chartreux.analyze (analysis cfg)

-- ## Validation 

def CountVerdict : InvKind → Cnt → Prop
  | .none, _ => True
  | .once, S => S 0 = false /\ S ω = false /\ S 1 = true
  | .atLeast, S => S 0 = false
  | .atMost, S => S ω = false

instance (κ : InvKind) (S : Cnt) : Decidable (CountVerdict κ S) := by
  cases κ <;> unfold CountVerdict <;> infer_instance

-- ## Correctness

/-- Every ghost-reachable configuration has coherent abstract count everywhere. 
    By direct application of `reachable_corr`. -/
theorem counting_correct (cfg : WFCFG)
    {rd : NodeID → Cnt}
    (hpf : PostFixpoint cfg.kappa.analysis (countingDFA cfg.val) rd)
    (hentry : (countingDFA cfg.val).entry ⊑ rd cfg.kappa.analysis.entry)
    {n : NodeID} {c : CntState}
    (hreach : Reachable cfg.kappa.analysis n c (LangSem.IsInit (g := cfg.kappa.analysis))) :
    cntCoh (rd n) c :=
  reachable_corr cfg.kappa.analysis (countingSemantics cfg)
    (fun h hcorr => cnt_mono_absorb h hcorr) hpf hentry hreach

end FDuke.Counting
