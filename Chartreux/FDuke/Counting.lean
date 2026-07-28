import Chartreux.FDuke.Semantics
import Chartreux.Analysis.Worklist

/-!
# The counting analysis for κ

The dataflow analysis that verifies the `κ` contract of a `call f { s }` site:
it counts (abstractly, in the three-point domain `{0, 1, ω}`) how many times a
lambda body may have been `invoke`d along each path of the callee's CFG. The
verdict at the callee's exit node decides whether the callee honours its `κ`
(`CountVerdict`), which is exactly the side condition under which the κ-shaped
plain edges emitted by `kappaEdges` are sound.

The analysis runs on the *κ-graph* (`CFG.kappa`, see `Chartreux.FDuke.Semantics`):
the callee CFG with its `.summary` edges removed, so the transfer functions
never see an opaque call summary. Its concrete anchor is a *ghost-counter*
semantics (`countingLangSem`): states are pairs `(σ, k)` of a store and the
number of `invoke` steps taken so far, and correctness (`counting_correct`)
says the abstraction `abs k` of the ghost counter is contained in the computed
fact at every reachable node.
-/

open Chartreux.Analysis Chartreux.Analysis.Generic

namespace FDuke.Counting

-- # The `Cnt` lattice

/-- Abstract invocation counts: exactly zero, exactly one, or "many" (`ω`). -/
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

/-- Edge transfer: the identity (the counting analysis is node-driven). -/
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

/-- The counting DFA over a callee CFG: at the entry nothing has been invoked
    yet (`{0}`); each `Invoke` node bumps every possible count. -/
@[reducible]
def countingDFA (cfg : CFG) : DFA NodeID Edge where
  L := Cnt
  nodeTransfer := cntTransfer cfg
  edgeTransfer := cntEdgeTransfer
  entry := fun i => i == 0

-- # The ghost-counter semantics

/-- Ghost-counter states: a store paired with the number of `invoke` steps
    taken so far. -/
abbrev CntState := State × Nat

/-- One ghost step out of node `n`: the store takes a `KappaStep` (an ordinary
    `IntraStep`, or the store-identity step of a `Call` node — the κ-graph's
    only way through a call site), and the counter increments exactly when `n`
    is an `Invoke` node. -/
def CntStep (cfg : CFG) (n : NodeID) (c c' : CntState) : Prop :=
  KappaStep cfg n c.1 c'.1 ∧
  c'.2 = if cfg.nodeKind n = some .Invoke then c.2 + 1 else c.2

/-- The ghost-counter `LangSem` over the κ-graph of a callee CFG. Every edge
    of `cfg.kappa` is `.plain`, so `LStep` is always a `CntStep`; bookkeeping
    is a stutter, which leaves both the store and the counter untouched. -/
instance countingLangSem (cfg : WFCFG) :
    LangSem NodeID Edge CntState cfg.kappa.analysis where
  LStep e c c' := CntStep cfg.val e.val.src c c'
  LStutter _ c c' := c = c'
  IsInit c := c.1 = State.empty ∧ c.2 = 0

/-- Correspondence: the abstraction of the ghost counter is a possible count. -/
def cntCoh (s : Cnt) (c : CntState) : Prop := s (abs c.2) = true

@[simp] theorem countingDFA_transferAlong (cfg : WFCFG)
    (e : EdgeOf cfg.kappa.analysis) (s : Cnt) :
    (countingDFA cfg.val).transferAlong cfg.kappa.analysis e s =
      cntTransfer cfg.val e.val.src s := rfl

/-- The counting `DFASemantics`: the DFA facts correctly track the ghost
    counter along every ghost transition. -/
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

/-- Absorption: growing the abstract fact preserves correspondence. -/
theorem cnt_mono_absorb {s t : Cnt} {c : CntState}
    (h : s ⊑ t) (hcorr : cntCoh s c) : cntCoh t c := by
  unfold cntCoh at *
  have hpt := congr_fun h (abs c.snd) ▸ Domain.max_app
  rw [hpt, hcorr]
  simp

-- # Per-κ exit checks

/-- The κ contract table on the counting fact `S` computed at the callee's
    exit: `κ = 1` demands exactly one invocation (`S = {1}`), `κ = +` at least
    one (`0 ∉ S`), `κ = ?` at most one (`ω ∉ S`), and `κ = ε` demands
    nothing. -/
def CountVerdict : InvKind → Cnt → Prop
  | .none, _ => True
  | .once, S => S 0 = false /\ S ω = false /\ S 1 = true
  | .atLeast, S => S 0 = false
  | .atMost, S => S ω = false

instance (κ : InvKind) (S : Cnt) : Decidable (CountVerdict κ S) := by
  cases κ <;> unfold CountVerdict <;> infer_instance

-- # Correctness

/-- **Correctness of the counting analysis.** For any post-fixpoint `rd` of
    the counting DFA on the κ-graph of `cfg`, every ghost-reachable
    configuration `(σ, k)` at node `n` has its abstract count in `rd n`. A
    direct application of the generic `reachable_corr`. -/
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
