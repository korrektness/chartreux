import Flow.Analysis.Lattice
import Flow.Analysis.CFG

namespace Flow.Analysis.Generic

variable (Node Edge State : Type) [DecidableEq Node] [DecidableEq Edge]
variable (g : AnalysisCFG Node Edge)

/-- Generic wrapper for semantics over the CFG.
    * `LStep`    : proper transition relation
    * `LStutter` : silent transition relation
-/
class LangSem where
  LStep : EdgeOf g -> State -> State -> Prop
  LStutter : Node -> State -> State -> Prop

structure DFA where
  L : Type
  nodeTransfer : Node -> L -> L
  edgeTransfer : Edge -> L -> L
  entry        : L

variable {Node Edge State : Type}
variable [DecidableEq Node] [DecidableEq Edge]
variable (g : AnalysisCFG Node Edge)
variable [ls : LangSem Node Edge State g]

def DFA.transferAlong (A : DFA Node Edge) (e : EdgeOf g) (ℓ : A.L) : A.L :=
  A.edgeTransfer e (A.nodeTransfer (g.srcOf e) ℓ)

/-- RTC of `LStep` along stutter edges. -/
inductive LSteps : Node -> State -> Node -> State -> Prop where
  | refl  (n : Node) (σ : State) : LSteps n σ n σ
  | step  {e : EdgeOf g} {n n'' : Node} {σ σ' σ'' : State} :
      LangSem.LStep e σ σ' ->
      LSteps (g.dstOf e) σ' n'' σ'' ->
      g.srcOf e = n ->
      LSteps n σ n'' σ''
  | stut {n n' : Node} {σ σ' σ'' : State} :
      LangSem.LStutter g n σ σ' ->
      LSteps n σ' n' σ'' ->
      LSteps n σ n' σ''

namespace LSteps

/-- lift a single `LStep` to a `LSteps`. -/
theorem single {e : EdgeOf g} {σ σ' : State} (hstep : LangSem.LStep e σ σ') :
    LSteps g (g.srcOf e) σ (g.dstOf e) σ' :=
  .step hstep (.refl _ _) rfl

/-- transitivity of `LSteps` -/
theorem trans {n n₁ n' : Node} {σ σ₁ σ' : State}
    (hl : LSteps g n σ n₁ σ₁) (hr : LSteps g n₁ σ₁ n' σ') :
    LSteps g n σ n' σ' := by
  induction hl with
  | refl _ _ => exact hr
  | step hstep _ hsrc ih => exact .step hstep (ih hr) hsrc
  | stut hstut _ ih => exact .stut hstut (ih hr)

end LSteps

/-- Logical semantics linking the DFA to the abstract LangSem relation -/
structure DFASemantics (A : DFA Node Edge) where
  Coh : A.L -> State -> Prop
  isInit : State -> Prop
  preserve_entry :
    ∀ {σ : State}, isInit σ -> Coh A.entry σ
  preserve_step :
    ∀ {e : EdgeOf g} {σ σ' : State} {ℓ : A.L},
      LangSem.LStep e σ σ' -> Coh ℓ σ -> Coh (A.transferAlong g e ℓ) σ'
  preserve_stutter :
    ∀ {n : Node} {σ σ' : State} {ℓ : A.L},
      LangSem.LStutter g n σ σ' -> Coh ℓ σ -> Coh ℓ σ'

/-- a node-indexed labelling is a post-fixpoint of `A`'s transfer if,
    for every `e`, the fact at `srcOf e` after transfer is absorbed
    by the fact at `dstOf e`. -/
def PostFixpoint (A : DFA Node Edge) (rd : Node -> A.L) [Max A.L] : Prop :=
  ∀ e : EdgeOf g,
    (A.transferAlong g e (rd (g.srcOf e))) ⊑ (rd (g.dstOf e))

/-- step preservation of analysis correctness -/
theorem step_preserves_corr
    {A : DFA Node Edge} (D : DFASemantics g A) [Max A.L]
    (mono_absorb : ∀ {ℓ ℓ' : A.L} {σ : State}, ℓ ⊑ ℓ' -> D.Coh ℓ σ -> D.Coh ℓ' σ)
    {rd : Node -> A.L} (hpf : PostFixpoint g A rd)
    {e : EdgeOf g} {σ σ' : State}
    (hstep : LangSem.LStep e σ σ')
    (hcorr : D.Coh (rd (g.srcOf e)) σ) :
    D.Coh (rd (g.dstOf e)) σ' :=
  mono_absorb (hpf e) (D.preserve_step hstep hcorr)

/-- lift of step preservation through the multi-step closure of the step relation. -/
theorem steps_preserves_corr
    {A : DFA Node Edge} (D : DFASemantics g A) [Max A.L]
    (mono_absorb : ∀ {ℓ ℓ' : A.L} {σ : State}, ℓ ⊑ ℓ' -> D.Coh ℓ σ -> D.Coh ℓ' σ)
    {rd : Node -> A.L} (hpf : PostFixpoint g A rd)
    {n n' : Node} {σ σ' : State}
    (hsteps : LSteps g n σ n' σ')
    (hcorr : D.Coh (rd n) σ) :
    D.Coh (rd n') σ' := by
  induction hsteps with
  | refl _ _ => exact hcorr
  | @step e n_src n'' σ_src σ' σ'' hstep _ hsrc ih =>
    apply ih
    simpa [hsrc, hcorr] using
      (step_preserves_corr g D mono_absorb hpf hstep)
  | stut hstut _ ih =>
    exact ih (D.preserve_stutter hstut hcorr)

/-- State `σ` is `Reachable` if there's an initial state `σ₀` such that a
    chain of steps exists from `σ₀` to `σ`. -/
def Reachable (n : Node) (σ : State) (isInit : State -> Prop) : Prop :=
  ∃ σ₀ : State, isInit σ₀ ∧ LSteps g g.entry σ₀ n σ

/-- If state σ' is `Reachable`, then the analysis result at the node
    corresponding to it is correct.
    Direct application of `steps_preserves_corr` -/
theorem reachable_corr
    {A : DFA Node Edge} (D : DFASemantics g A) [Max A.L]
    (mono_absorb : ∀ {ℓ ℓ' : A.L} {σ : State}, ℓ ⊑ ℓ' -> D.Coh ℓ σ -> D.Coh ℓ' σ)
    {rd : Node -> A.L} (hpf : PostFixpoint g A rd)
    (hentry : A.entry ⊑ (rd g.entry))
    {n : Node} {σ : State}
    (hreach : Reachable g n σ D.isInit) :
    D.Coh (rd n) σ := by
  obtain ⟨σ₀, hinit, hsteps⟩ := hreach
  have h_entry : D.Coh A.entry σ₀ := D.preserve_entry hinit
  have h_rd0   : D.Coh (rd g.entry) σ₀ := mono_absorb hentry h_entry
  exact steps_preserves_corr g D mono_absorb hpf hsteps h_rd0

end Flow.Analysis.Generic
