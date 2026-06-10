import Flow.Analysis.Lattice

namespace Flow.Analysis.Generic

variable {Node Edge State : Type} [DecidableEq Node] [DecidableEq Edge]

structure DFA (Node Edge : Type) [DecidableEq Node] [DecidableEq Edge] where
  L : Type
  nodeTransfer : Node -> L -> L
  edgeTransfer : Edge -> L -> L
  entry        : L

def DFA.transferAlong
    (A : DFA Node Edge) (g : AnalysisCFG Node Edge)
    (e : Edge) (ℓ : A.L) : A.L :=
  A.edgeTransfer e (A.nodeTransfer (g.srcOf e) ℓ)

/-- Generic wrapper for semantics over the CFG.
    * `LStep` : proper transition relation
    * `LStutter` : silent transition relation
    * `IsInitial` : predicate for selecting the initial states
    * `LStep_edge_mem` : every step follows a recognized edge.
-/
class LangSem (Node Edge State : Type)
    [DecidableEq Node] [DecidableEq Edge] where
  LStep (g : AnalysisCFG Node Edge) : EdgeOf g -> State -> State -> Prop
  LStutter : AnalysisCFG Node Edge -> Node -> State -> State -> Prop

/-- RTC of `LStep` along stutter edges. -/
inductive LSteps [LangSem Node Edge State] (g : AnalysisCFG Node Edge) :
    Node -> State -> Node -> State -> Prop where
  | refl  (n : Node) (σ : State) : LSteps g n σ n σ
  | step  {e : EdgeOf g} {n n'' : Node} {σ σ' σ'' : State} :
      LangSem.LStep g e σ σ' ->
      LSteps g (g.dstOf e) σ' n'' σ'' ->
      g.srcOf e = n ->
      LSteps g n σ n'' σ''
  | stut  {n n' : Node} {σ σ' σ'' : State} :
      LangSem.LStutter g n σ σ' ->
      LSteps g n σ' n' σ'' ->
      LSteps g n σ n' σ''

namespace LSteps

variable [LangSem Node Edge State]

/-- lift a single `LStep` to a `LSteps`. -/
theorem single {g : AnalysisCFG Node Edge} {e : EdgeOf g}
    {σ σ' : State} (hstep : LangSem.LStep g e σ σ') :
    LSteps g (g.srcOf e) σ (g.dstOf e) σ' :=
  .step hstep (.refl _ _) rfl

/-- transitivity of `LSteps` -/
theorem trans {g : AnalysisCFG Node Edge}
    {n n₁ n' : Node} {σ σ₁ σ' : State}
    (hl : LSteps g n σ n₁ σ₁) (hr : LSteps g n₁ σ₁ n' σ') :
    LSteps g n σ n' σ' := by
  induction hl with
  | refl _ _ => exact hr
  | step hstep _ hsrc ih => exact .step hstep (ih hr) hsrc
  | stut hstut _ ih => exact .stut hstut (ih hr)

end LSteps

structure DFASemantics [LangSem Node Edge State] (A : DFA Node Edge) where
  Corr : A.L -> State -> Prop
  isInit : State -> Prop
  preserve_entry :
    ∀ {σ : State}, isInit σ -> Corr A.entry σ
  preserve_step :
    ∀ {g : AnalysisCFG Node Edge} {e : EdgeOf g} {σ σ' : State} {ℓ : A.L},
      LangSem.LStep g e σ σ' -> Corr ℓ σ -> Corr (A.transferAlong g e ℓ) σ'
  preserve_stutter :
    ∀ {g : AnalysisCFG Node Edge} {n : Node} {σ σ' : State} {ℓ : A.L},
      LangSem.LStutter g n σ σ' -> Corr ℓ σ -> Corr ℓ σ'

/-- a node-indexed labelling is a post-fixpoint of `A`'s transfer if,
    for every `e`, the fact at `srcOf e` after transfer is absorbed
    by the fact at `dstOf e`. -/
def PostFixpoint
    (A : DFA Node Edge) (absorbs : A.L -> A.L -> Prop)
    (g : AnalysisCFG Node Edge) (rd : Node -> A.L) : Prop :=
  ∀ e ∈ g.edges, absorbs (A.transferAlong g e (rd (g.srcOf e))) (rd (g.dstOf e))

/-- step preservation of analysis correctness: if state `σ`
    * is abstracted by the result at node `srcOf e`
    * steps to state `σ'` through `e`
    then `σ'` is abstracted by the result at node `dstOf e` -/
theorem step_preserves_corr
    [LangSem Node Edge State]
    {A : DFA Node Edge} (S : DFASemantics A)
    {absorbs : A.L -> A.L -> Prop}
    (mono_absorb :
      ∀ {ℓ ℓ' : A.L} {σ : State},
        absorbs ℓ ℓ' -> S.Corr ℓ σ -> S.Corr ℓ' σ)
    {g : AnalysisCFG Node Edge} {rd : Node -> A.L}
    (hpf : PostFixpoint A absorbs g rd)
    {e : EdgeOf g} {σ σ' : State}
    (hstep : LangSem.LStep g e σ σ')
    (hcorr : S.Corr (rd (g.srcOf e)) σ) :
    S.Corr (rd (g.dstOf e)) σ' :=
  mono_absorb (hpf e.val e.prop) (S.preserve_step hstep hcorr)

/-- lift of step preservation through the multi-step closure of the step relation. -/
theorem steps_preserves_corr
    [LangSem Node Edge State]
    {A : DFA Node Edge} (S : DFASemantics A)
    {absorbs : A.L -> A.L -> Prop}
    (mono_absorb : ∀ {ℓ ℓ' : A.L} {σ : State},
        absorbs ℓ ℓ' -> S.Corr ℓ σ -> S.Corr ℓ' σ)
    {g : AnalysisCFG Node Edge} {rd : Node -> A.L}
    (hpf : PostFixpoint A absorbs g rd)
    {n n' : Node} {σ σ' : State}
    (hsteps : LSteps g n σ n' σ')
    (hcorr : S.Corr (rd n) σ) :
    S.Corr (rd n') σ' := by
  induction hsteps with
  | refl _ _ => exact hcorr
  | @step e n n'' σ σ' σ'' hstep _ hsrc ih =>
    apply ih
    simpa [hsrc, hcorr] using
      (step_preserves_corr S mono_absorb hpf hstep)
  | stut hstut _ ih =>
    exact ih (S.preserve_stutter hstut hcorr)

/-- State `σ` is `Reachable` if there's an initial state `σ₀` such that a
    chain of steps exists from `σ₀` to `σ`. -/
def Reachable [LangSem Node Edge State] (g : AnalysisCFG Node Edge)
    (n : Node) (σ : State) (isInit : State -> Prop) : Prop :=
  ∃ σ₀ : State, isInit σ₀ ∧ LSteps g g.entry σ₀ n σ

/-- If state σ' is `Reachable`, then the analysis result at the node
    corresponding to it is correct.
    Direct application of `steps_preserves_corr` -/
theorem reachable_corr
    [LangSem Node Edge State]
    {A : DFA Node Edge} (S : DFASemantics A)
    {absorbs : A.L -> A.L -> Prop}
    (mono_absorb :
      ∀ {ℓ ℓ' : A.L} {σ : State},
        absorbs ℓ ℓ' -> S.Corr ℓ σ -> S.Corr ℓ' σ)
    {g : AnalysisCFG Node Edge} {rd : Node -> A.L}
    (hpf : PostFixpoint A absorbs g rd)
    (hentry : absorbs A.entry (rd g.entry))
    {n : Node} {σ : State}
    (hreach : Reachable g n σ S.isInit) :
    S.Corr (rd n) σ := by
  obtain ⟨σ₀, hinit, hsteps⟩ := hreach
  have h_entry : S.Corr A.entry σ₀ := S.preserve_entry hinit
  have h_rd0   : S.Corr (rd g.entry) σ₀ := mono_absorb hentry h_entry
  exact steps_preserves_corr S mono_absorb hpf hsteps h_rd0

end Flow.Analysis.Generic
