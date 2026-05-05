import Flow.Lang.CFG
import Flow.Lang.Eval
import Flow.Eval.Refinement

namespace Flow.Analysis.Generic

open Flow.Eval.Refinement

/-! ## Abstract dataflow framework -/

structure DFA where
  L        : Type
  transfer : CFG → NodeID → L → L
  entry    : CFG → L

structure DFASemantics (A : DFA) where
  Corr : CFG → A.L → CEK → Prop
  preserve_id :
    ∀ {g : CFG} {n : NodeID} {ℓ : A.L} {σ σ' : CEK},
      NodeNonMutating g n →
      σ'.E = σ.E →
      Corr g ℓ σ →
      Corr g ℓ σ'
  preserve_assign :
    ∀ {g : CFG} {n : NodeID} {ℓ : A.L} {σ σ' : CEK}
      {x : String} {e : Expr} {v : Val},
      NodeAssigns g n x e →
      EvalExpr σ.E e v ->
      σ'.E = σ.E.updated x v →
      Corr g ℓ σ →
      Corr g (A.transfer g n ℓ) σ'

def PostFixpoint (A : DFA) (absorbs : A.L → A.L → Prop)
    (g : CFG) (rd : NodeID → A.L) : Prop :=
  ∀ n n' : NodeID, n < g.nodes.length → n' < g.nodes.length →
    (∃ k, g.hasEdge n n' k) →
    absorbs (A.transfer g n (rd n)) (rd n')

theorem step_preserves_corr
    {A : DFA} (S : DFASemantics A)
    {absorbs : A.L → A.L → Prop}
    (mono_absorb :
      ∀ {g : CFG} {ℓ ℓ' : A.L} {σ : CEK},
        absorbs ℓ ℓ' → S.Corr g ℓ σ → S.Corr g ℓ' σ)
    {g : CFG} {rd : NodeID → A.L}
    (hpf : PostFixpoint A absorbs g rd)
    {n n' : Nat}
    {h : n < g.nodes.length} {h' : n' < g.nodes.length}
    {σ σ' : CEK}
    (hsim : StepN g h σ h' σ')
    (hcorr : S.Corr g (rd n) σ) :
    S.Corr g (rd n') σ' := by
  cases hsim with
  | stutter _ _ hnm hE =>
    exact S.preserve_id hnm hE hcorr
  | mutate _ _ x e v _ hassign heval hedge hE =>
    have hadv := S.preserve_assign (x := x) (e := e) (v := v)
                   hassign heval hE hcorr
    exact mono_absorb (hpf n n' h h' hedge) hadv

theorem steps_preserves_corr
    {A : DFA} (S : DFASemantics A)
    {absorbs : A.L → A.L → Prop}
    (mono_absorb :
      ∀ {g : CFG} {ℓ ℓ' : A.L} {σ : CEK},
        absorbs ℓ ℓ' → S.Corr g ℓ σ → S.Corr g ℓ' σ)
    {g : CFG} {rd : NodeID → A.L}
    (hpf : PostFixpoint A absorbs g rd)
    {n n' : Nat}
    {h : n < g.nodes.length} {h' : n' < g.nodes.length}
    {σ σ' : CEK}
    (hsteps : StepsN g h σ h' σ')
    (hcorr : S.Corr g (rd n) σ) :
    S.Corr g (rd n') σ' := by
  induction hsteps with
  | refl _ _ => exact hcorr
  | step _ _ _ hsim _ ih =>
    exact ih (step_preserves_corr S mono_absorb hpf hsim hcorr)

end Flow.Analysis.Generic
