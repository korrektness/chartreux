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
    ∀ {g : CFG} {ℓ : A.L} {σ σ' : CEK},
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
  preserve_branch :
    ∀ {g : CFG} {n : NodeID} {ℓ : A.L} {σ σ' : CEK}
      {c : Expr} {k : EdgeKind} {v : Val},
      NodeBranches g n c →
      EvalExpr σ.E c v →
      BranchTaken k v →
      σ'.E = σ.E →
      Corr g ℓ σ →
      Corr g (A.transfer g n ℓ) σ'
  /-- Node-advancing without writeback: at a `.Skip` node, the environment
      is preserved and the CFG advances along a `.Normal` edge. The
      analysis must show that applying the local transfer at `n` keeps
      `Corr` for the post-state under any value of the post-fixpoint. -/
  preserve_advance :
    ∀ {g : CFG} {n : NodeID} {ℓ : A.L} {σ σ' : CEK},
      g.nodeKind n = some .Skip →
      σ'.E = σ.E →
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
  | stutter _ _ hE =>
    exact S.preserve_id hE hcorr
  | mutate _ _ x e v _ hassign heval hedge hE =>
    have hadv := S.preserve_assign (x := x) (e := e) (v := v)
                   hassign heval hE hcorr
    exact mono_absorb (hpf n n' h h' hedge) hadv
  | branch _ _ c k v _ hbr hedge heval hbt hE =>
    have hadv := S.preserve_branch (c := c) (k := k) (v := v)
                   hbr heval hbt hE hcorr
    exact mono_absorb (hpf n n' h h' ⟨k, hedge⟩) hadv
  | advance _ _ _ hskip hedge hE =>
    have hadv := S.preserve_advance (n := n) hskip hE hcorr
    exact mono_absorb (hpf n n' h h' ⟨_, hedge⟩) hadv

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
  | @skipBridge n₀ n₁ n₂ h₀ h₁ h₂ σ σ' hkind₀ hedge _ ih =>
    apply ih
    have hadv := S.preserve_advance (n := n₀) hkind₀ rfl hcorr
    exact mono_absorb (hpf n₀ n₁ h₀ h₁ ⟨_, hedge⟩) hadv


end Flow.Analysis.Generic
