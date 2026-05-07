import Flow.Analysis.Generic
import Flow.Lang.CFG
import Flow.Lang.Eval
import Flow.Eval.Refinement

namespace Flow.Eval.Collection

open Flow.Analysis.Generic
open Flow.Eval.Refinement

abbrev SetState := State → Prop

def transfer (g : CFG) (n : NodeID) (R : SetState) : SetState :=
  match g.nodeKind n with
  | some (.Assign x e) =>
      fun σ' => ∃ σ v, R σ ∧ EvalExpr σ e v ∧ σ' = σ.updated x v
  | some (.Decl   x e) =>
      fun σ' => ∃ σ v, R σ ∧ EvalExpr σ e v ∧ σ' = σ.updated x v
  | some .Skip       => R
  | some (.Cond _)   => R
  | none             => R

def Collecting : DFA where
  L            := SetState
  nodeTransfer := transfer
  edgeTransfer := fun _ _ R => R
  entry        := fun _ _ => True

@[simp] theorem Collecting_transferAlong (g : CFG) (e : Edge) (R : SetState) :
    Collecting.transferAlong g e R = transfer g e.src R := rfl

def Corr (_ : CFG) (R : SetState) (σ : CEK) : Prop := R σ.E

def CollectingSem : DFASemantics Collecting where
  Corr := Corr
  preserve_id := by
    intro g R σ σ' hE hR
    show R σ'.E
    simp [hE]
    exact hR
  preserve_assign := by
    intro g n R σ σ' x e v edge _hmem hsrc hassign heval hE hR
    rw [Collecting_transferAlong, hsrc]
    show (transfer g n R) σ'.E
    rcases hassign with h | h
    · simp only [transfer, h]
      exact ⟨σ.E, v, hR, heval, hE⟩
    · simp only [transfer, h]
      exact ⟨σ.E, v, hR, heval, hE⟩
  preserve_branch := by
    intro g n R σ σ' c _k _v edge _hmem hsrc _hkind hbr _heval _hbt hE hR
    rw [Collecting_transferAlong, hsrc]
    show (transfer g n R) σ'.E
    simp [NodeBranches] at hbr
    simp only [transfer, hbr, hE]
    exact hR
  preserve_advance := by
    intro g n R σ σ' edge _hmem hsrc _hkind hskip hE hR
    rw [Collecting_transferAlong, hsrc]
    show (transfer g n R) σ'.E
    simp only [transfer, hskip, hE]
    exact hR

-- set inclusion
def absorbs (R R' : SetState) : Prop := ∀ σ, R σ → R' σ

theorem mono_absorb
    {g : CFG} {R R' : SetState} {σ : CEK}
    (h : absorbs R R') (hR : Corr g R σ) : Corr g R' σ :=
  h _ hR

theorem soundness
    {g : CFG} {rd : NodeID → SetState}
    (hpf : PostFixpoint Collecting absorbs g rd)
    {n n' : Nat}
    {h : n < g.nodes.length} {h' : n' < g.nodes.length}
    {σ σ' : CEK}
    (hsteps : StepsN g h σ h' σ')
    (hcorr : Corr g (rd n) σ) :
    Corr g (rd n') σ' :=
  steps_preserves_corr CollectingSem (@mono_absorb) hpf hsteps hcorr

end Flow.Eval.Collection
