import Flow.Analysis.Generic
import Flow.TIP.Regular.CFG
import Flow.TIP.Eval
import Flow.TIP.Regular.Correspondence.Refinement
import Flow.TIP.Regular.LangSem

namespace Flow.Eval.Collection

open Flow.Analysis Flow.Analysis.Generic
open Flow.Eval.Refinement
open Flow.TIP (tipLStep tipLStutter tipLangSem WFCFG)

abbrev SetState := State -> Prop

def transfer (cfg : CFG) (n : NodeID) (R : SetState) : SetState :=
  match cfg.nodeKind n with
  | some (.Assign x e) =>
      fun σ' => ∃ σ v, R σ ∧ EvalExpr σ e v ∧ σ' = σ.updated x v
  | some (.Decl   x e) =>
      fun σ' => ∃ σ v, R σ ∧ EvalExpr σ e v ∧ σ' = σ.updated x v
  | some .Skip       => R
  | some (.Cond _)   => R
  | none             => R

/-- The collecting-semantics DFA, parameterised by the underlying TIP CFG. -/
def Collecting (cfg : WFCFG) : DFA NodeID Edge State cfg.analysis where
  L            := SetState
  nodeTransfer := transfer cfg
  edgeTransfer := fun _ R => R
  entry        := fun _ => True

@[simp] private lemma Collecting_transferAlong
    (cfg : WFCFG) (e : EdgeOf cfg.analysis) :
    (Collecting cfg).transferAlong cfg.analysis e ℓ =
    transfer cfg e.val.src ℓ := rfl

def Corr (R : SetState) (σ : State) : Prop :=
  R σ

def CollectingSem
    (cfg : WFCFG) :
    DFASemantics (State := State) cfg.analysis (Collecting cfg) :=
  { Corr := Corr
    isInit := State.isInit
    preserve_entry := by intros σ hσ; cases hσ; simp [Corr, Collecting]
    preserve_step := by
      intro e σ σ' R hstep hR
      simp only [Collecting_transferAlong, transfer]
      rcases hstep with ⟨x, e', v, hassign, heval, hE⟩
                      | ⟨c, _v, hbr, _heval, _hbt, hE⟩
                      | ⟨hskip, _hkind, hE⟩
      · rcases hassign with hh | hh
        · simp only [hh]; exact ⟨σ, v, hR, heval, hE⟩
        · simp only [hh]; exact ⟨σ, v, hR, heval, hE⟩
      · simp [NodeBranches] at hbr
        simp only [hbr, hE]; exact hR
      · simp only [hskip, hE]; exact hR
    preserve_stutter := by
      intro _n σ σ' R hstut hR
      change σ' = σ at hstut
      simpa [Corr, hstut] using hR }

def absorbs (R R' : SetState) : Prop := ∀ σ, R σ -> R' σ

theorem mono_absorb {R R' : SetState} {σ : State}
    (h : absorbs R R') (hR : Corr R σ) : Corr R' σ :=
  h _ hR

end Flow.Eval.Collection
