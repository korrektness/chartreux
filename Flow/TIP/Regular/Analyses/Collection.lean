import Flow.Analysis.Generic
import Flow.TIP.Regular.CFG
import Flow.TIP.Eval
import Flow.TIP.Regular.Correspondence.Refinement
import Flow.TIP.Regular.LangSem

namespace Flow.Eval.Collection

open Flow.Analysis Flow.Analysis.Generic
open Flow.Eval.Refinement
open Flow.TIP (tipLStep tipLStutter tipLangSem)

abbrev SetState := State → Prop

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
def Collecting (cfg : CFG) : DFA NodeID Edge where
  L            := SetState
  nodeTransfer := fun _G n => transfer cfg n
  edgeTransfer := fun _G _e R => R
  entry        := fun _G _ => True

@[simp] theorem Collecting_transferAlong (cfg : CFG)
    (G : AnalysisCFG NodeID Edge) (e : Edge) (R : SetState) :
    (Collecting cfg).transferAlong G e R = transfer cfg (G.srcOf e) R := rfl

def Corr (_cfg : CFG) (_G : AnalysisCFG NodeID Edge) (R : SetState) (σ : CEK) : Prop :=
  R σ.E

def CollectingSem (cfg : CFG) :
    letI := tipLangSem cfg
    DFASemantics (State := CEK) (Collecting cfg) :=
  letI : LangSem NodeID Edge CEK := tipLangSem cfg
  { Corr := Corr cfg
    preserve_entry := by intro _ _ _; trivial
    preserve_step := by
      intro G e σ σ' R hstep hR
      obtain ⟨_hmem, hsrc, _hdst, hcase⟩ := hstep
      simp only [Collecting_transferAlong, hsrc]
      rcases hcase with ⟨x, e', v, hassign, heval, hE⟩
                       | ⟨c, _v, hbr, _heval, _hbt, hE⟩
                       | ⟨hskip, _hkind, hE⟩
      · change (transfer cfg e.src R) σ'.E
        rcases hassign with hh | hh
        · simp only [transfer, hh]; exact ⟨σ.E, v, hR, heval, hE⟩
        · simp only [transfer, hh]; exact ⟨σ.E, v, hR, heval, hE⟩
      · change (transfer cfg e.src R) σ'.E
        simp [NodeBranches] at hbr
        simp only [transfer, hbr, hE]; exact hR
      · change (transfer cfg e.src R) σ'.E
        simp only [transfer, hskip, hE]; exact hR
    preserve_stutter := by
      intro _G _n σ σ' R hstut hR
      change σ'.E = σ.E at hstut
      simpa [Corr, hstut] using hR }

def absorbs (R R' : SetState) : Prop := ∀ σ, R σ → R' σ

theorem mono_absorb
    {cfg : CFG} {G : AnalysisCFG NodeID Edge} {R R' : SetState} {σ : CEK}
    (h : absorbs R R') (hR : Corr cfg G R σ) : Corr cfg G R' σ :=
  h _ hR

end Flow.Eval.Collection
