import Chartreux.FDuke.Defs
import Chartreux.FDuke.Eval
import Chartreux.FDuke.CFG
import Chartreux.FDuke.Utils
import Chartreux.FDuke.Refinement
import Chartreux.FDuke.Analyses.Nullability
import Chartreux.FDuke.Analyses.Initialization
import Chartreux.FDuke.CFGSafety
import Chartreux.Analysis.WorklistProofs

open Chartreux.Analysis FDuke.Analysis.Nullability Chartreux.Analysis.Generic
open FDuke.Refinement
open FDuke.Counting
open FDuke.CFGSafety
open Duke.Syntax

def Φ : FunEnv := [ ⟨"run", .once, @invoke⟩ ]

def prog : Stmt :=
  @let "x" := null ;;
  @call "run" { @let "x" := 4 }

def cfg := prog.wfcfg Φ

def P : Program := {
  phi := Φ
  main := prog
}

def a := P.family

#eval checkCFG cfg

def sv : { l : List String // l.Nodup } := vars cfg

def result : Chartreux.AnalysisResult (analysis sv.prop cfg) :=
  analyzeCFG sv.prop cfg

def initResult : Chartreux.AnalysisResult (FDuke.Analysis.Initialization.analysis sv.prop cfg) :=
  FDuke.Analysis.Initialization.analyzeCFG sv.prop cfg

theorem result_correct {n : NodeID} {σ : State}
    (hreach : Chartreux.Analysis.Generic.Reachable cfg.analysis n σ State.isInit) :
    coh (result.inFacts n) σ := by
  exact reachable_correct sv.prop cfg hreach

set_option linter.style.nativeDecide false in
theorem P_checked : FamilyChecked P.family := by
  let cfg := (invoke ;; .Skip).wfcfgFrom Φ 1
  intro q hq
  change q ∈ [("run", InvKind.once, cfg)] at hq
  simp only [List.mem_singleton] at hq
  subst q
  let result := FDuke.Counting.analyzeCFG cfg
  refine ⟨result.inFacts, result.isPostFix, result.inFacts_entry, ?_⟩
  change CountVerdict .once (result.inFacts 1)
  native_decide

theorem P_correct {n' : NodeID} {σ' : State} {ρ' : Option Clo}
    (hsteps : Steps P.family ⟨(.main, cfg.analysis.entry), State.empty, none, []⟩
      ⟨(.main, n'), σ', ρ', []⟩) :
    coh (result.inFacts n') σ' := by
  apply result_correct
  refine ⟨State.empty, rfl, ?_⟩
  exact cek_projection P P_checked (self := .main) cfg (by rfl) hsteps

theorem P_progress {n' : NodeID} {σ' : State} {ρ' : Option Clo}
    (hsteps : Steps P.family ⟨(.main, cfg.analysis.entry), State.empty, none, []⟩
      ⟨(.main, n'), σ', ρ', []⟩)
    (e : FExpr)
    (hnull : checkExpr (result.inFacts n') e)
    (hinit : FDuke.Analysis.Initialization.checkExpr (initResult.inFacts n') e) :
    ∃ v, EvalExpr σ' e v := by
  apply eval_expr_progress e (P_correct hsteps).left
  · exact FDuke.Analysis.Initialization.reachable_correct sv.prop cfg
      ⟨State.empty, rfl, cek_projection P P_checked (self := .main) cfg (by rfl) hsteps⟩
  · exact hnull
  · exact hinit

#eval IO.println (cfg.val.toDotWithFn
  (fun n => formatFact sv.val (result.inFacts n))
  (fun n => formatFact sv.val (result.outFacts n)))


