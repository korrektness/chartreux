import Chartreux.Duke.Defs
import Chartreux.Duke.Eval
import Chartreux.Duke.CFG
import Chartreux.Duke.Utils
import Chartreux.Duke.Analyses.Nullability
import Chartreux.Analysis.WorklistProofs

open Chartreux.Analysis Duke.Analysis.Nullability Chartreux.Analysis.Generic
open Duke.Syntax

def prog : Stmt :=
  @let "x" := 0 ;;
  @let "p" := null ;;
  @let "q" := null ;;
  @while ("x" @< 10) @do (
    @let "p_wit" := @!(¿ "p") ;;
    -- @let "p" := null ;;
    @if ("p_wit" @&& @!(¿ "q")) @then
      "x" ::= ("p" + "q")
    @else
      "p" ::= 1 ;;
      "q" ::= 2 ;;
      "x" ::= "x" + 1
  ) ;;
  skip


def cfg := prog.wfcfg

#eval checkCFG cfg

def sv : { l : List String // l.Nodup } := vars cfg

def result : Chartreux.AnalysisResult (analysis sv.prop cfg) :=
  analyzeCFG sv.prop cfg

#eval IO.println (cfg.val.toDotWithFn (A := String)
  (fun n => formatFact sv.val (result.inFacts n))
  (fun n => formatFact sv.val (result.outFacts n)))
