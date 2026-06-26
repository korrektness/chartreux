import Flow.Duke.Defs
import Flow.Duke.Eval
import Flow.Duke.CFG
import Flow.Duke.Utils
import Flow.Duke.Analyses.Nullability
import Flow.Analysis.WorklistProofs

open Flow.Analysis Duke.Analysis.Nullability Flow.Analysis.Generic
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

def result : Flow.AnalysisResult (analysis sv.prop cfg) :=
  analyzeCFG sv.prop cfg

#eval IO.println (cfg.val.toDotWithFn (A := String)
  (fun n => formatFact sv.val (result.inFacts n))
  (fun n => formatFact sv.val (result.outFacts n)))
