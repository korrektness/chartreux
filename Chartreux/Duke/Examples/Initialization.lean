import Chartreux.Duke.Defs
import Chartreux.Duke.Eval
import Chartreux.Duke.CFG
import Chartreux.Duke.Utils
import Chartreux.Duke.Resolve
import Chartreux.Duke.Analyses.Initialization
import Chartreux.Analysis.WorklistProofs

open Chartreux.Analysis Duke.Analysis.Initialization Chartreux.Analysis.Generic
open Duke.Syntax

def prog : SStmt :=
  @let "x" := 0 ;;
  @let "p" := null ;;
  @let "q" := null ;;
  @while ("x" @< 10) @do (
    @let "p_wit" := @!(¿ "p") ;;
    @if ("p_wit" @&& @!(¿ "q")) @then
      "x" ::= ("p" + "q")
    @else
      "p" ::= 1 ;;
      "q" ::= 2 ;;
      "x" ::= "x" + 1
  ) ;;
  skip

def resolved :=
  match h : resolve prog with
  | some res => res
  | none => by contradiction

def nprog := resolved.fst
def mapping := resolved.snd

def cfg := nprog.wfcfg
def vars := totalVars cfg

#eval checkCFG cfg

def result : Chartreux.AnalysisResult (@analysis vars cfg) :=
  @analyzeCFG vars cfg

#eval IO.println (cfg.val.toDotWithFn mapping
  (fun n => formatFact mapping vars (result.inFacts n))
  (fun n => formatFact mapping vars (result.outFacts n)))
