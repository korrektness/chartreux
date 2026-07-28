import Chartreux.TIP.Defs
import Chartreux.TIP.Regular.CFG
import Chartreux.TIP.Regular.Analyses.CP
import Chartreux.TIP.Regular.LangSem
import Chartreux.TIP.Utils.DotPrinter
import Chartreux.Analysis.WorklistProofs

open Chartreux.Analysis Chartreux.Analysis.CP Chartreux.Analysis.Generic CFGBuilder
open Chartreux.Eval.Refinement
open Chartreux.TIP (tipLangSem forCFG WFCFG stepsN_to_lsteps)

section Simple
open Expr Stmt BinOp in
def simple :=
  Seq (Decl "a" (.Int 0))
    (Seq (Decl "b" (.Int 1))
      (If (BinOp gt (Var "n") (.Int 0))
        (Assign "b" (BinOp add (Var "a") (Var "b")))
        (Assign "b" (BinOp add (Var "b") (Var "b")))))

def simpleCFG : CFG := CFG.ofStmt simple

private lemma simpleCFG_wf : simpleCFG.WellFormed := by decide

def simpleWFCFG : WFCFG := ⟨simpleCFG, simpleCFG_wf⟩

def sv : { l : List String // l.Nodup } := simpleCFG.vars

instance instlangsem_simple : LangSem NodeID Edge State simpleWFCFG.analysis :=
  tipLangSem simpleWFCFG

/-- The bundled CP analysis result on `simpleCFG`. -/
def simpleResult :
    Chartreux.AnalysisResult (cpAnalysis sv.val sv.property simpleWFCFG) :=
  cpAnalyzeCFG sv.val sv.property simpleWFCFG

theorem cp_correct_reachable :
    ∀ {n : NodeID} {σ : State},
      Reachable simpleWFCFG.analysis n σ State.isInit ->
      cpβ_corr (simpleResult.inFacts n) σ := by
  intro n σ hreach
  exact cp_reachable_correct sv.property simpleWFCFG hreach

#eval IO.println (CFG.toDot simpleCFG)
#eval IO.println
  (CFG.toDotWithFn (A := CPFact sv.val) simpleCFG
    simpleResult.inFacts simpleResult.outFacts)

end Simple

section Hard
open Expr Stmt BinOp in
def loopy : Stmt :=
  Seq (Decl "x" (.Int 2))
    (Seq (Decl "y" (.Int 3))
      (Seq (Decl "i" (.Int 0))
        (Seq (Decl "z" (.Int 0))
          (While (BinOp gt (Var "n") (Var "i"))
            (Seq (Assign "i" (BinOp add (Var "i") (.Int 1)))
                 (If (BinOp gt (Var "x") (.Int 0))
                   (Assign "z" (BinOp mul (Var "x") (Var "y")))
                   (Assign "z" (BinOp mul (Var "y") (Var "x")))))))))

def loopyCFG : CFG := CFG.ofStmt loopy

private lemma loopyCFG_wf : loopyCFG.WellFormed := by decide

def loopyVars : { l : List String // l.Nodup } := loopyCFG.vars

def loopyWFCFG : WFCFG := ⟨loopyCFG, loopyCFG_wf⟩

instance instlangsem_loopy : LangSem NodeID Edge State loopyWFCFG.analysis :=
  tipLangSem loopyWFCFG

def loopyResult :
    Chartreux.AnalysisResult (cpAnalysis loopyVars.val loopyVars.property loopyWFCFG) :=
  cpAnalyzeCFG loopyVars.val loopyVars.property loopyWFCFG

theorem loopy_cp_correct :
    ∀ {n : NodeID} {σ : State},
      Reachable loopyWFCFG.analysis n σ State.isInit ->
      cpβ_corr (loopyResult.inFacts n) σ := by
  intro n σ hreach
  exact cp_reachable_correct loopyVars.property loopyWFCFG hreach

#eval IO.println (CFG.toDot loopyCFG)
#eval IO.println
  (CFG.toDotWithFn (A := CPFact loopyVars.val) loopyCFG
    loopyResult.inFacts loopyResult.outFacts)
end Hard
