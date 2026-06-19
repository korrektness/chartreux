import Flow.TIP.Defs
import Flow.TIP.Regular.CFG
import Flow.TIP.Regular.Analyses.CP
import Flow.TIP.Regular.LangSem
import Flow.TIP.Utils.DotPrinter
import Flow.Analysis.WorklistProofs

open Flow.Analysis Flow.Analysis.CP Flow.Analysis.Generic CFGBuilder Flow.Eval.Refinement
open Flow.TIP (tipLangSem forCFG WFCFG stepsN_to_lsteps)

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
    Flow.AnalysisResult (cpAnalysis sv.val sv.prop simpleWFCFG) :=
  cpAnalyzeCFG sv.val sv.prop simpleWFCFG

theorem cp_correct_reachable :
    ∀ {n : NodeID} {σ : State},
      Reachable simpleWFCFG.analysis n σ State.isInit ->
      cpβ_corr (simpleResult.inFacts n) σ := by
  intro n σ hreach
  exact cp_reachable_correct sv.prop simpleWFCFG hreach

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
    Flow.AnalysisResult (cpAnalysis loopyVars.val loopyVars.prop loopyWFCFG) :=
  cpAnalyzeCFG loopyVars.val loopyVars.prop loopyWFCFG

theorem loopy_cp_correct :
    ∀ {n : NodeID} {σ : State},
      Reachable loopyWFCFG.analysis n σ State.isInit ->
      cpβ_corr (loopyResult.inFacts n) σ := by
  intro n σ hreach
  exact cp_reachable_correct loopyVars.prop loopyWFCFG hreach

#eval IO.println (CFG.toDot loopyCFG)
#eval IO.println
  (CFG.toDotWithFn (A := CPFact loopyVars.val) loopyCFG
    loopyResult.inFacts loopyResult.outFacts)
end Hard
