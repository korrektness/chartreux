import Flow.TIP.Defs
import Flow.TIP.Regular.CFG
import Flow.TIP.Regular.Analyses.CP
import Flow.TIP.Regular.LangSem
import Flow.TIP.Utils.DotPrinter
import Flow.Analysis.WorklistProofs

open Flow.Analysis Flow.Analysis.CP Flow.Analysis.Generic CFGBuilder Flow.Eval.Refinement
open Flow.TIP (tipLangSem forCFG forCFG_of_wf stepsN_to_lsteps)

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

def sv : { l : List String // l.Nodup } := simpleCFG.vars

instance instlangsem_simple : LangSem NodeID Edge CEK := tipLangSem simpleCFG

/-- The bundled CP analysis result on `simpleCFG`. -/
def simpleResult :
    letI := tipLangSem simpleCFG
    Flow.AnalysisResult (cpAnalysis sv.val sv.prop simpleCFG)
      (forCFG_of_wf simpleCFG simpleCFG_wf) :=
  cpAnalyzeCFG sv.val sv.prop simpleCFG simpleCFG_wf

theorem cp_correct_reachable :
    letI := tipLangSem simpleCFG
    ∀ {n : NodeID} {σ : CEK},
      Reachable (forCFG_of_wf simpleCFG simpleCFG_wf) n σ →
      cpβ_corr simpleCFG (simpleResult.inFacts n) σ := by
  letI : LangSem NodeID Edge CEK := tipLangSem simpleCFG
  intro n σ hreach
  exact cp_reachable_correct sv.prop simpleCFG simpleCFG_wf hreach

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

instance instlangsem_loop : LangSem NodeID Edge CEK := tipLangSem loopyCFG

private lemma loopyCFG_wf : loopyCFG.WellFormed := by decide

def loopyVars : { l : List String // l.Nodup } := loopyCFG.vars

def loopyResult :
    letI := tipLangSem loopyCFG
    Flow.AnalysisResult (cpAnalysis loopyVars.val loopyVars.prop loopyCFG)
      (forCFG_of_wf loopyCFG loopyCFG_wf) :=
  cpAnalyzeCFG loopyVars.val loopyVars.prop loopyCFG loopyCFG_wf

theorem loopy_cp_correct :
    letI := tipLangSem loopyCFG
    ∀ {n : NodeID} {σ : CEK},
      Reachable (forCFG_of_wf loopyCFG loopyCFG_wf) n σ →
      cpβ_corr loopyCFG (loopyResult.inFacts n) σ := by
  letI : LangSem NodeID Edge CEK := tipLangSem loopyCFG
  intro n σ hreach
  exact cp_reachable_correct loopyVars.prop loopyCFG loopyCFG_wf hreach

#eval IO.println (CFG.toDot loopyCFG)
#eval IO.println
  (CFG.toDotWithFn (A := CPFact loopyVars.val) loopyCFG
    loopyResult.inFacts loopyResult.outFacts)
end Hard
