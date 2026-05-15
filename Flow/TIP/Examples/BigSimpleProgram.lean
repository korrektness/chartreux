import Flow.TIP.Defs
import Flow.TIP.Big.CFG
import Flow.TIP.Utils.BigDotPrinter
import Flow.Analysis.WorklistProofs

open Flow.Analysis Flow.Analysis.Generic BigCFGBuilder

open Expr Stmt BinOp in
def simpleBig :=
  Seq (Decl "a" (.Int 0))
    (Seq (Decl "b" (.Int 1))
      (If (BinOp gt (Var "n") (.Int 0))
        (Assign "b" (BinOp add (Var "a") (Var "b")))
        (Assign "b" (BinOp add (Var "b") (Var "b")))))

def test := BigCFG.ofStmt simpleBig

#eval (IO.println (BigCFG.toDot test))
