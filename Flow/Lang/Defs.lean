inductive BinOp where
| add | sub | mul | div | gt | eq
deriving DecidableEq, Repr

inductive Expr where
| Int (n : Int)
| Var (x : String)
| BinOp (o : BinOp) (e₁ e₂ : Expr)
deriving DecidableEq, Repr

inductive Stmt where
| Skip
| Assign (x : String) (e : Expr)
| If (c : Expr) (t e : Stmt)
| While (c : Expr) (b : Stmt)
| Seq (s₁ s₂ : Stmt)
deriving DecidableEq, Repr

structure Fun where
  name : String
  params : List String
  locals : List String
  body : Stmt
  ret : Expr
deriving Repr
