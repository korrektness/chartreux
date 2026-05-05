inductive BinOp where
| add | sub | mul | gt | eq
deriving DecidableEq, Repr

inductive Expr where
| Int (n : Int)
| Var (x : String)
| BinOp (o : BinOp) (e₁ e₂ : Expr)
deriving DecidableEq, Repr

inductive Val where
| Int (n : Int)
deriving DecidableEq, Repr

inductive Stmt where
| Skip
| Decl (x : String) (e : Expr)
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
