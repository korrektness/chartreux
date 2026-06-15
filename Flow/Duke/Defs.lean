inductive BinOp where
| add | sub | mul | lt | eq | and
deriving DecidableEq, Repr

inductive Expr where
| Null
| Int (n : Int)
| Var (x : String)
| IsNull (e : Expr)
| Not (e : Expr)
| BinOp (o : BinOp) (e₁ e₂ : Expr)
deriving DecidableEq, Repr

inductive Val where
| Null
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
