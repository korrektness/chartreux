import Flow.Lang.Defs

inductive Val where
| Int (n : Int)
deriving DecidableEq, Repr

def State := String -> Option Val
def State.updated (σ : State) (x : String) (v : Val) : State :=
  fun y => if x = y then v else σ y

def applyOp : BinOp -> Int -> Int -> Option Int
| .add, n₁, n₂ => some (n₁ + n₂)
| .sub, n₁, n₂ => some (n₁ - n₂)
| .mul, n₁, n₂ => some (n₁ * n₂)
| .div, _,  0  => none
| .div, n₁, n₂ => some (n₁ / n₂)
| .gt,  n₁, n₂ => some (if n₁ > n₂ then 1 else 0)
| .eq,  n₁, n₂ => some (if n₁ = n₂ then 1 else 0)

inductive EvalExpr : State -> Expr -> Val -> State -> Prop where
| int : EvalExpr σ (.Int n) (.Int n) σ
| var : σ x = some v -> EvalExpr σ (.Var x) v σ
| arith :
    o ≠ .eq -> EvalExpr σ n₁ (.Int v₁) σ₁ -> EvalExpr σ₁ n₂ (.Int v₂) σ₂ ->
    applyOp o v₁ v₂ = some v ->
    EvalExpr σ (.BinOp o n₁ n₂) (.Int v) σ₂
| eq :
    EvalExpr σ e₁ v₁ σ₁ → EvalExpr σ₁ e₂ v₂ σ₂ →
    EvalExpr σ (.BinOp .eq e₁ e₂) (.Int (if v₁ = v₂ then 1 else 0)) σ₂

inductive Step : Stmt -> State -> Option Stmt -> State -> Prop where
| skip : Step .Skip σ none σ
| assign : EvalExpr σ e v σ' -> Step (.Assign x e) σ none (σ'.updated x v)
| seq_step :
    Step s₁ σ (some s₁') σ' →
    Step (.Seq s₁ s₂) σ (some (.Seq s₁' s₂)) σ'
| seq_done :
    Step s₁ σ none σ' →
    Step (.Seq s₁ s₂) σ (some s₂) σ'
| ite_true :
    EvalExpr σ c (.Int n) σ' -> n ≠ 0 -> Step (.If c t _) σ (some t) σ'
| ite_false :
    EvalExpr σ c (.Int n) σ' -> n = 0 -> Step (.If c _ e) σ (some e) σ'
| while :
    Step (.While c b) σ (some (.If c (.Seq b (.While c b)) .Skip)) σ

inductive Steps : Option Stmt → State → Option Stmt → State → Prop where
  | refl : Steps s σ s σ
  | step : Step s σ s' σ' → Steps s' σ' s'' σ'' →
           Steps (some s) σ s'' σ''

def Terminates (s : Stmt) (σ : State) (σ' : State) : Prop :=
  Steps (some s) σ none σ'
