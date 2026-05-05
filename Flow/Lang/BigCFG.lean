import Flow.Lang.Defs

inductive NodeKind where
| entry
| exit
| stmtEntry (s : Stmt)
| stmtExit (s : Stmt)
| exprEntry (e : Expr)
| exprExit (e : Expr)
| literal (e : Val)
| cond (c : Expr)
deriving DecidableEq, Repr

inductive EdgeKind where
| normal
| trueBranch
| falseBranch
deriving DecidableEq, Repr

structure Edge where
  src : Nat
  dst : Nat
  kind : EdgeKind
deriving DecidableEq, Repr

structure BigCFG where
  nodes : List NodeKind
  edges : List Edge
  entry : Nat
  exit  : Nat

namespace BigCFG
def nodeKind (g : BigCFG) (n : Nat) : Option NodeKind :=
  g.nodes[n]?

def succ (g : BigCFG) (n : Nat) : List Nat :=
  g.edges.filterMap (fun ⟨src, dst, _⟩ => if src = n then some dst else none)

def pred (g : BigCFG) (n : Nat) : List Nat :=
  g.edges.filterMap (fun ⟨src, dst, _⟩ => if dst = n then some src else none)

def hasEdge (g : BigCFG) (src dst : Nat) (lbl : EdgeKind) : Prop :=
  ⟨src, dst, lbl⟩ ∈ g.edges

end BigCFG

structure CFGBuilder where
  cfg : BigCFG
  nextId : Nat

namespace CFGBuilder

def empty : CFGBuilder :=
  { cfg := { nodes := [], edges := [], entry := 0, exit := 0 }, nextId := 0 }

def addNode (builder : CFGBuilder) (kind : NodeKind) : CFGBuilder × Nat :=
  let nodeId := builder.nextId
  let cfg := { builder.cfg with nodes := builder.cfg.nodes ++ [kind] }
  ({ cfg := cfg, nextId := nodeId + 1 }, nodeId)

def addEdge (builder : CFGBuilder) (src dst : Nat) (kind : EdgeKind := .normal) : CFGBuilder :=
  { builder with cfg := { builder.cfg with edges := builder.cfg.edges ++ [⟨src, dst, kind⟩] } }

def buildExpr (builder : CFGBuilder) (e : Expr) : CFGBuilder × (Nat × Nat) :=
  match e with
  | .Int n =>
      let (builder, node) := addNode builder (.literal (.Int n))
      (builder, (node, node))
  | .Var x =>
      let (builder, entry) := addNode builder (.exprEntry (.Var x))
      let (builder, exit) := addNode builder (.exprExit (.Var x))
      let builder := addEdge builder entry exit
      (builder, (entry, exit))
  | .BinOp o e₁ e₂ =>
      let (builder, entry) := addNode builder (.exprEntry (.BinOp o e₁ e₂))
      let (builder, (leftEntry, leftExit)) := buildExpr builder e₁
      let builder := addEdge builder entry leftEntry
      let (builder, (rightEntry, rightExit)) := buildExpr builder e₂
      let builder := addEdge builder leftExit rightEntry
      let (builder, exit) := addNode builder (.exprExit (.BinOp o e₁ e₂))
      let builder := addEdge builder rightExit exit
      (builder, (entry, exit))

def buildStmt (builder : CFGBuilder) (s : Stmt) (whileBackEdge : Bool := true) : CFGBuilder × (Nat × Nat) :=
  match s with
  | .Skip =>
      let (builder, entry) := addNode builder (.stmtEntry .Skip)
      let (builder, exit) := addNode builder (.stmtExit .Skip)
      let builder := addEdge builder entry exit
      (builder, (entry, exit))
  | .Decl x e =>
      let (builder, entry) := addNode builder (.stmtEntry (.Decl x e))
      let (builder, (exprEntry, exprExit)) := buildExpr builder e
      let builder := addEdge builder entry exprEntry
      let (builder, exit) := addNode builder (.stmtExit (.Decl x e))
      let builder := addEdge builder exprExit exit
      (builder, (entry, exit))
  | .Assign x e =>
      let (builder, entry) := addNode builder (.stmtEntry (.Assign x e))
      let (builder, (exprEntry, exprExit)) := buildExpr builder e
      let builder := addEdge builder entry exprEntry
      let (builder, exit) := addNode builder (.stmtExit (.Assign x e))
      let builder := addEdge builder exprExit exit
      (builder, (entry, exit))
  | .Seq s₁ s₂ =>
      let (builder, entry) := addNode builder (.stmtEntry (.Seq s₁ s₂))
      let (builder, (leftEntry, leftExit)) := buildStmt builder s₁ whileBackEdge
      let builder := addEdge builder entry leftEntry
      let (builder, (rightEntry, rightExit)) := buildStmt builder s₂ whileBackEdge
      let builder := addEdge builder leftExit rightEntry
      let (builder, exit) := addNode builder (.stmtExit (.Seq s₁ s₂))
      let builder := addEdge builder rightExit exit
      (builder, (entry, exit))
  | .If c t f =>
      let (builder, entry) := addNode builder (.stmtEntry (.If c t f))
      let (builder, (condEntry, condExit)) := buildExpr builder c
      let builder := addEdge builder entry condEntry
      let (builder, condNode) := addNode builder (.cond c)
      let builder := addEdge builder condExit condNode
      let (builder, (thenEntry, thenExit)) := buildStmt builder t whileBackEdge
      let (builder, (elseEntry, elseExit)) := buildStmt builder f whileBackEdge
      let builder := addEdge builder condNode thenEntry .trueBranch
      let builder := addEdge builder condNode elseEntry .falseBranch
      let (builder, exit) := addNode builder (.stmtExit (.If c t f))
      let builder := addEdge builder thenExit exit
      let builder := addEdge builder elseExit exit
      (builder, (entry, exit))
  | .While c body =>
      let (builder, entry) := addNode builder (.stmtEntry (.While c body))
      let (builder, (condEntry, condExit)) := buildExpr builder c
      let builder := addEdge builder entry condEntry
      let (builder, condNode) := addNode builder (.cond c)
      let builder := addEdge builder condExit condNode
      let (builder, (bodyEntry, bodyExit)) := buildStmt builder body whileBackEdge
      let builder := addEdge builder condNode bodyEntry .trueBranch
      let (builder, exit) := addNode builder (.stmtExit (.While c body))
      let builder := addEdge builder condNode exit .falseBranch
      let builder := if whileBackEdge then addEdge builder bodyExit condEntry else addEdge builder bodyExit exit
      (builder, (entry, exit))

def buildProgram (s : Stmt) (whileBackEdge : Bool := true) : BigCFG :=
  let (builder, (stmtEntry, stmtExit)) := buildStmt empty s whileBackEdge
  let (builder, entry) := addNode builder .entry
  let (builder, exit) := addNode builder .exit
  let builder := addEdge builder entry stmtEntry
  let builder := addEdge builder stmtExit exit
  { builder.cfg with entry := entry, exit := exit }

end CFGBuilder
