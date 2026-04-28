import Flow.Lang.Defs

inductive NodeKind where
| entry
| exit
| skip
| assign (x : String) (e : Expr)
| varDecl (x : String)
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

structure CFG where
  nodes : List NodeKind
  edges : List Edge
  entry : Nat
  exit  : Nat

def CFG.nodeKind (g : CFG) (n : Nat) : Option NodeKind :=
  g.nodes[n]?

def CFG.succ (g : CFG) (n : Nat) : List Nat :=
  g.edges.filterMap (fun ⟨src, dst, _⟩ => if dst = n then some src else none)

def CFG.pred (g : CFG) (n : Nat) : List Nat :=
  g.edges.filterMap (fun ⟨src, dst, _⟩ => if src = n then some dst else none)

structure CFGBuilder where
  cfg : CFG
  nextId : Nat

namespace CFGBuilder

def empty : CFGBuilder where
  cfg := ⟨[], [], 0, 0⟩
  nextId := 0

def addNode (b : CFGBuilder) (label : NodeKind) : CFGBuilder × Nat :=
  let id := b.nextId
  let b' := { b with
    cfg := { b.cfg with nodes := b.cfg.nodes ++ [label] }
    nextId := b.nextId + 1 }
  (b', id)

/-- Add an edge. -/
def addEdge (b : CFGBuilder) (src dst : Nat) (label : EdgeKind := .normal) :
    CFGBuilder :=
  { b with cfg := { b.cfg with edges := b.cfg.edges ++ [⟨src, dst, label⟩] } }

end CFGBuilder

structure BuildResult where
  builder : CFGBuilder
  entry : Nat
  exit : Nat

namespace BuildResult

def single (k : NodeKind) : BuildResult :=
  let (b, enid) := CFGBuilder.empty.addNode .entry
  let (b, stid) := b.addNode k
  let (b, exid) := b.addNode .exit
  let b := b.addEdge enid stid
  let b := b.addEdge stid exid
  { builder := b, entry := enid, exit := exid }

def seq (r₁ r₂ : BuildResult) : BuildResult :=
  let ofst := r₁.builder.nextId
  let n₂ := r₂.builder.cfg.nodes
  let e₂ := r₂.builder.cfg.edges.map (fun ⟨s, d, k⟩ => ⟨s + ofst, d + ofst, k⟩)
  let combined := {
    cfg := {
      nodes := r₁.builder.cfg.nodes ++ n₂
      edges := r₁.builder.cfg.edges ++ e₂ ++ [⟨r₁.exit, r₂.entry + ofst, .normal⟩]
      entry := r₁.entry
      exit := r₂.exit + ofst
    }
    nextId := ofst + r₂.builder.nextId
  }
  { builder := combined, entry := r₁.entry, exit := r₂.exit + ofst}

def ite (c : Expr) (t f : BuildResult) : BuildResult :=
  let (b, enid) := CFGBuilder.empty.addNode .entry
  let (b, cid) := b.addNode (.cond c)
  let (b, exid) := b.addNode .exit
  let b := b.addEdge enid cid
  -- t ofst
  let tofst := b.nextId
  let tn := t.builder.cfg.nodes
  let te := t.builder.cfg.edges.map fun ⟨s, d, l⟩ =>
    ⟨s + tofst, d + tofst, l⟩
  let b : CFGBuilder := {
    cfg := { nodes := b.cfg.nodes ++ tn, edges := b.cfg.edges ++ te,
             entry := enid, exit := exid }
    nextId := b.nextId + t.builder.nextId
  }
  -- f ofst
  let fofst := b.nextId
  let fn := f.builder.cfg.nodes
  let fe := f.builder.cfg.edges.map fun ⟨s, d, l⟩ =>
    ⟨s + fofst, d + fofst, l⟩
  let b : CFGBuilder := {
    cfg := {
      nodes := b.cfg.nodes ++ fn
      edges := b.cfg.edges ++ fe ++
        [⟨cid, t.entry + tofst, .trueBranch⟩,
         ⟨cid, f.entry + fofst, .falseBranch⟩,
         ⟨t.exit + tofst, exid, .normal⟩,
         ⟨f.exit + fofst, exid, .normal⟩]
      entry := enid
      exit := exid
    }
    nextId := b.nextId + f.builder.nextId
  }
  { builder := b, entry := enid, exit := exid }

def whil (c : Expr) (body : BuildResult) : BuildResult :=
  let (b, enid) := CFGBuilder.empty.addNode .entry
  let (b, cid) := b.addNode (.cond c)
  let (b, exid) := b.addNode .exit
  let b := b.addEdge enid cid
  -- t ofst
  let bofst := b.nextId
  let bn := body.builder.cfg.nodes
  let be := body.builder.cfg.edges.map fun ⟨s, d, l⟩ =>
    ⟨s + bofst, d + bofst, l⟩
  let b : CFGBuilder := {
    cfg := {
      nodes := b.cfg.nodes ++ bn,
      edges := b.cfg.edges ++ be ++ [
        ⟨cid, body.entry + bofst, .trueBranch⟩,
        ⟨cid, exid, .falseBranch⟩,
        ⟨body.exit + bofst, cid, .normal⟩
      ],
      entry := enid, exit := exid }
    nextId := b.nextId + body.builder.nextId
  }
  { builder := b, entry := enid, exit := exid }

end BuildResult

def BuildResult.skip : BuildResult :=
  let (b, enid) := CFGBuilder.empty.addNode .skip
  let (b, exid) := b.addNode .exit
  let b := b.addEdge enid exid
  { builder := b, entry := enid, exit := exid }

def Stmt.buildCFG : Stmt -> BuildResult
| .Assign x e => BuildResult.single (.assign x e)
| .Skip => BuildResult.skip
| .Seq s₁ s₂ => BuildResult.seq s₁.buildCFG s₂.buildCFG
| .While c b => BuildResult.whil c b.buildCFG
| .If c t f => BuildResult.ite c t.buildCFG f.buildCFG

def BuildResult.toCFG (b : BuildResult) : CFG :=
  {b.builder.cfg with entry := b.entry, exit := b.exit}
