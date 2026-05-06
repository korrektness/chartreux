import Flow.Lang.Defs

inductive NodeKind where
| Assign (x : String) (e : Expr)
| Decl (x : String) (e : Expr)
| Cond (c : Expr)
| Skip
deriving DecidableEq, Repr

abbrev NodeID := Nat

inductive EdgeKind where
| Normal
| TBranch
| FBranch
deriving DecidableEq, Repr

structure Edge where
  src : NodeID
  dst : NodeID
  kind : EdgeKind
deriving DecidableEq, Repr

structure CFG where
  nodes : List NodeKind
  edges : List Edge
  entry : Nat
  exit : Nat

namespace CFG
def nodeKind (g : CFG) (n : NodeID) : Option NodeKind :=
  g.nodes[n]?
def succ (g : CFG) (n : NodeID) : List NodeID :=
  g.edges.filterMap (fun ⟨src, dst, _⟩ => if src = n then dst else none)
def pred (g : CFG) (n : NodeID) : List NodeID :=
  g.edges.filterMap (fun ⟨src, dst, _⟩ => if dst = n then src else none)
def hasEdge (g : CFG) (src dst : NodeID) (k : EdgeKind) : Prop :=
  ⟨src, dst, k⟩ ∈ g.edges
end CFG

-- could the builder carry invariants about the current CFG shape and
-- edges formation, to avoid rebuilding over and over again?
structure CFGBuilder where
  cfg : CFG
  nextID : NodeID

namespace CFGBuilder
def empty : CFGBuilder := {
  cfg := ⟨[], [], 0, 0⟩
  nextID := 0
}

def addNode (b : CFGBuilder) (k : NodeKind) : (CFGBuilder × NodeID) := ({
  cfg := { b.cfg with nodes := b.cfg.nodes ++ [k] }
  nextID := b.nextID + 1
}, b.nextID)

def addEdge (b : CFGBuilder) (s d : NodeID) (k : EdgeKind) : CFGBuilder := {
  b with cfg := { b.cfg with edges := b.cfg.edges ++ [⟨s, d, k⟩] }
}

def buildGraph (b : CFGBuilder) (s : Stmt) : (CFGBuilder × (Nat × Nat)) :=
  match s with
  | .Skip =>
    let (b, n) := b.addNode .Skip
    (b, (n, n))
  | .Decl x e =>
    let (b, n) := b.addNode (.Decl x e)
    (b, (n, n))
  | .Assign x e =>
    let (b, n) := b.addNode (.Assign x e)
    (b, (n, n))
  | .Seq s₁ s₂ =>
    let (b, (nen₁, nex₁)) := b.buildGraph s₁
    let (b, (nen₂, nex₂)) := b.buildGraph s₂
    let b := b.addEdge nex₁ nen₂ .Normal
    (b, (nen₁, nex₂))
  | .While cond body =>
    let (b, nenc) := b.addNode (.Cond cond)
    let (b, (nenb, nexb)) := b.buildGraph body
    let (b, nex) := b.addNode .Skip
    let b := b.addEdge nenc nenb .TBranch
    let b := b.addEdge nexb nenc .Normal
    let b := b.addEdge nenc nex .FBranch
    (b, (nenc, nex))
  | .If c t f =>
    let (b, nenc) := b.addNode (.Cond c)
    let (b, (nent, next)) := b.buildGraph t
    let (b, (nenf, nexf)) := b.buildGraph f
    let (b, nexit) := b.addNode .Skip
    let b := b.addEdge nenc nent .TBranch
    let b := b.addEdge nenc nenf .FBranch
    let b := b.addEdge next nexit .Normal
    let b := b.addEdge nexf nexit .Normal
    (b, (nenc, nexit))
end CFGBuilder
