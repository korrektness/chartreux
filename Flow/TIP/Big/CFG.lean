import Flow.Tip.Regular.CFG
import Flow.Analysis.Lattice
import Mathlib.Tactic.Lemma
import Mathlib.Data.List.Nodup

inductive BigNodeKind where
| SEntry (s : Stmt)
| SExit
| EEntry (e : Expr)
| EExit
deriving DecidableEq, Repr

abbrev BigNodeID := Nat

structure BigCFG where
  nodes : List BigNodeKind
  edges : List Edge
  entry : Nat
  exit : Nat

namespace BigCFG
def nodeKind (g : BigCFG) (n : BigNodeID) : Option BigNodeKind :=
  g.nodes[n]?
def succ (g : BigCFG) (n : BigNodeID) : List BigNodeID :=
  g.edges.filterMap (fun ⟨src, dst, _⟩ => if src = n then dst else none)
def pred (g : BigCFG) (n : BigNodeID) : List BigNodeID :=
  g.edges.filterMap (fun ⟨src, dst, _⟩ => if dst = n then src else none)
def hasEdge (g : BigCFG) (src dst : BigNodeID) (k : EdgeKind) : Prop :=
  ⟨src, dst, k⟩ ∈ g.edges
end BigCFG

structure BigCFGBuilder where
  cfg : BigCFG
  nextID : BigNodeID

namespace BigCFGBuilder
def empty : BigCFGBuilder := {
  cfg := ⟨[], [], 0, 0⟩,
  nextID := 0
}

def addNode (b : BigCFGBuilder) (k : BigNodeKind) : (BigCFGBuilder × BigNodeID) := ({
  cfg := { b.cfg with nodes := b.cfg.nodes ++ [k] }
  nextID := b.nextID + 1
}, b.nextID)

def addEdge (b : BigCFGBuilder) (s d : BigNodeID) (k : EdgeKind) : BigCFGBuilder := {
  b with cfg := { b.cfg with edges := b.cfg.edges ++ [⟨s, d, k⟩] }
}

/-- Well-formedness: `nextID` matches the node list length. -/
def BuilderWF (b : BigCFGBuilder) : Prop :=
  b.nextID = b.cfg.nodes.length

namespace BuilderWF

@[simp] lemma empty : BuilderWF BigCFGBuilder.empty := by simp [BuilderWF, BigCFGBuilder.empty]

lemma addNode {b} (h : BuilderWF b) (k : BigNodeKind) :
    BuilderWF (b.addNode k).fst := by
  simpa [BuilderWF, BigCFGBuilder.addNode] using h

lemma addEdge {b} (h : BuilderWF b) (s d : BigNodeID) (ek : EdgeKind) :
    BuilderWF (b.addEdge s d ek) := by
  simpa [BuilderWF, BigCFGBuilder.addEdge] using h

end BuilderWF
end BigCFGBuilder

namespace BigCFGBuilder

def assignGraph (b : BigCFGBuilder) (x : String) (e : Expr) : BigCFGBuilder :=
  ((((((b.addNode (.SEntry (.Assign x e))).fst.addNode (.EEntry e)).fst.addNode
    .EExit).fst.addNode .SExit).fst.addEdge b.nextID (b.nextID + 1) .Normal).addEdge
    (b.nextID + 1) (b.nextID + 2) .Normal).addEdge (b.nextID + 2) (b.nextID + 3) .Normal

def declGraph (b : BigCFGBuilder) (x : String) (e : Expr) : BigCFGBuilder :=
  ((((((b.addNode (.SEntry (.Decl x e))).fst.addNode (.EEntry e)).fst.addNode
    .EExit).fst.addNode .SExit).fst.addEdge b.nextID (b.nextID + 1) .Normal).addEdge
    (b.nextID + 1) (b.nextID + 2) .Normal).addEdge (b.nextID + 2) (b.nextID + 3) .Normal

def ifPrelude (b : BigCFGBuilder) (c : Expr) (t f : Stmt) : BigCFGBuilder :=
  let b₀ := (((b.addNode (.SEntry (.If c t f))).fst.addNode (.EEntry c)).fst.addNode .EExit).fst
  (b₀.addEdge b.nextID (b.nextID + 1) .Normal).addEdge (b.nextID + 1) (b.nextID + 2) .Normal

def whilePrelude (b : BigCFGBuilder) (c : Expr) (body : Stmt) : BigCFGBuilder :=
  let b₀ := (((b.addNode (.SEntry (.While c body))).fst.addNode (.EEntry c)).fst.addNode .EExit).fst
  (b₀.addEdge b.nextID (b.nextID + 1) .Normal).addEdge (b.nextID + 1) (b.nextID + 2) .Normal

/-- Witness that `⟨b, s⟩ -> b'` for the BigCFG builder -/
inductive BuildSpec : BigCFGBuilder → Stmt → BigCFGBuilder → BigNodeID → BigNodeID → Prop where
| skip (b : BigCFGBuilder) :
    BuildSpec b .Skip (b.addNode (.SEntry .Skip)).fst b.nextID b.nextID
| assign (b : BigCFGBuilder) (x : String) (e : Expr) :
    -- SEntry -> EEntry(e) -> EExit -> SExit
    BuildSpec b (.Assign x e) (assignGraph b x e)
      b.nextID (b.nextID + 3)
| decl (b : BigCFGBuilder) (x : String) (e : Expr) :
    BuildSpec b (.Decl x e) (declGraph b x e)
      b.nextID (b.nextID + 3)
| seq {b b₁ b₂ : BigCFGBuilder} {s₁ s₂ : Stmt} {en₁ ex₁ en₂ ex₂ : BigNodeID} :
    BuildSpec b s₁ b₁ en₁ ex₁ →
    BuildSpec b₁ s₂ b₂ en₂ ex₂ →
    BuildSpec b (.Seq s₁ s₂) (b₂.addEdge ex₁ en₂ .Normal) en₁ ex₂
| if_ {b b₁ b₂ : BigCFGBuilder} {c : Expr} {t f : Stmt} {en_t ex_t en_f ex_f : BigNodeID} :
    BuildSpec (ifPrelude b c t f) t b₁ en_t ex_t →
    BuildSpec b₁ f b₂ en_f ex_f →
    BuildSpec b (.If c t f)
      (let b₃ := (b₂.addNode .SExit).fst
        let nenc := b.nextID + 2
        let nexit := b₂.nextID
        (((b₃.addEdge nenc en_t .TBranch).addEdge nenc en_f .FBranch).addEdge
            ex_t nexit .Normal).addEdge ex_f nexit .Normal)
      b.nextID b₂.nextID
| while_ {b b₁ : BigCFGBuilder} {c : Expr} {body : Stmt} {en_b ex_b : BigNodeID} :
    BuildSpec (whilePrelude b c body) body b₁ en_b ex_b →
    BuildSpec b (.While c body)
      (let b₂ := (b₁.addNode .SExit).fst
        let nenc := b.nextID + 2
        let nex := b₁.nextID
        ((b₂.addEdge nenc en_b .TBranch).addEdge ex_b nenc .Normal).addEdge nenc nex .FBranch)
      b.nextID b₁.nextID

/-! Builder: produce a paired witness for builds -/
def buildGraphSpec (b : BigCFGBuilder) (s : Stmt) :
    Σ' (b' : BigCFGBuilder) (en ex : BigNodeID), BuildSpec b s b' en ex :=
  match s with
  | .Skip => ⟨(b.addNode (.SEntry .Skip)).fst, b.nextID, b.nextID, .skip b⟩
  | .Assign x e =>
    ⟨assignGraph b x e, b.nextID, b.nextID + 3, .assign b x e⟩
  | .Decl x e =>
    ⟨declGraph b x e, b.nextID, b.nextID + 3, .decl b x e⟩
  | .Seq s₁ s₂ =>
    let r₁ := buildGraphSpec b s₁
    let r₂ := buildGraphSpec r₁.1 s₂
    ⟨r₂.1.addEdge r₁.2.2.1 r₂.2.1 .Normal, r₁.2.1, r₂.2.2.1,
      .seq r₁.2.2.2 r₂.2.2.2⟩
  | .If c t f =>
    let b₀ := ifPrelude b c t f
    let r_t := buildGraphSpec b₀ t
    let r_f := buildGraphSpec r_t.1 f
    let b₃  := (r_f.1.addNode .SExit).fst
    let nenc := b.nextID + 2
    let nexit := r_f.1.nextID
    ⟨(((b₃.addEdge nenc r_t.2.1 .TBranch).addEdge nenc r_f.2.1 .FBranch).addEdge
      r_t.2.2.1 nexit .Normal).addEdge r_f.2.2.1 nexit .Normal,
    b.nextID, nexit, .if_ r_t.2.2.2 r_f.2.2.2⟩
  | .While c body =>
    let b₀ := whilePrelude b c body
    let r_b := buildGraphSpec b₀ body
    let b₂ := (r_b.1.addNode .SExit).fst
    let nenc := b.nextID + 2
    let nex := r_b.1.nextID
    ⟨((b₂.addEdge nenc r_b.2.1 .TBranch).addEdge r_b.2.2.1 nenc .Normal).addEdge
        nenc nex .FBranch,
      b.nextID, nex, .while_ r_b.2.2.2⟩

def buildGraphTuple (b : BigCFGBuilder) (s : Stmt) : BigCFGBuilder × (BigNodeID × BigNodeID) :=
  let r := buildGraphSpec b s
  (r.1, (r.2.1, r.2.2.1))

end BigCFGBuilder

/-! High-level convenience -/
/-- Build a BigCFG from a `Stmt` using the empty builder. -/
def BigCFG.ofStmt (s : Stmt) : BigCFG :=
  let r := BigCFGBuilder.empty.buildGraphTuple s
  { r.1.cfg with entry := r.2.1, exit := r.2.2 }
