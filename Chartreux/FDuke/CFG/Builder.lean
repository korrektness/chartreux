import Chartreux.FDuke.CFG.Core

-- # Builder
structure BState where
  cfg : CFG
  nextID : NodeID
  /-- global lambda id, unique for every `call f { s }`. -/
  nextLam : Nat := 0
  /-- Call-site κ-gadgets emitted while constructing `cfg`, in lowering order. -/
  callGadgets : List CallGadget := []
abbrev Builder := StateM BState

namespace Builder
def addNode (k : NodeKind) : Builder NodeID := do
  let s <- get
  set { s with
        cfg   := { s.cfg with nodes := s.cfg.nodes ++ [k] }
        nextID := s.nextID + 1 }
  pure s.nextID
def addEdge (src dst : NodeID) : Builder Unit := do
  modify fun s => { s with
    cfg := { s.cfg with edges := s.cfg.edges ++ [⟨src, dst, .plain⟩] } }
def addEdges (es : List Edge) : Builder Unit := do
  modify fun s => { s with
    cfg := { s.cfg with edges := s.cfg.edges ++ es } }
def addCallNode (f : String) : Builder NodeID := do
  let s <- get
  set { s with
        cfg    := { s.cfg with nodes := s.cfg.nodes ++ [NodeKind.Call f s.nextLam] },
        nextID := s.nextID + 1,
        nextLam := s.nextLam + 1 }
  pure s.nextID
def addCallNodeWithLam (f : String) : Builder (NodeID × Nat) := do
  let s <- get
  set { s with
        cfg    := { s.cfg with nodes := s.cfg.nodes ++ [NodeKind.Call f s.nextLam] },
        nextID := s.nextID + 1,
        nextLam := s.nextLam + 1 }
  pure (s.nextID, s.nextLam)
end Builder

/-- Structural CFG edges induced by an invocation mode. -/
def kappaEdges (κ : InvKind) (en enL exL r : NodeID) : List Edge :=
  match κ with
  | .none    => [⟨en, enL, .plain⟩, ⟨en, r, .plain⟩, ⟨exL, r, .plain⟩,
                 ⟨exL, enL, .plain⟩]
  | .once    => [⟨en, enL, .plain⟩, ⟨exL, r, .plain⟩]
  | .atLeast => [⟨en, enL, .plain⟩, ⟨exL, r, .plain⟩, ⟨exL, enL, .plain⟩]
  | .atMost  => [⟨en, enL, .plain⟩, ⟨exL, r, .plain⟩, ⟨en, r, .plain⟩]

@[simp] theorem kappaEdges_length (κ : InvKind) (en enL exL r : NodeID) :
    (kappaEdges κ en enL exL r).length =
      match κ with
      | .none => 4
      | .once => 2
      | .atLeast | .atMost => 3 := by
  cases κ <;> rfl

def CallGadget.edges (g : CallGadget) : List Edge :=
  kappaEdges g.kappa g.en g.enL g.exL g.ret

@[simp] theorem CallGadget.edges_mk (en : NodeID) (f : String) (lamID : Nat)
    (kappa : InvKind) (enL exL ret : NodeID) (body : Stmt) :
    (CallGadget.mk en f lamID kappa enL exL ret body).edges =
      kappaEdges kappa en enL exL ret := rfl

def CallGadget.standaloneRef (site : CallGadget) : CFGRef := .lam site.lamID

def CallGadget.standaloneStartLam (site : CallGadget) : Nat := site.lamID + 1

def CallGadget.standaloneStmt (site : CallGadget) : Stmt := site.body ;; .Skip

namespace Builder
def addCallGadget (site : CallGadget) : Builder Unit := do
  modify fun s => { s with
    cfg := { s.cfg with edges := s.cfg.edges ++ site.edges },
    callGadgets := s.callGadgets ++ [site] }
end Builder

theorem kappaEdges_en_enL (κ : InvKind) (en enL exL r : NodeID) :
    (⟨en, enL, .plain⟩ : Edge) ∈ kappaEdges κ en enL exL r := by
  cases κ <;> simp [kappaEdges]

theorem kappaEdges_exL_r (κ : InvKind) (en enL exL r : NodeID) :
    (⟨exL, r, .plain⟩ : Edge) ∈ kappaEdges κ en enL exL r := by
  cases κ <;> simp [kappaEdges]

theorem kappaEdges_mem (κ : InvKind) (en enL exL r : NodeID) (e : Edge)
    (he : e ∈ kappaEdges κ en enL exL r) :
    (e.src = en ∨ e.src = exL) ∧ (e.dst = enL ∨ e.dst = r) := by
  cases κ <;>
    simp only [kappaEdges, List.mem_cons, List.not_mem_nil, or_false] at he <;>
    grind

/-- A graph contains the complete κ-gadget for the specified call-site nodes. -/
def CFG.HasKappaGadget (g : CFG) (κ : InvKind) (en enL exL r : NodeID) : Prop :=
  ∀ ⦃e⦄, e ∈ kappaEdges κ en enL exL r → e ∈ g.edges

/-- All construction-time call certificates retained by a builder are present
in its current graph. -/
def BState.CallGadgetsValid (s : BState) : Prop :=
  ∀ site ∈ s.callGadgets,
    s.cfg.HasKappaGadget site.kappa site.en site.enL site.exL site.ret

def callKind (Φ : FunEnv) (f : String) : InvKind :=
  ((Φ.lookup f).map (·.1)).getD .none

open Builder
def lowerStmt (Φ : FunEnv) : Stmt -> Builder (NodeID × NodeID)
| .Skip => do
    let n <- addNode (.Skip)
    pure (n, n)
| .Decl x e | .Assign x e => do
    let n <- addNode (.Assign x e)
    pure (n, n)
| .Seq s₁ s₂ => do
    let (en₁, ex₁) <- lowerStmt Φ s₁
    let (en₂, ex₂) <- lowerStmt Φ s₂
    addEdge ex₁ en₂
    pure (en₁, ex₂)
| .If c t f => do
    let en <- addNode (.Skip) -- could probably be something in relation to c
    let atru <- addNode (.Assume c)
    let afls <- addNode (.Assume (.Not c))
    let (ent, ext) <- lowerStmt Φ t
    let (enf, exf) <- lowerStmt Φ f
    let ex <- addNode (.Skip)
    addEdge en atru; addEdge en afls
    addEdge atru ent; addEdge afls enf
    addEdge ext ex; addEdge exf ex
    pure (en, ex)
| .While c b => do
    let en <- addNode (.Skip) -- could probably be something in relation to c
    let atru <- addNode (.Assume c)
    let afls <- addNode (.Assume (.Not c))
    let (enb, exb) <- lowerStmt Φ b
    addEdge en atru; addEdge en afls
    addEdge atru enb
    addEdge exb en
    pure (en, afls)
| .Invoke => do
    let n <- addNode (.Invoke)
    pure (n, n)
| .Call f lam => do
    let (en, lamID) <- addCallNodeWithLam f
    let (enL, exL) <- lowerStmt Φ lam
    let r <- addNode (.Skip)
    addCallGadget ⟨en, f, lamID, callKind Φ f, enL, exL, r, lam⟩
    pure (en, r)

def Stmt.cfg (Φ : FunEnv) (s : Stmt) : CFG :=
    let (res, st) := (lowerStmt Φ s).run { cfg := ⟨[], [], 0, 0⟩, nextID := 0 }
    { st.cfg with entry := res.1, exit := res.2 }

/-- A CFG together with the construction-time call certificates from its
lowering run. `Stmt.cfg` remains the projection used by existing consumers. -/
structure GeneratedCFG where
  cfg : CFG
  callGadgets : List CallGadget

/-- Build a certificate-bearing CFG for `s`, allocating call-site lambda ids
starting at `startLam`.  This is the generated counterpart of `cfgFrom`. -/
def Stmt.generatedCFGFrom (Φ : FunEnv) (startLam : Nat) (s : Stmt) : GeneratedCFG :=
  let (res, st) := (lowerStmt Φ s).run
    { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam }
  ⟨{ st.cfg with entry := res.1, exit := res.2 }, st.callGadgets⟩

def Stmt.generatedCFG (Φ : FunEnv) (s : Stmt) : GeneratedCFG :=
  s.generatedCFGFrom Φ 0

/-- build cfg for `s` starting from lambda id `startLam`. -/
def Stmt.cfgFrom (Φ : FunEnv) (startLam : Nat) (s : Stmt) : CFG :=
    let (res, st) := (lowerStmt Φ s).run { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam }
    { st.cfg with entry := res.1, exit := res.2 }
