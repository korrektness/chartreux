import Chartreux.FDuke.CFG.BuilderCorrect

-- temporary
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

/-- collect all occurrences of lambda bodies. -/
def collectLams : Stmt → StateM Nat (List (Nat × Stmt))
  | .Seq s₁ s₂  => do let a ← collectLams s₁; let b ← collectLams s₂; pure (a ++ b)
  | .If _ t f   => do let a ← collectLams t;  let b ← collectLams f;  pure (a ++ b)
  | .While _ b  => collectLams b
  | .Call _ body => do
      let ℓ ← modifyGet (fun n => (n, n + 1))
      let rest ← collectLams body
      pure ((ℓ, body) :: rest)
  | _ => pure []

private theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl
private theorem id_map {α β : Type} (f : α → β) (x : Id α) : f <$> x = f x := rfl
private theorem id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl

-- temporary
set_option linter.flexible false in
/-- `collectLams` allocates consecutive identifiers, starting at its input
counter. -/
theorem collectLams_allocation (s : Stmt) : ∀ start : Nat,
    let out := (collectLams s).run start
    out.2 = start + out.1.length ∧
      out.1.map Prod.fst = List.range' start out.1.length := by
  intro start
  induction s generalizing start <;>
    simp [collectLams, StateT.run_bind, StateT.run_pure, id_bind, id_map, id_pure,
      *, Nat.add_assoc, Nat.add_comm]
  rw [Nat.add_comm 1, List.range'_succ]

/-- The collector advances its counter by exactly the number of lambda bodies
it reports. -/
theorem collectLams_end_eq_start_add_length (s : Stmt) (start : Nat) :
    ((collectLams s).run start).2 = start + ((collectLams s).run start).1.length :=
  (collectLams_allocation s start).1

/-- The lambda identifiers emitted by one collector run are pairwise distinct. -/
theorem collectLams_ids_nodup (s : Stmt) (start : Nat) :
    (((collectLams s).run start).1.map Prod.fst).Nodup := by
  rw [(collectLams_allocation s start).2]
  exact List.nodup_range' 1

/-- Every identifier emitted by a collector run lies in the half-open interval
from the input counter to the resulting counter. -/
theorem collectLams_id_mem_bounds (s : Stmt) (start : Nat) {ℓ : Nat}
    (hℓ : ℓ ∈ ((collectLams s).run start).1.map Prod.fst) :
    start ≤ ℓ ∧ ℓ < ((collectLams s).run start).2 := by
  rw [(collectLams_allocation s start).2] at hℓ
  rw [List.mem_range'_1] at hℓ
  simpa [collectLams_end_eq_start_add_length] using hℓ

/-- Pair membership in collector output exposes the corresponding allocation
interval directly. -/
theorem collectLams_pair_mem_bounds (s : Stmt) (start : Nat) {ℓ : Nat} {body : Stmt}
    (hpair : (ℓ, body) ∈ ((collectLams s).run start).1) :
    start ≤ ℓ ∧ ℓ < ((collectLams s).run start).2 :=
  collectLams_id_mem_bounds s start (List.mem_map_of_mem hpair)

/-- Two collector runs threaded through their counters allocate disjoint,
collectively unique identifier sequences. This is the composition fact needed
when a program family is assembled by a fold. -/
theorem collectLams_threaded_ids_nodup (s₁ s₂ : Stmt) (start : Nat) :
    (((collectLams s₁).run start).1.map Prod.fst ++
      ((collectLams s₂).run ((collectLams s₁).run start).2).1.map Prod.fst).Nodup := by
  rw [(collectLams_allocation s₁ start).2,
    (collectLams_allocation s₂ ((collectLams s₁).run start).2).2,
    collectLams_end_eq_start_add_length]
  rw [show List.range' start ((collectLams s₁).run start).1.length ++
      List.range' (start + ((collectLams s₁).run start).1.length)
        ((collectLams s₂).run
          (start + ((collectLams s₁).run start).1.length)).1.length =
      List.range' start (((collectLams s₁).run start).1.length +
        ((collectLams s₂).run
          (start + ((collectLams s₁).run start).1.length)).1.length) by
        simpa using (List.range'_append (s := start)
          (m := ((collectLams s₁).run start).1.length)
          (n := ((collectLams s₂).run
            (start + ((collectLams s₁).run start).1.length)).1.length) (step := 1))]
  exact List.nodup_range' 1

/-- The identifiers from two threaded collector runs are disjoint. -/
theorem collectLams_threaded_ids_disjoint (s₁ s₂ : Stmt) (start : Nat) :
    (((collectLams s₁).run start).1.map Prod.fst).Disjoint
      (((collectLams s₂).run ((collectLams s₁).run start).2).1.map Prod.fst) :=
  List.disjoint_of_nodup_append (collectLams_threaded_ids_nodup s₁ s₂ start)

/-- Lowering consumes lambda identifiers in precisely the order reported by
`collectLams`.  The statement is append-relative so it also applies while a
component is being built inside a larger lowering run. -/
theorem lowerStmt_callGadgets_collectLams (Φ : FunEnv) (s : Stmt) :
    ∀ b : BState,
      let b' := ((lowerStmt Φ s).run b).2
      b'.nextLam = ((collectLams s).run b.nextLam).2 ∧
      ∀ site ∈ b'.callGadgets, site ∈ b.callGadgets ∨
        (site.lamID, site.body) ∈ ((collectLams s).run b.nextLam).1 := by
  intro b
  induction s generalizing b <;>
    simp [lowerStmt, collectLams, Builder.addNode, Builder.addEdge,
      Builder.addCallNodeWithLam, Builder.addCallGadget, id_bind, id_map, id_pure,
      *, List.append_assoc]
  all_goals grind

/-- Every construction-time call-gadget certificate in a generated CFG is the
lambda occurrence allocated by the matching collector run. -/
theorem Stmt.generatedCFGFrom_callGadget_provenance
    (Φ : FunEnv) (startLam : Nat) (s : Stmt) {site : CallGadget}
    (hsite : site ∈ (s.generatedCFGFrom Φ startLam).callGadgets) :
    (site.lamID, site.body) ∈ ((collectLams s).run startLam).1 := by
  have h := lowerStmt_callGadgets_collectLams Φ s
    { cfg := ⟨[], [], 0, 0⟩, nextID := 0, nextLam := startLam }
  simp only [Stmt.generatedCFGFrom] at hsite
  simpa using (h.2 site hsite).resolve_left (by simp)

/-- Resolve the first retained call gadget whose call node is `n`. -/
def List.lookupCallGadget (sites : List CallGadget) (n : NodeID) : Option CallGadget :=
  sites.find? (·.en = n)

theorem List.lookupCallGadget_mem {sites : List CallGadget} {n : NodeID}
    {site : CallGadget} (hlookup : sites.lookupCallGadget n = some site) :
    site ∈ sites :=
  List.mem_of_find?_eq_some hlookup

@[simp] theorem List.lookupCallGadget_en {sites : List CallGadget} {n : NodeID}
    {site : CallGadget} (hlookup : sites.lookupCallGadget n = some site) :
    site.en = n := by
  have hfound : sites.find? (·.en = n) = some site := by
    simpa [List.lookupCallGadget] using hlookup
  exact of_decide_eq_true (List.find?_some
    (p := fun candidate : CallGadget => candidate.en = n)
    (a := site) (l := sites) hfound)

theorem List.lookupCallGadget_unique {sites : List CallGadget} {n : NodeID}
    {site₁ site₂ : CallGadget} (h₁ : sites.lookupCallGadget n = some site₁)
    (h₂ : sites.lookupCallGadget n = some site₂) : site₁ = site₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- A syntactic call occurrence, named by the same globally fresh lambda id
    that `lowerStmt` puts in its `NodeKind.Call` node.  Keeping the body here
    is important: it identifies the lambda CFG that `Program.family` must
    register, including for calls nested arbitrarily deeply in another lambda. -/
structure CallSite where
  lamID : Nat
  body : Stmt
deriving DecidableEq, Repr

/-- Enumerate all call occurrences in lowering order.  This deliberately uses
    `collectLams`, rather than a second traversal with a subtly different
    counter discipline, so its ids are exactly the ids consumed by lowering. -/
def Stmt.callSites (s : Stmt) : StateM Nat (List CallSite) := fun start =>
  let out := (collectLams s).run start
  (out.1.map fun pair => { lamID := pair.1, body := pair.2 }, out.2)

/-- The call-site trace and lambda collector share both order and allocation.
    This is the bridge from nested lowering provenance to family registration. -/
theorem Stmt.callSites_collectLams (s : Stmt) (start : Nat) :
    ((s.callSites.run start).1.map fun site => (site.lamID, site.body)) =
      ((collectLams s).run start).1 := by
  change List.map (fun site : CallSite => (site.lamID, site.body))
      (((collectLams s).run start).1.map fun pair =>
        { lamID := pair.1, body := pair.2 }) = ((collectLams s).run start).1
  induction ((collectLams s).run start).1 with
  | nil => rfl
  | cons pair rest ih => simp [ih]

-- # Family of CFGs

/-- The common reference-indexed shape shared by ordinary and generated CFG
families. -/
structure CFGFamilyView (Component : Type) where
  funComponents : List (String × InvKind × Component)
  lamComponents : List (Nat × Component) := []
  mainComponent : Component

namespace CFGFamilyView

/-- Resolve a component independently of the information carried by it. -/
def cfgAt? {Component : Type} (fam : CFGFamilyView Component) : CFGRef → Option Component
  | .main  => some fam.mainComponent
  | .fn f  => (fam.funComponents.find? (·.1 = f)).map (·.2.2)
  | .lam ℓ => (fam.lamComponents.find? (·.1 = ℓ)).map (·.2)

/-- Map every component while retaining family references and invocation kinds. -/
def map {α β : Type} (f : α → β) (fam : CFGFamilyView α) : CFGFamilyView β :=
  { funComponents := fam.funComponents.map fun (name, κ, component) =>
      (name, κ, f component)
    lamComponents := fam.lamComponents.map fun (lamID, component) =>
      (lamID, f component)
    mainComponent := f fam.mainComponent }

end CFGFamilyView

/-- Runtime-relevant information retained after certification proofs are erased. -/
structure ErasedCFGComponent where
  wfcfg : WFCFG
  callGadgets : List CallGadget

/-- lists of CFGs for functions & lambdas + single CFG for main -/
structure CFGFamily where
  funCFGs : List (String × InvKind × WFCFG)
  lamCFGs : List (Nat × WFCFG) := []
  mainCFG : WFCFG
  funCallGadgets : List (String × InvKind × List CallGadget) := []
  lamCallGadgets : List (Nat × List CallGadget) := []
  mainCallGadgets : List CallGadget := []

/-- Project a metadata-bearing component view to the compatibility family
representation. -/
def CFGFamily.ofErasedView (fam : CFGFamilyView ErasedCFGComponent) : CFGFamily :=
  { funCFGs := fam.funComponents.map fun (f, κ, component) => (f, κ, component.wfcfg)
    lamCFGs := fam.lamComponents.map fun (ℓ, component) => (ℓ, component.wfcfg)
    mainCFG := fam.mainComponent.wfcfg
    funCallGadgets := fam.funComponents.map fun (f, κ, component) =>
      (f, κ, component.callGadgets)
    lamCallGadgets := fam.lamComponents.map fun (ℓ, component) =>
      (ℓ, component.callGadgets)
    mainCallGadgets := fam.mainComponent.callGadgets }

private def familyStep (p : Program) := fun
    (acc : List (String × InvKind × WFCFG) × List (Nat × Stmt) × Nat)
    (fb : String × InvKind × Stmt) =>
  let (funs, lams, c) := acc
  let (f, κ, body) := fb
  let wrapped := Stmt.Seq body Stmt.Skip
  let (bl, c') := (collectLams wrapped).run c
  (funs ++ [(f, κ, wrapped.wfcfgFrom p.phi c)], lams ++ bl, c')

private def familyMetadataStep (p : Program) := fun
    (acc : List (String × InvKind × List CallGadget) × List (Nat × Stmt) × Nat)
    (fb : String × InvKind × Stmt) =>
  let (funs, lams, c) := acc
  let (f, κ, body) := fb
  let wrapped := Stmt.Seq body Stmt.Skip
  let (bl, c') := (collectLams wrapped).run c
  (funs ++ [(f, κ, (wrapped.generatedCFGFrom p.phi c).callGadgets)], lams ++ bl, c')

/-- Lower a `Program` into its family of well-formed CFGs: every `(f, κ, body)`
    binding in `Φ` becomes `(f, κ, (body ;; skip).wfcfg Φ)`, and `p.main`
    becomes `mainCFG`. -/
def Program.family (p : Program) : CFGFamily :=
  let (mainLams, c₁) := (collectLams p.main).run 0
  let (funCFGs, funLams, _) := p.phi.foldl (familyStep p) ([], [], c₁)
  let (funCallGadgets, _, _) := p.phi.foldl (familyMetadataStep p) ([], [], c₁)
  { funCFGs := funCFGs
    mainCFG := p.main.wfcfg p.phi
    lamCFGs := (mainLams ++ funLams).map (fun (ℓ, body) =>
      (ℓ, (body ;; Stmt.Skip).wfcfgFrom p.phi (ℓ + 1)))
    funCallGadgets := funCallGadgets
    mainCallGadgets := (p.main.generatedCFG p.phi).callGadgets
    lamCallGadgets := (mainLams ++ funLams).map (fun (ℓ, body) =>
      (ℓ, ((body ;; Stmt.Skip).generatedCFGFrom p.phi (ℓ + 1)).callGadgets)) }

/-- The certificate-bearing companion to `CFGFamily`. Every component retains
its generated graph and certified call-site metadata. -/
structure GeneratedCFGFamily where
  funCFGs : List (String × InvKind × CertifiedGeneratedCFG)
  lamCFGs : List (Nat × CertifiedGeneratedCFG) := []
  mainCFG : CertifiedGeneratedCFG

def CertifiedGeneratedCFG.wfcfg (component : CertifiedGeneratedCFG) : WFCFG :=
  ⟨component.generated.cfg, component.wellFormed⟩

def GeneratedCFGFamily.view (fam : GeneratedCFGFamily) :
    CFGFamilyView CertifiedGeneratedCFG :=
  { funComponents := fam.funCFGs
    lamComponents := fam.lamCFGs
    mainComponent := fam.mainCFG }

@[simp] theorem Stmt.certifiedGeneratedCFGFrom_wfcfg
    (Φ : FunEnv) (startLam : Nat) (s : Stmt) :
    (s.certifiedGeneratedCFGFrom Φ startLam).wfcfg = s.wfcfgFrom Φ startLam := rfl

@[simp] theorem Stmt.certifiedGeneratedCFG_wfcfg (Φ : FunEnv) (s : Stmt) :
    (s.certifiedGeneratedCFG Φ).wfcfg = s.wfcfg Φ := rfl

/-- Canonical proof-erased, metadata-bearing view of a generated family. -/
def GeneratedCFGFamily.erasedView (fam : GeneratedCFGFamily) :
    CFGFamilyView ErasedCFGComponent :=
  fam.view.map fun component =>
    { wfcfg := component.wfcfg, callGadgets := component.generated.callGadgets }

/-- Forget construction-time certificates, recovering the pre-existing family
shape for clients that only consume well-formed CFGs. -/
def GeneratedCFGFamily.erase (fam : GeneratedCFGFamily) : CFGFamily :=
  CFGFamily.ofErasedView fam.erasedView

@[simp] theorem GeneratedCFGFamily.erase_funCFGs (fam : GeneratedCFGFamily) :
    fam.erase.funCFGs = fam.funCFGs.map fun (f, κ, component) => (f, κ, component.wfcfg) :=
  by simp [GeneratedCFGFamily.erase, CFGFamily.ofErasedView,
    GeneratedCFGFamily.erasedView, GeneratedCFGFamily.view, CFGFamilyView.map]

@[simp] theorem GeneratedCFGFamily.erase_lamCFGs (fam : GeneratedCFGFamily) :
    fam.erase.lamCFGs = fam.lamCFGs.map fun (ℓ, component) => (ℓ, component.wfcfg) :=
  by simp [GeneratedCFGFamily.erase, CFGFamily.ofErasedView,
    GeneratedCFGFamily.erasedView, GeneratedCFGFamily.view, CFGFamilyView.map]

@[simp] theorem GeneratedCFGFamily.erase_mainCFG (fam : GeneratedCFGFamily) :
    fam.erase.mainCFG = fam.mainCFG.wfcfg := by
  simp [GeneratedCFGFamily.erase, CFGFamily.ofErasedView,
    GeneratedCFGFamily.erasedView, GeneratedCFGFamily.view, CFGFamilyView.map]

private def generatedFamilyStep (p : Program) := fun
    (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat)
    (fb : String × InvKind × Stmt) =>
  let (funs, lams, c) := acc
  let (f, κ, body) := fb
  let wrapped := Stmt.Seq body Stmt.Skip
  let (bl, c') := (collectLams wrapped).run c
  (funs ++ [(f, κ, wrapped.certifiedGeneratedCFGFrom p.phi c)], lams ++ bl, c')

/-- Lower every program component to a certificate-bearing CFG. The allocation
and component order intentionally mirror `Program.family`, including the
lambda-id offsets used for functions and registered lambda bodies. -/
def Program.generatedFamily (p : Program) : GeneratedCFGFamily :=
  let (mainLams, c₁) := (collectLams p.main).run 0
  let (funCFGs, funLams, _) := p.phi.foldl (generatedFamilyStep p) ([], [], c₁)
  { funCFGs := funCFGs
    mainCFG := p.main.certifiedGeneratedCFG p.phi
    lamCFGs := (mainLams ++ funLams).map (fun (ℓ, body) =>
      (ℓ, (body ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (ℓ + 1))) }

/-- Every function component accumulated by `generatedFamilyStep` is the
canonical certified lowering of its recorded source, environment, and lambda
counter. -/
private theorem generatedFamilyFold_components_canonical (p : Program) :
    ∀ (xs : FunEnv)
      (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat),
      (∀ entry ∈ acc.1,
        entry.2.2 = entry.2.2.source.certifiedGeneratedCFGFrom
          p.phi entry.2.2.startLam) →
      ∀ entry ∈ (xs.foldl (generatedFamilyStep p) acc).1,
        entry.2.2 = entry.2.2.source.certifiedGeneratedCFGFrom
          p.phi entry.2.2.startLam := by
  intro xs
  induction xs with
  | nil =>
      intro acc hacc entry hentry
      exact hacc entry hentry
  | cons hd tl ih =>
      intro acc hacc
      simp only [List.foldl]
      apply ih
      intro entry hentry
      unfold generatedFamilyStep at hentry
      generalize hrun :
        (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out at hentry
      rcases out with ⟨lams, next⟩
      simp only [hrun, List.mem_append, List.mem_singleton] at hentry
      rcases hentry with hold | hnew
      · exact hacc entry hold
      · rcases hnew with rfl
        rfl

/-- Collecting a call body recursively accounts for all calls nested in that
body.  This closure property lets a generated lambda component inherit the
registration of any call gadget it contains. -/
private theorem collectLams_nested_mem (s : Stmt) : ∀ {start ℓ body ℓ' body'},
    (ℓ, body) ∈ ((collectLams s).run start).1 →
    (ℓ', body') ∈ ((collectLams body).run (ℓ + 1)).1 →
    (ℓ', body') ∈ ((collectLams s).run start).1 := by
  intro start ℓ body ℓ' body' houter hinner
  induction s generalizing start ℓ body ℓ' body' <;>
    simp [collectLams, StateT.run_bind, StateT.run_pure, id_bind, id_map, id_pure] at *
  all_goals grind

private theorem find?_eq_some_of_mem_nodup
    (xs : List (Nat × CertifiedGeneratedCFG)) (ℓ : Nat) (component : CertifiedGeneratedCFG)
    (hnodup : (xs.map Prod.fst).Nodup) (hmem : (ℓ, component) ∈ xs) :
    xs.find? (·.1 = ℓ) = some (ℓ, component) := by
  induction xs with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨headℓ, headComponent⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.mem_cons] at hmem
    by_cases hhead : headℓ = ℓ
    · subst headℓ
      have hcomponent : headComponent = component := by
        rcases hmem with hmem | hmem
        · exact (Prod.mk.inj hmem).2.symm
        · exact False.elim (hnodup.1 (List.mem_map_of_mem hmem))
      subst headComponent
      simp
    · simp only [hhead, decide_false, Bool.false_eq_true, not_false_eq_true,
      List.find?_cons_of_neg]
      rcases hmem with hmem | hmem
      · exact False.elim (hhead (Prod.mk.inj hmem).1.symm)
      · exact ih hnodup.2 hmem

private theorem generatedFamilyFold_lam_ids (p : Program) :
    ∀ (xs : FunEnv)
      (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat),
      ∀ start, acc.2.1.map Prod.fst = List.range' start acc.2.1.length →
        acc.2.2 = start + acc.2.1.length →
      ((xs.foldl (generatedFamilyStep p) acc).2.1).map Prod.fst =
        List.range' start ((xs.foldl (generatedFamilyStep p) acc).2.1).length := by
  intro xs
  induction xs with
  | nil => intro acc start hacc _; exact hacc
  | cons hd tl ih =>
    intro acc start hacc hcounter
    simp only [List.foldl]
    generalize hrun : (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out
    rcases out with ⟨bl, c'⟩
    have halloc := collectLams_allocation (hd.2.2 ;; Stmt.Skip) acc.2.2
    rw [hrun] at halloc
    simp only at halloc
    apply ih
    · simp only [generatedFamilyStep, hrun, List.map_append]
      rw [hacc, halloc.2, hcounter]
      simp only [List.length_append]
      simpa using (List.range'_append (s := start) (m := acc.2.1.length)
      (n := bl.length) (step := 1))
    · simp only [generatedFamilyStep, hrun]
      simp only [List.length_append]
      rw [halloc.1, hcounter]
      change start + acc.2.1.length + bl.length = start + (acc.2.1.length + bl.length)
      omega

/-- Function-family collection allocates consecutive lambda identifiers from
the counter inherited from the main component. -/
private theorem generatedFamilyFold_new_lam_ids (p : Program) :
    ∀ (xs : FunEnv) (start : Nat),
      ((xs.foldl (generatedFamilyStep p) ([], [], start)).2.1).map Prod.fst =
        List.range' start ((xs.foldl (generatedFamilyStep p) ([], [], start)).2.1).length := by
  intro xs start
  apply generatedFamilyFold_lam_ids p xs ([], [], start) start <;> rfl

private theorem generatedFamilyFold_gadget_mem (p : Program) :
    ∀ (xs : FunEnv)
      (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat),
      (∀ f κ source, (f, κ, source) ∈ acc.1 → ∀ site ∈ source.generated.callGadgets,
        (site.lamID, site.body) ∈ acc.2.1) →
      ∀ f κ source, (f, κ, source) ∈ (xs.foldl (generatedFamilyStep p) acc).1 →
        ∀ site ∈ source.generated.callGadgets,
          (site.lamID, site.body) ∈ (xs.foldl (generatedFamilyStep p) acc).2.1 := by
  intro xs
  induction xs with
  | nil =>
    intro acc hacc f κ source hsource site hsite
    exact hacc f κ source hsource site hsite
  | cons hd tl ih =>
    intro acc hacc f κ source hsource site hsite
    simp only [List.foldl] at hsource ⊢
    generalize hrun : (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out
    rcases out with ⟨bl, c'⟩
    apply ih
    · intro f κ source hsource site hsite
      simp only [generatedFamilyStep, hrun, List.mem_append, List.mem_cons] at hsource ⊢
      rcases hsource with hsource | hsource
      · exact Or.inl (hacc f κ source hsource site hsite)
      · rcases hsource with hsource | hsource
        · rcases hsource with ⟨rfl, rfl, rfl⟩
          exact Or.inr (by
            simpa [hrun] using
              (Stmt.generatedCFGFrom_callGadget_provenance p.phi acc.2.2
                (hd.2.2 ;; Stmt.Skip) hsite))
        · simp at hsource
    · exact hsource
    · exact hsite

private theorem generatedFamilyFold_lam_nested_mem (p : Program) :
    ∀ (xs : FunEnv)
      (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat),
      (∀ ℓ body, (ℓ, body) ∈ acc.2.1 → ∀ ℓ' body',
        (ℓ', body') ∈ ((collectLams body).run (ℓ + 1)).1 → (ℓ', body') ∈ acc.2.1) →
      ∀ ℓ body, (ℓ, body) ∈ (xs.foldl (generatedFamilyStep p) acc).2.1 → ∀ ℓ' body',
        (ℓ', body') ∈ ((collectLams body).run (ℓ + 1)).1 →
          (ℓ', body') ∈ (xs.foldl (generatedFamilyStep p) acc).2.1 := by
  intro xs
  induction xs with
  | nil => grind
  | cons hd tl ih =>
    intro acc hacc ℓ body houter ℓ' body' hinner
    simp only [List.foldl] at houter ⊢
    generalize hrun : (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out
    rcases out with ⟨bl, c'⟩
    apply ih
    · intro ℓ body houter ℓ' body' hinner
      simp only [generatedFamilyStep, hrun, List.mem_append] at houter ⊢
      rcases houter with houter | houter
      · exact Or.inl (hacc ℓ body houter ℓ' body' hinner)
      · exact Or.inr (by
          have houter' : (ℓ, body) ∈
              ((collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2).1 := by
            simpa only [hrun] using houter
          simpa [hrun] using
            (collectLams_nested_mem (hd.2.2 ;; Stmt.Skip) (start := acc.2.2)
              houter' hinner))
    · exact houter
    · exact hinner

namespace GeneratedCFGFamily

/-- Resolve a certificate-bearing component using the same reference scheme as
the ordinary `CFGFamily` resolver. -/
def cfgAt? (fam : GeneratedCFGFamily) (ref : CFGRef) : Option CertifiedGeneratedCFG :=
  fam.view.cfgAt? ref

/-- Resolve retained metadata for the call at node `n` in component `ref`. -/
def gadgetAt? (fam : GeneratedCFGFamily) (ref : CFGRef) (n : NodeID) :
    Option CallGadget :=
  (fam.cfgAt? ref).bind fun component =>
    component.generated.callGadgets.lookupCallGadget n

theorem gadgetAt?_resolved {fam : GeneratedCFGFamily} {ref : CFGRef} {n : NodeID}
    {site : CallGadget} (hlookup : fam.gadgetAt? ref n = some site) :
    ∃ component, fam.cfgAt? ref = some component ∧
      site ∈ component.generated.callGadgets ∧ site.en = n := by
  obtain ⟨component, hcomponent, hsite⟩ := Option.bind_eq_some_iff.mp hlookup
  exact ⟨component, hcomponent, List.lookupCallGadget_mem hsite,
    List.lookupCallGadget_en hsite⟩

theorem gadgetAt?_unique {fam : GeneratedCFGFamily} {ref : CFGRef} {n : NodeID}
    {site₁ site₂ : CallGadget} (h₁ : fam.gadgetAt? ref n = some site₁)
    (h₂ : fam.gadgetAt? ref n = some site₂) : site₁ = site₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

@[simp] theorem cfgAt_main (fam : GeneratedCFGFamily) :
    fam.cfgAt? .main = some fam.mainCFG := rfl

/-- A component resolved from a generated program family is exactly the
canonical certified lowering recorded by its `source` and `startLam` fields. -/
theorem Program.generatedFamily_component_canonical (p : Program) {ref : CFGRef}
    {component : CertifiedGeneratedCFG}
    (hresolve : p.generatedFamily.cfgAt? ref = some component) :
    component = component.source.certifiedGeneratedCFGFrom p.phi component.startLam := by
  cases ref <;> simp only [cfgAt?, GeneratedCFGFamily.view,
    CFGFamilyView.cfgAt?] at hresolve
  · cases hresolve;
    rfl;
  · contrapose! hresolve; simp_all +decide only [ne_eq, Option.map_eq_some_iff,
    Prod.exists, exists_eq_right, not_exists] ;
    intro f κ hfind
    have := List.mem_of_find?_eq_some hfind
    simp_all +decide only [Program.generatedFamily, List.map_append]
    exact hresolve <| by simpa using
      generatedFamilyFold_components_canonical p p.phi ([], [], (collectLams p.main).run 0 |>.2) (by simp) _ this;
  · obtain ⟨entry, hfind, hentry⟩ := Option.map_eq_some_iff.mp hresolve
    rcases entry with ⟨w, foundComponent⟩
    simp only at hentry
    subst foundComponent
    have hmem := List.mem_of_find?_eq_some hfind
    simp only [Program.generatedFamily] at hmem
    change (w, component) ∈ List.map _ _ at hmem
    obtain ⟨pair, _, heq⟩ := List.mem_map.mp hmem
    injection heq with _ hcomponent
    rw [← hcomponent]
    unfold Stmt.certifiedGeneratedCFGFrom
    rfl

/-- A resolved component exposes the complete κ-gadget for every recorded
certificate. -/
theorem cfgAt_gadget_present (fam : GeneratedCFGFamily) {ref : CFGRef}
    {component : CertifiedGeneratedCFG} (_hresolve : fam.cfgAt? ref = some component)
    {site : CallGadget} (hsite : site ∈ component.generated.callGadgets) :
    component.generated.cfg.HasKappaGadget
      site.kappa site.en site.enL site.exL site.ret :=
  component.gadget_present hsite

end GeneratedCFGFamily

/-- Certificate-bearing lowering output for the program's main component.
This is the provenance interface paired with `p.family.mainCFG`; the latter
remains unchanged for existing CFG-family consumers. -/
def Program.generatedMainCFG (p : Program) : GeneratedCFG :=
  p.main.generatedCFG p.phi

namespace CFGFamily

/-- View the compatibility-oriented `WFCFG` fields through the common family
representation. -/
def view (fam : CFGFamily) : CFGFamilyView WFCFG :=
  { funComponents := fam.funCFGs
    lamComponents := fam.lamCFGs
    mainComponent := fam.mainCFG }

/-- View retained call-gadget metadata through the common family
representation. -/
def callGadgetsView (fam : CFGFamily) : CFGFamilyView (List CallGadget) :=
  { funComponents := fam.funCallGadgets
    lamComponents := fam.lamCallGadgets
    mainComponent := fam.mainCallGadgets }

/-- Resolve a CFG reference through the family, if it is registered. -/
def cfgAt? (fam : CFGFamily) (ref : CFGRef) : Option WFCFG :=
  fam.view.cfgAt? ref

/-- Resolve retained metadata for the call at node `n` in component `ref`. -/
def gadgetAt? (fam : CFGFamily) (ref : CFGRef) (n : NodeID) : Option CallGadget :=
  (fam.callGadgetsView.cfgAt? ref).bind fun sites => sites.lookupCallGadget n

theorem gadgetAt?_resolved {fam : CFGFamily} {ref : CFGRef} {n : NodeID}
    {site : CallGadget} (hlookup : fam.gadgetAt? ref n = some site) :
    ∃ sites, fam.callGadgetsView.cfgAt? ref = some sites ∧
      site ∈ sites ∧ site.en = n := by
  obtain ⟨sites, hsites, hsite⟩ := Option.bind_eq_some_iff.mp hlookup
  exact ⟨sites, hsites, List.lookupCallGadget_mem hsite,
    List.lookupCallGadget_en hsite⟩

theorem gadgetAt?_unique {fam : CFGFamily} {ref : CFGRef} {n : NodeID}
    {site₁ site₂ : CallGadget} (h₁ : fam.gadgetAt? ref n = some site₁)
    (h₂ : fam.gadgetAt? ref n = some site₂) : site₁ = site₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- Resolve the canonical erased component used by execution-facing clients.
The `WFCFG` result remains available through `cfgAt?`; this lookup additionally
retains construction-time call-gadget metadata. -/
def componentAt? (fam : CFGFamily) (ref : CFGRef) : Option ErasedCFGComponent :=
  (fam.cfgAt? ref).map fun cfg =>
    { wfcfg := cfg
      callGadgets := (fam.callGadgetsView.cfgAt? ref).getD [] }

/-- The distinguished main CFG is always resolvable through a family. -/
@[simp] theorem cfgAt_main (fam : CFGFamily) :
    fam.cfgAt? .main = some fam.mainCFG := rfl

/-- A function entry in a family makes the corresponding function reference resolvable. -/
theorem fn_registered_of_mem (fam : CFGFamily) {f : String} {κ : InvKind} {cfg : WFCFG}
    (hmem : (f, κ, cfg) ∈ fam.funCFGs) :
    ∃ cfg, fam.cfgAt? (.fn f) = some cfg := by
  let found := fam.funCFGs.find? (·.1 = f)
  have hfound : found ≠ none := by
    intro hnone
    have hnone' : fam.funCFGs.find? (·.1 = f) = none := by
      simpa [found] using hnone
    rw [List.find?_eq_none] at hnone'
    exact hnone' _ hmem (by simp)
  rcases hopt : found with _ | entry
  · exact False.elim (hfound hopt)
  · exact ⟨entry.2.2, by
      simp [cfgAt?, view, CFGFamilyView.cfgAt?, found, hopt]⟩

/-- A lambda entry in a family makes the corresponding lambda reference resolvable. -/
theorem lam_registered_of_mem (fam : CFGFamily) {ℓ : Nat} {cfg : WFCFG}
    (hmem : (ℓ, cfg) ∈ fam.lamCFGs) :
    ∃ cfg, fam.cfgAt? (.lam ℓ) = some cfg := by
  let found := fam.lamCFGs.find? (·.1 = ℓ)
  have hfound : found ≠ none := by
    intro hnone
    have hnone' : fam.lamCFGs.find? (·.1 = ℓ) = none := by
      simpa [found] using hnone
    rw [List.find?_eq_none] at hnone'
    exact hnone' _ hmem (by simp)
  rcases hopt : found with _ | entry
  · exact False.elim (hfound hopt)
  · exact ⟨entry.2, by
      simp [cfgAt?, view, CFGFamilyView.cfgAt?, found, hopt]⟩

end CFGFamily

private theorem find?_erase_funCFGs
    (xs : List (String × InvKind × CertifiedGeneratedCFG)) (f : String) :
    (xs.map fun (name, κ, component) => (name, κ, component.wfcfg)).find? (·.1 = f) =
      (xs.find? (·.1 = f)).map fun (name, κ, component) => (name, κ, component.wfcfg) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.find?_cons]
    split <;> simp [*]

private theorem find?_erase_lamCFGs
    (xs : List (Nat × CertifiedGeneratedCFG)) (ℓ : Nat) :
    (xs.map fun (lamID, component) => (lamID, component.wfcfg)).find? (·.1 = ℓ) =
      (xs.find? (·.1 = ℓ)).map fun (lamID, component) => (lamID, component.wfcfg) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.find?_cons]
    split <;> simp [*]

/-- Resolving a certificate-erased family is equivalent to resolving its
certificate-bearing source and then forgetting the certificate. -/
theorem GeneratedCFGFamily.erase_cfgAt? (fam : GeneratedCFGFamily) (ref : CFGRef) :
    fam.erase.cfgAt? ref = (fam.cfgAt? ref).map CertifiedGeneratedCFG.wfcfg := by
  cases ref <;>
    simp [GeneratedCFGFamily.erase, CFGFamily.cfgAt?, CFGFamily.view,
      CFGFamilyView.cfgAt?, GeneratedCFGFamily.cfgAt?, GeneratedCFGFamily.view,
      CFGFamily.ofErasedView, GeneratedCFGFamily.erasedView, CFGFamilyView.map,
      Function.comp_def]

/-- Erasing certificates preserves call-node gadget lookup exactly. -/
theorem GeneratedCFGFamily.erase_gadgetAt? (fam : GeneratedCFGFamily)
    (ref : CFGRef) (n : NodeID) :
    fam.erase.gadgetAt? ref n = fam.gadgetAt? ref n := by
  cases ref with
  | main => rfl
  | fn f =>
    simp only [CFGFamily.gadgetAt?, CFGFamily.callGadgetsView,
      GeneratedCFGFamily.gadgetAt?, GeneratedCFGFamily.cfgAt?,
      GeneratedCFGFamily.view, GeneratedCFGFamily.erase,
      GeneratedCFGFamily.erasedView, CFGFamily.ofErasedView,
      CFGFamilyView.cfgAt?, CFGFamilyView.map]
    generalize fam.funCFGs = xs
    induction xs with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, List.find?_cons]
      cases h : decide (hd.1 = f)
      · cases htail : tl.find? (·.1 = f) <;>
          simp [htail, Function.comp_def]
      · simp
  | lam ℓ =>
    simp only [CFGFamily.gadgetAt?, CFGFamily.callGadgetsView,
      GeneratedCFGFamily.gadgetAt?, GeneratedCFGFamily.cfgAt?,
      GeneratedCFGFamily.view, GeneratedCFGFamily.erase,
      GeneratedCFGFamily.erasedView, CFGFamily.ofErasedView,
      CFGFamilyView.cfgAt?, CFGFamilyView.map]
    generalize fam.lamCFGs = xs
    induction xs with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, List.find?_cons]
      cases h : decide (hd.1 = ℓ)
      · cases htail : tl.find? (·.1 = ℓ) <;>
          simp [htail, Function.comp_def]
      · simp

private def eraseFamilyAcc
    (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat) :
    List (String × InvKind × WFCFG) × List (Nat × Stmt) × Nat :=
  (acc.1.map fun (f, κ, component) => (f, κ, component.wfcfg), acc.2)

private def eraseFamilyMetadataAcc
    (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat) :
    List (String × InvKind × List CallGadget) × List (Nat × Stmt) × Nat :=
  (acc.1.map fun (f, κ, component) => (f, κ, component.generated.callGadgets), acc.2)

private theorem generatedFamilyFold_erase (p : Program) :
    ∀ (xs : FunEnv)
      (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat),
      eraseFamilyAcc (xs.foldl (generatedFamilyStep p) acc) =
        xs.foldl (familyStep p) (eraseFamilyAcc acc) := by
  intro xs
  induction xs with
  | nil => intro acc; rfl
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl]
    rw [ih]
    generalize hrun : (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out
    rcases out with ⟨bl, c'⟩
    simp [hrun, generatedFamilyStep, familyStep, eraseFamilyAcc]

private theorem generatedFamilyFold_erase_metadata (p : Program) :
    ∀ (xs : FunEnv)
      (acc : List (String × InvKind × CertifiedGeneratedCFG) × List (Nat × Stmt) × Nat),
      eraseFamilyMetadataAcc (xs.foldl (generatedFamilyStep p) acc) =
        xs.foldl (familyMetadataStep p) (eraseFamilyMetadataAcc acc) := by
  intro xs
  induction xs with
  | nil => intro acc; rfl
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl]
    rw [ih]
    generalize hrun : (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out
    rcases out with ⟨bl, c'⟩
    simp [hrun, generatedFamilyStep, familyMetadataStep, eraseFamilyMetadataAcc,
      Stmt.certifiedGeneratedCFGFrom]

/-- Forgetting construction-time certificates from a generated family recovers
exactly the existing program CFG family. -/
theorem Program.generatedFamily_erase (p : Program) :
    p.generatedFamily.erase = p.family := by
  unfold Program.generatedFamily Program.family GeneratedCFGFamily.erase CFGFamily.ofErasedView
  generalize hmain : (collectLams p.main).run 0 = mainResult
  rcases mainResult with ⟨mainLams, c₁⟩
  simp only
  generalize hgen : p.phi.foldl (generatedFamilyStep p) ([], [], c₁) = generatedResult
  rcases generatedResult with ⟨funCFGs, funLams, c⟩
  have hfold := generatedFamilyFold_erase p p.phi ([], [], c₁)
  have hmetadata := generatedFamilyFold_erase_metadata p p.phi ([], [], c₁)
  rw [hgen] at hfold
  rw [hgen] at hmetadata
  simp only [eraseFamilyAcc, List.map_nil] at hfold
  simp only [eraseFamilyMetadataAcc, List.map_nil] at hmetadata
  rw [← hfold]
  rw [← hmetadata]
  have hlam :
      (fun x : Nat × CertifiedGeneratedCFG => (x.1, x.2.wfcfg)) ∘
          (fun x : Nat × Stmt =>
            (x.1, (x.2 ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (x.1 + 1))) =
        (fun x : Nat × Stmt =>
          (x.1, (x.2 ;; Stmt.Skip).wfcfgFrom p.phi (x.1 + 1))) := by
    funext x
    rcases x with ⟨ℓ, body⟩
    simp
  have hlamMetadata :
      (fun x : Nat × CertifiedGeneratedCFG =>
          (x.1, x.2.generated.callGadgets)) ∘
          (fun x : Nat × Stmt =>
            (x.1, (x.2 ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (x.1 + 1))) =
        (fun x : Nat × Stmt =>
          (x.1, ((x.2 ;; Stmt.Skip).generatedCFGFrom p.phi (x.1 + 1)).callGadgets)) := by
    funext x
    rcases x with ⟨ℓ, body⟩
    rfl
  simp [GeneratedCFGFamily.erasedView, GeneratedCFGFamily.view, CFGFamilyView.map,
    Function.comp_def, Stmt.certifiedGeneratedCFG_wfcfg,
    Stmt.certifiedGeneratedCFGFrom]
  constructor
  · congr 1
  · rfl

/-- Existing family-resolution hypotheses can be lifted to the corresponding
certificate-bearing generated component. -/
theorem Program.family_cfgAt?_iff_generatedFamily (p : Program) (ref : CFGRef) (cfg : WFCFG) :
    p.family.cfgAt? ref = some cfg ↔
      ∃ component, p.generatedFamily.cfgAt? ref = some component ∧ component.wfcfg = cfg := by
  rw [← p.generatedFamily_erase, GeneratedCFGFamily.erase_cfgAt?]
  constructor
  · intro h
    cases hresolve : p.generatedFamily.cfgAt? ref with
    | none => simp [hresolve] at h
    | some component =>
      refine ⟨component, rfl, ?_⟩
      simpa [hresolve] using h
  · rintro ⟨component, hresolve, hcomponent⟩
    simp [hresolve, hcomponent]

/-- Every call gadget of a resolved generated component has its standalone
lambda component registered at exactly the identifier assigned during lowering.
This includes gadgets in the main component, function components, and lambda
components nested at arbitrary depth. -/
theorem Program.generatedFamily_gadget_standalone (p : Program) {ref : CFGRef}
    {source : CertifiedGeneratedCFG}
    (hresolve : p.generatedFamily.cfgAt? ref = some source)
    {site : CallGadget} (hsite : site ∈ source.generated.callGadgets) :
    p.generatedFamily.cfgAt? (.lam site.lamID) =
      some ((site.body ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (site.lamID + 1)) := by
  unfold Program.generatedFamily at hresolve ⊢
  generalize hmain : (collectLams p.main).run 0 = mainResult
  rcases mainResult with ⟨mainLams, c₁⟩
  generalize hfold : p.phi.foldl (generatedFamilyStep p) ([], [], c₁) = foldResult
  rcases foldResult with ⟨funCFGs, funLams, c₂⟩
  have hmainAlloc := collectLams_allocation p.main 0
  rw [hmain] at hmainAlloc
  simp only at hmainAlloc
  have hfunIds := generatedFamilyFold_new_lam_ids p p.phi c₁
  rw [hfold] at hfunIds
  simp only at hfunIds
  have hnodup : ((mainLams ++ funLams).map Prod.fst).Nodup := by
    rw [List.map_append, hmainAlloc.2, hfunIds, hmainAlloc.1]
    have happend : List.range' 0 mainLams.length ++
        List.range' (0 + mainLams.length) funLams.length =
        List.range' 0 (mainLams.length + funLams.length) := by
      simpa using (List.range'_append (s := 0) (m := mainLams.length)
        (n := funLams.length) (step := 1))
    rw [happend]
    exact List.nodup_range' 1
  have hmainNested : ∀ ℓ body, (ℓ, body) ∈ mainLams → ∀ ℓ' body',
      (ℓ', body') ∈ ((collectLams body).run (ℓ + 1)).1 → (ℓ', body') ∈ mainLams := by
    intro ℓ body houter ℓ' body' hinner
    have houter' : (ℓ, body) ∈ ((collectLams p.main).run 0).1 := by
      rw [hmain]
      exact houter
    have h := collectLams_nested_mem p.main houter' hinner
    simpa only [hmain] using h
  have hfunNested := generatedFamilyFold_lam_nested_mem p p.phi ([], [], c₁) (by simp)
  rw [hfold] at hfunNested
  simp only at hfunNested
  have hfunGadgets := generatedFamilyFold_gadget_mem p p.phi ([], [], c₁) (by simp)
  rw [hfold] at hfunGadgets
  simp only at hfunGadgets
  rw [hmain] at hresolve
  simp only at hresolve
  rw [hfold] at hresolve
  simp only at hresolve
  simp only
  rw [hfold]
  simp only
  have hpair : (site.lamID, site.body) ∈ mainLams ++ funLams := by
    cases ref with
    | main =>
      change some (p.main.certifiedGeneratedCFG p.phi) = some source at hresolve
      simp only [Option.some.injEq] at hresolve
      subst source
      apply List.mem_append_left
      simpa [hmain] using Stmt.generatedCFGFrom_callGadget_provenance p.phi 0 p.main hsite
    | fn f =>
      change (funCFGs.find? (fun x => x.1 = f)).map (·.2.2) = some source at hresolve
      cases hfound : funCFGs.find? (fun x => x.1 = f) with
      | none => simp [hfound] at hresolve
      | some entry =>
        rcases entry with ⟨name, κ, component⟩
        simp only [hfound, Option.map_some, Option.some.injEq] at hresolve
        subst source
        apply List.mem_append_right
        apply hfunGadgets name κ component
        · exact List.mem_of_find?_eq_some hfound
        · exact hsite
    | lam ℓ =>
      let entries := (mainLams ++ funLams).map
        (fun x => (x.1, (x.2 ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (x.1 + 1)))
      change (entries.find? (fun x => x.1 = ℓ)).map Prod.snd = some source at hresolve
      cases hfound : entries.find? (fun x => x.1 = ℓ) with
      | none => simp [hfound] at hresolve
      | some entry =>
        rcases entry with ⟨lamID, component⟩
        simp only [hfound, Option.map_some, Option.some.injEq] at hresolve
        subst source
        have hentry := List.mem_of_find?_eq_some hfound
        dsimp [entries] at hentry
        simp only [List.mem_map] at hentry
        rcases hentry with ⟨outer, houter, houterEq⟩
        rcases outer with ⟨outerID, outerBody⟩
        simp only [Prod.mk.injEq] at houterEq
        rcases houterEq with ⟨hID, hcomponent⟩
        subst lamID
        subst component
        have hinner : (site.lamID, site.body) ∈
            ((collectLams outerBody).run (outerID + 1)).1 := by
          simpa [collectLams, StateT.run_bind, StateT.run_pure, id_bind, id_map, id_pure] using
            (Stmt.generatedCFGFrom_callGadget_provenance p.phi (outerID + 1)
              (outerBody ;; Stmt.Skip) hsite)
        rcases List.mem_append.mp houter with houter | houter
        · exact List.mem_append_left _ (hmainNested outerID outerBody houter _ _ hinner)
        · exact List.mem_append_right _ (hfunNested outerID outerBody houter _ _ hinner)
  change (((mainLams ++ funLams).map fun x =>
    (x.1, (x.2 ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (x.1 + 1))).find?
      (fun x => x.1 = site.lamID)).map Prod.snd = _
  rw [find?_eq_some_of_mem_nodup
    (xs := (mainLams ++ funLams).map fun x =>
      (x.1, (x.2 ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (x.1 + 1)))
    (ℓ := site.lamID)
    (component := (site.body ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi (site.lamID + 1))]
  · rfl
  · simpa only [List.map_map, Function.comp_apply] using hnodup
  · exact List.mem_map.mpr ⟨(site.lamID, site.body), hpair, rfl⟩

/-- Node-indexed generated-family lookup resolves the standalone component of
the selected callback lambda. -/
theorem Program.generatedFamily_gadgetAt_standalone (p : Program) {ref : CFGRef}
    {n : NodeID} {site : CallGadget}
    (hlookup : p.generatedFamily.gadgetAt? ref n = some site) :
    p.generatedFamily.cfgAt? (.lam site.lamID) =
      some ((site.body ;; Stmt.Skip).certifiedGeneratedCFGFrom p.phi
        (site.lamID + 1)) := by
  obtain ⟨component, hcomponent, hsite, _⟩ :=
    GeneratedCFGFamily.gadgetAt?_resolved hlookup
  exact p.generatedFamily_gadget_standalone hcomponent hsite

/-- Program-family lookup and certificate-bearing lookup select identical
call metadata. -/
theorem Program.family_gadgetAt?_eq_generatedFamily (p : Program)
    (ref : CFGRef) (n : NodeID) :
    p.family.gadgetAt? ref n = p.generatedFamily.gadgetAt? ref n := by
  rw [← p.generatedFamily_erase]
  exact p.generatedFamily.erase_gadgetAt? ref n

private theorem familyFold_preserves (p : Program) :
    ∀ (xs : FunEnv) (acc : List (String × InvKind × WFCFG) × List (Nat × Stmt) × Nat)
      (entry : String × InvKind × WFCFG),
      entry ∈ acc.1 → entry ∈ (xs.foldl (familyStep p) acc).1 := by
  intro xs
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    intro acc entry h
    simp only [List.foldl]
    refine ih _ entry ?_
    generalize hrun : (collectLams (hd.2.2 ;; Stmt.Skip)).run acc.2.2 = out
    rcases out with ⟨bl, c'⟩
    simp [familyStep, hrun, h]

private theorem familyFold_registers (p : Program) :
    ∀ (xs : FunEnv) (acc : List (String × InvKind × WFCFG) × List (Nat × Stmt) × Nat)
      (f : String) (κ : InvKind) (body : Stmt),
      (f, κ, body) ∈ xs →
      ∃ cfg : WFCFG, (f, κ, cfg) ∈ (xs.foldl (familyStep p) acc).1 := by
  intro xs
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    intro acc f κ body h
    simp only [List.mem_cons] at h
    rcases h with h | h
    · subst hd
      refine ⟨(body ;; .Skip).wfcfgFrom p.phi acc.2.2, ?_⟩
      simp only [List.foldl]
      apply familyFold_preserves p tl _
      generalize hrun : (collectLams (body ;; Stmt.Skip)).run acc.2.2 = out
      rcases out with ⟨bl, c'⟩
      simp [familyStep, hrun]
    · simp only [List.foldl]
      exact ih _ _ _ _ h

private theorem lookup_mem (xs : FunEnv) (f : String) (κ : InvKind) (body : Stmt)
    (h : xs.lookup f = some (κ, body)) : (f, κ, body) ∈ xs := by
  induction xs generalizing f with
  | nil => simp [FunEnv.lookup] at h
  | cons hd tl ih =>
    simp only [FunEnv.lookup] at h
    split at h
    · rcases hd with ⟨g, κ', body'⟩
      simp only [Option.some.injEq] at h
      rcases h with ⟨hκ, hbody⟩
      subst f
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih f h)

/-- A successful environment lookup has a matching function CFG entry in `p.family`. -/
theorem Program.family_fun_binding (p : Program) {f : String} {κ : InvKind} {body : Stmt}
    (hlookup : p.phi.lookup f = some (κ, body)) :
    ∃ cfg : WFCFG, (f, κ, cfg) ∈ p.family.funCFGs := by
  unfold Program.family
  dsimp
  apply familyFold_registers p
  exact lookup_mem _ _ _ _ hlookup

/-- A successful environment lookup is resolvable through the CFG family. -/
theorem Program.family_fn_registered (p : Program) {f : String} {κ : InvKind} {body : Stmt}
    (hlookup : p.phi.lookup f = some (κ, body)) :
    ∃ cfg, p.family.cfgAt? (.fn f) = some cfg := by
  obtain ⟨cfg, hmem⟩ := p.family_fun_binding hlookup
  exact CFGFamily.fn_registered_of_mem p.family hmem

/-- The main component of `p.family` is available at the main reference. -/
@[simp] theorem Program.family_main_registered (p : Program) :
    p.family.cfgAt? .main = some p.family.mainCFG :=
  CFGFamily.cfgAt_main p.family

/-- Every lambda CFG entry of `p.family` is resolvable at its lambda reference.
    This membership form covers lambdas collected from both the main statement
    and function bodies. -/
theorem Program.family_lam_registered (p : Program) {ℓ : Nat} {cfg : WFCFG}
    (hmem : (ℓ, cfg) ∈ p.family.lamCFGs) :
    ∃ cfg', p.family.cfgAt? (.lam ℓ) = some cfg' :=
  CFGFamily.lam_registered_of_mem p.family hmem

/-- A lambda collected from the main statement is registered in `p.family`. -/
theorem Program.family_main_lam_registered (p : Program) {ℓ : Nat} {body : Stmt}
    (hcollect : (ℓ, body) ∈ ((collectLams p.main).run 0).1) :
    ∃ cfg, p.family.cfgAt? (.lam ℓ) = some cfg := by
  apply CFGFamily.lam_registered_of_mem
    (cfg := (body ;; Stmt.Skip).wfcfgFrom p.phi (ℓ + 1))
  unfold Program.family
  dsimp
  simp only [List.map_append]
  apply List.mem_append_left _
  exact List.mem_map.mpr ⟨(ℓ, body), hcollect, rfl⟩

/-- Every call occurrence in the main lowering trace resolves to its lambda
    component in `Program.family`.  Since `Stmt.callSites` is recursive through
    call bodies, this covers nested calls at every depth, not just root calls. -/
theorem Program.family_main_callSite_registered (p : Program) {site : CallSite}
    (hsite : site ∈ (p.main.callSites.run 0).1) :
    ∃ cfg, p.family.cfgAt? (.lam site.lamID) = some cfg := by
  apply p.family_main_lam_registered (body := site.body)
  have htrace := p.main.callSites_collectLams 0
  rw [← htrace]
  exact List.mem_map.mpr ⟨site, hsite, rfl⟩

-- # Graphviz (DOT) rendering

/-- Infix symbol for a binary operator, used in node labels. -/
def BinOp.symbol : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .lt  => "<"
  | .eq  => "=="
  | .and => "&&"

/-- Render an expression to a short human-readable string for CFG labels. -/
def FExpr.render : FExpr → String
  | .Null          => "null"
  | .Int n         => toString n
  | .Var x         => x
  | .IsNull e      => "isNull(" ++ e.render ++ ")"
  | .Not e         => "!" ++ e.render
  | .BinOp o e₁ e₂ => "(" ++ e₁.render ++ " " ++ BinOp.symbol o ++ " " ++ e₂.render ++ ")"

/-- A short label describing a CFG node. -/
def NodeKind.label : NodeKind → String
  | .Assume e   => "assume " ++ e.render
  | .Assign x e => x ++ " = " ++ e.render
  | .Skip       => "skip"
  | .Call f _   => "call " ++ f
  | .Invoke     => "invoke"

/-- Escape a string for inclusion inside a DOT double-quoted label. -/
def dotEscape (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\"" "\\\""

/-- One-character rendering of an invocation kind `κ` (ε/1/+/?). -/
def InvKind.symbol : InvKind → String
  | .none    => "ε"
  | .once    => "1"
  | .atLeast => "+"
  | .atMost  => "?"

def CFG.toDotStmts (g : CFG) (pfx : String) (ind : String) : String :=
  let nodeLines := g.nodes.mapIdx (fun i k =>
    let shape :=
      if i = g.entry && i = g.exit then ", shape=box, style=\"rounded,bold\""
      else if i = g.entry then ", shape=box, style=bold"
      else if i = g.exit then ", shape=doublecircle"
      else ""
    s!"{ind}{pfx}{i} [label=\"{i}: {dotEscape k.label}\"{shape}];")
  let edgeLines := g.edges.map (fun e =>
    s!"{ind}{pfx}{e.src} -> {pfx}{e.dst};")
  String.intercalate "\n" (nodeLines ++ edgeLines)

/-- Render a single CFG as a complete Graphviz `digraph`. -/
def CFG.toDot (g : CFG) (name : String := "cfg") : String :=
  "digraph \"" ++ dotEscape name ++ "\" {\n  node [shape=box];\n" ++
    g.toDotStmts "n" "  " ++ "\n}\n"

/-- Render an entire family of CFGs as one Graphviz `digraph`. -/
def CFGFamily.toDot (fam : CFGFamily) (name : String := "family") : String :=
  let lamClusters := fam.lamCFGs.mapIdx (fun i entry =>
    let (f, g) := entry
    "subgraph cluster_l" ++ toString i ++ " {\n" ++
      "    label=\"G_" ++ toString f ++ "\";\n" ++
      g.val.toDotStmts s!"l{i}_" "      " ++ "\n }")
  let funClusters := fam.funCFGs.mapIdx (fun i entry =>
    let (f, κ, g) := entry
    "  subgraph cluster_f" ++ toString i ++ " {\n" ++
      "    label=\"G_" ++ f ++ " (κ=" ++ κ.symbol ++ ")\";\n" ++
      g.val.toDotStmts s!"f{i}_" "    " ++ "\n  }")
  let mainCluster :=
    "  subgraph cluster_main {\n    label=\"main\";\n" ++
      fam.mainCFG.val.toDotStmts "main_" "    " ++ "\n  }"
  "digraph \"" ++ dotEscape name ++ "\" {\n  node [shape=box];\n" ++
    String.intercalate "\n" (funClusters ++ lamClusters ++ [mainCluster]) ++ "\n}\n"

/-- Render a single CFG as one Graphviz `digraph`, augmented with analysis information. -/
def CFG.toDotWithFn (g : CFG) (inF outF : NodeID -> String)
  (name : String := "cfg") : String :=
    let nodeLines := g.nodes.mapIdx (fun i k =>
      let shape :=
        if i = g.entry && i = g.exit then ", shape=box, style=\"rounded,bold\""
        else if i = g.entry then ", shape=box, style=bold"
        else if i = g.exit then ", shape=doublecircle"
        else ""
      let label := s!"IN: {inF i}\n{i}: {k.label}\nOUT: {outF i}"
      s!"  n{i} [label=\"{dotEscape label}\"{shape}];")
    let edgeLines := g.edges.map (fun e =>
      s!"  n{e.src} -> n{e.dst};")
    "digraph \"" ++ dotEscape name ++ "\" {\n  node [shape=box];\n" ++
      String.intercalate "\n" (nodeLines ++ edgeLines) ++ "\n}\n"

@[reducible]
def DukeAnalysisCFG (g : CFG) (hg : g.WellFormed) :
    AnalysisCFG NodeID Edge where
  nodes     := List.range g.nodes.length
  edges     := g.edges
  entry     := g.entry
  srcOf e   := e.src
  dstOf e   := e.dst
  srcOf_mem := by
    intros e he
    have hsrc := hg.2.1
    exact List.mem_range.mpr (hsrc e he)
  dstOf_mem := by
    intros e he
    have hdst := hg.2.2.1
    exact List.mem_range.mpr (hdst e he)
  entry_mem := by simpa using hg.1

@[reducible]
def WFCFG.analysis (g : WFCFG) : AnalysisCFG NodeID Edge :=
  DukeAnalysisCFG g g.2

/-- All variables appearing in the program , de-duplicated, with a `Nodup` witness. -/
def vars (g : CFG) : { l : List String // l.Nodup } :=
  let base := g.nodes.filterMap (fun k =>
  match k with
  | .Assign x _ => some x
  | _           => none)
  ⟨base.eraseDups, Utils.List.eraseDups_nodup base⟩
