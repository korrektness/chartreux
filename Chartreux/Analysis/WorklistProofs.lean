import Chartreux.Analysis.Worklist
import Chartreux.Analysis.Generic

namespace Chartreux.Analysis

variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]
variable {L : Type}

section Helpers
private theorem ite_decEq_irrel {α : Type} {p : Prop}
    (d1 d2 : Decidable p) (a b : α) :
    @ite α p d1 a b = @ite α p d2 a b := by
  cases d1 <;> cases d2 <;> simp_all

private theorem foldl_join_eT_update
    [Bot L] [Max L]
    (g : AnalysisCFG Node Edge)
    (edgeTransfer : Edge -> L -> L) (outF : StateN g L)
    (n : NodeOf g) (v : L) (m : NodeOf g) (edges : List {e // e ∈ g.inEdges m.val})
    (hnoedge : ∀ e ∈ edges, g.srcOf e.val ≠ n.val) (init : L) :
    (edges.foldl (fun acc ⟨e, he⟩ =>
      acc ⊔ edgeTransfer e ((outF.update n v) ⟨g.srcOf e, g.inEdges_src_mem m.val e he⟩)) init)
    =
    (edges.foldl (fun acc ⟨e, he⟩ =>
      acc ⊔ edgeTransfer e (outF ⟨g.srcOf e, g.inEdges_src_mem m.val e he⟩)) init) := by
  induction edges generalizing init with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    have he_src : g.srcOf e.val ≠ n.val := hnoedge e (List.Mem.head _)
    have hne : (⟨g.srcOf e.val, g.inEdges_src_mem m.val e.val e.property⟩ : NodeOf g) ≠ n := by
      intro h
      have hval : g.srcOf e.val = n.val := congrArg Subtype.val h
      exact he_src hval
    simp only [StateN.update, hne, if_false]
    exact ih (fun e' he' => hnoedge e' (List.mem_cons_of_mem e he')) _

private theorem joinPredEdges_update_non_pred
    [Bot L] [Max L]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> L -> L) (outF : StateN g L)
    (n : NodeOf g) (v : L) (m : NodeOf g)
    (hnoedge : ∀ e ∈ g.inEdges m.val, g.srcOf e ≠ n.val) :
    (joinPredEdges g edgeTransfer (outF.update n v) m) =
      (joinPredEdges g edgeTransfer outF m) := by
  unfold joinPredEdges
  exact foldl_join_eT_update g edgeTransfer outF n v m (g.inEdges m.val).attach
    (fun e _ => hnoedge e.val e.property) ⊥

private theorem not_succ_no_in_edge
    (g : AnalysisCFG Node Edge) (n m : NodeOf g) (h : m ∉ g.succOf n) :
    ∀ e ∈ g.inEdges m.val, g.srcOf e ≠ n.val := by
  intro e he hsrc
  apply h
  unfold AnalysisCFG.succOf
  rw [List.mem_filter]
  refine ⟨List.mem_attach _ _, ?_⟩
  simp only [List.any_eq_true, decide_eq_true_eq]
  exact ⟨e, he, hsrc⟩

private theorem expectedIn_update_non_pred
    [Bot L] [Max L]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> L -> L) (outF : StateN g L)
    (entryInit : L) (n : NodeOf g) (v : L) (m : NodeOf g) (h : m ∉ g.succOf n) :
    (expectedIn g edgeTransfer entryInit (outF.update n v) m) =
       (expectedIn g edgeTransfer entryInit outF m) := by
  simp only [expectedIn]
  rw [joinPredEdges_update_non_pred g edgeTransfer outF n v m
      (not_succ_no_in_edge g n m h)]
end Helpers

/-- a mapping is a forward fixpoint if, at every node, applying the
    transfer function to the incoming facts yields outF itself. -/
def IsForwardFixpoint [Bot L] [Max L]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> L -> L) (edgeTransfer : Edge -> L -> L)
    (entryInit : L) (outF : StateN g L) : Prop :=
  ∀ n : NodeOf g,
    outF n = nodeTransfer n.val (expectedIn g edgeTransfer entryInit outF n)

/-- a mapping is a forward post-fixpoint if, at every node, joining the
    transfer function result with outF yields no change. -/
def IsForwardPostFixpoint [Bot L] [Max L]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> L -> L) (edgeTransfer : Edge -> L -> L)
    (entryInit : L) (outF : StateN g L) : Prop :=
  ∀ n : NodeOf g,
    (nodeTransfer n.val (expectedIn g edgeTransfer entryInit outF n)) ⊑ outF n

private theorem foldl_join_eT_mono
    [Bot L] [Max L] [FiniteHeight L] [ll : SemiLattice L]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> L -> L)
    (edge_mono : ∀ e, mono_f (edgeTransfer e))
    (outF1 outF2 : StateN g L) (hle : StateN.le outF1 outF2)
    (m : NodeOf g) (edges : List {e // e ∈ g.inEdges m.val})
    (acc1 acc2 : L) (hacc : acc1 ⊑ acc2) :
    ((edges.foldl (fun acc ⟨e, he⟩ =>
        acc ⊔ edgeTransfer e (outF1 ⟨g.srcOf e, g.inEdges_src_mem m.val e he⟩)) acc1) ⊔
      (edges.foldl (fun acc ⟨e, he⟩ =>
        acc ⊔ edgeTransfer e (outF2 ⟨g.srcOf e, g.inEdges_src_mem m.val e he⟩)) acc2))
    =
    (edges.foldl (fun acc ⟨e, he⟩ =>
      acc ⊔ edgeTransfer e (outF2 ⟨g.srcOf e, g.inEdges_src_mem m.val e he⟩)) acc2) := by
  induction edges generalizing acc1 acc2 with
  | nil => exact hacc
  | cons e es ih =>
    simp only [List.foldl_cons]
    apply ih
    let e_mem : NodeOf g := ⟨g.srcOf e.val, g.inEdges_src_mem m.val e.val e.property⟩
    grind [edge_mono e.val _ _ (hle e_mem), ll.join_assoc, ll.join_comm]

private theorem joinPredEdges_mono
    [Bot L] [Max L] [FiniteHeight L] [ll : SemiLattice L]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> L -> L)
    (edge_mono : ∀ e, mono_f (edgeTransfer e))
    (outF1 outF2 : StateN g L) (hle : StateN.le outF1 outF2) (n : NodeOf g) :
    (joinPredEdges g edgeTransfer outF1 n) ⊑ (joinPredEdges g edgeTransfer outF2 n) := by
  unfold joinPredEdges
  exact foldl_join_eT_mono g edgeTransfer edge_mono
    outF1 outF2 hle n (g.inEdges n.val).attach ⊥ ⊥ (ll.join_idem ⊥)

private theorem expectedIn_mono
    [Bot L] [Max L] [FiniteHeight L]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> L -> L) (edgeTransfer : Edge -> L -> L)
    (entryInit : L)
    [ll : SemiLattice L] [tm : TransferMono nodeTransfer edgeTransfer]
    (outF1 outF2 : StateN g L)
    (hle : StateN.le outF1 outF2) (n : NodeOf g) :
    (expectedIn g edgeTransfer entryInit outF1 n) ⊑
        (expectedIn g edgeTransfer entryInit outF2 n) := by
  simp only [expectedIn]
  split
    <;> grind [ll.join_assoc, ll.join_idem, ll.join_comm,
               joinPredEdges_mono g edgeTransfer tm.edge_mono outF1 outF2 hle n]

private theorem T_postfix_of_postfix
    [Bot L] [Max L] [FiniteHeight L]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> L -> L) (edgeTransfer : Edge -> L -> L)
    (entryInit : L) (f : StateN g L)
    [ll : SemiLattice L] [tm : TransferMono nodeTransfer edgeTransfer]
    (hpost : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit f) :
    IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit
      (fun n => nodeTransfer n.val (expectedIn g edgeTransfer entryInit f n)) := by
  intro n
  apply tm.node_mono
  apply expectedIn_mono g nodeTransfer edgeTransfer entryInit
    (fun m => nodeTransfer m.val (expectedIn g edgeTransfer entryInit f m)) f
  intro m
  simpa [ll.join_comm] using hpost m

/-- the result of the worklist algorithm is always ⊒ the initial facts. -/
theorem worklistForward_mono
    [Bot L] [Max L] [DecidableEq L] [FiniteHeight L]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> L -> L) (edgeTransfer : Edge -> L -> L)
    (entryInit : L) (outF : StateN g L) (wl : List (NodeOf g))
    [ll : SemiLattice L] :
    let res := worklistForward g nodeTransfer edgeTransfer entryInit outF wl
    StateN.le outF res := by
  induction outF, wl using worklistForward.induct g nodeTransfer edgeTransfer entryInit with
  | case1 o =>
    simp only [worklistForward, StateN.le]
    intro n; exact ll.join_idem _
  | case2 o n r nin nout hnout ih =>
    rw [worklistForward.eq_2, if_pos (by assumption)]
    exact ih
  | case3 o n r nin nout hnout o' wl' ih =>
    rw [worklistForward, if_neg (by assumption)]
    exact StateN.le_trans _ _ _
      (StateN.le_update_join o n _) ih

/-- generic invariant propagation combinator for the worklist algorithm.
    if a predicate `P` on `(outF, wl)` holds initially and is preserved by
    both the "unchanged" and "changed" branches, then `P (result, [])` holds. -/
private theorem worklistForward_invariant
    [Bot L] [Max L] [DecidableEq L] [FiniteHeight L] [ll : SemiLattice L]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> L -> L) (edgeTransfer : Edge -> L -> L)
    (entryInit : L) (outF : StateN g L) (wl : List (NodeOf g))
    (P : StateN g L -> List (NodeOf g) -> Prop)
    (hinit : P outF wl)
    (hstep_same : ∀ (ρ : StateN g L) (n : NodeOf g) (rest : List (NodeOf g)),
      P ρ (n :: rest) ->
      let newIn := expectedIn g edgeTransfer entryInit ρ n
      let newOut := nodeTransfer n.val newIn
      newOut ⊑ ρ n ->
      P ρ rest)
    (hstep_changed : ∀ (ρ : StateN g L) (n : NodeOf g) (rest : List (NodeOf g)),
      P ρ (n :: rest) ->
      let newIn := expectedIn g edgeTransfer entryInit ρ n
      let newOut := ρ n ⊔ nodeTransfer n.val newIn
      ¬(newOut = ρ n) ->
      P (ρ.update n newOut) (rest ++ g.succOf n)) :
    P (worklistForward g nodeTransfer edgeTransfer entryInit outF wl) [] := by
  induction outF, wl using worklistForward.induct g nodeTransfer edgeTransfer entryInit with
  | case1 o =>
    simp only [worklistForward]
    exact hinit
  | case2 o n r nin nout hnout ih =>
    rw [worklistForward.eq_2, if_pos (by assumption)]
    apply ih; apply hstep_same
    · assumption
    · rw [<-hnout, <-ll.join_assoc, ll.join_comm, <-ll.join_assoc, ll.join_idem, ll.join_comm]
  | case3 o n r nin nout hnout o' wl' ih =>
    rw [worklistForward, if_neg (by assumption)]
    exact ih (hstep_changed o n r hinit hnout)

/-- the result of the worklist algorithm is always a post-fixpoint -/
theorem worklistForward_sound_postfixpoint
    [Bot L] [Max L] [DecidableEq L] [FiniteHeight L]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> L -> L) (edgeTransfer : Edge -> L -> L)
    (entryInit : L) (ρ : StateN g L) (wl0 : List (NodeOf g))
    [ll : SemiLattice L]
    (hinv0 : ∀ m : NodeOf g, m ∉ wl0 ->
        nodeTransfer m.val (expectedIn g edgeTransfer entryInit ρ m) ⊑ ρ m) :
    let res := worklistForward g nodeTransfer edgeTransfer entryInit ρ wl0
    IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit res := by
  let P : StateN g L -> List (NodeOf g) -> Prop := fun o wl =>
    ∀ m : NodeOf g, m ∉ wl ->
      nodeTransfer m.val (expectedIn g edgeTransfer entryInit o m) ⊑ o m
  intro res n
  refine worklistForward_invariant g nodeTransfer edgeTransfer entryInit
    ρ wl0 P hinv0 ?_ ?_ _ (by grind)
  · grind
  · intros o n rest hP newIn newOut hneq m hmem
    let t := (o n ⊔ nodeTransfer n.val (expectedIn g edgeTransfer entryInit o n))
    have heexp := expectedIn_update_non_pred g edgeTransfer o entryInit n t m (by grind)
    by_cases hm : m = n
    · subst hm
      simp [StateN.update]
      grind [ll.join_comm, ll.join_assoc, ll.join_idem]
    · have ho_m : StateN.update o n
        (o n ⊔ nodeTransfer n.val (expectedIn g edgeTransfer entryInit o n)) m = o m :=
        by dsimp [StateN.update]; exact if_neg hm
      rw [ho_m]
      grind [List.mem_cons.mp]

/-- Least post-fixpoint completeness, derived via the invariant combinator. -/
theorem worklistForward_complete_least_postfixpoint
    [Bot L] [Max L] [DecidableEq L] [FiniteHeight L]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> L -> L) (edgeTransfer : Edge -> L -> L)
    (entryInit : L) (outF : StateN g L) (wl : List (NodeOf g))
    [ll : SemiLattice L] [tm : TransferMono nodeTransfer edgeTransfer]
    (post : StateN g L) (hpost : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit post)
    (hinv : StateN.le outF post) :
    let res := worklistForward g nodeTransfer edgeTransfer entryInit outF wl
    StateN.le res post := by
  let P : StateN g L -> List (NodeOf g) -> Prop := fun o _ => StateN.le o post
  apply worklistForward_invariant g nodeTransfer edgeTransfer entryInit outF wl P
    hinv (by grind)
  intros o m rest hP newIn hlub hneq n
  by_cases hmn : m = n
  · subst hmn
    have h_nT_mono := tm.node_mono m.val _ _ (
      expectedIn_mono g nodeTransfer edgeTransfer entryInit o post hP m
    )
    grind [StateN.update, hP m, hpost m, ll.join_comm, ll.join_assoc]
  · have : ¬(n = m) := by exact Ne.intro fun a ↦ hmn (id (Eq.symm a))
    simp only [StateN.update, this, ↓reduceIte]
    exact hP n

/-- fixpoint soundness, derived via the invariant combinator. -/
theorem worklistForward_sound_fixpoint
    [Bot L] [Max L] [DecidableEq L] [FiniteHeight L]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> L -> L) (edgeTransfer : Edge -> L -> L)
    (entryInit : L) (ρ : StateN g L) (wl0 : List (NodeOf g))
    [ll : SemiLattice L] [tm : TransferMono nodeTransfer edgeTransfer]
    (hinv0 : ∀ m : NodeOf g, m ∉ wl0 ->
       nodeTransfer m.val (expectedIn g edgeTransfer entryInit ρ m) ⊑ ρ m)
    (hbot : ∀ (n : NodeOf g) v, ρ n ⊑ v) :
    let res := worklistForward g nodeTransfer edgeTransfer entryInit ρ wl0
    IsForwardFixpoint g nodeTransfer edgeTransfer entryInit res := by
  intro res n
  have hpostres : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit res :=
    worklistForward_sound_postfixpoint g nodeTransfer edgeTransfer entryInit ρ wl0 hinv0
  have hpostT : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit
      (fun n => nodeTransfer n.val (expectedIn g edgeTransfer entryInit res n)) :=
    T_postfix_of_postfix g nodeTransfer edgeTransfer entryInit res hpostres
  have hbase : StateN.le ρ
    (fun n => nodeTransfer n.val (expectedIn g edgeTransfer entryInit res n)) :=
      fun n => by apply hbot
  have hleast : StateN.le res
    (fun n => nodeTransfer n.val (expectedIn g edgeTransfer entryInit res n)) :=
    worklistForward_complete_least_postfixpoint g nodeTransfer edgeTransfer entryInit ρ
      wl0 _ hpostT hbase
  grind [hleast n, hpostres n, ll.join_comm]

private theorem foldl_join_absorb
    [Bot L] [Max L] [FiniteHeight L] [ll : SemiLattice L]
    {α : Type} (f : α -> L) (x : L) :
    ∀ (l : List α) (acc : L), x ⊑ acc ->
      x ⊑ (l.foldl (fun a y => a ⊔ f y) acc)
  | [], acc, h => by simpa using h
  | hd :: tl, acc, h => by
    simp only [List.foldl_cons]
    apply foldl_join_absorb f x tl
    rw [<-ll.join_assoc, h]

private theorem foldl_ge_of_mem
    [Bot L] [Max L] [FiniteHeight L] [ll : SemiLattice L]
    {α : Type} (f : α -> L)
    (l : List α) (a : α) (ha : a ∈ l) (init : L) :
    f a ⊑ (l.foldl (fun acc x => acc ⊔ f x) init) := by
  induction l generalizing init with
  | nil => cases ha
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp ha with
    | inl heq =>
      subst heq
      apply foldl_join_absorb f (f a) tl
      rw [ll.join_comm, ll.join_assoc, ll.join_idem]
    | inr htl => exact ih htl _

private theorem joinPredEdges_ge_edge
    [Bot L] [Max L] [FiniteHeight L] [ll : SemiLattice L]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> L -> L)
    (ρ : StateN g L) (n : NodeOf g)
    (e : Edge) (he : e ∈ g.inEdges n.val) :
    edgeTransfer e (ρ ⟨g.srcOf e, g.inEdges_src_mem n.val e he⟩)
      ⊑ (joinPredEdges g edgeTransfer ρ n) := by
  unfold joinPredEdges
  let f : {x // x ∈ g.inEdges n.val} -> L := fun ⟨x, hx⟩ =>
    edgeTransfer x (ρ ⟨g.srcOf x, g.inEdges_src_mem n.val x hx⟩)
  have ha : (⟨e, he⟩ : {x // x ∈ g.inEdges n.val}) ∈ (g.inEdges n.val).attach :=
    List.mem_attach _ _
  exact foldl_ge_of_mem f (g.inEdges n.val).attach ⟨e, he⟩ ha ⊥

end Chartreux.Analysis

namespace Chartreux.Analysis

open Chartreux.Analysis Chartreux.Analysis.Generic

variable {Node Edge State : Type} [DecidableEq Node] [DecidableEq Edge]
variable {g : AnalysisCFG Node Edge}
variable [ls : LangSem Node Edge State g]

theorem postFixpoint_of_isForwardPostFixpoint
    [Bot L] [Max L] [FiniteHeight L] [ll : SemiLattice L]
    (nodeTransfer : Node -> L -> L) (edgeTransfer : Edge -> L -> L)
    (edge_mono : ∀ e, mono_f (edgeTransfer e))
    (entryInit : L) (ρ : StateN g L)
    (hpost : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit ρ) :
    Generic.PostFixpoint g
      ({ L := L
       , nodeTransfer := nodeTransfer
       , edgeTransfer := edgeTransfer
       , entry := entryInit } : DFA Node Edge)
      (fun n =>
        if h : n ∈ g.nodes then
          expectedIn g edgeTransfer entryInit ρ ⟨n, h⟩
        else ⊥) := by
  intro ⟨e, he⟩
  have he_in : e ∈ g.inEdges (g.dstOf e) := g.edges_mem_inEdges e he
  have hdst_mem : g.dstOf e ∈ g.nodes := g.dstOf_mem e he
  have hsrc_mem : g.srcOf e ∈ g.nodes := g.inEdges_src_mem _ e he_in
  let m_src : NodeOf g := ⟨g.srcOf e, hsrc_mem⟩
  let m_dst : NodeOf g := ⟨g.dstOf e, hdst_mem⟩
  change edgeTransfer e (nodeTransfer (g.srcOf e)
              (if h : g.srcOf e ∈ g.nodes then
                 expectedIn g edgeTransfer entryInit ρ ⟨g.srcOf e, h⟩
               else ⊥))
        ⊑ (if h : g.dstOf e ∈ g.nodes then expectedIn g edgeTransfer entryInit ρ ⟨g.dstOf e, h⟩
          else ⊥)
  rw [dif_pos hsrc_mem, dif_pos hdst_mem]
  have h_node : nodeTransfer (g.srcOf e)
                    (expectedIn g edgeTransfer entryInit ρ m_src) ⊑ ρ m_src := hpost m_src
  have h_edge : edgeTransfer e
                  (nodeTransfer (g.srcOf e)
                    (expectedIn g edgeTransfer entryInit ρ m_src)) ⊑ edgeTransfer e (ρ m_src)
    := edge_mono e _ _ h_node
  have h_outF_eq : ρ ⟨g.srcOf e, g.inEdges_src_mem m_dst.val e he_in⟩ = ρ m_src := rfl
  have h_join_ge :
      edgeTransfer e (ρ m_src) ⊑ joinPredEdges g edgeTransfer ρ m_dst := by
    have h := joinPredEdges_ge_edge g edgeTransfer ρ m_dst e he_in
    rw [h_outF_eq] at h
    exact h
  have h_expIn_ge :
    joinPredEdges g edgeTransfer ρ m_dst ⊑ expectedIn g edgeTransfer entryInit ρ m_dst := by
    unfold expectedIn
    split <;> grind [ll.join_assoc, ll.join_comm, ll.join_idem]
  exact join_ge_trans _ _ _ h_edge (join_ge_trans _ _ _ h_join_ge h_expIn_ge)

end Chartreux.Analysis

namespace Chartreux

open Chartreux.Analysis Chartreux.Analysis.Generic

/-- Analysis bundle instance -/
structure Analysis (Node Edge State : Type)
    [DecidableEq Node] [DecidableEq Edge]
    {g : AnalysisCFG Node Edge}
    [ls : LangSem Node Edge State g] where
  dfa : DFA Node Edge
  botL : Bot dfa.L
  maxL : Max dfa.L
  decEqL : DecidableEq dfa.L
  fhL : FiniteHeight dfa.L
  llL : SemiLattice dfa.L
  semantics : DFASemantics (ls := ls) g dfa
  mono_absorb :
    ∀ {ℓ ℓ' : dfa.L} {σ : State},
      ℓ ⊑ ℓ' -> semantics.Coh ℓ σ -> semantics.Coh ℓ' σ
  edge_mono : ∀ e, mono_f (dfa.edgeTransfer e)

structure AnalysisResult {Node Edge State : Type}
    [DecidableEq Node] [DecidableEq Edge]
    {g : AnalysisCFG Node Edge}
    [ls : LangSem Node Edge State g]
    (a : Analysis (ls := ls) Node Edge State) where
  inFacts : Node -> a.dfa.L
  outFacts : Node -> a.dfa.L
  isPostFix : letI := a.maxL; Generic.PostFixpoint g a.dfa inFacts
  inFacts_entry : letI := a.maxL; a.dfa.entry ⊑ (inFacts g.entry)

def analyze {Node Edge State : Type}
    [DecidableEq Node] [DecidableEq Edge]
    {g : AnalysisCFG Node Edge}
    [ls : LangSem Node Edge State g]
    (a : Analysis Node Edge State) :
    AnalysisResult (ls := ls) a :=
  letI := a.botL
  letI := a.maxL
  letI := a.decEqL
  letI := a.fhL
  letI := a.llL
  let entryInit := a.dfa.entry
  let nT : Node -> a.dfa.L -> a.dfa.L := a.dfa.nodeTransfer
  let eT : Edge -> a.dfa.L -> a.dfa.L := a.dfa.edgeTransfer
  let res := runDataflow g nT eT entryInit
  let inFacts : Node -> a.dfa.L := fun n =>
    if hn : n ∈ g.nodes then expectedIn g eT entryInit res.2 ⟨n, hn⟩
    else ⊥
  let outFacts : Node -> a.dfa.L := fun n =>
    if hn : n ∈ g.nodes then res.2 ⟨n, hn⟩
    else ⊥
  have hpost : IsForwardPostFixpoint g nT eT entryInit res.2 :=
    worklistForward_sound_postfixpoint g nT eT entryInit (fun _ => ⊥)
      g.nodes_mem (by intro m hm; exact absurd (List.mem_attach _ m) hm)
  have hpf : Generic.PostFixpoint g a.dfa inFacts := by
    apply postFixpoint_of_isForwardPostFixpoint (edge_mono := a.edge_mono)
    assumption
  have hentry : a.dfa.entry ⊑ (inFacts g.entry) := by
    change a.dfa.entry ⊑
      (if hn : g.entry ∈ g.nodes then
         expectedIn g eT entryInit res.2 ⟨g.entry, hn⟩
       else ⊥)
    rw [dif_pos g.entry_mem]
    unfold expectedIn
    rw [if_pos (show (⟨g.entry, g.entry_mem⟩ : NodeOf g).val = g.entry from rfl)]
    simp only
    rw [<-a.llL.join_assoc, a.llL.join_idem]
  { inFacts := inFacts
  , outFacts := outFacts
  , isPostFix := hpf
  , inFacts_entry := hentry }

end Chartreux
