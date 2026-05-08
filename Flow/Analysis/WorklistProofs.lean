import Flow.Analysis.Worklist
import Flow.Analysis.Generic


namespace Flow.Analysis

variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]
variable {A : Type}

/-! ## Helpers -/

private lemma ite_decEq_irrel {α : Type} {p : Prop}
    (d1 d2 : Decidable p) (a b : α) :
    @ite α p d1 a b = @ite α p d2 a b := by
  cases d1 <;> cases d2 <;> simp_all

private lemma newIn_eq_expectedIn
    [Bot A] [Max A]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> A -> A)
    (entryInit : A) (outF : StateN g A) (n : NodeOf g)
    (newIn : A)
    (hdef : Eq newIn (if _ : n.val = g.entry then entryInit
        else joinPredEdges g edgeTransfer outF n)) :
    Eq newIn (expectedIn g edgeTransfer entryInit outF n) := by
  rw [hdef]; simp only [expectedIn]; exact ite_decEq_irrel _ _ _ _

private lemma foldl_join_eT_update
    [Bot A] [Max A]
    (g : AnalysisCFG Node Edge)
    (edgeTransfer : Edge -> A -> A) (outF : StateN g A)
    (n : NodeOf g) (v : A) (m : NodeOf g) (edges : List {e // e ∈ g.inEdges m.val})
    (hnoedge : ∀ e ∈ edges, g.srcOf e.val ≠ n.val) (init : A) :
    Eq (edges.foldl (fun acc ⟨e, he⟩ =>
        acc ⊔ edgeTransfer e ((outF.update n v) ⟨g.srcOf e, g.inEdges_src_mem m.val e he⟩)) init)
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

private lemma joinPredEdges_update_non_pred
    [Bot A] [Max A]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> A -> A) (outF : StateN g A)
    (n : NodeOf g) (v : A) (m : NodeOf g)
    (hnoedge : ∀ e ∈ g.inEdges m.val, g.srcOf e ≠ n.val) :
    Eq (joinPredEdges g edgeTransfer (outF.update n v) m)
       (joinPredEdges g edgeTransfer outF m) := by
  unfold joinPredEdges
  exact foldl_join_eT_update g edgeTransfer outF n v m (g.inEdges m.val).attach
    (fun e _ => hnoedge e.val e.property) ⊥

private lemma not_succ_no_in_edge
    (g : AnalysisCFG Node Edge) (n m : NodeOf g) (h : m ∉ g.succOf n) :
    ∀ e ∈ g.inEdges m.val, g.srcOf e ≠ n.val := by
  intro e he hsrc
  apply h
  unfold AnalysisCFG.succOf
  rw [List.mem_filter]
  refine ⟨List.mem_attach _ _, ?_⟩
  simp only [List.any_eq_true, decide_eq_true_eq]
  exact ⟨e, he, hsrc⟩

private lemma expectedIn_update_non_pred
    [Bot A] [Max A]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> A -> A) (outF : StateN g A)
    (entryInit : A) (n : NodeOf g) (v : A) (m : NodeOf g) (h : m ∉ g.succOf n) :
    Eq (expectedIn g edgeTransfer entryInit (outF.update n v) m)
       (expectedIn g edgeTransfer entryInit outF m) := by
  simp only [expectedIn]
  split
  · rfl
  · exact joinPredEdges_update_non_pred g edgeTransfer outF n v m
      (not_succ_no_in_edge g n m h)

/-! ## Predicates -/

/-- a mapping is a forward fixpoint if, at every node, applying the
    transfer function to the incoming facts yields outF itself. -/
def IsForwardFixpoint [Bot A] [Max A]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> A -> A) (edgeTransfer : Edge -> A -> A)
    (entryInit : A) (outF : StateN g A) : Prop :=
  ∀ n : NodeOf g,
    outF n = nodeTransfer n.val (expectedIn g edgeTransfer entryInit outF n)

/-- a mapping is a forward post-fixpoint if, at every node, joining the
    transfer function result with outF yields no change. -/
def IsForwardPostFixpoint [Bot A] [Max A]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> A -> A) (edgeTransfer : Edge -> A -> A)
    (entryInit : A) (outF : StateN g A) : Prop :=
  ∀ n : NodeOf g,
    (nodeTransfer n.val (expectedIn g edgeTransfer entryInit outF n)) ⊔ (outF n) = (outF n)

/-! ## Monotonicity -/

private lemma foldl_join_eT_mono
    [Bot A] [Max A] [FiniteHeight A] [ll : LatticeLike A]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> A -> A)
    (edge_mono : ∀ e, mono_f (edgeTransfer e))
    (outF1 outF2 : StateN g A) (hle : StateN.le outF1 outF2)
    (m : NodeOf g) (edges : List {e // e ∈ g.inEdges m.val})
    (acc1 acc2 : A) (hacc : acc1 ⊔ acc2 = acc1) :
    Eq ((edges.foldl (fun acc ⟨e, he⟩ =>
          acc ⊔ edgeTransfer e (outF1 ⟨g.srcOf e, g.inEdges_src_mem m.val e he⟩)) acc1) ⊔
        (edges.foldl (fun acc ⟨e, he⟩ =>
          acc ⊔ edgeTransfer e (outF2 ⟨g.srcOf e, g.inEdges_src_mem m.val e he⟩)) acc2))
       (edges.foldl (fun acc ⟨e, he⟩ =>
          acc ⊔ edgeTransfer e (outF1 ⟨g.srcOf e, g.inEdges_src_mem m.val e he⟩)) acc1) := by
  induction edges generalizing acc1 acc2 with
  | nil => exact hacc
  | cons e es ih =>
    simp only [List.foldl_cons]
    apply ih
    let e_mem : NodeOf g := ⟨g.srcOf e.val, g.inEdges_src_mem m.val e.val e.property⟩
    have h_eT : (edgeTransfer e.val (outF1 e_mem)) ⊔ (edgeTransfer e.val (outF2 e_mem))
              = edgeTransfer e.val (outF1 e_mem) := edge_mono e.val _ _ (hle e_mem)
    calc (acc1 ⊔ edgeTransfer e.val (outF1 e_mem)) ⊔ (acc2 ⊔ edgeTransfer e.val (outF2 e_mem))
        = ((acc1 ⊔ edgeTransfer e.val (outF1 e_mem)) ⊔ acc2) ⊔
            edgeTransfer e.val (outF2 e_mem) := by
            rw [← ll.join_assoc]
      _ = (acc1 ⊔ (edgeTransfer e.val (outF1 e_mem) ⊔ acc2)) ⊔
            edgeTransfer e.val (outF2 e_mem) := by
            rw [ll.join_assoc acc1]
      _ = (acc1 ⊔ (acc2 ⊔ edgeTransfer e.val (outF1 e_mem))) ⊔
            edgeTransfer e.val (outF2 e_mem) := by
            rw [ll.join_comm (edgeTransfer e.val (outF1 e_mem)) acc2]
      _ = ((acc1 ⊔ acc2) ⊔ edgeTransfer e.val (outF1 e_mem)) ⊔
            edgeTransfer e.val (outF2 e_mem) := by
            rw [← ll.join_assoc acc1 acc2]
      _ = (acc1 ⊔ edgeTransfer e.val (outF1 e_mem)) ⊔
            edgeTransfer e.val (outF2 e_mem) := by rw [hacc]
      _ = acc1 ⊔ (edgeTransfer e.val (outF1 e_mem) ⊔
            edgeTransfer e.val (outF2 e_mem)) := by rw [ll.join_assoc]
      _ = acc1 ⊔ edgeTransfer e.val (outF1 e_mem) := by rw [h_eT]

private lemma joinPredEdges_mono
    [Bot A] [Max A] [FiniteHeight A] [ll : LatticeLike A]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge -> A -> A)
    (edge_mono : ∀ e, mono_f (edgeTransfer e))
    (outF1 outF2 : StateN g A) (hle : StateN.le outF1 outF2) (n : NodeOf g) :
    (joinPredEdges g edgeTransfer outF1 n) ⊑ (joinPredEdges g edgeTransfer outF2 n) := by
  unfold joinPredEdges
  exact foldl_join_eT_mono g edgeTransfer edge_mono
    outF1 outF2 hle n (g.inEdges n.val).attach ⊥ ⊥ (ll.join_idem ⊥)

private lemma expectedIn_mono
    [Bot A] [Max A] [FiniteHeight A]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> A -> A) (edgeTransfer : Edge -> A -> A)
    (entryInit : A)
    [ll : LatticeLike A] [tm : TransferMono nodeTransfer edgeTransfer]
    (outF1 outF2 : StateN g A)
    (hle : StateN.le outF1 outF2) (n : NodeOf g) :
    (expectedIn g edgeTransfer entryInit outF1 n) ⊑
        (expectedIn g edgeTransfer entryInit outF2 n) := by
  simp only [expectedIn]
  split
  · exact ll.join_idem _
  · exact joinPredEdges_mono g edgeTransfer tm.edge_mono
      outF1 outF2 hle n

private lemma T_postfix_of_postfix
    [Bot A] [Max A] [FiniteHeight A]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node → A → A) (edgeTransfer : Edge → A → A)
    (entryInit : A) (f : StateN g A)
    [ll : LatticeLike A] [tm : TransferMono nodeTransfer edgeTransfer]
    (hpost : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit f) :
    IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit
      (fun n => nodeTransfer n.val (expectedIn g edgeTransfer entryInit f n)) := by
  intro n
  rw [ll.join_comm]
  apply tm.node_mono
  apply expectedIn_mono g nodeTransfer edgeTransfer entryInit f
    (fun m => nodeTransfer m.val (expectedIn g edgeTransfer entryInit f m))
  intro m
  simpa [ll.join_comm] using hpost m

/-! ## Main theorems -/

/-- the result of the worklist algorithm is always ⊑ the initial facts. -/
theorem worklistForward_mono
    [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> A -> A) (edgeTransfer : Edge -> A -> A)
    (entryInit : A) (outF : StateN g A) (wl : List (NodeOf g))
    [ll : LatticeLike A] :
    let res := worklistForward g nodeTransfer edgeTransfer entryInit outF wl
    StateN.le res outF := by
  induction outF, wl using worklistForward.induct g nodeTransfer edgeTransfer entryInit with
  | case1 o =>
    simp only [worklistForward, StateN.le]
    intro n; exact ll.join_idem _
  | case2 o n r nin nout hnout ih =>
    rw [worklistForward.eq_2, if_pos (by assumption)]
    exact ih
  | case3 o n r nin nout hnout o' wl' ih =>
    rw [worklistForward, if_neg (by assumption)]
    exact StateN.le_trans _ _ _ ih
      (StateN.le_update_join o n _)

/-- Generic invariant propagation combinator for the worklist algorithm.
    If a predicate `P` on `(outF, wl)` holds initially and is preserved by
    both the "unchanged" and "changed" branches, then `P (result, [])` holds. -/
private theorem worklistForward_invariant
    [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> A -> A) (edgeTransfer : Edge -> A -> A)
    (entryInit : A) (outF : StateN g A) (wl : List (NodeOf g))
    (P : StateN g A → List (NodeOf g) → Prop)
    (hinit : P outF wl)
    (hstep_same : ∀ (o : StateN g A) (n : NodeOf g) (rest : List (NodeOf g)),
      P o (n :: rest) →
      let newIn := if n.val = g.entry then entryInit else joinPredEdges g edgeTransfer o n
      o n ⊔ nodeTransfer n.val newIn = o n →
      P o rest)
    (hstep_changed : ∀ (o : StateN g A) (n : NodeOf g) (rest : List (NodeOf g)),
      P o (n :: rest) →
      let newIn := if n.val = g.entry then entryInit else joinPredEdges g edgeTransfer o n
      let newOut := o n ⊔ nodeTransfer n.val newIn
      ¬(newOut = o n) →
      P (o.update n newOut) (rest ++ g.succOf n)) :
    P (worklistForward g nodeTransfer edgeTransfer entryInit outF wl) [] := by
  induction outF, wl using worklistForward.induct g nodeTransfer edgeTransfer entryInit with
  | case1 o =>
    simp only [worklistForward]
    exact hinit
  | case2 o n r nin nout hnout ih =>
    rw [worklistForward.eq_2, if_pos (by assumption)]
    exact ih (hstep_same o n r hinit hnout)
  | case3 o n r nin nout hnout o' wl' ih =>
    rw [worklistForward, if_neg (by assumption)]
    exact ih (hstep_changed o n r hinit hnout)

/-- the result of the worklist algorithm is always a post-fixpoint -/
theorem worklistForward_sound_postfixpoint
    [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> A -> A) (edgeTransfer : Edge -> A -> A)
    (entryInit : A) (out0 : StateN g A) (wl0 : List (NodeOf g))
    [ll : LatticeLike A] [TransferMono nodeTransfer edgeTransfer]
    (hinv0 : ∀ m : NodeOf g, m ∉ wl0 →
      Eq
        ((nodeTransfer m.val (expectedIn g edgeTransfer entryInit out0 m)) ⊔ (out0 m))
        (out0 m)) :
    let res := worklistForward g nodeTransfer edgeTransfer entryInit out0 wl0
    IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit res := by
  let P : StateN g A → List (NodeOf g) → Prop := fun o wl =>
    ∀ m : NodeOf g, m ∉ wl →
      (nodeTransfer m.val (expectedIn g edgeTransfer entryInit o m)) ⊔ (o m) = (o m)
  intro res n
  refine worklistForward_invariant g nodeTransfer edgeTransfer entryInit
    out0 wl0 P hinv0 ?_ ?_ _ (by grind)
  · intros o n rest hP newIn ho m hmem
    by_cases hm : m = n <;> try grind
    subst hm
    have := newIn_eq_expectedIn g edgeTransfer entryInit o m newIn
      (by simp only [dite_eq_ite, newIn])
    simpa [ll.join_comm, <- this] using ho
  · intros o n rest hP newIn newOut hneq m hmem
    let t := (o n ⊔ nodeTransfer n.val
      (if n.val = g.entry then entryInit else joinPredEdges g edgeTransfer o n))
    have heexp := expectedIn_update_non_pred _ edgeTransfer o entryInit n t m
      (by grind)
    rw [heexp] at *
    by_cases hm : m = n
    · subst hm
      dsimp [newOut]
      simp [StateN.update, expectedIn, newIn]
      grind [ll.join_comm, ll.join_assoc, ll.join_idem]
    · have ho_m : StateN.update o n (o n ⊔ nodeTransfer n.val
        (if n.val = g.entry then entryInit else joinPredEdges g edgeTransfer o n)) m
        = o m := by dsimp [StateN.update]; exact if_neg hm
      rw [ho_m]
      grind [List.mem_cons.mp]

/-- Least post-fixpoint completeness, derived via the invariant combinator. -/
theorem worklistForward_complete_least_postfixpoint
    [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> A -> A) (edgeTransfer : Edge -> A -> A)
    (entryInit : A) (outF : StateN g A) (wl : List (NodeOf g))
    [ll : LatticeLike A] [tm : TransferMono nodeTransfer edgeTransfer]
    (post : StateN g A) (hpost : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit post)
    (hinv : StateN.le post outF) :
    let res := worklistForward g nodeTransfer edgeTransfer entryInit outF wl
    StateN.le post res := by
  let P : StateN g A → List (NodeOf g) → Prop := fun o _ => StateN.le post o
  apply worklistForward_invariant g nodeTransfer edgeTransfer entryInit outF wl P
    hinv (by grind)
  intros o m rest hP newIn hlub hneq n
  by_cases hmn : m = n
  · subst hmn
    have h_nT_mono := tm.node_mono m.val _ _ (
      expectedIn_mono g nodeTransfer edgeTransfer entryInit post o hP m
    )
    have := newIn_eq_expectedIn g edgeTransfer entryInit o m newIn rfl
    grind [StateN.update, hP m, hpost m, ll.join_comm, ll.join_assoc]
  · have : ¬(n = m) := by exact Ne.intro fun a ↦ hmn (id (Eq.symm a))
    simp only [StateN.update, this, ↓reduceIte]
    exact hP n

/-- Fixpoint soundness, derived via the invariant combinator. -/
theorem worklistForward_sound_fixpoint
    [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : AnalysisCFG Node Edge) (nodeTransfer : Node -> A -> A) (edgeTransfer : Edge -> A -> A)
    (entryInit : A) (out0 : StateN g A) (wl0 : List (NodeOf g))
    [ll : LatticeLike A] [tm : TransferMono nodeTransfer edgeTransfer]
    (hinv0 : ∀ m : NodeOf g, m ∉ wl0 →
      Eq ((nodeTransfer m.val (expectedIn g edgeTransfer entryInit out0 m)) ⊔ (out0 m)) (out0 m))
    (hbot : ∀ (n : NodeOf g) v, out0 n ⊔ v = v) :
    let res := worklistForward g nodeTransfer edgeTransfer entryInit out0 wl0
    IsForwardFixpoint g nodeTransfer edgeTransfer entryInit res := by
  intro res n
  have hpostres : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit res :=
    worklistForward_sound_postfixpoint g nodeTransfer edgeTransfer entryInit out0 wl0 hinv0
  have hpostT : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit
      (fun n => nodeTransfer n.val (expectedIn g edgeTransfer entryInit res n)) :=
    T_postfix_of_postfix g nodeTransfer edgeTransfer entryInit res hpostres
  have hbase : StateN.le (fun n => nodeTransfer n.val (expectedIn g edgeTransfer entryInit res n))
                out0 :=
    fun n => by simp only [ll.join_comm]; exact hbot n _
  have hleast : StateN.le (fun n => nodeTransfer n.val (expectedIn g edgeTransfer entryInit res n))
                res :=
    worklistForward_complete_least_postfixpoint g nodeTransfer edgeTransfer entryInit out0
      wl0 _ hpostT hbase
  grind [hleast n, hpostres n]

private lemma foldl_join_absorb
    [Bot A] [Max A] [FiniteHeight A] [ll : LatticeLike A]
    {α : Type} (f : α → A) (x : A) :
    ∀ (l : List α) (acc : A), acc ⊔ x = acc →
      (l.foldl (fun a y => a ⊔ f y) acc) ⊔ x =
        l.foldl (fun a y => a ⊔ f y) acc
  | [], acc, h => by simpa using h
  | hd :: tl, acc, h => by
    simp only [List.foldl_cons]
    apply foldl_join_absorb f x tl
    rw [ll.join_assoc, ll.join_comm (f hd) x, ← ll.join_assoc, h]

private lemma foldl_ge_of_mem
    [Bot A] [Max A] [FiniteHeight A] [ll : LatticeLike A]
    {α : Type} (f : α → A)
    (l : List α) (a : α) (ha : a ∈ l) (init : A) :
    (l.foldl (fun acc x => acc ⊔ f x) init) ⊑ f a := by
  induction l generalizing init with
  | nil => cases ha
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp ha with
    | inl heq =>
      subst heq
      apply foldl_join_absorb f (f a) tl
      rw [ll.join_assoc, ll.join_idem]
    | inr htl => exact ih htl _

private lemma joinPredEdges_ge_edge
    [Bot A] [Max A] [FiniteHeight A] [ll : LatticeLike A]
    (g : AnalysisCFG Node Edge) (edgeTransfer : Edge → A → A)
    (outF : StateN g A) (n : NodeOf g)
    (e : Edge) (he : e ∈ g.inEdges n.val) :
    (joinPredEdges g edgeTransfer outF n) ⊑
      edgeTransfer e (outF ⟨g.srcOf e, g.inEdges_src_mem n.val e he⟩) := by
  unfold joinPredEdges
  let f : {x // x ∈ g.inEdges n.val} → A := fun ⟨x, hx⟩ =>
    edgeTransfer x (outF ⟨g.srcOf x, g.inEdges_src_mem n.val x hx⟩)
  have ha : (⟨e, he⟩ : {x // x ∈ g.inEdges n.val}) ∈ (g.inEdges n.val).attach :=
    List.mem_attach _ _
  exact foldl_ge_of_mem f (g.inEdges n.val).attach ⟨e, he⟩ ha ⊥

end Flow.Analysis

namespace Flow.Analysis

/-- Bridge: isForwardFixpoint to Generic.PostFixpoint -/
theorem postFixpoint_of_isForwardPostFixpoint
    {A : Type} [Bot A] [Max A] [FiniteHeight A] [ll : LatticeLike A]
    (g : CFG) (G : AnalysisCFG NodeID Edge)
    (hnodes : ∀ n, n ∈ G.nodes ↔ n < g.nodes.length)
    (hedges : G.edges = g.edges)
    (hentry : G.entry = g.entry)
    (hsrcOf : ∀ e : Edge, G.srcOf e = e.src)
    (hinEdges : ∀ n (e : Edge), e ∈ G.inEdges n ↔ e ∈ g.edges ∧ e.dst = n)
    (nodeTransfer : NodeID → A → A) (edgeTransfer : Edge → A → A)
    [tm : TransferMono nodeTransfer edgeTransfer]
    (entryInit : A) (outF : StateN G A)
    (hpost : IsForwardPostFixpoint G nodeTransfer edgeTransfer entryInit outF)
    (hno_entry_edge : ∀ e ∈ g.edges, e.dst ≠ g.entry) :
    Generic.PostFixpoint
      ({ L := A
       , nodeTransfer := fun _ n a => nodeTransfer n a
       , edgeTransfer := fun _ e a => edgeTransfer e a
       , entry := fun _ => entryInit } : Generic.DFA)
      (fun a b => b ⊑ a) g
      (fun n =>
        if h : n ∈ G.nodes then
          expectedIn G edgeTransfer entryInit outF ⟨n, h⟩
        else ⊥) := by
  intro e he hsrc hdst
  have hsrc_mem : e.src ∈ G.nodes := (hnodes e.src).mpr hsrc
  have hdst_mem : e.dst ∈ G.nodes := (hnodes e.dst).mpr hdst
  let m_src : NodeOf G := ⟨e.src, hsrc_mem⟩
  let m_dst : NodeOf G := ⟨e.dst, hdst_mem⟩
  change (if h : e.dst ∈ G.nodes then expectedIn G edgeTransfer entryInit outF ⟨e.dst, h⟩
          else ⊥)
         ⊑ edgeTransfer e (nodeTransfer e.src
              (if h : e.src ∈ G.nodes then expectedIn G edgeTransfer entryInit outF ⟨e.src, h⟩
               else ⊥))
  rw [dif_pos hsrc_mem, dif_pos hdst_mem]
  have h_dst_ne : m_dst.val ≠ G.entry := by
    rw [hentry]; exact hno_entry_edge e he
  have h_expIn_dst : expectedIn G edgeTransfer entryInit outF m_dst
                  = joinPredEdges G edgeTransfer outF m_dst := by
    simp [expectedIn, h_dst_ne]
  rw [show
        (expectedIn G edgeTransfer entryInit outF ⟨e.dst, hdst_mem⟩)
          = joinPredEdges G edgeTransfer outF m_dst from h_expIn_dst]
  have h_node : outF m_src ⊑
                  nodeTransfer e.src (expectedIn G edgeTransfer entryInit outF m_src) := by
    have h := hpost m_src
    change outF m_src ⊔ _ = outF m_src
    rw [ll.join_comm]; exact h
  have h_edge : edgeTransfer e (outF m_src) ⊑
                edgeTransfer e
                  (nodeTransfer e.src (expectedIn G edgeTransfer entryInit outF m_src)) :=
    tm.edge_mono e _ _ h_node
  have he_in : e ∈ G.inEdges m_dst.val :=
    (hinEdges m_dst.val e).mpr ⟨hedges ▸ he, rfl⟩
  have h_outF_eq : outF ⟨G.srcOf e, G.inEdges_src_mem m_dst.val e he_in⟩ = outF m_src := by
    apply congrArg outF
    apply Subtype.ext
    change G.srcOf e = e.src
    exact hsrcOf e
  have h_join_ge :
      joinPredEdges G edgeTransfer outF m_dst ⊑ edgeTransfer e (outF m_src) := by
    have h := joinPredEdges_ge_edge G edgeTransfer outF m_dst e he_in
    rw [h_outF_eq] at h
    exact h
  exact join_ge_trans _ _ _ h_join_ge h_edge

end Flow.Analysis
