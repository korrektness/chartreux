import Flow.TIP.Eval
import Flow.TIP.Big.CFG
import Flow.TIP.Big.Correspondence.Refinement

namespace Flow.Eval.Big.Located

open Flow.Eval.Big.Refinement
open BigCFGBuilder

mutual
inductive LocatedAt (g : BigCFG) : BigNodeID -> CEK -> Prop where
| at_skip {n E K} :
    g.nodeKind n = some (.SEntry .Skip) ->
    KontMatches g K n E ->
    LocatedAt g n ⟨.inl .Skip, E, K⟩
| at_assign {n m x e K E} :
    g.nodeKind n = some (.SEntry (.Assign x e)) ->
    g.hasEdge n m .Normal ->
    LocatedAt g m ⟨.inr e, E, .AssignK x :: K⟩ ->
    KontMatches g K n E ->
    LocatedAt g n ⟨.inl (.Assign x e), E, K⟩
| at_declare {n m x e K E} :
    g.nodeKind n = some (.SEntry (.Decl x e)) ->
    g.hasEdge n m .Normal ->
    LocatedAt g m ⟨.inr e, E, .DeclK x :: K⟩ ->
    KontMatches g K n E ->
    LocatedAt g n ⟨.inl (.Decl x e), E, K⟩
| at_if {n m c t e K E} :
    g.nodeKind n = some (.SEntry (.If c t e)) ->
    g.hasEdge n m .Normal ->
    g.nodeKind m = some (.EEntry c) ->
    KontMatches g K n E ->
    LocatedAt g n ⟨.inl (.If c t e), E, K⟩
| at_while {n m c b K E} :
    g.nodeKind n = some (.SEntry (.While c b)) ->
    g.hasEdge n m .Normal ->
    g.nodeKind m = some (.EEntry c) ->
    KontMatches g K n E ->
    LocatedAt g n ⟨.inl (.While c b), E, K⟩
| at_seq {n s₁ s₂ K E} :
    LocatedAt g n ⟨.inl s₁, E, .SeqK s₂ :: K⟩ ->
    LocatedAt g n ⟨.inl (.Seq s₁ s₂), E, K⟩
| at_sexit {n K E} :
    g.nodeKind n = some (.SExit) ->
    KontMatches g K n E ->
    LocatedAt g n ⟨.inl .Skip, E, K⟩
| at_expr {n m e E K} :
    g.nodeKind n = some (.EEntry e) ->
    g.hasEdge n m .Normal ->
    g.nodeKind m = some (.EExit) ->
    KontMatches g K n E ->
    KontMatches g K m E ->
    LocatedAt g n ⟨.inr e, E, K⟩
| at_eexit {n K E v} :
    g.nodeKind n = some (.EExit) ->
    KontMatches g K n E ->
    LocatedAt g n ⟨.inr (.Int v), E, K⟩

-- continuation matches current state
inductive KontMatches (g : BigCFG) : List Cont -> NodeID -> State -> Prop where
  | nil {n E} : KontMatches g [] n E
  | seqK {n m s₂ E K} :
      g.hasEdge n m .Normal ->
      LocatedAt g m ⟨.inl s₂, E, K⟩ ->
      KontMatches g (.SeqK s₂ :: K) n E
  | assignK {n m x v E K} :
      g.hasEdge n m .Normal ->
      g.nodeKind m = some (.SEntry .Skip) ->
      KontMatches g K m (E.updated x v) ->
      KontMatches g (.AssignK x :: K) n E
  | declK {n m x v E K} :
      g.hasEdge n m .Normal ->
      g.nodeKind m = some (.SEntry .Skip) ->
      KontMatches g K m (E.updated x v) ->
      KontMatches g (.DeclK x :: K) n E
  | ifKT {n t nT E K f} :
      g.hasEdge n nT .TBranch ->
      LocatedAt g nT ⟨.inl t, E, K⟩ ->
      KontMatches g (.IfK t f :: K) n E
  | ifKF {n t nF E K f} :
      g.hasEdge n nF .TBranch ->
      LocatedAt g nF ⟨.inl f, E, K⟩ ->
      KontMatches g (.IfK t f :: K) n E
  | whileKT {n nT c b E K} :
      g.hasEdge n nT .TBranch ->
      LocatedAt g nT ⟨.inl b, E, .WhileBackK c b :: K⟩ ->
      KontMatches g (.WhileK c b :: K) n E
  | whileKF {n nF c b E K} :
      g.hasEdge n nF .FBranch ->
      LocatedAt g nF ⟨.inl b, E, .WhileBackK c b :: K⟩ ->
      KontMatches g (.WhileK c b :: K) n E
  | whileBackK {n nc c b E K} :
      g.hasEdge n nc .Normal ->
      LocatedAt g nc ⟨.inl (.While c b), E, K⟩ ->
      KontMatches g (.WhileBackK c b :: K) n E
  | skipBridge {n m E K} :
      g.nodeKind n = some (.SEntry .Skip) ->
      g.nodeKind m = some (.SEntry .Skip) ->
      g.hasEdge n m .Normal ->
      KontMatches g K m E ->
      KontMatches g K n E
  | binOpLK {n o ne₂ e₂ E K} :
      g.hasEdge n ne₂ .Normal ->
      KontMatches g K ne₂ E ->
      KontMatches g (.BinOpLK o e₂ :: K) n E
  | binOpRK {n v o nex E K} :
      g.hasEdge n nex .Normal ->
      KontMatches g K nex E ->
      KontMatches g (.BinOpRK v o :: K) n E
end

private lemma nodeKind_lt {g : BigCFG} {n k}
    (h : g.nodeKind n = some k) : n < g.nodes.length := by
  unfold BigCFG.nodeKind at h; grind

theorem LocatedAt.bound {g : BigCFG} {n σ}
    (h : LocatedAt g n σ) : n < g.nodes.length := by
  induction h using LocatedAt.rec (motive_2 := fun _ _ _ _ => True) <;>
    first
    | trivial
    | (expose_names; exact nodeKind_lt h) -- ew

theorem step_decorate {g : BigCFG} {n : BigNodeID} {σ σ' : CEK}
    (hloc : LocatedAt g n σ) (hstep : Step σ σ') :
    ∃ (n' : NodeID) (h : n < g.nodes.length) (h' : n' < g.nodes.length),
      BigStepsN g h σ h' σ' ∧ LocatedAt g n' σ' := by
  have hn := hloc.bound
  cases hstep with
  | @SeqEnter s₁ s₂ E K =>
    cases hloc
    case _ hloc =>
    refine ⟨n, hn, hn, ?_, hloc⟩
    apply BigStepsN.single
    grind [BigStepN.stutter, Step.SeqEnter]
  | @SeqMid s₁ s₂ E =>
    cases hloc with
    | at_skip hk hmatch =>
      cases hmatch with
      | seqK hedge hloc' =>
        refine ⟨_, hn, hloc'.bound, ?_, ?_⟩
        · apply BigStepsN.single
          grind [BigStepN.advance, Step.SeqMid]
        · exact hloc'
      | @skipBridge _ m _ _ hk' hk'' hedge ih =>
        refine ⟨m, hn, nodeKind_lt hk'', ?_, ?_⟩
        · sorry
        · sorry
    | at_sexit =>
      sorry
  | @Decl x e E K =>
    cases hloc
    case _ m he hk hmatch hloc =>
    cases hloc with
    | at_expr hm hmatch' =>
      have := nodeKind_lt hm
      refine ⟨m, hn, this, ?_, ?_⟩
      · apply BigStepsN.single
        grind [BigStepN.advance, Step.Decl]
      · constructor <;> assumption
    | @at_eexit _ _ _ v hm hmatch =>
      have := nodeKind_lt hm
      refine ⟨m, hn, this, ?_, ?_⟩
      · apply BigStepsN.single
        grind [BigStepN.advance, Step.Decl]
      · exact LocatedAt.at_eexit hm hmatch
  | @Assign x e E K =>
    cases hloc
    case _ m hedge hk hmatch hloc =>
    cases hloc with
    | @at_expr _ m' _ _ _ hm he hm' hmatch' hmatch'' =>
      have := nodeKind_lt hm
      refine ⟨m, hn, this, ?_, ?_⟩
      · apply BigStepsN.single
        grind [BigStepN.advance, Step.Assign]
      · exact LocatedAt.at_expr hm he hm' hmatch' hmatch''
    | @at_eexit _ _ _ v hm hmatch =>
      have := nodeKind_lt hm
      refine ⟨m, hn, this, ?_, ?_⟩
      · apply BigStepsN.single
        grind [BigStepN.advance, Step.Assign]
      · exact LocatedAt.at_eexit hm hmatch
  | @DeclD v E x K =>
    sorry
  | @AssignD v E x K =>
    sorry
  | @Var E x K v henv =>
    cases hloc
    case at_expr m hm he hk hmatch hmatch' =>
    have := nodeKind_lt hm
    refine ⟨m, hn, this, ?_, ?_⟩
    · apply BigStepsN.single
      grind [BigStepN.advance, Step.Var]
    · exact LocatedAt.at_eexit hm hmatch
  | _ => sorry




end Flow.Eval.Big.Located
