From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh.
From SST Require Import lemma.inversion lemma.inversion_expr lemma.substitution_helper lemma.substitution.

Lemma triv_pt_p : forall p q x0,
    wfgC (gtt_send p q x0) -> 
    isgPartsC p (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. destruct H1.
  unfold isgPartsC in *.
  pinversion H; try easy. 
  - subst. exists (g_send p q xs). split. pfold. easy. split. easy. constructor.
  - subst. specialize(guard_breakG G H1); intros. 
    destruct H5. destruct H5. destruct H6.
   
    destruct H7.
    - subst. 
      specialize(gttTC_after_subst (g_rec G) g_end (gtt_send p q x0) H5); intros.
      assert(gttTC g_end (gtt_send p q x0)). 
      apply H7. pfold. easy. pinversion H8. 
      apply gttT_mon.
    destruct H7. destruct H7. destruct H7.
    - subst.
      specialize(gttTC_after_subst (g_rec G) (g_send x1 x2 x3) (gtt_send p q x0) H5); intros.
      assert(gttTC (g_send x1 x2 x3) (gtt_send p q x0)).
      apply H7. pfold. easy.
      pinversion H8. subst.
      exists (g_send p q x3). split; try easy. pfold. easy. split. easy.
      constructor.
    apply gttT_mon.
    apply gttT_mon.
Qed.

Lemma triv_pt_q : forall p q x0,
    wfgC (gtt_send p q x0) -> 
    isgPartsC q (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. destruct H1.
  unfold isgPartsC in *.
  pinversion H; try easy. 
  - subst. exists (g_send p q xs). split. pfold. easy. constructor. easy. constructor.
  - subst. specialize(guard_breakG G H1); intros. 
    destruct H5. destruct H5. destruct H6.
   
    destruct H7.
    - subst. 
      specialize(gttTC_after_subst (g_rec G) g_end (gtt_send p q x0) H5); intros.
      assert(gttTC g_end (gtt_send p q x0)). 
      apply H7. pfold. easy. pinversion H8. 
      apply gttT_mon.
    destruct H7. destruct H7. destruct H7.
    - subst.
      specialize(gttTC_after_subst (g_rec G) (g_send x1 x2 x3) (gtt_send p q x0) H5); intros.
      assert(gttTC (g_send x1 x2 x3) (gtt_send p q x0)).
      apply H7. pfold. easy.
      pinversion H8. subst.
      exists (g_send p q x3). split; try easy. pfold. easy. 
      split. easy. constructor.
    apply gttT_mon.
    apply gttT_mon.
Qed.

Lemma triv_pt_p_s : forall p q x0,
    wfgCw (gtt_send p q x0) -> 
    isgPartsC p (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. pose proof H1 as H2.
  unfold isgPartsC in *.
  pinversion H; try easy. 
  - subst. exists (g_send p q xs). split. pfold. easy. split. easy. constructor.
  - subst. specialize(guard_breakG G H1); intros. 
    destruct H5. destruct H5. destruct H6.
   
    destruct H7.
    - subst. 
      specialize(gttTC_after_subst (g_rec G) g_end (gtt_send p q x0) H5); intros.
      assert(gttTC g_end (gtt_send p q x0)). 
      apply H7. pfold. easy. pinversion H8. 
      apply gttT_mon.
    destruct H7. destruct H7. destruct H7.
    - subst.
      specialize(gttTC_after_subst (g_rec G) (g_send x1 x2 x3) (gtt_send p q x0) H5); intros.
      assert(gttTC (g_send x1 x2 x3) (gtt_send p q x0)).
      apply H7. pfold. easy.
      pinversion H8. subst.
      exists (g_send p q x3). split; try easy. pfold. easy. split. easy.
      constructor.
    apply gttT_mon.
    apply gttT_mon.
Qed.

Lemma triv_pt_q_s : forall p q x0,
    wfgCw (gtt_send p q x0) -> 
    isgPartsC q (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. pose proof H1 as H2.
  unfold isgPartsC in *.
  pinversion H; try easy. 
  - subst. exists (g_send p q xs). split. pfold. easy. constructor. easy. constructor.
  - subst. specialize(guard_breakG G H1); intros. 
    destruct H5. destruct H5. destruct H6.
   
    destruct H7.
    - subst. 
      specialize(gttTC_after_subst (g_rec G) g_end (gtt_send p q x0) H5); intros.
      assert(gttTC g_end (gtt_send p q x0)). 
      apply H7. pfold. easy. pinversion H8. 
      apply gttT_mon.
    destruct H7. destruct H7. destruct H7.
    - subst.
      specialize(gttTC_after_subst (g_rec G) (g_send x1 x2 x3) (gtt_send p q x0) H5); intros.
      assert(gttTC (g_send x1 x2 x3) (gtt_send p q x0)).
      apply H7. pfold. easy.
      pinversion H8. subst.
      exists (g_send p q x3). split; try easy. pfold. easy. 
      split. easy. constructor.
    apply gttT_mon.
    apply gttT_mon.
Qed.

Lemma isgParts_xs : forall [s s' x o p],
    isgParts p (g_send s s' x) ->
    isgParts p (g_send s s' (o :: x)).
Proof.
  intros. inversion H. subst. 
  constructor. 
  subst. constructor.
  subst. apply pa_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
Qed.

Lemma isgParts_x : forall [s s' x s0 g p],
    isgParts p g -> 
    isgParts p (g_send s s' (Some (s0, g) :: x)).
Proof.
    intros.
    - case_eq (eqb p s); intros.
      assert (p = s). apply eqb_eq; try easy. subst. apply pa_sendp.
    - case_eq (eqb p s'); intros.
      assert (p = s'). apply eqb_eq; try easy. subst. apply pa_sendq.
    - assert (p <> s). apply eqb_neq; try easy. 
      assert (p <> s'). apply eqb_neq; try easy.
      apply pa_sendr with (n := 0) (s := s0) (g := g); try easy.
Qed.

Lemma isgParts_depth_exists : forall r Gl,
    isgParts r Gl -> exists n, isgParts_depth n r Gl.
Proof.
  induction Gl using global_ind_ref; intros; try easy.
  inversion H0.
  - subst. exists 0. constructor.
  - subst. exists 0. constructor.
  - subst. 
    specialize(some_onth_implies_In n lis (s, g) H7); intros.
    specialize(Forall_forall (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (isgParts r g -> exists n : fin, isgParts_depth n r g))) lis); intros.
    destruct H2. specialize(H2 H). clear H H3.
    specialize(H2 (Some (s, g)) H1).
    destruct H2; try easy. destruct H. destruct H. destruct H. inversion H. subst. clear H.
    specialize(H2 H8). destruct H2.
    exists (S x1). apply dpth_c with (s := x) (g := x0) (k := n); try easy.
  - inversion H. subst. specialize(IHGl H2). destruct IHGl. exists (S x). constructor. easy.
Qed.

Lemma isgParts_depth_back : forall G n r,
      isgParts_depth n r G -> isgParts r G.
Proof.
  induction G using global_ind_ref; intros; try easy.
  inversion H0. 
  - subst. constructor.
  - subst. constructor.
  - subst. 
    specialize(some_onth_implies_In k lis (s, g) H8); intros.
    specialize(Forall_forall (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (forall (n : fin) (r : string),
           isgParts_depth n r g -> isgParts r g))) lis); intros.
    destruct H2. specialize(H2 H). clear H H3.
    specialize(H2 (Some (s, g)) H1). destruct H2; try easy. destruct H. destruct H. destruct H.
    inversion H. subst.
    specialize(H2 n0 r H9). 
    apply pa_sendr with (n := k) (s := x) (g := x0); try easy.
  inversion H. subst.
  - specialize(IHG n0 r H3). constructor. easy.
Qed.


Lemma subst_parts_helper : forall k0 xs s g0 r n0 lis m n g,
      onth k0 xs = Some (s, g0) -> 
      isgParts_depth n0 r g0 ->
      Forall2
       (fun u v : option (sort * global) =>
        u = None /\ v = None \/
        (exists (s : sort) (g0 g' : global),
           u = Some (s, g0) /\ v = Some (s, g') /\ subst_global m n (g_rec g) g0 g')) xs lis -> 
      Forall
      (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (forall (m n k : fin) (r : string) (g0 g' : global),
           isgParts_depth k r g' -> subst_global m n (g_rec g0) g' g -> isgParts_depth k r g))) lis -> 
      exists g', onth k0 lis = Some (s, g') /\ isgParts_depth n0 r g'.
Proof.
  induction k0; intros; try easy.
  - destruct xs; try easy.
    simpl in H. subst. destruct lis; try easy. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    clear H4 H7. destruct H5; try easy. destruct H. destruct H. destruct H. destruct H.
    destruct H1. inversion H. subst.
    destruct H3; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
    specialize(H3 m n n0 r g x0 H0 H2).
    exists x3. split; try easy.
  - destruct xs; try easy. destruct lis; try easy. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    specialize(IHk0 xs s g0 r n0 lis m n g). apply IHk0; try easy.
Qed.

Lemma subst_parts_depth : forall m n k r g g' Q,
      subst_global m n (g_rec g) g' Q -> 
      isgParts_depth k r g' -> 
      isgParts_depth k r Q.
Proof.
  intros. revert H0 H. revert m n k r g g'.
  induction Q using global_ind_ref; intros; try easy.
  inversion H.
  - subst. inversion H0; try easy.
  - subst. inversion H0; try easy. 
  - subst. inversion H0; try easy.
  - inversion H. subst. inversion H0. 
  - inversion H1. subst.
    inversion H0. 
    - subst. constructor.
    - subst. constructor.
    - subst. 
      specialize(subst_parts_helper k0 xs s g0 r n0 lis m n g H10 H11 H7 H); intros. 
      destruct H2. destruct H2.
      apply dpth_c with (n := n0) (s := s) (g := x) (k := k0); try easy.
  - inversion H. subst. inversion H0. 
  - subst. inversion H0. subst.
    constructor. specialize(IHQ m.+1 n.+1 n0 r g P). apply IHQ; try easy.
Qed.

Lemma part_after_step_helper : forall G1 q p x0,
    gttTC G1 (gtt_send q p x0) -> 
    (forall n : fin, exists m : fin, guardG n m G1) -> 
    exists ys, gttTC (g_send q p ys) (gtt_send q p x0) /\ (forall n : fin, exists m : fin, guardG n m (g_send q p ys)).
Proof.
  intros. pinversion H; try easy. subst.
  - exists xs. split. pfold. easy. easy.
  - subst. specialize(guard_breakG G H0); intros.
    destruct H3. destruct H3. destruct H4.
    specialize(gtt_after_betaL (g_rec G) x (gtt_send q p x0)); intros.
    assert(gttTC x (gtt_send q p x0)). 
    apply H6; try easy. pfold. easy.
    destruct H5. pinversion H7; try easy. subst. easy. subst. easy.
    apply gttT_mon.
    destruct H5. destruct H5. destruct H5. subst.
    pinversion H7; try easy. subst. exists x3. split. pfold. easy. easy.
    apply gttT_mon.
    apply gttT_mon.
Qed.

Lemma part_break_s : forall G pt, 
    isgPartsC pt G -> 
    exists Gl, gttTC Gl G /\ isgParts pt Gl /\ (Gl = g_end \/ exists p q lis, Gl = g_send p q lis).
Proof.
  intros. pose proof H as H0.
  unfold isgPartsC in H0. destruct H0. destruct H0.
  rename x into Gl. destruct H1.
  specialize(isgParts_depth_exists pt Gl H2); intros. destruct H3. rename x into n.
  
  clear H.
  clear H2.
  revert H3 H0 H1. revert G pt Gl.
  induction n; intros; try easy.
  - inversion H3. subst.
    exists (g_send pt q lis). split. easy. split. constructor. right. exists pt. exists q. exists lis. easy.
  - subst.
    exists (g_send p pt lis). split. easy. split. constructor. right. exists p. exists pt. exists lis. easy.
  - inversion H3. subst.
    pinversion H0. subst.
    specialize(subst_parts_depth 0 0 n pt g g Q H4 H2); intros.
    apply IHn with (Gl := Q); try easy.
    - intros. specialize(H1 n0). destruct H1. 
      inversion H1. exists 0. constructor.
      subst. exists m. specialize(subst_injG 0 0 (g_rec g) g Q Q0 H7 H4); intros. subst. easy.
    apply gttT_mon.
  - subst. 
    exists (g_send p q lis). split. easy.
    split.
    apply pa_sendr with (n := k) (s := s) (g := g); try easy.
    apply isgParts_depth_back with (n := n); try easy.
    right. exists p. exists q. exists lis. easy.
Qed.

Lemma part_break_s2 : forall G pt, 
    isgPartsC pt G -> 
    exists Gl, gttTC Gl G /\ isgParts pt Gl /\ (forall n : fin, exists m : fin, guardG n m Gl) /\ (Gl = g_end \/ exists p q lis, Gl = g_send p q lis).
Proof.
  intros. pose proof H as H0.
  unfold isgPartsC in H0. destruct H0. destruct H0.
  rename x into Gl. destruct H1.
  specialize(isgParts_depth_exists pt Gl H2); intros. destruct H3. rename x into n.
  
  clear H.
  clear H2.
  revert H3 H0 H1. revert G pt Gl.
  induction n; intros; try easy.
  - inversion H3. subst.
    exists (g_send pt q lis). split. easy. split. constructor. split. easy. right. exists pt. exists q. exists lis. easy.
  - subst.
    exists (g_send p pt lis). split. easy. split. constructor. split. easy. right. exists p. exists pt. exists lis. easy.
  - inversion H3. subst.
    pinversion H0. subst.
    specialize(subst_parts_depth 0 0 n pt g g Q H4 H2); intros.
    apply IHn with (Gl := Q); try easy.
    - intros. specialize(H1 n0). destruct H1. 
      inversion H1. exists 0. constructor.
      subst. exists m. specialize(subst_injG 0 0 (g_rec g) g Q Q0 H7 H4); intros. subst. easy.
    apply gttT_mon.
  - subst. 
    exists (g_send p q lis). split. easy.
    split.
    apply pa_sendr with (n := k) (s := s) (g := g); try easy.
    apply isgParts_depth_back with (n := n); try easy. split. easy.
    right. exists p. exists q. exists lis. easy.
Qed.

Lemma part_break : forall G pt,
    wfgC G -> 
    isgPartsC pt G -> 
    exists Gl, gttTC Gl G /\ isgParts pt Gl /\ (forall n : fin, exists m : fin, guardG n m Gl) /\ (Gl = g_end \/ exists p q lis, Gl = g_send p q lis).
Proof.
  intros. 
  unfold isgPartsC in H0. destruct H0. destruct H0.
  rename x into Gl. destruct H1.
  specialize(isgParts_depth_exists pt Gl H2); intros. destruct H3. rename x into n.
  
  clear H.
  clear H2.
  revert H3 H0 H1. revert G pt Gl.
  induction n; intros; try easy.
  - inversion H3. subst.
    exists (g_send pt q lis). split. easy. split. constructor. split. easy. right. exists pt. exists q. exists lis. easy.
  - subst.
    exists (g_send p pt lis). split. easy. split. constructor. split. easy. right. exists p. exists pt. exists lis. easy.
  - inversion H3. subst.
    pinversion H0. subst.
    specialize(subst_parts_depth 0 0 n pt g g Q H4 H2); intros.
    apply IHn with (Gl := Q); try easy.
    - intros. specialize(H1 n0). destruct H1. 
      inversion H1. exists 0. constructor.
      subst. exists m. specialize(subst_injG 0 0 (g_rec g) g Q Q0 H7 H4); intros. subst. easy.
    apply gttT_mon.
  - subst. 
    exists (g_send p q lis). split. easy.
    split.
    apply pa_sendr with (n := k) (s := s) (g := g); try easy.
    apply isgParts_depth_back with (n := n); try easy. split. easy.
    right. exists p. exists q. exists lis. easy.
Qed.


Lemma part_betaG : forall G G' pt, multiS betaG G G' -> isgParts pt G -> isgParts pt G'.
Proof.
  intros.
  specialize(isgParts_depth_exists pt G H0); intros. destruct H1 as (n, H1). clear H0.
  revert H1. revert pt n.
  induction H; intros.
  - inversion H. subst.
    inversion H1. subst.
    specialize(subst_parts_depth 0 0 n0 pt G G y H0 H5); intros.
    specialize(isgParts_depth_back y n0 pt H2); intros. easy.
  - inversion H. subst.
    inversion H1. subst.
    specialize(subst_parts_depth 0 0 n0 pt G G y H2 H6); intros.
    specialize(isgParts_depth_back y n0 pt H3); intros.
    specialize(isgParts_depth_exists pt y H4); intros. destruct H5 as (n1, H5).
    specialize(IHmultiS pt n1). apply IHmultiS; try easy.
Qed.

Lemma subst_after_incrG_b : forall G G' m n pt,
    isgParts pt G' -> incr_freeG m n G = G' -> isgParts pt G.
Proof.
  induction G using global_ind_ref; intros; try easy.
  - subst. inversion H; try easy.
  - subst. inversion H; try easy.
  - subst. 
    inversion H0; try easy. subst. constructor. subst. constructor.
    subst.
    assert(exists g', onth n0 lis = Some(s, g') /\ g = incr_freeG m n g').
    {
      clear H8 H6 H4 H0 H. revert H7. revert lis.
      induction n0; intros; try easy. destruct lis; try easy. simpl in H7.
      destruct o; try easy. destruct p0; try easy. inversion H7. subst.
      exists g0. easy.
      destruct lis; try easy. specialize(IHn0 lis H7). apply IHn0; try easy.
    }
    destruct H1 as (g1,(Ha,Hb)). 
    specialize(Forall_forall (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (forall (G' : global) (m n : fin) (pt : string),
           isgParts pt G' -> incr_freeG m n g = G' -> isgParts pt g))) lis); intros.
    destruct H1. specialize(H1 H). clear H2 H.
    specialize(some_onth_implies_In n0 lis (s, g1) Ha); intros.
    specialize(H1 (Some (s, g1)) H). destruct H1; try easy. 
    destruct H1 as (s0,(g2,(Hd,He))). inversion Hd. subst.
    specialize(He (incr_freeG m n g2) m n pt).
    apply pa_sendr with (n := n0) (s := s0) (g := g2); try easy. 
    apply He; try easy.
  - subst. inversion H. subst.
    specialize(IHG (incr_freeG m.+1 n G) (S m) n pt). 
    constructor. apply IHG; try easy.
Qed.

Lemma subst_part_b : forall m n G G1 G2 pt,
    isgParts pt G2 -> 
    subst_global m n G G1 G2 -> 
    (isgParts pt G \/ isgParts pt G1).
Proof.
  intros. revert H0 H. revert pt m n G G1.
  induction G2 using global_ind_ref; intros; try easy.
  - inversion H0.
    - subst. left.
      specialize(subst_after_incrG_b G (g_send p q lis) 0 n pt); intros.
      apply H2; try easy.
    - subst.
      inversion H1.
      - subst. right. constructor.
      - subst. right. constructor.
      subst.
      revert H10 H9 H8 H5 H7 H. clear H0 H1.
      revert p q lis pt m n G xs s g.
      induction n0; intros; try easy.
      - destruct lis; try easy. destruct xs; try easy. 
        inversion H7. subst. clear H7. inversion H. subst. clear H.
        simpl in H9. subst. 
        destruct H3; try easy. destruct H as (s0,(g1,(g2,(Ha,(Hb,Hc))))). inversion Hb. subst.
        destruct H2; try easy. destruct H as (s1,(g3,(Hd,He))). inversion Hd. subst.
        specialize(He pt m n G g1 Hc H10).
        destruct He. left. easy.
        right. apply pa_sendr with (n := 0) (s := s1) (g := g1); try easy.
      - destruct lis; try easy. destruct xs; try easy. 
        inversion H7. subst. clear H7. inversion H. subst. clear H.
        specialize(IHn0 p q lis pt m n G xs s g).
        assert(isgParts pt G \/ isgParts pt (g_send p q xs)). apply IHn0; try easy.
        destruct H. left. easy.
        right. inversion H; try easy. subst. easy. subst. easy.
        subst.
        apply pa_sendr with (n := S n1) (s := s0) (g := g0); try easy.
    - inversion H0. subst.
      - specialize(subst_after_incrG_b G (g_rec G2) 0 n pt); intros.
        left. apply H1; try easy.
      - subst. inversion H. subst.
        specialize(IHG2 pt (S m) (S n) G P H6 H3). 
        destruct IHG2. left. easy. right. constructor. easy.
Qed.

Lemma part_betaG_b : forall G G' pt, multiS betaG G G' -> isgParts pt G' -> isgParts pt G.
Proof.
  intros.
  specialize(isgParts_depth_exists pt G' H0); intros. destruct H1 as (n, H1). clear H0.
  revert H1. revert pt n.
  induction H; intros.
  - inversion H. subst.
    specialize(subst_parts_depth 0 0 n pt G G y H0); intros.
    specialize(subst_part_b 0 0 (g_rec G) G y pt); intros.
    specialize(isgParts_depth_back y n pt H1); intros.
    constructor.
    assert(isgParts pt (g_rec G) \/ isgParts pt G). apply H3; try easy.
    destruct H5; try easy. inversion H5; try easy.
  - inversion H. subst.
    specialize(IHmultiS pt n H1). clear H1 H0 H.
    specialize(subst_part_b 0 0 (g_rec G) G y pt); intros. 
    assert(isgParts pt (g_rec G) \/ isgParts pt G).
    apply H; try easy. destruct H0; try easy. constructor; try easy.
Qed.

Lemma guardG_betaG : forall G G1,
          (forall n : fin, exists m : fin, guardG n m G) -> 
          multiS betaG G G1 -> 
          (forall n : fin, exists m : fin, guardG n m G1).
Proof.  
  intros. revert n. revert H. 
  induction H0; intros; try easy.
  - inversion H. subst.
    specialize(H0 n). destruct H0. inversion H0. subst. exists 0. constructor.
    subst. specialize(subst_injG 0 0 (g_rec G) G y Q H3 H1); intros. subst. exists m. easy.
  - revert n. apply IHmultiS. clear IHmultiS H0.
    inversion H. subst. intros.
    specialize(H1 n). destruct H1. inversion H1. exists 0. constructor.
    subst. specialize(subst_injG 0 0 (g_rec G) G y Q H3 H0); intros. subst. exists m. easy.
Qed.

Lemma decidable_isgPartsC_helper : forall k lis s g ys xs,
          onth k lis = Some (s, g) -> 
          Forall2
           (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
            u = None /\ v = None \/
            (exists (s : sort) (g : global) (g' : gtt),
               u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) lis ys ->
          Forall
           (fun u : option (sort * global) =>
            u = None \/
            (exists (s : sort) (g : global),
               u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) lis ->
          Forall2
           (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
            u = None /\ v = None \/
            (exists (s : sort) (g : global) (g' : gtt),
               u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) xs ys ->
          Forall
           (fun u : option (sort * global) =>
            u = None \/
            (exists (s : sort) (g : global),
               u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) xs -> 
          exists g' g'', onth k ys = Some(s, g') /\ gttTC g g' /\
          (forall n : fin, exists m : fin, guardG n m g) /\
          onth k xs = Some(s, g'') /\ gttTC g'' g' /\ 
          (forall n : fin, exists m : fin, guardG n m g'').
Proof.
  induction k; intros; try easy.
  - destruct lis; try easy. destruct ys; try easy. destruct xs; try easy.
    inversion H0. subst. clear H0. inversion H2. subst. clear H2.
    inversion H1. subst. clear H1. inversion H3. subst. clear H3.
    simpl in H. subst.
    destruct H4; try easy. destruct H as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
    destruct H7; try easy. destruct H as (s2,(g2,(g3,(Hc,(Hd,He))))). inversion Hc. subst.
    destruct H6; try easy. destruct H as (s3,(g4,(g5,(Hf,(Hg,Hh))))). inversion Hg. subst.
    destruct H2; try easy. destruct H as (s4,(g6,(Hi,Hj))). inversion Hi. subst.
    simpl. exists g5. exists g6. pclearbot. easy.
  - destruct lis; try easy. destruct ys; try easy. destruct xs; try easy.
    inversion H0. subst. clear H0. inversion H2. subst. clear H2.
    inversion H1. subst. clear H1. inversion H3. subst. clear H3.
    specialize(IHk lis s g ys xs). apply IHk; try easy.
Qed.


Lemma ishParts_x : forall [p s1 s2 o1 o2 xs0],
    (ishParts p (gtth_send s1 s2 (Some (o1,o2) :: xs0)) -> False) ->
    (ishParts p o2 -> False).
Proof.
  intros. apply H. 
  - case_eq (eqb p s1); intros.
    assert (p = s1). apply eqb_eq; try easy. subst. apply ha_sendp.
  - case_eq (eqb p s2); intros.
    assert (p = s2). apply eqb_eq; try easy. subst. apply ha_sendq.
  - assert (p <> s1). apply eqb_neq; try easy. 
    assert (p <> s2). apply eqb_neq; try easy.
    apply ha_sendr with (n := 0) (s := o1) (g := o2); try easy.
Qed.

Lemma ishParts_hxs : forall [p s1 s2 o1 xs0],
    (ishParts p (gtth_send s1 s2 (o1 :: xs0)) -> False) ->
    (ishParts p (gtth_send s1 s2 xs0) -> False).
Proof.
  intros. apply H.
  inversion H0. subst. apply ha_sendp. apply ha_sendq.
  subst. apply ha_sendr with (n := Nat.succ n) (s := s) (g := g); try easy.
Qed.

Lemma ishParts_n : forall [n p s s' xs s0 g],
    (ishParts p (gtth_send s s' xs) -> False) ->
    onth n xs = Some(s0, g) -> 
    (ishParts p g -> False).
Proof.  
  induction n; intros; try easy.
  - apply H. destruct xs; try easy. simpl in *. subst.
    - case_eq (eqb p s); intros.
      assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
    - case_eq (eqb p s'); intros.
      assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
    - assert (p <> s). apply eqb_neq; try easy. 
      assert (p <> s'). apply eqb_neq; try easy.
      apply ha_sendr with (n := 0) (s := s0) (g := g); try easy.
  - destruct xs; try easy.
    specialize(ishParts_hxs H); intros.
    specialize(IHn p s s' xs s0 g). apply IHn; try easy.
Qed.

Lemma mergeCtx_to_2R : forall ctxGLis ctxG,
    isMergeCtx ctxG ctxGLis -> 
    Forall (fun u => u = None \/ (exists ctxGi, u = Some ctxGi /\
      Forall2R (fun u v => (u = None \/ u = v)) ctxGi ctxG
    )) ctxGLis.
Proof.
  induction ctxGLis; intros; try easy.
  inversion H.
  - subst. constructor; try easy. right. exists ctxG.
    split. easy. clear H IHctxGLis. induction ctxG; intros.
    constructor. constructor; try easy. right. easy.
  - subst. specialize(IHctxGLis ctxG H2). constructor; try easy. left. easy.
  - subst.
    specialize(IHctxGLis t H4). clear H.
    constructor.
    - right. exists t'. split. easy.
      clear H4 IHctxGLis.
      apply Forall3S_to_Forall2_r with (ctxG0 := t); try easy.
      revert IHctxGLis. apply Forall_mono; intros.
      destruct H. left. easy.
      destruct H as (ctxGi,(Ha,Hb)). subst. right. exists ctxGi. split. easy.
      specialize(Forall3S_to_Forall2_l t t' ctxG H3); intros.
      clear H3 H4. clear ctxGLis t'.
      revert Hb H. revert t ctxG.
      induction ctxGi; intros; try easy.
      - constructor.
      - destruct t; try easy. destruct ctxG; try easy.
        inversion Hb. subst. clear Hb. inversion H. subst. clear H.
        specialize(IHctxGi t ctxG H5 H7). constructor; try easy.
        clear H5 H7.
        destruct H3. left. easy.
        subst. destruct H4. left. easy. subst. right. easy.
Qed.

Lemma typh_with_more : forall gl ctxJ ctxG g3,
            typ_gtth ctxJ gl g3 -> 
            Forall2R (fun u v : option gtt => u = None \/ u = v) ctxJ ctxG -> 
            typ_gtth ctxG gl g3.
Proof.
  induction gl using gtth_ind_ref; intros.
  - inversion H. subst. constructor.
    clear H. revert H3 H0. revert ctxG ctxJ. induction n; intros.
    - destruct ctxJ; try easy. destruct ctxG; try easy.
      inversion H0. subst. clear H0.
      simpl in H3. subst. destruct H4; try easy. 
    - destruct ctxJ; try easy. destruct ctxG; try easy.
      inversion H0. subst. clear H0.
      specialize(IHn ctxG ctxJ). apply IHn; try easy.
  - inversion H0. subst. constructor; try easy.
    clear H7 H0. revert H8 H1 H.
    revert xs ctxJ ctxG. clear p q.
    induction ys; intros.
    - destruct xs; try easy.
    - destruct xs; try easy. inversion H. subst. clear H. inversion H8. subst. clear H8.
      specialize(IHys xs ctxJ ctxG H7 H1 H4). constructor; try easy. clear H7 H4 IHys.
      destruct H5. left. easy.
      destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
      destruct H3; try easy. destruct H as (s2,(g3,(Hd,He))). inversion Hd. subst.
      right. exists s2. exists g3. exists g2. split. easy. split. easy.
      specialize(He ctxJ ctxG g2). apply He; try easy.
Qed.

Lemma typ_gtth_pad_l : forall Gl' g1 ctxJ ctxG,
    typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) Gl' g1 -> 
    typ_gtth (ctxJ ++ ctxG)%list Gl' g1.
Proof.
  intros.
  specialize(typh_with_more Gl' (noneLis (Datatypes.length ctxJ) ++ ctxG) (ctxJ ++ ctxG) g1); intros. apply H0; try easy.
  clear H0 H. induction ctxJ; intros; try easy.
  - simpl. induction ctxG; intros; try easy. constructor. constructor; try easy. right. easy.
  - constructor; try easy. left. easy.
Qed.

Lemma typ_gtth_pad_r : forall g2 g3 ctxJ ctxG,
        typ_gtth ctxJ g2 g3 -> 
        typ_gtth (ctxJ ++ ctxG)%list g2 g3.
Proof.
  intros.
  specialize(typh_with_more g2 ctxJ (ctxJ ++ ctxG) g3); intros.
  apply H0; try easy.
  clear H0 H. induction ctxJ; intros; try easy. constructor.
  constructor; try easy. right. easy.
Qed.

Lemma typh_with_less : forall ctxGi' ctxG g4 g3,
            typ_gtth ctxG g4 g3 -> 
            Forall2R (fun u v : option gtt => u = None \/ u = v) ctxGi' ctxG -> 
            usedCtx ctxGi' g4 -> 
            typ_gtth ctxGi' g4 g3.
Proof.
  intros. revert H H0 H1. revert g3 ctxGi' ctxG.
  induction g4 using gtth_ind_ref; intros.
  - inversion H. subst. constructor; try easy. 
    inversion H1. subst.
    clear H1 H. revert H4 H0. revert g3 ctxG G. induction n; intros; try easy.
    - destruct ctxG; try easy. simpl in H4. subst.
      inversion H0. subst. simpl. destruct H3; try easy.
    - destruct ctxG; try easy. inversion H0. subst. 
      apply IHn with (ctxG := ctxG); try easy.
  - inversion H0. subst.
    constructor; try easy. 
    inversion H2. subst.
    specialize(mergeCtx_to_2R ctxGLis ctxGi' H6); intros. clear H6 H8 H2 H0.
    revert H3 H10 H9 H1 H. revert ctxGi' ctxG ys ctxGLis. clear p q.
    induction xs; intros; try easy.
    - destruct ys; try easy.
    - destruct ys; try easy. destruct ctxGLis; try easy.
      inversion H. subst. clear H. inversion H9. subst. clear H9.
      inversion H3. subst. clear H3. inversion H10. subst. clear H10.
      specialize(IHxs ctxGi' ctxG ys ctxGLis).
      assert(Forall2
         (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
          u = None /\ v = None \/
          (exists (s : sort) (g : gtth) (g' : gtt),
             u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxGi' g g')) xs ys).
      apply IHxs; try easy. constructor; try easy.
      clear H H12 H7 H8 H5 IHxs.
      destruct H6. left. easy.
      destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
      destruct H4; try easy. destruct H as (s2,(g3,(Hd,He))). inversion Hd. subst.
      destruct H9; try easy. destruct H as (ct,(s3,(g4,(Hf,(Hg,Hh))))). inversion Hg. subst.
      destruct H2; try easy. destruct H as (ct2,(Hi,Hj)). inversion Hi. subst.
      right. exists s3. exists g4. exists g2.
      split. easy. split. easy.
      specialize(He g2 ct2 ctxG).
      assert(typ_gtth ct2 g4 g2).
      {
        apply He; try easy.
        clear Hh Hi Hc Hd He Hg. 
        revert Hj H1. revert ctxGi' ctxG.
        induction ct2; intros; try easy.
        - constructor.
        - destruct ctxGi'; try easy. destruct ctxG; try easy.
          inversion Hj. subst. clear Hj. inversion H1. subst. clear H1.
          specialize(IHct2 ctxGi' ctxG H5 H7). constructor; try easy.
          destruct H3. left. easy. subst. destruct H4. left. easy. subst. right. easy.
      }
      apply typh_with_more with (ctxJ := ct2); try easy.
Qed.

Lemma typh_with_more2 {A} : forall ctxGi' ctxG (ctxJ : list A) gl g3,
            typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxGi') gl g3 -> 
            Forall2R (fun u v : option gtt => u = None \/ u = v) ctxGi' ctxG -> 
            typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) gl g3.
Proof.
  intros.
  apply typh_with_more with (ctxJ := (noneLis (Datatypes.length ctxJ) ++ ctxGi')); try easy.
  clear H.
  induction ctxJ; intros; try easy.
  constructor; try easy. left. easy.
Qed.

Lemma ctx_back : forall s s' xs ys0 ctxG,
      typ_gtth ctxG (gtth_send s s' xs) (gtt_send s s' ys0) -> 
      usedCtx ctxG (gtth_send s s' xs) -> 
      exists ctxGLis, 
      Forall3 (fun u v w => (u = None /\ v = None /\ w = None) \/ (exists ct s g g', u = Some ct /\ v = Some(s, g) /\ w = Some(s, g') /\ typ_gtth ct g g' /\ usedCtx ct g)) ctxGLis xs ys0 /\
      isMergeCtx ctxG ctxGLis.
Proof.
  intros.
  inversion H. subst. clear H.
  inversion H0. subst. clear H0.
  clear H4. clear s s'.
  specialize(mergeCtx_to_2R ctxGLis ctxG H3); intros. 
  exists ctxGLis. split; try easy. clear H3.
  revert H7 H6 H. revert ys0 ctxG ctxGLis.
  induction xs; intros.
  - destruct ys0; try easy. destruct ctxGLis; try easy. constructor.
  - destruct ys0; try easy. destruct ctxGLis; try easy.
    inversion H7. subst. clear H7. inversion H6. subst. clear H6.
    inversion H. subst. clear H.
    specialize(IHxs ys0 ctxG ctxGLis H5 H8 H6). constructor; try easy.
    clear H6 H8 H5 IHxs.
    - destruct H4. destruct H. subst. destruct H3. destruct H. subst. left. easy.
      destruct H as (s1,(g1,(g2,Ha))). easy.
    - destruct H as (ct,(s1,(g1,(Ha,(Hb,Hc))))). subst.
      destruct H3; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,Hf))))). inversion Hd. subst.
      destruct H2; try easy. destruct H as (ct2,(Hg,Hh)). inversion Hg. subst.
      right. exists ct2. exists s2. exists g2. exists g3.
      split. easy. split. easy. split. easy. split; try easy.
      apply typh_with_less with (ctxG := ctxG); try easy.
Qed.

Lemma mergeCtx_sl : forall n ctxGLis ctxGi ctxG,
        onth n ctxGLis = Some ctxGi -> 
        isMergeCtx ctxG ctxGLis -> 
        Forall2R (fun u v => u = v \/ u = None) ctxGi ctxG.
Proof.
  induction n; intros.
  - destruct ctxGLis; try easy. 
    simpl in H. subst.
    inversion H0. subst. 
    - clear H0. induction ctxGi; intros; try easy. constructor.
      constructor; try easy. left. easy.
    - subst.
      clear H4 H0. clear ctxGLis.
      revert H3. revert ctxG t. induction ctxGi; intros; try easy.
      - constructor.
      - inversion H3; try easy.
        - subst. clear H3 IHctxGi. constructor. left. easy. clear a.
          induction ctxGi; intros; try easy. constructor. constructor; try easy. left. easy.
        - subst. specialize(IHctxGi xc xa H6). constructor; try easy.
          clear H3 H6. 
          - destruct H4. destruct H as (Ha,(Hb,Hc)). subst. left. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. right. easy.
          - destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
  - destruct ctxGLis; try easy.
    inversion H0; try easy.
    - subst. destruct n; try easy.
    - subst. specialize(IHn ctxGLis ctxGi ctxG). apply IHn; try easy.
    - subst. specialize(IHn ctxGLis ctxGi t H H5).
      clear H0 H H5.
      clear ctxGLis n.
      revert H4 IHn. revert t ctxG t'.
      induction ctxGi; intros; try easy.
      - constructor.
      - inversion H4. 
        - subst. inversion IHn; try easy.
        - subst. destruct ctxG; try easy.
        - subst. clear H4.
          inversion IHn. subst. clear IHn.
          specialize(IHctxGi xa xc xb H0 H6). constructor; try easy.
          clear IHctxGi H0 H6.
          destruct H4. subst.
          - destruct H. destruct H as (Ha,(Hb,Hc)). subst. left. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. right. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
          - destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
          subst. right. easy.
Qed.

Lemma shift_to : forall (g1 : gtt) (p : string) (Gl : gtth) (ctxG ctxJ : seq.seq (option gtt)),
typ_gtth ctxG Gl g1 ->
(ishParts p Gl -> False) ->
usedCtx ctxG Gl ->
exists Gl' : gtth,
  typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) Gl' g1 /\
  usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxG) Gl' /\ (ishParts p Gl' -> False).
Proof.
  intros g1 p Gl. revert g1 p.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion H1. subst.
    exists (gtth_hol ((Datatypes.length ctxJ) + n)).
    assert(extendLis (Datatypes.length ctxJ + n) (Some G) =
     (noneLis (Datatypes.length ctxJ) ++ extendLis n (Some G))%SEQ).
      {
       clear H1 H0 H. clear g1 p. induction ctxJ; intros; try easy.
       simpl in *. replace (extendLis (Datatypes.length ctxJ + n)%Nrec (Some G))%SEQ with
          ((noneLis (Datatypes.length ctxJ) ++ extendLis n (Some G))%SEQ). easy. 
      }
      rename H2 into Ht.
    split.
    - inversion H. subst. 
      specialize(extendExtract n (Some G)); intros.
      specialize(eq_trans (esym H4) H2); intros. inversion H3. subst.
      clear H4 H3 H2.
      constructor. clear H1 H0 H Ht. clear p. revert G n.
      induction ctxJ; intros; try easy. simpl in *.
      apply extendExtract; try easy.
      specialize(IHctxJ G n). easy.
    - split.
      replace ((noneLis (Datatypes.length ctxJ) ++ extendLis n (Some G))) with (extendLis (Datatypes.length ctxJ + n) (Some G)). constructor.
    - intros. inversion H2; try easy.
  - inversion H0. subst.
    inversion H2. subst.
    assert(
      exists zs,
      Forall2 (fun u v => (u = None /\ v = None) \/ exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) g g') zs ys /\
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists ctxGi s g, u = Some ctxGi /\ v = Some (s, g) /\ usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxGi) g)) ctxGLis zs /\
      Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ (ishParts p0 g -> False))) zs 
    ). 
    {
      specialize(mergeCtx_to_2R ctxGLis ctxG H6); intros.
      clear H6 H8 H2 H0.
      revert H H1 H9 H10 H3.
      revert p q xs p0 ctxG ctxJ ctxGLis.
      induction ys; intros; try easy.
      - destruct xs; try easy. destruct ctxGLis; try easy.
        exists nil. easy.
      - destruct xs; try easy. destruct ctxGLis; try easy.
        inversion H9. subst. clear H9. inversion H10. subst. clear H10.
        inversion H3. subst. clear H3. inversion H. subst. clear H.
        assert(exists zs : seq.seq (option (sort * gtth)),
         Forall2
           (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
            u = None /\ v = None \/
            (exists (s : sort) (g : gtth) (g' : gtt),
               u = Some (s, g) /\
               v = Some (s, g') /\ typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) g g')) zs ys /\
         Forall2
           (fun (u : option (seq.seq (option gtt))) (v : option (sort * gtth)) =>
            u = None /\ v = None \/
            (exists (ctxGi : seq.seq (option gtt)) (s : sort) (g : gtth),
               u = Some ctxGi /\
               v = Some (s, g) /\ usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxGi) g)) ctxGLis zs /\
         Forall
           (fun u : option (sort * gtth) =>
            u = None \/ (exists (s : sort) (g : gtth), u = Some (s, g) /\ (ishParts p0 g -> False))) zs).
        specialize(IHys p q xs p0 ctxG ctxJ ctxGLis). apply IHys; try easy.
        specialize(ishParts_hxs H1); try easy.
        clear IHys H10 H8 H9 H7.
        destruct H as (zs,(Ha,(Hb,Hc))).
        destruct H6.
        - destruct H. subst. destruct H5. destruct H. subst.
          exists (None :: zs).
          - split. constructor; try easy. left. easy.
          - split. constructor; try easy. left. easy.
          - constructor; try easy. left. easy.
          destruct H as (s1,(g1,(g2,Ht))). easy.
        - destruct H as (ctxGi,(s1,(g1,(Hd,(He,Hf))))). subst.
          destruct H5; try easy. destruct H as (s2,(g2,(g3,(Hg,(Hh,Hi))))). inversion Hg. subst.
          destruct H4; try easy. destruct H as (ctxGi',(Hj,Hk)). inversion Hj. subst.
          destruct H3; try easy. destruct H as (s3,(g4,(Hl,Hm))). inversion Hl. subst.
          specialize(Hm g3 p0 ctxGi' ctxJ).
          assert(exists Gl' : gtth,
       typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxGi') Gl' g3 /\
       usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxGi') Gl' /\ (ishParts p0 Gl' -> False)).
          {
            apply Hm; try easy.
            - apply typh_with_less with (ctxG := ctxG); try easy.
            - specialize(ishParts_x H1); try easy.
          }
          destruct H as (gl,(Hd,(He,Hta))). exists (Some (s3, gl) :: zs).
          - split. constructor; try easy.
            right. exists s3. exists gl. exists g3. split. easy. split. easy.
            apply typh_with_more2 with (ctxGi' := ctxGi'); try easy.
          - split. constructor; try easy. right. exists ctxGi'. exists s3. exists gl. easy.
          - constructor; try easy. right. exists s3. exists gl. easy.
    } 
    destruct H3 as (zs,(Ha,(Hb,Hc))).
    exists (gtth_send p q zs).
    - split. constructor; try easy.
      clear H H0 H1 H2 H6 H10 Hb Hc. 
      revert Ha H9 H8. revert ctxG ctxJ ys zs. clear p q p0 ctxGLis.
      induction xs; intros; try easy.
      specialize(SList_f a xs H8); intros.
      destruct ys; try easy. destruct zs; try easy. inversion Ha. subst. clear Ha. 
      inversion H9. subst. clear H9.
      destruct H.
      - specialize(IHxs ctxG ctxJ ys zs). apply SList_b. apply IHxs; try easy.
      - destruct H as (H,(a0,Ha)). subst. 
        destruct ys; try easy. destruct zs; try easy. clear H7 H5 H8 IHxs.
        destruct H4; try easy.
        destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
        destruct H3; try easy. destruct H as (s2,(g3,(g4,(Hd,(He,Hf))))). subst. easy.
    - split.
      assert(exists ks, Forall2 (fun u v => (u = None /\ v = None) \/ (exists ctxGi ctxGi', u = Some ctxGi /\ v = Some ctxGi' /\ (noneLis (Datatypes.length ctxJ) ++ ctxGi) = ctxGi')) ctxGLis ks).
      {
        clear Hc Hb Ha H10 H6 H9 H8 H2 H1 H0 H.
        induction ctxGLis; intros; try easy.
        exists nil. easy.
        destruct IHctxGLis as (ks, H).
        destruct a.
        - exists (Some (noneLis (Datatypes.length ctxJ) ++ l) :: ks). constructor; try easy.
          right. exists l. exists (noneLis (Datatypes.length ctxJ) ++ l). easy.
        - exists (None :: ks). constructor; try easy. left. easy.
      }
      destruct H3 as (ks, H3).
      clear Hc Ha H10 H9 H8 H2 H1 H0 H.
      clear p0 ys. 
      apply used_con with (ctxGLis := ks); try easy.
      - clear Hb. revert H3 H6. 
        revert ctxG ctxJ ks. clear p q xs zs.
        induction ctxGLis; intros; try easy.
        destruct ks; try easy. inversion H3. subst. clear H3.
        inversion H6.
        - subst. destruct ks; try easy. destruct H2; try easy.
          destruct H as (ct1,(ct2,(Ha,(Hb,Hc)))). inversion Ha. subst. constructor.
        - subst. destruct H2. destruct H. subst.
          specialize(IHctxGLis ctxG ctxJ ks). 
          assert(isMergeCtx (noneLis (Datatypes.length ctxJ) ++ ctxG) ks). apply IHctxGLis; try easy.
          constructor. easy.
          destruct H as (ct1,(ct2,Ha)). easy.
        - subst. specialize(IHctxGLis t ctxJ ks H5 H4).
          destruct H2; try easy. destruct H as (ct1,(ct2,(Ha,(Hb,Hc)))). inversion Ha. subst.
          apply cmconss with (t := (noneLis (Datatypes.length ctxJ) ++ t)); try easy.
          clear H4 H5 Ha H6 IHctxGLis. induction ctxJ; intros; try easy.
          simpl. constructor; try easy. left. easy.
      - revert H3 Hb. clear H6.
        revert ctxJ zs ks. clear p q xs ctxG.
        induction ctxGLis; intros.
        - destruct ks; try easy. destruct zs; try easy.
        - destruct ks; try easy. destruct zs; try easy. 
          inversion H3. subst. clear H3. inversion Hb. subst. clear Hb.
          specialize(IHctxGLis ctxJ zs ks H5 H6). constructor; try easy.
          clear IHctxGLis H5 H6.
          - destruct H2. destruct H. subst. destruct H3. destruct H. subst. left. easy.
            destruct H as(ct,(s1,(g1,Ha))). easy.
          - destruct H as (ct1,(ct2,(Ha,(Hb,Hc)))). subst.
            destruct H3; try easy. destruct H as (ct2,(s2,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
            right. exists (noneLis (Datatypes.length ctxJ) ++ ct2). exists s2. exists g2. easy.
    - intros.
      inversion H3. 
      - subst. apply H1. constructor.
      - subst. apply H1. constructor.
      - subst. specialize(some_onth_implies_In n zs (s, g) H14); intros.
        specialize(Forall_forall (fun u : option (sort * gtth) =>
        u = None \/ (exists (s : sort) (g : gtth), u = Some (s, g) /\ (ishParts p0 g -> False))) zs); intros.
        destruct H5. specialize(H5 Hc). clear H7 Hc.
        specialize(H5 (Some(s, g)) H4). destruct H5; try easy.
        destruct H5 as (s1,(g1,(Hta,Htb))). inversion Hta. subst.
        apply Htb; try easy.
Qed.

Lemma ctx_merge : forall s s0 s1 g1 l p,
    p <> s -> p <> s0 ->
    (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' g1 /\
       (ishParts p G' -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
             u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' (gtt_send s s0 l) /\
       (ishParts p G' -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
             u = Some (gtt_send   p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
  typ_gtth ctxG G' (gtt_send s s0 (Some (s1, g1) :: l)) /\
  (ishParts p G' -> False) /\
  Forall
    (fun u : option gtt =>
     u = None \/
     (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
        u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
  usedCtx ctxG G').
Proof.
  intros.
  destruct H1 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
  destruct H2 as (Gl2,(ctxJ,(He,(Hf,(Hg,Hh))))).
  inversion He. subst.
  - specialize(some_onth_implies_In n ctxJ (gtt_send s s0 l) H1); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxJ); intros.
    destruct H3. specialize(H3 Hg). clear H4 Hg.
    specialize(H3 (Some (gtt_send s s0 l)) H2). destruct H3; try easy.
    destruct H3 as (q1,(lsg,H3)).
    - destruct H3. inversion H3. subst. easy.
    - destruct H3. inversion H3. subst. easy.
    - inversion H3.
  - subst.
    assert(exists Gl', typ_gtth (noneLis (List.length ctxJ) ++ ctxG) Gl' g1 /\ usedCtx (noneLis (List.length ctxJ) ++ ctxG) Gl' /\ (ishParts p Gl' -> False)).
    {
      clear Hc Hf He Hg Hh H5 H7.
      clear H H0.
      revert Ha Hb Hd. revert g1 p Gl ctxG ctxJ. clear s s0 s1 l xs.
      apply shift_to; try easy.
    }
    destruct H1 as (Gl',(H1,(H2,Htm))).
    exists (gtth_send s s0 (Some (s1, Gl') :: xs)). exists (ctxJ ++ ctxG).
    - split.
      constructor; try easy. apply SList_b; try easy.
      constructor; try easy.
      - right. exists s1. exists Gl'. exists g1. split. easy. split. easy.
        apply typ_gtth_pad_l; try easy.
      - revert H7. apply Forall2_mono; intros.
        destruct H3. left. easy.
        right. destruct H3 as (s2,(g2,(g3,(Hta,(Htb,Htc))))). subst.
        exists s2. exists g2. exists g3. split. easy. split. easy.
        apply typ_gtth_pad_r with (ctxG := ctxG); try easy.
    - split.
      intros. inversion H3. subst. easy. subst. easy. subst.
      destruct n.
      - simpl in H12. inversion H12. subst. apply Hb. easy.
      - apply Hf. apply ha_sendr with (n := n) (s := s2) (g := g); try easy.
    - split.
      clear Htm H2 H1 H7 H5 Hh He Hf Hd Hb Ha H0 H. revert Hg Hc.
      revert p ctxG. clear s s0 s1 g1 l Gl xs Gl'.
      induction ctxJ; intros; try easy. inversion Hg. subst. clear Hg.
      specialize(IHctxJ p ctxG H2 Hc). constructor; try easy.
    - inversion Hh. subst.
      apply used_con with (ctxGLis := Some (noneLis (Datatypes.length ctxJ) ++ ctxG) :: ctxGLis); try easy.
      apply cmconss with (t := ctxJ); try easy.
      clear H10 H8 Htm H2 H1 H7 H5  Hh Hg He Hf Hd Hc Hb Ha H0 H.
      clear ctxGLis Gl' xs Gl p l g1 s1 s s0.
      induction ctxJ; intros; try easy. simpl. constructor.
      constructor; try easy. 
      destruct a. right. right. left. exists g. easy.
      left. easy.
    - constructor; try easy. right. exists (noneLis (Datatypes.length ctxJ) ++ ctxG).
      exists s1. exists Gl'. easy.
Qed.


Lemma part_cont : forall ys r p q,
    isgPartsC r (gtt_send p q ys) -> 
    r <> p -> r <> q ->
    exists n s g, onth n ys = Some(s, g) /\ isgPartsC r g.
Proof.
  induction ys; intros; try easy.
  - specialize(part_break_s (gtt_send p q []) r H); intros.
    destruct H2 as (Gl,(Ha,(Hb,Hc))). 
    destruct Hc. subst. pinversion Ha; try easy. 
    destruct H2 as (p1,(q1,(lis,Hc))). subst. pinversion Ha; try easy. subst. destruct lis; try easy.
    inversion Hb.
    - subst. easy. 
    - subst. easy.
    - destruct n; try easy.
    apply gttT_mon.
  - specialize(part_break_s2 (gtt_send p q (a :: ys)) r H); intros.
    destruct H2 as (Gl,(Ha,(Hb,(Hc,Hd)))). 
    destruct Hd. subst. pinversion Ha; try easy. 
    destruct H2 as (p1,(q1,(lis,He))). subst. pinversion Ha; try easy. subst. destruct lis; try easy.
    inversion H3. subst. clear H3.
    inversion Hb; try easy. subst.
    destruct n.
    - simpl in H10. subst.
      destruct H6; try easy. destruct H2 as (s1,(g1,(g2,(Hsa,(Hsb,Hsc))))). inversion Hsa. subst.
      exists 0. exists s1. exists g2. split; try easy.
      unfold isgPartsC. exists g1. destruct Hsc; try easy. 
      specialize(guard_cont Hc); intros. inversion H3. subst.
      destruct H7; try easy. destruct H4 as (s2,(g3,(Hma,Hmb))). inversion Hma. subst.
      easy.
    - specialize(IHys r p q).
      assert(exists (n : fin) (s : sort) (g : gtt), onth n ys = Some (s, g) /\ isgPartsC r g).
      {
        apply IHys; try easy.
        unfold isgPartsC. exists (g_send p q lis).
        split. pfold. constructor; try easy.
        split. 
        apply guard_cont_b. specialize(guard_cont Hc); intros. inversion H2; try easy.
        apply pa_sendr with (n := n) (s := s) (g := g); try easy.
      }
      destruct H2. exists (S x). easy.
    apply gttT_mon.
Qed.
  
Lemma part_cont_b : forall n ys s g r p q,
    onth n ys = Some(s, g) ->
    isgPartsC r g ->
    r <> p -> r <> q -> 
    wfgC (gtt_send p q ys) -> 
    isgPartsC r (gtt_send p q ys).
Proof.
  intros.
  unfold wfgC in H3.
  destruct H3 as (Gl,(Ha,(Hb,(Hc,Hd)))).
  unfold isgPartsC in *. destruct H0 as (G1,(He,(Hf,Hg))).
  pinversion Ha; try easy.
  - subst.
    exists (g_send p q (overwrite_lis n (Some (s, G1)) xs)).
    specialize(guard_cont Hc); intros. clear Hc Ha Hb Hd.
    revert H0 H4 Hg Hf He H H1 H2. revert xs G1 r p q g s ys.
    induction n; intros; try easy.
    - destruct ys; try easy. destruct xs; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      simpl in H. subst. destruct H8; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      inversion Hb. subst.
      destruct H6; try easy. destruct H as (s2,(g3,(Hi,Hh))). inversion Hi. subst.
      pclearbot.
      - split. pfold. constructor; try easy. constructor; try easy.
        right. exists s2. exists G1. exists g2.
        split. easy. split. easy. left. easy.
      - split. apply guard_cont_b. constructor; try easy. right.
        exists s2. exists G1. easy.
      - apply pa_sendr with (n := 0) (s := s2) (g := G1); try easy.
    - destruct ys; try easy. destruct xs; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      assert(gttTC (g_send p q (overwrite_lis n (Some (s, G1)) xs)) (gtt_send p q ys) /\
      (forall n0 : fin, exists m : fin, guardG n0 m (g_send p q (overwrite_lis n (Some (s, G1)) xs))) /\
      isgParts r (g_send p q (overwrite_lis n (Some (s, G1)) xs))).
      specialize(IHn xs G1 r p q g s ys). apply IHn; try easy. clear IHn.
      destruct H0 as (Hta,(Htb,Htc)).
      - split. pfold. constructor. 
        pinversion Hta; try easy. subst. constructor; try easy. apply gttT_mon.
      - split. apply guard_cont_b. specialize(guard_cont Htb); intros.
        constructor; try easy.
      - inversion Htc; try easy. subst.
        apply pa_sendr with (n := S n0) (s := s0) (g := g0); try easy.
  - subst.
    clear H0 H3.
    specialize(guard_breakG G Hc); intros.
    destruct H0 as (Gl,(Hh,(Hi,Hj))).
    specialize(gttTC_after_subst (g_rec G) Gl (gtt_send p q ys)); intros.
    assert(gttTC Gl (gtt_send p q ys)). apply H0; try easy. pfold. easy.
    clear H0. destruct Hj. subst. pinversion H3. apply gttT_mon.
    destruct H0 as (p1,(q1,(lis,Hj))). subst. pinversion H3; try easy. subst.
    specialize(guardG_betaG (g_rec G) (g_send p q lis)); intros.
    exists (g_send p q (overwrite_lis n (Some (s, G1)) lis)).
    clear H0 H3 Hh Hd Ha Hb Hc.
    specialize(guard_cont Hi); intros. clear Hi.
    revert H0 H4 H2 H1 Hg Hf He H.
    revert ys s g r p q G1 lis. clear G Q.
    induction n; intros; try easy.
    - destruct ys; try easy. destruct lis; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      simpl in H. subst. destruct H8; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      inversion Hb. subst.
      destruct H6; try easy. destruct H as (s2,(g3,(Hi,Hh))). inversion Hi. subst.
      pclearbot.
      - split. pfold. constructor; try easy. constructor; try easy.
        right. exists s2. exists G1. exists g2.
        split. easy. split. easy. left. easy.
      - split. apply guard_cont_b. constructor; try easy. right.
        exists s2. exists G1. easy.
      - apply pa_sendr with (n := 0) (s := s2) (g := G1); try easy.
    - destruct ys; try easy. destruct lis; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      assert(gttTC (g_send p q (overwrite_lis n (Some (s, G1)) lis)) (gtt_send p q ys) /\
      (forall n0 : fin, exists m : fin, guardG n0 m (g_send p q (overwrite_lis n (Some (s, G1)) lis))) /\
      isgParts r (g_send p q (overwrite_lis n (Some (s, G1)) lis))).
      specialize(IHn ys s g r p q G1 lis). apply IHn; try easy. clear IHn.
      destruct H0 as (Hta,(Htb,Htc)).
      - split. pfold. constructor. 
        pinversion Hta; try easy. subst. constructor; try easy. apply gttT_mon.
      - split. apply guard_cont_b. specialize(guard_cont Htb); intros.
        constructor; try easy.
      - inversion Htc; try easy. subst.
        apply pa_sendr with (n := S n0) (s := s0) (g := g0); try easy.
    apply gttT_mon.
    apply gttT_mon.
Qed.

Lemma part_cont_b_s : forall n ys s g r p q,
    onth n ys = Some(s, g) ->
    isgPartsC r g ->
    r <> p -> r <> q -> 
    wfgCw (gtt_send p q ys) -> 
    isgPartsC r (gtt_send p q ys).
Proof.
  intros.
  unfold wfgC in H3.
  destruct H3 as (Gl,(Ha,(Hb,Hc))).
  unfold isgPartsC in *. destruct H0 as (G1,(He,(Hf,Hg))).
  pinversion Ha; try easy.
  - subst.
    exists (g_send p q (overwrite_lis n (Some (s, G1)) xs)).
    specialize(guard_cont Hc); intros. clear Hc Ha Hb.
    revert H0 H4 Hg Hf He H H1 H2. revert xs G1 r p q g s ys.
    induction n; intros; try easy.
    - destruct ys; try easy. destruct xs; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      simpl in H. subst. destruct H8; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      inversion Hb. subst.
      destruct H6; try easy. destruct H as (s2,(g3,(Hi,Hh))). inversion Hi. subst.
      pclearbot.
      - split. pfold. constructor; try easy. constructor; try easy.
        right. exists s2. exists G1. exists g2.
        split. easy. split. easy. left. easy.
      - split. apply guard_cont_b. constructor; try easy. right.
        exists s2. exists G1. easy.
      - apply pa_sendr with (n := 0) (s := s2) (g := G1); try easy.
    - destruct ys; try easy. destruct xs; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      assert(gttTC (g_send p q (overwrite_lis n (Some (s, G1)) xs)) (gtt_send p q ys) /\
      (forall n0 : fin, exists m : fin, guardG n0 m (g_send p q (overwrite_lis n (Some (s, G1)) xs))) /\
      isgParts r (g_send p q (overwrite_lis n (Some (s, G1)) xs))).
      specialize(IHn xs G1 r p q g s ys). apply IHn; try easy. clear IHn.
      destruct H0 as (Hta,(Htb,Htc)).
      - split. pfold. constructor. 
        pinversion Hta; try easy. subst. constructor; try easy. apply gttT_mon.
      - split. apply guard_cont_b. specialize(guard_cont Htb); intros.
        constructor; try easy.
      - inversion Htc; try easy. subst.
        apply pa_sendr with (n := S n0) (s := s0) (g := g0); try easy.
  - subst.
    clear H0 H3.
    specialize(guard_breakG G Hc); intros.
    destruct H0 as (Gl,(Hh,(Hi,Hj))).
    specialize(gttTC_after_subst (g_rec G) Gl (gtt_send p q ys)); intros.
    assert(gttTC Gl (gtt_send p q ys)). apply H0; try easy. pfold. easy.
    clear H0. destruct Hj. subst. pinversion H3. apply gttT_mon.
    destruct H0 as (p1,(q1,(lis,Hj))). subst. pinversion H3; try easy. subst.
    specialize(guardG_betaG (g_rec G) (g_send p q lis)); intros.
    exists (g_send p q (overwrite_lis n (Some (s, G1)) lis)).
    clear H0 H3 Hh Ha Hb Hc.
    specialize(guard_cont Hi); intros. clear Hi.
    revert H0 H4 H2 H1 Hg Hf He H.
    revert ys s g r p q G1 lis. clear G Q.
    induction n; intros; try easy.
    - destruct ys; try easy. destruct lis; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      simpl in H. subst. destruct H8; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      inversion Hb. subst.
      destruct H6; try easy. destruct H as (s2,(g3,(Hi,Hh))). inversion Hi. subst.
      pclearbot.
      - split. pfold. constructor; try easy. constructor; try easy.
        right. exists s2. exists G1. exists g2.
        split. easy. split. easy. left. easy.
      - split. apply guard_cont_b. constructor; try easy. right.
        exists s2. exists G1. easy.
      - apply pa_sendr with (n := 0) (s := s2) (g := G1); try easy.
    - destruct ys; try easy. destruct lis; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      assert(gttTC (g_send p q (overwrite_lis n (Some (s, G1)) lis)) (gtt_send p q ys) /\
      (forall n0 : fin, exists m : fin, guardG n0 m (g_send p q (overwrite_lis n (Some (s, G1)) lis))) /\
      isgParts r (g_send p q (overwrite_lis n (Some (s, G1)) lis))).
      specialize(IHn ys s g r p q G1 lis). apply IHn; try easy. clear IHn.
      destruct H0 as (Hta,(Htb,Htc)).
      - split. pfold. constructor. 
        pinversion Hta; try easy. subst. constructor; try easy. apply gttT_mon.
      - split. apply guard_cont_b. specialize(guard_cont Htb); intros.
        constructor; try easy.
      - inversion Htc; try easy. subst.
        apply pa_sendr with (n := S n0) (s := s0) (g := g0); try easy.
    apply gttT_mon.
    apply gttT_mon.
Qed.

Lemma word_to_parts : forall G w' p q0,
             gttmap G w' None (gnode_pq p q0) \/
             gttmap G w' None (gnode_pq q0 p) -> 
             wfgCw G -> 
             isgPartsC p G.
Proof.
  intros G w'. revert G.
  induction w'; intros.
  - destruct H.
    inversion H. subst. apply triv_pt_p_s; try easy.
    inversion H. subst. apply triv_pt_q_s; try easy.
  - destruct H.
    - inversion H. subst.
      specialize(wfgCw_after_step_all); intros.
      specialize(wfgCw_triv p0 q xs H0); intros. destruct H2.
      specialize(H1 xs p0 q H2 H0); intros.
      clear H2 H3.
      specialize(Forall_prop a xs (st, gk) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgCw g)) H4 H1); intros.
      destruct H2; try easy. destruct H2 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
      specialize(IHw' g1 p q0).
      assert(isgPartsC p g1). apply IHw'; try easy.
      left. easy.
      - case_eq (eqb p p0); intros.
        assert (p = p0). apply eqb_eq; try easy. subst. apply triv_pt_p_s; try easy.
      - case_eq (eqb p q); intros.
        assert (p = q). apply eqb_eq; try easy. subst. apply triv_pt_q_s; try easy.
      - assert (p <> p0). apply eqb_neq; try easy.
        assert (p <> q). apply eqb_neq; try easy.
        apply part_cont_b_s with (n := a) (s := s1) (g := g1); try easy.
    - inversion H. subst.
      specialize(wfgCw_after_step_all); intros.
      specialize(wfgCw_triv p0 q xs H0); intros. destruct H2.
      specialize(H1 xs p0 q H2 H0); intros.
      clear H2 H3.
      specialize(Forall_prop a xs (st, gk) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgCw g)) H4 H1); intros.
      destruct H2; try easy. destruct H2 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
      specialize(IHw' g1 p q0).
      assert(isgPartsC p g1). apply IHw'; try easy.
      right. easy.
      - case_eq (eqb p p0); intros.
        assert (p = p0). apply eqb_eq; try easy. subst. apply triv_pt_p_s; try easy.
      - case_eq (eqb p q); intros.
        assert (p = q). apply eqb_eq; try easy. subst. apply triv_pt_q_s; try easy.
      - assert (p <> p0). apply eqb_neq; try easy.
        assert (p <> q). apply eqb_neq; try easy.
        apply part_cont_b_s with (n := a) (s := s1) (g := g1); try easy.
Qed.