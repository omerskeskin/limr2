From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh src.step src.merge src.projection. 
From SST Require Import lemma.inversion lemma.inversion_expr lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step.


Lemma proj_mon: monotone3 projection.
Proof. unfold monotone3.
       intros.
       induction IN; intros.
       - constructor. easy.
       - constructor; try easy. 
         revert ys H1. clear H0.
         induction xs; intros.
         + subst. inversion H1. constructor.
         + subst. inversion H1. constructor.
           destruct H3 as [(H3a, H3b) | (s,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs. easy.
       - constructor. easy. easy.
         revert ys H1. clear H0.
         induction xs; intros.
         + subst. inversion H1. constructor.
         + subst. inversion H1. constructor.
           destruct H3 as [(H3a, H3b) | (s,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs. easy.
       - apply proj_cont with (ys := ys); try easy.
         revert H3. apply Forall2_mono; intros.
         destruct H3. left. easy.
         destruct H3. destruct H3. destruct H3. destruct H3. destruct H5. subst.
         right. exists x0. exists x1. exists x2. split. easy. split. easy.
         apply LE; try easy.
Qed.


Lemma proj_forward : forall p q xs, 
  wfgC (gtt_send p q xs) ->
  projectableA (gtt_send p q xs) -> 
  List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ projectableA g)) xs.
Proof.
  intros.
  apply Forall_forall; intros.
  destruct x. 
  - destruct p0. right. exists s. exists g. split. easy.
    unfold projectableA in *.
    intros. specialize(H0 pt). destruct H0 as (T, H0).
    specialize(in_some_implies_onth (s, g) xs H1); intros.
    destruct H2 as (n, H2). clear H1.
    pinversion H0; try easy.
    - subst. 
      assert(p <> q).
      {
        unfold wfgC in H. 
        destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
        specialize(guard_breakG_s2 (gtt_send p q xs) Gl Hc Hb Ha); intros.
        destruct H as (Gl2,(Hta,(Htb,(Htc,Htd)))).
        destruct Hta. subst. pinversion Htd; try easy. apply gttT_mon.
        destruct H as (p1,(q1,(lis,Hte))). subst. pinversion Htd; try easy. subst.
        inversion Htc; try easy.
        apply gttT_mon.
      }
      specialize(wfgC_after_step_all H3 H); intros.
      specialize(some_onth_implies_In n xs (s, g) H2); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) xs); intros.
      destruct H6. specialize(H6 H4). clear H7 H4.
      specialize(H6 (Some (s, g)) H5). destruct H6; try easy.
      destruct H4 as (st,(g0,(Ha,Hb))). inversion Ha. subst. clear H5 Ha.
      specialize(decidable_isgPartsC g0 pt Hb); intros.
      unfold decidable in H4. unfold not in H4.
      destruct H4.
      - assert False. apply H1.
        - case_eq (eqb pt p); intros.
          assert (pt = p). apply eqb_eq; try easy. subst. apply triv_pt_p; try easy.
        - case_eq (eqb pt q); intros.
          assert (pt = q). apply eqb_eq; try easy. subst. apply triv_pt_q; try easy.
        - assert (pt <> p). apply eqb_neq; try easy. 
          assert (pt <> q). apply eqb_neq; try easy.
          apply part_cont_b with (n := n) (s := st) (g := g0); try easy. easy.
      - exists ltt_end. pfold. constructor; try easy.
    - subst.
      clear H8 H5 H0 H. revert H9 H2.
      revert xs pt ys s g. clear p.
      induction n; intros; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        simpl in H2. subst. destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
        inversion Ha. subst. exists t1. destruct Hc; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        specialize(IHn xs pt ys s g). apply IHn; try easy.
    - subst.
      clear H8 H5 H0 H. revert H9 H2.
      revert xs pt ys s g. clear q.
      induction n; intros; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        simpl in H2. subst. destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
        inversion Ha. subst. exists t1. destruct Hc; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        specialize(IHn xs pt ys s g). apply IHn; try easy.
    - subst. clear H12 H8 H7 H6 H5 H0 H.
      revert H2 H11.
      revert xs pt s g ys. clear p q T.
      induction n; intros; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H11. subst. clear H11.
        simpl in H2. subst. destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
        inversion Ha. subst.
        exists t1. destruct Hc; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H11. subst. clear H11.
        specialize(IHn xs pt s g ys). apply IHn; try easy.
    apply proj_mon.
    left. easy.
Qed.

Lemma pmergeCR_helper : forall n ys ys0 xs r s g ctxG,
    Forall (fun u : option ltt => u = None \/ u = Some ltt_end) ys0 -> 
    Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys -> 
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys0 -> 
    Forall2
       (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys -> 
    onth n ys = Some (s, g) -> 
    exists g', wfgC g /\
    onth n ys0 = Some ltt_end /\ projectionC g r ltt_end /\
    onth n xs = Some(s, g') /\ typ_gtth ctxG g' g.
Proof.
  induction n; intros.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    simpl in H3. subst. inversion H. subst. clear H.
    destruct H8; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
    destruct H6; try easy. destruct H as (s2,(g2,(Hd,He))). inversion Hd. subst.
    destruct H5; try easy. destruct H as (s3,(g3,(g4,(Hf,(Hg,Hh))))). inversion Hg. subst.
    destruct H2; try easy. inversion H. subst.
    exists g3. destruct Hc; try easy.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    simpl in H3. subst. inversion H. subst. clear H.
    specialize(IHn ys ys0 xs r s g ctxG). apply IHn; try easy.
Qed.

Lemma pmergeCR: forall G r,
          wfgC G ->
          projectionC G r ltt_end ->
          (isgPartsC r G -> False).
Proof. intros.
  specialize(balanced_to_tree G r H H1); intros.
  destruct H2 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  revert Hc Hb Ha. rename H1 into Ht.
  revert H0 H Ht. revert G r ctxG.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion Ha. subst.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send r q lsg) \/ u = Some (gtt_send q r lsg) \/ u = Some gtt_end)) ctxG); intros.
    destruct H1. specialize(H1 Hc). clear Hc H2. 
    specialize(some_onth_implies_In n ctxG G H3); intros.
    specialize(H1 (Some G) H2). destruct H1; try easy.
    destruct H1 as (q,(lsg,Hd)).
    - destruct Hd. inversion H1. subst. pinversion H0; try easy.  
      apply proj_mon.
    - destruct H1. inversion H1. subst. pinversion H0; try easy.
      apply proj_mon.
    - inversion H1. subst.
      specialize(part_break gtt_end r H Ht); intros.
      destruct H4 as (Gl,(Hta,(Htb,(Htc,Htd)))).
      destruct Htd. subst. inversion Htb; try easy.
      destruct H4 as (p1,(q1,(lis1,Htd))). subst.
      pinversion Hta; try easy. apply gttT_mon. 
  - inversion Ha. subst.
    pinversion H0; try easy. subst.
    specialize(part_cont ys r p q); intros.
    assert(exists (n : fin) (s : sort) (g : gtt), onth n ys = Some (s, g) /\ isgPartsC r g).
    apply H2; try easy.
    destruct H3 as (n,(s,(g,(Hd,He)))). clear H2 H10.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G : gtt) (r : string) (ctxG : seq.seq (option gtt)),
           projectionC G r ltt_end ->
           wfgC G ->
           isgPartsC r G ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some (gtt_send r q lsg) \/ u0 = Some (gtt_send q r lsg) \/ u0 = Some gtt_end))
             ctxG -> (ishParts r g -> False) -> typ_gtth ctxG g G -> False))) xs); intros.
    destruct H2. specialize(H2 H). clear H H3.
    specialize(triv_merge_ltt_end ys0 H14); intros.
    specialize(wfgC_after_step_all H5 H1); intros.
    clear Ht H1 H0 Ha H7 H5 H6 H9.
    specialize(pmergeCR_helper n ys ys0 xs r s g ctxG); intros.
    assert(exists g' : gtth,
       wfgC g /\
       onth n ys0 = Some ltt_end /\
       projectionC g r ltt_end /\ onth n xs = Some (s, g') /\ typ_gtth ctxG g' g).
    apply H0; try easy. clear H0 H3 H H13 H8.
    destruct H1 as (g',(Hf,(Hg,(Hh,(Hi,Hj))))).
    specialize(some_onth_implies_In n xs (s, g') Hi); intros.
    specialize(H2 (Some (s, g')) H).
    destruct H2; try easy. destruct H0 as (s1,(g1,(Hk,Hl))). inversion Hk. subst.
    specialize(Hl g r ctxG).
    apply Hl; try easy.
    specialize(ishParts_n Hb Hi); intros. apply H0; try easy.
  apply proj_mon.
Qed.

Lemma pmergeCR_s : forall G r,
    projectionC G r ltt_end ->
    (isgPartsC r G -> False).
Proof.
  intros.
  unfold isgPartsC in H0.
  destruct H0 as (Gl,(Ha,(Hb,Hc))).
  specialize(isgParts_depth_exists r Gl Hc); intros. destruct H0 as (n, H0). clear Hc.
  revert H0 Hb Ha H. revert G r Gl.
  induction n; intros.
  - inversion H0. 
    subst. 
    pinversion Ha. subst. pinversion H; try easy. subst.
    apply H1. unfold isgPartsC. exists (g_send r q lis). split. pfold. easy. 
    split. easy. apply isgParts_depth_back with (n := 0); try easy.
    apply proj_mon.
    apply gttT_mon.
  - subst. 
    pinversion Ha. subst. pinversion H; try easy. subst.
    apply H1. unfold isgPartsC. exists (g_send p r lis). split. pfold. easy. 
    split. easy. apply isgParts_depth_back with (n := 0); try easy.
    apply proj_mon.
    apply gttT_mon.
  inversion H0.
  - subst.
    pinversion Ha. subst.
    specialize(subst_parts_depth 0 0 n r g g Q H3 H2); intros.
    specialize(IHn G r Q). apply IHn; try easy.
    intros. specialize(Hb n0). destruct Hb.
    inversion H5. subst. exists 0. constructor.
    - subst. specialize(subst_injG 0 0 (g_rec g) g Q Q0 H7 H3); intros. subst.
      exists m. easy.
      apply gttT_mon.
  - subst. pinversion H; try easy.
    - subst. apply H1. unfold isgPartsC. exists (g_send p q lis).
      split. easy. split. easy. apply isgParts_depth_back with (n := S n); try easy.
    - subst.
      specialize(triv_merge_ltt_end ys H10); intros.
      pinversion Ha. subst.
      specialize(guard_cont Hb); intros.
      specialize(Forall2_prop_r k lis xs (s, g) (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : global) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) H4 H13); intros.
       destruct H14 as (p1,(Hc,Hd)).
       destruct Hd; try easy. destruct H14 as (s1,(g1,(g2,(He,(Hf,Hg))))). inversion He. subst. clear H13.
       specialize(Forall2_prop_r k xs ys (s1, g2) (fun (u : option (sort * gtt)) (v : option ltt) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtt) (t : ltt),
           u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) Hf H9); intros.
       destruct H13 as (p1,(Hh,Hi)).
       destruct Hi; try easy. destruct H13 as (s2,(g3,(g4,(Hj,(Hk,Hl))))). inversion Hj. subst.
       clear H9.
       specialize(Forall_prop k lis (s2, g1) (fun u : option (sort * global) =>
         u = None \/
         (exists (s : sort) (g : global),
            u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) H4 H12); intros.
       destruct H9; try easy. destruct H9 as (s3,(g5,(Hm,Hn))). inversion Hm. subst. clear H12.
       specialize(Forall_prop k ys g4 (fun u : option ltt => u = None \/ u = Some ltt_end) Hk H11); intros.
       destruct H9; try easy. inversion H9. subst.
       pclearbot. destruct Hl; try easy.
       specialize(IHn g3 r g5). apply IHn; try easy.
     apply gttT_mon.
     apply proj_mon.
Qed.

Lemma non_triv_proj_part : forall [G p q x],
    projectionC G p (ltt_send q x) -> isgPartsC p G.
Proof.
  intros. pinversion H; try easy.
  apply proj_mon.
Qed.

Lemma ctx_merge2 : forall s s0 s1 g1 l p q x,
    p <> s -> p <> s0 ->
    (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' g1 /\
       (ishParts p G' -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg /\
             Forall2
               (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                u0 = None /\ v = None \/
                (exists (s : sort) (t : ltt) (g' : gtt),
                   u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' (gtt_send s s0 l) /\
       (ishParts p G' -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg /\
             Forall2
               (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                u0 = None /\ v = None \/
                (exists (s : sort) (t : ltt) (g' : gtt),
                   u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
  typ_gtth ctxG G' (gtt_send s s0 (Some (s1, g1) :: l)) /\
  (ishParts p G' -> False) /\
  Forall
    (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg /\
             Forall2
               (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                u0 = None /\ v = None \/
                (exists (s : sort) (t : ltt) (g' : gtt),
                   u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG /\
  usedCtx ctxG G').
Proof.
  intros.
  destruct H1 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
  destruct H2 as (Gl2,(ctxJ,(He,(Hf,(Hg,Hh))))).
  inversion He. subst.
  - specialize(some_onth_implies_In n ctxJ (gtt_send s s0 l) H1); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxJ); intros.
    destruct H3. specialize(H3 Hg). clear H4 Hg.
    specialize(H3 (Some (gtt_send s s0 l)) H2). destruct H3; try easy.
    destruct H3 as (g2,(lsg,(Hi,(Hj,Hk)))). inversion Hi. subst. inversion H4. subst. easy.
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

Lemma proj_end_cont_end : forall s s' ys p,
        wfgC (gtt_send s s' ys) ->
        s <> s' ->
        projectionC (gtt_send s s' ys) p ltt_end -> 
        List.Forall (fun u => u = None \/ (exists st g, u = Some(st, g) /\ projectionC g p ltt_end)) ys.
Proof.
  intros. pinversion H1. subst.
  - assert(List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ (isgPartsC p g -> False))) ys).
    {
      specialize(wfgC_after_step_all H0 H); intros. clear H0 H1. rename H into Ht.
      apply Forall_forall; intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys); intros.
      destruct H0. specialize(H0 H3). clear H3 H1.
      specialize(H0 x H). destruct H0. left. easy.
      destruct H0 as (st,(g,(Ha,Hb))). subst.
      right. exists st. exists g. split. easy.
      intros. apply H2. unfold isgPartsC.
      pose proof Ht as Ht2.
      unfold wfgC in Ht. destruct Ht as (Gl,(Hta,(Htb,(Htc,Htd)))).
      specialize(guard_breakG_s2 (gtt_send s s' ys) Gl Htc Htb Hta); intros. clear Hta Htb Htc. clear Gl.
      destruct H1 as (Gl,(Hta,(Htb,(Htc,Hte)))).
      destruct Hta.
      - subst. pinversion Hte. apply gttT_mon.
      - destruct H1 as (p1,(q1,(lis,Hsa))). subst.
        pinversion Hte; try easy. subst. 
        specialize(in_some_implies_onth (st,g) ys H); intros. destruct H1 as (n,Hsb).
        unfold isgPartsC in H0. destruct H0 as (G1,(Hla,Hlb)).
        exists (g_send s s' (overwrite_lis n (Some (st, G1)) lis)).
        split.
        pfold. constructor. revert Hsb H3 Hla.
        clear Htd H2 H Hb Hlb Hte Htc Htb Ht2. revert ys st g G1 lis. clear s s' p.
        induction n; intros; try easy.
        - destruct ys; try easy. destruct lis; try easy. inversion H3. subst. clear H3.
          constructor; try easy. right. exists st. exists G1. 
          simpl in Hsb. subst. destruct H2; try easy.
          exists g. split. easy. split. easy. left. easy.
        - destruct ys; try easy. destruct lis; try easy. inversion H3. subst. clear H3.
          specialize(IHn ys st g G1 lis Hsb H5 Hla).
          constructor; try easy.
            split. 
            - destruct Hlb. intros. destruct n0. exists 0. constructor.
              specialize(H0 n0). specialize(Htb (S n0)).
              destruct Htb. destruct H0. exists (Nat.max x0 x).
              constructor. inversion H4. subst.
              clear Hsb H3 H4 Htc Hte Ht2 H1 Hb H H2 Htd Hla. revert H8 H0.
              revert st G1 x0 lis x n0. clear s s' ys p g.
              induction n; intros; try easy. destruct lis; try easy.
              - constructor; try easy. right. exists st. exists G1. split. easy.
                specialize(guardG_more n0 x0 (Nat.max x0 x) G1); intros. apply H; try easy.
                apply max_l; try easy.
              - inversion H8. subst. constructor; try easy. right. exists st. exists G1.
                split. easy. specialize(guardG_more n0 x0 (Nat.max x0 x) G1); intros. apply H; try easy.
                apply max_l; try easy.
                apply Forall_forall; intros. 
                specialize(Forall_forall (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ guardG n0 x g)) lis); intros.
                destruct H1. specialize(H1 H3). clear H4 H3. specialize(H1 x1 H).
                destruct H1. left. easy. destruct H1 as (s1,(g1,(Ha,Hb))). subst.
                right. exists s1. exists g1. split. easy.
                specialize(guardG_more n0 x (Nat.max x0 x) g1); intros. apply H1; try easy.
                apply max_r; try easy.
              - destruct lis; try easy. constructor; try easy. left. easy.
                specialize(IHn st G1 x0 nil x n0 H8 H0). apply IHn; try easy.
                inversion H8. subst. clear H8.
                specialize(IHn st G1 x0 lis x n0 H3 H0). constructor; try easy.
                destruct H2. left. easy.
                destruct H as (s,(g,(Ha,Hb))). subst. right. exists s. exists g.
                split. easy.
                specialize(guardG_more n0 x (Nat.max x0 x) g); intros. apply H; try easy.
                apply max_r; try easy. 
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply pa_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply pa_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply pa_sendr with (n := n) (s := st) (g := G1); try easy. 
            apply overwriteExtract; try easy.
      apply gttT_mon.
    }
    apply Forall_forall; intros.
    specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ (isgPartsC p g -> False))) ys); intros.
    destruct H5. specialize(H5 H3). clear H6 H3. specialize(H5 x H4).
    destruct H5. left. easy. destruct H3 as (st,(g,(Ha,Hb))). subst.
    right. exists st. exists g. split. easy. pfold. apply proj_end; try easy.
  - subst.
    specialize(triv_merge_ltt_end ys0 H12); intros. clear H12 H7 H6 H5 H1 H.
    revert H11 H2. clear H0 H8. clear s s'. revert p ys0.
    induction ys; intros; try easy.
    - destruct ys0; try easy. inversion H2. subst. clear H2. inversion H11. subst. clear H11.
      specialize(IHys p ys0 H6 H3). constructor; try easy.
      clear IHys H6 H3. destruct H4. left. easy.
      destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). subst.
      right. exists s. exists g. split. easy. destruct H1; try easy. inversion H. subst. 
      destruct Hc; try easy.
    apply proj_mon.
Qed.

Lemma proj_inj_list : forall lsg ys ys0 p r,
      (forall (t t' : ltt) (g : gtt),
      wfgC g -> projectionC g p t -> projectionC g p t' -> r t t') -> 
      Forall2
       (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtt) (t : ltt),
           u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g p t)) lsg ys -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g p t)) lsg ys0 -> 
      Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) lsg -> 
      isoList (upaco2 lttIso r) ys ys0.
Proof.
  induction lsg; intros.
  - destruct ys; try easy. destruct ys0; try easy.
  - destruct ys; try easy. destruct ys0; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    specialize(IHlsg ys ys0 p r H H8 H9 H4). clear H4 H9 H8.
    
    destruct H6. destruct H0. subst. 
    destruct H5. destruct H0. subst. easy.
    destruct H0 as (s,(g,(t,(Ha,(Hb,Hc))))). easy.
    destruct H0 as (s,(g,(t,(Ha,(Hb,Hc))))). subst.
    destruct H3; try easy. destruct H0 as (s1,(g1,(Hd,He))). inversion Hd. subst.
    destruct H5; try easy. destruct H0 as (s2,(g2,(t',(Hg,(Hh,Hi))))). inversion Hg. subst.
    simpl. split. easy. split; try easy.
    right. pclearbot. specialize(H t t' g2). apply H; try easy.
Qed.

Lemma proj_end_inj_helper : forall n1 ys0 ys1 ys xs ctxG s1 g1 r,
      Forall (fun u : option ltt => u = None \/ u = Some ltt_end) ys0 -> 
      Forall
      (fun u : option (sort * gtt) =>
       u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys -> 
      Forall2
       (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys0 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys1 ->
      onth n1 ys = Some (s1, g1) -> 
      exists g2 t,
      onth n1 xs = Some(s1, g2) /\ typ_gtth ctxG g2 g1 /\
      onth n1 ys0 = Some ltt_end /\ projectionC g1 r ltt_end /\
      onth n1 ys1 = Some t /\ projectionC g1 r t /\ wfgC g1.
Proof.
  induction n1; intros; try easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2.
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    inversion H. subst. clear H.
    simpl in H4. subst.
    destruct H6; try easy. destruct H as (s2,(g2,(g3,(Ha,(Hb,Hc))))). inversion Hb. subst.
    destruct H3; try easy. destruct H as (s3,(g4,(Hd,He))). inversion Hd. subst.
    destruct H7; try easy. destruct H as (s4,(g5,(t1,(Hf,(Hg,Hh))))). inversion Hf. subst.
    destruct H8; try easy. destruct H as (s5,(g6,(t2,(Hi,(Hj,Hk))))). inversion Hi. subst.
    destruct H2; try easy. inversion H. subst.
    simpl. exists g2. exists t2. destruct Hh; try easy. destruct Hk; try easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2.
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    inversion H. subst. clear H.
    specialize(IHn1 ys0 ys1 ys xs ctxG s1 g1 r). apply IHn1; try easy.
Qed.

Lemma proj_end_inj : forall g t p,
          wfgC g -> 
          projectionC g p ltt_end -> 
          projectionC g p t -> 
          t = ltt_end.
Proof.
  intros.
  specialize(decidable_isgPartsC g p H); intros. unfold decidable in H2.
  destruct H2.
  - specialize(balanced_to_tree g p H H2); intros.
    destruct H3 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd. rename H2 into Ht.
    revert Hc Hb Ha H1 H0 H Ht. revert ctxG p t g.
    induction Gl using gtth_ind_ref; intros.
    - inversion Ha. subst.
      specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
      destruct H2. specialize(H2 Hc). clear Hc H3.
      specialize(some_onth_implies_In n ctxG g H4); intros.
      specialize(H2 (Some g) H3). destruct H2; try easy.
      destruct H2 as (q1,(lsg1,Hc)). 
      - destruct Hc. inversion H2. subst. pinversion H0; try easy. 
        apply proj_mon.
      - destruct H2. inversion H2. subst. pinversion H0; try easy.
        apply proj_mon.
      - inversion H2. subst. pinversion H1; try easy. apply proj_mon.
    - inversion Ha. subst.
      pinversion H0; try easy. subst.
      pinversion H1; try easy. subst. clear H17 H16 H13 H12. rename p0 into r.
      specialize(part_cont ys r p q H11); intros.
      assert(exists (n : fin) (s : sort) (g : gtt), onth n ys = Some (s, g) /\ isgPartsC r g).
      apply H3; try easy.
      clear H3. destruct H4 as (n1,(s1,(g1,(He,Hf)))).
      specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : seq.seq (option gtt)) (p : string) (t : ltt) (g0 : gtt),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some (gtt_send p q lsg) \/ u0 = Some (gtt_send q p lsg) \/ u0 = Some gtt_end))
             ctxG ->
           (ishParts p g -> False) ->
           typ_gtth ctxG g g0 ->
           projectionC g0 p t -> projectionC g0 p ltt_end -> wfgC g0 -> isgPartsC p g0 -> t = ltt_end)))
      xs); intros.
      destruct H3. specialize(H3 H). clear H H4.
      specialize(wfgC_after_step_all H6 H2); intros.
      specialize(triv_merge_ltt_end ys0 H15); intros.
      specialize(proj_end_inj_helper n1 ys0 ys1 ys xs ctxG s1 g1 r); intros.
      assert(exists (g2 : gtth) (t : ltt),
       onth n1 xs = Some (s1, g2) /\
       typ_gtth ctxG g2 g1 /\
       onth n1 ys0 = Some ltt_end /\
       projectionC g1 r ltt_end /\ onth n1 ys1 = Some t /\ projectionC g1 r t /\ wfgC g1).
      apply H5; try easy. clear H5 H4 H H20 H14 H9.
      destruct H12 as (g2,(t1,(Hta,(Htb,(Htc,(Htd,(Hte,Htf))))))).
      specialize(some_onth_implies_In n1 xs (s1, g2) Hta); intros.
      specialize(H3 (Some (s1, g2)) H). destruct H3; try easy.
      destruct H3 as (s2,(g3,(Hsa,Hsb))). inversion Hsa. subst.
      specialize(Hsb ctxG r t1 g1).
      assert(t1 = ltt_end). apply Hsb; try easy.
      specialize(ishParts_n Hb Hta); intros. apply H3; try easy. subst.
      specialize(merge_end_back n1 ys1 t); intros. apply H3; try easy.
      apply proj_mon. apply proj_mon.
  - unfold not in H2. pinversion H0; try easy.
    subst. pinversion H1; try easy.
    - subst. specialize(H2 H5). easy.
    - subst. specialize(H2 H5). easy.
    - subst. specialize(H2 H7). easy.
  apply proj_mon. 
  subst. specialize(H2 H6). easy. apply proj_mon.
Qed.

Theorem proj_inj : forall [g p t t'],
          wfgC g -> 
          projectionC g p t -> 
          projectionC g p t' -> 
          t = t'.
Proof.
  intros.
  apply lltExt. revert H H0 H1. revert t t' g. pcofix CIH; intros.
  specialize(decidable_isgPartsC g p H0); intros. unfold decidable in H.
  destruct H.
  pose proof H0 as Ht. unfold wfgC in H0. destruct H0 as (Gl,(Ha,(Hb,(Hc,Hd)))).
  specialize(balanced_to_tree g p Ht H); intros. clear Ha Hb Hc Hd. clear H. rename H0 into H.
  destruct H as (G,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  revert H1 H2 Ht Ha Hb Hc CIH. revert t t' g. clear Gl.
  induction G using gtth_ind_ref; intros; try easy. 
  
  - inversion Ha. subst.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/
           u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
    destruct H. specialize(H Hc). clear Hc H0. 
    specialize(some_onth_implies_In n ctxG g H3); intros.
    specialize(H (Some g) H0). destruct H; try easy.
    destruct H as (q,(lsg,Hd)). 
    clear H0. destruct Hd.
    - inversion H. subst.
      pinversion H1; try easy. subst. 
      assert False. apply H0. apply triv_pt_p; try easy. easy.
      subst. 
      pinversion H2; try easy. subst.
      pfold. constructor.
      specialize(wfgC_after_step_all H8 Ht); intros.
      specialize(proj_inj_list lsg ys ys0 p r); intros. apply H4; try easy.
      apply proj_mon. apply proj_mon.
    destruct H.
    - inversion H. subst.
      pinversion H1; try easy. subst. 
      assert False. apply H0. apply triv_pt_q; try easy. easy.
      subst. 
      pinversion H2; try easy. subst.
      pfold. constructor.
      specialize(wfgC_after_step_all H8 Ht); intros.
      specialize(proj_inj_list lsg ys ys0 p r); intros. apply H4; try easy.
      apply proj_mon. apply proj_mon.
    - inversion H. subst.
      pinversion H2. subst. pinversion H1. subst. pfold. constructor.
      apply proj_mon. apply proj_mon.
  - inversion Ha. subst. 
    rename p0 into s. rename q into s'.
    pinversion H2. 
    - subst. 
      specialize(proj_end_inj (gtt_send s s' ys) t p); intros.
      assert(t = ltt_end).
      {
        apply H3; try easy. pfold. easy.
      }
      subst. pfold. constructor.
    - subst. assert False. apply Hb. constructor. easy. subst.
      pinversion H1; try easy. subst.
      pfold. constructor.
      specialize(proj_inj_list ys ys1 ys0 p r); intros.
      apply H0; try easy. 
      specialize(wfgC_after_step_all H6 Ht); try easy.
      apply proj_mon.
    - subst. 
      pinversion H1; try easy. subst.
      {
        assert (List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists t t', u = Some t /\ v = Some t' /\ paco2 lttIso r t t')) ys1 ys0).
        {
          specialize(wfgC_after_step_all H11 Ht); intros.
          clear H20 H16 H15 H12 H11 H14 H10 H9 H6 H5 H7 H1 H2 Ht Ha.
          revert H0 H19 H13 H8 CIH Hc Hb H.
          revert p r s s' xs ctxG ys1 ys0. clear t t'.
          induction ys; intros; try easy.
          - destruct ys0; try easy. destruct ys1; try easy.
          - destruct ys0; try easy. destruct ys1; try easy. destruct xs; try easy.
            inversion H0. subst. clear H0. inversion H19. subst. clear H19.
            inversion H13. subst. clear H13. inversion H8. subst. clear H8.
            inversion H. subst. clear H.
            specialize(IHys p r s s' xs ctxG ys1 ys0).
            assert(Forall2
               (fun u v : option ltt =>
                u = None /\ v = None \/
                (exists t t' : ltt, u = Some t /\ v = Some t' /\ paco2 lttIso r t t')) ys1 ys0).
            apply IHys; try easy. specialize(ishParts_hxs Hb); try easy.
            subst.
            constructor; try easy.
            {
              clear H8 H12 H10 H7 H4 IHys.
              destruct H5. 
              - destruct H0. subst. destruct H6. destruct H0. subst. left. easy.
                destruct H0 as (st,(g,(t,(Ha,(Hd,Hf))))). subst. easy. clear H.
              - destruct H0 as (s1,(g1,(t1,(Hd,(He,Hf))))).
                subst.
                destruct H3; try easy. destruct H as (s2,(g2,(Hg,Hh))). inversion Hg. subst.
                destruct H9; try easy. destruct H as (s3,(g3,(g4,(Hi,(Hj,Hk))))). inversion Hj. subst.
                destruct H6; try easy. destruct H as (s4,(g5,(t2,(Hl,(Hm,Hn))))). inversion Hl. subst.
                destruct H2; try easy. destruct H as (s5,(g6,(Ho,Hp))). inversion Ho. subst.
                clear Hl Hj Hg Ho.
                specialize(Hp t1 t2 g5).
                right. exists t1. exists t2.
                split. easy. split. easy. pclearbot. apply Hp; try easy.
                specialize(ishParts_x Hb); try easy.
            }
        }
        subst.
        specialize(isMerge_injw t t' r ys1 ys0 H0); intros. subst.
        apply H3; try easy.
      }
    apply proj_mon.
    apply proj_mon.
  - unfold not in *.
    pinversion H1; try easy. 
    - subst. pinversion H2; try easy. subst. pfold. constructor.
    - subst. specialize(H3 H5). easy.
    - subst. specialize(H3 H5). easy.
    - subst. specialize(H3 H7). easy.
    apply proj_mon.
  - subst. specialize(H H4). easy.
  - subst. specialize(H H4). easy.
  - subst. specialize(H H6). easy.
  apply proj_mon.
Qed.

Lemma canon_rep_11 : forall G p q x,
    wfgC G ->
    projectionC G p (ltt_send q x) ->
    exists G' ctxJ, 
      typ_gtth ctxJ G' G /\ (ishParts p G' -> False) /\
      List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
        List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t g', u = Some(s, g') /\ v = Some(s, t) /\
          projectionC g' p t
        )) lsg x 
      )) ctxJ /\ usedCtx ctxJ G'.
Proof.
    intros.
    specialize(non_triv_proj_part H0); intros Ht1.
    pose proof H as Ht. unfold wfgC in H. destruct H as (G',(Ha,(Hb,(Hc,Hd)))). clear Hc Hb Ha.
    specialize(balanced_to_tree G p Ht Ht1); intros. destruct H as (Gl,(ctxG,(Hta,(Htb,(Htc,Htd))))).
    
    clear Ht Hd Htd Ht1.
    clear G'.
    revert Htc Htb Hta H0. revert G p q x ctxG.
    induction Gl using gtth_ind_ref; intros; try easy.
    - inversion Hta. subst. exists (gtth_hol n).
      exists (extendLis n (Some G)).
      split. 
      constructor.
      specialize(extendExtract n (Some G)); try easy.
      split. easy.
      specialize(Forall_forall (fun u : option gtt =>
         u = None \/
         (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
            u = Some (gtt_send p q lsg) \/
            u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
      destruct H. specialize(H Htc). clear Htc H1. 
      specialize(some_onth_implies_In n ctxG G H2); intros.
      specialize(H (Some G) H1). destruct H; try easy.
      destruct H as (r,(lsg,Hsa)).
      
      destruct Hsa. inversion H. subst.
      - pinversion H0; try easy. subst. clear H7. clear H10.
        revert H11. clear H8 H1 H H2 H0 Hta Htb. clear ctxG. revert lsg x p q.
        induction n; intros; try easy. simpl. split.
        - constructor; try easy. right. exists (gtt_send p q lsg). exists lsg.
          split. easy. split. easy. revert H11.
          apply Forall2_mono; intros. destruct H. left. easy.
          right. destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). subst. exists s. exists t. exists g. pclearbot. easy.
          specialize(used_hol 0 (gtt_send p q lsg)); intros. easy.
        - specialize(IHn lsg x p q H11). split. constructor; try easy. left. easy.
          constructor.
        apply proj_mon.
      - destruct H. inversion H. subst. pinversion H0; try easy. apply proj_mon.
      - inversion H. subst. pinversion H0; try easy. apply proj_mon.
    - inversion Hta. subst.
      rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
      - assert(List.Forall2 (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ 
           exists (G' : gtth) (ctxJ : seq.seq (option gtt)),
             typ_gtth ctxJ G' g' /\
             (ishParts p G' -> False) /\
             Forall
               (fun u0 : option gtt =>
                u0 = None \/
                (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                   u0 = Some g0 /\
                   g0 = gtt_send p q lsg /\
                   Forall2
                     (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                      u1 = None /\ v = None \/
                      (exists (s0 : sort) (t : ltt) (g' : gtt),
                         u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x)) ctxJ /\
             usedCtx ctxJ G')) xs ys).
        {
          clear H6 Hta.
          pinversion H0. subst. assert False. apply Htb. constructor. easy.
          subst. 
          clear H8 H6 H5 H4 H0.
          revert H12 H11 H7 Htb Htc H. revert xs p q x ys ctxG s s'.
          induction ys0; intros; try easy.
          destruct ys; try easy. destruct xs; try easy. 
          specialize(IHys0 xs p q x ys ctxG s s').
          inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion H. subst. clear H.
          inversion H12.
          - subst.
            destruct ys; try easy. destruct xs; try easy.
            clear H6 H8 H5 IHys0.
            constructor; try easy. destruct H4. left. easy.
            destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
            right. exists s1. exists g1. exists g2. split. easy. split. easy.
            destruct H3; try easy. destruct H as (s2,(g3,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
            inversion He. subst. 
            destruct H2; try easy. destruct H as (s3,(g4,(Hg,Hh))). inversion Hg. subst.
            pclearbot.
            specialize(Hh g3 p q x ctxG). apply Hh; try easy.
            assert(onth 0 [Some (s3, g4)] = Some (s3, g4)). easy.
            specialize(ishParts_n Htb H); try easy.
          - subst.
            destruct H4. destruct H. subst.
            constructor; try easy. left. easy.
            apply IHys0; try easy.
            specialize(ishParts_hxs Htb); try easy.
            destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
            destruct H3; try easy. destruct H as (s2,(g3,(t1,(Hd,(He,Hf))))). easy.
          - subst.
            assert(Forall2
          (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
           u = None /\ v = None \/
           (exists (s : sort) (g : gtth) (g' : gtt),
              u = Some (s, g) /\
              v = Some (s, g') /\
              (exists (G' : gtth) (ctxJ : seq.seq (option gtt)),
                 typ_gtth ctxJ G' g' /\
                 (ishParts p G' -> False) /\
                 Forall
                   (fun u0 : option gtt =>
                    u0 = None \/
                    (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                       u0 = Some g0 /\
                       g0 = gtt_send p q lsg /\
                       Forall2
                         (fun (u1 : option (sort * gtt)) (v0 : option (sort * ltt)) =>
                          u1 = None /\ v0 = None \/
                          (exists (s0 : sort) (t : ltt) (g'0 : gtt),
                             u1 = Some (s0, g'0) /\ v0 = Some (s0, t) /\ projectionC g'0 p t)) lsg x))
                   ctxJ /\ usedCtx ctxJ G'))) xs ys).
            {
              apply IHys0; try easy.
              specialize(ishParts_hxs Htb); try easy.
            }
            constructor; try easy.
            clear H H1 H6 H8 H5 H12 IHys0.
            destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Hb. subst.
            destruct H4; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,Hf))))). inversion He. subst.
            destruct H2; try easy. destruct H as (s3,(g4,(Hg,Hh))). inversion Hg. subst.
            right. exists s3. exists g4. exists g3. split. easy. split. easy. pclearbot.
            specialize(Hh g3 p q x ctxG). apply Hh; try easy.
            specialize(ishParts_x Htb); try easy.
          apply proj_mon.
        }
        clear H7 Htb Htc H.
        - case_eq (eqb p s); intros.
          pinversion H0; try easy. subst.
          exists (gtth_hol 0). exists [Some (gtt_send p q ys)].
          - split. constructor. easy.
          - split. intros. inversion H2.
          - split. constructor; try easy. right. exists (gtt_send p q ys). exists ys.
            split. easy. split. easy.
            revert H11. apply Forall2_mono; intros; try easy.
            destruct H2. left. easy. right.
            destruct H2 as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst. exists s1. exists t1. exists g1.
            pclearbot. easy. 
          - assert(usedCtx (extendLis 0 (Some (gtt_send p q ys))) (gtth_hol 0)). constructor. simpl in H2. easy. subst.
            assert (p = s). apply eqb_eq; try easy. subst. easy.
            apply proj_mon.
        - case_eq (eqb p s'); intros.
          assert (p = s'). apply eqb_eq; try easy. subst.
          pinversion H0; try easy. apply proj_mon.
        - assert (p <> s). apply eqb_neq; try easy. 
          assert (p <> s'). apply eqb_neq; try easy.
      - clear H H2.
        clear H0 Hta.
        revert H3 H4 H1 H6. revert s s' p q x ys. clear ctxG.
        induction xs; intros; try easy.
        destruct ys; try easy. inversion H1. subst. clear H1.
        specialize(SList_f a xs H6); intros.
        specialize(IHxs s s' p q x ys H3 H4).
        destruct H.
        - assert(exists (G' : gtth) (ctxJ : seq.seq (option gtt)),
         typ_gtth ctxJ G' (gtt_send s s' ys) /\
         (ishParts p G' -> False) /\
         Forall
           (fun u : option gtt =>
            u = None \/
            (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
               u = Some g /\
               g = gtt_send p q lsg /\
               Forall2
                 (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                  u0 = None /\ v = None \/
                  (exists (s : sort) (t : ltt) (g' : gtt),
                     u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxJ /\
         usedCtx ctxJ G'). apply IHxs; try easy. clear IHxs H8 H6.
          destruct H5.
          - destruct H1. subst.
            destruct H0 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
            inversion Ha. subst. 
            - specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG); intros.
              destruct H1. specialize(H1 Hc). clear H2 Hc.
              specialize(some_onth_implies_In n ctxG (gtt_send s s' ys) H0); intros.
              specialize(H1 (Some (gtt_send s s' ys)) H2).
              destruct H1; try easy. destruct H1 as (g1,(lsg1,(He,(Hf,Hg)))). inversion He. subst.
              inversion H5. subst. easy.
            - subst. exists (gtth_send s s' (None :: xs0)). exists ctxG.
              - split. constructor. apply SList_b. easy.
                constructor; try easy. left. easy.
              - split. intros. apply Hb.
                inversion H0. subst. easy. subst. easy. subst.
                destruct n; try easy. apply ha_sendr with (n := n) (s := s0) (g := g); try easy.
              - split. easy.
              - inversion Hd. subst.
                apply used_con with (ctxGLis := None :: ctxGLis); try easy.
                constructor; try easy. constructor; try easy. left. easy.
          destruct H1 as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst. clear H.
          apply ctx_merge2; try easy.
        - destruct H as (H,(a0,Ht)). subst.
          destruct ys; try easy. clear H8 IHxs H6.
          destruct H5; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
          destruct Hc as (Gl,(ctxG,(Hc,(Hd,(He,Hf))))).
          exists (gtth_send s s' [Some (s1, Gl)]). exists ctxG.
          - split. constructor; try easy. constructor; try easy. 
            right. exists s1. exists Gl. exists g2. easy.
          - split. intros. apply Hd. inversion H. subst. easy. subst. easy. subst.
            destruct n; try easy. inversion H8. subst. easy.
            destruct n; try easy.
          - split. easy.
          - apply used_con with (ctxGLis := [Some ctxG]); try easy. constructor.
            constructor; try easy. right. exists ctxG. exists s1. exists Gl. easy.
Qed.

Lemma canon_rep_part : forall ctxG G' G p q x ys,
    typ_gtth ctxG G' G -> 
    projectionC G p (ltt_send q x) ->
    projectionC G q (ltt_recv p ys) ->
    (ishParts p G' -> False) -> 
    (ishParts q G' -> False).
Proof.
    intros ctxG G'. revert ctxG.
    induction G' using gtth_ind_ref; intros; try easy.
    rename p into r. rename q into s. rename p0 into p. rename q0 into q.
    inversion H0. subst.
    inversion H4; try easy. 
    - subst.
      pinversion H2; try easy. subst.
      apply proj_mon.
    - subst. 
      pinversion H2; try easy. subst.
      apply H3. constructor.
      apply proj_mon.
    - subst.
      specialize(some_onth_implies_In n xs (s0, g) H13); intros.
      specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : seq.seq (option gtt)) (G : gtt) (p q : string)
             (x ys : seq.seq (option (sort * ltt))),
           typ_gtth ctxG g G ->
           projectionC G p (ltt_send q x) ->
           projectionC G q (ltt_recv p ys) ->
           (ishParts p g -> False) -> ishParts q g -> False))) xs); intros.
    destruct H6. specialize(H6 H). clear H H7.
    specialize(H6 (Some (s0, g)) H5).
    destruct H6; try easy.
    destruct H. destruct H. destruct H.
    inversion H. subst. clear H.
    case_eq (eqb p s); intros; try easy.
    - assert (p = s). apply eqb_eq; easy. subst. apply H3. constructor.
    case_eq (eqb p r); intros; try easy.
    - assert (p = r). apply eqb_eq; easy. subst. apply H3. constructor.
    assert (p <> s). apply eqb_neq; try easy.
    assert (p <> r). apply eqb_neq; try easy.
    assert (ishParts p x1 -> False). 
    {
      intros. apply H3.
      apply ha_sendr with (n := n) (s := x0) (g := x1); try easy.
    }
    assert (exists g', typ_gtth ctxG x1 g' /\ onth n ys0 = Some (x0, g')).
    {
      clear H2 H1 H0 H3 H4 H10 H8 H12 H5 H14 H6 H H7 H9 H15 H16. clear p q r s.
      clear x ys.
      revert H11 H13. revert xs ctxG ys0 x0 x1.
      induction n; intros; try easy.
      - destruct xs; try easy. 
        destruct ys0; try easy.
        inversion H11. simpl in *. subst.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst.
        exists x3; try easy.
      - destruct xs; try easy.
        destruct ys0; try easy.
        apply IHn with (xs := xs) (ys0 := ys0) (x0 := x0); try easy.
        inversion H11. easy.
    }
    destruct H17. 
    specialize(H6 ctxG x2 p q).
    pinversion H2; try easy. subst.
    pinversion H1; try easy. subst. destruct H17.
    assert (exists t t', projectionC x2 p t /\ projectionC x2 q t' /\ onth n ys2 = Some t /\ onth n ys1 = Some t').
    {
      clear H2 H1 H0 H3 H4 H10 H8 H12 H5 H14 H13 H6 H H7 H9 H15 H16 H17 H21 H22 H23 H24. clear H29 H26 H25 H34 H11 H28 H30.
      clear r s x1 x ys xs ctxG.
      revert H18 H27 H33. revert p q x0 x2 ys0 ys1 ys2.
      induction n; intros; try easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H27. subst. inversion H33. subst. clear H27 H33.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. inversion H. subst.
        destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2. inversion H0. subst.
        pclearbot. exists x4. exists x3. easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H27. subst. inversion H33. subst. clear H27 H33.
        apply IHn with (x0 := x0) (ys0 := ys0) (ys1 := ys1) (ys2 := ys2); try easy.
    }
    destruct H19. destruct H19. destruct H19. destruct H20. destruct H31.
    specialize(canon_rep_part_helper_recv n ys1 x4 p ys H32 H28); intros. destruct H35. subst.
    specialize(canon_rep_part_helper_send n ys2 x3 q x H31 H34); intros. destruct H35. subst.
    specialize(H6 x4 x5). apply H6; try easy.
    apply proj_mon.
    apply proj_mon.
Qed.
    
Lemma canon_rep_16 : forall G' ctxG G p q ys x, 
    projectionC G q (ltt_recv p ys) -> 
    Forall
          (fun u : option gtt =>
           u = None \/
           (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
              u = Some g /\
              g = gtt_send p q lsg /\
              Forall2
                (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                 u0 = None /\ v = None \/
                 (exists (s : sort) (t : ltt) (g' : gtt),
                    u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG ->
    usedCtx ctxG G' ->
    (ishParts p G' -> False) ->
    (ishParts q G' -> False) -> 
    typ_gtth ctxG G' G -> 
    Forall
          (fun u : option gtt =>
           u = None \/
           (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
              u = Some g /\
              g = gtt_send p q lsg /\
              Forall2
                (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                 u0 = None /\ v = None \/
                 (exists (s : sort) (t : ltt) (g' : gtt),
                    u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x /\
              Forall2
                (fun u v => (u = None /\ v = None) \/ 
                 (exists s t g', u = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg ys
              )) ctxG.
Proof.
  induction G' using gtth_ind_ref; intros; try easy.
  - inversion H4. subst.
    inversion H1. subst.
    clear H2 H3 H1 H4.
    revert H0 H7 H. revert G p q ys x G0.
    induction n; intros; try easy.
    - simpl in *. inversion H7. subst.
      inversion H0. subst. clear H0 H4.
      destruct H3; try easy. destruct H0 as (g,(lsg,(Ha,(Hb,Hc)))).
      inversion Ha. subst.
      pinversion H; try easy. subst. clear H4.
      constructor; try easy. right. exists (gtt_send p q lsg). exists lsg.
      split. easy. split. easy. split. easy.
      revert H8. apply Forall2_mono; intros.
      destruct H0. left. easy. 
      destruct H0 as (s,(g,(t,(Hd,(He,Hf))))). subst. right. exists s. exists t. exists g.
      destruct Hf; try easy.
    apply proj_mon.
    simpl in *. inversion H0. subst. clear H0.
    specialize(IHn G p q ys x G0 H4).
    constructor. left. easy. apply IHn; try easy.
  - inversion H5. subst. 
    pinversion H0. subst.
    - assert False. apply H3. constructor. easy.
    - subst. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
      clear H14.
      clear H12.
      specialize(ctx_back s s' xs ys0 ctxG H5 H2); intros.
      destruct H6 as (ctxGLis,(H6,H7)).
      assert(Forall (fun u => u = None \/ exists ctxGi, u = Some ctxGi /\
        Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' q t)) lsg ys)) ctxGi
      ) ctxGLis).
      {
        apply Forall_forall; intros.
        destruct x0. right.
        specialize(in_some_implies_onth l ctxGLis H8); intros.
        destruct H12 as (n, H12). rename l into ctxGi. exists ctxGi. split. easy.
        clear H8. clear H11 H9 H10 H13 H5 H2.
        assert(exists s g1 g2 t, onth n xs = Some (s, g1) /\ onth n ys0 = Some (s, g2) /\ typ_gtth ctxGi g1 g2 /\ usedCtx ctxGi g1 /\ onth n ys1 = Some t /\ projectionC g2 q t).
        {
          revert H12 H6 H17.
          clear H7 H18 H4 H3 H1 H0 H.
          revert xs q ys0 ys1 ctxGLis ctxGi. clear s s' ctxG p ys x.
          induction n; intros.
          - destruct ctxGLis; try easy. destruct xs; try easy. destruct ys0; try easy.
            destruct ys1; try easy. inversion H6. subst. clear H6.
            inversion H17. subst. clear H17.
            simpl in H12. subst.
            destruct H3; try easy. destruct H as (ctxG,(s1,(g1,(g2,(Ha,(Hb,(Hc,(Hd,He)))))))).
            inversion Ha. subst.
            destruct H2; try easy. destruct H as (s2,(g3,(t1,(Hf,(Hg,Hh))))). inversion Hf. subst.
            simpl. exists s2. exists g1. exists g3. exists t1. destruct Hh; try easy.
          - destruct ctxGLis; try easy. destruct xs; try easy. destruct ys0; try easy.
            destruct ys1; try easy. inversion H6. subst. clear H6.
            inversion H17. subst. clear H17.
            specialize(IHn xs q ys0 ys1 ctxGLis ctxGi). apply IHn; try easy.
        }
        destruct H2 as (s1,(g1,(g2,(t1,(Hta,(Htb,(Htc,(Htd,(Hte,Htf))))))))).
        clear H6 H17.
        specialize(some_onth_implies_In n xs (s1, g1) Hta); intros.
        specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : seq.seq (option gtt)) (G : gtt) (p q : string)
             (ys x : seq.seq (option (sort * ltt))),
           projectionC G q (ltt_recv p ys) ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x)) ctxG ->
           usedCtx ctxG g ->
           (ishParts p g -> False) ->
           (ishParts q g -> False) ->
           typ_gtth ctxG g G ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' q t)) lsg ys)) ctxG)))
      xs); intros.
        destruct H5. specialize(H5 H). clear H H6.
        specialize(H5 (Some (s1, g1)) H2). destruct H5; try easy.
        destruct H as(s2,(g3,(Ha,Hb))). inversion Ha. subst.
        specialize(Hb ctxGi g2 p q ys x).
        apply Hb; try easy.
        - specialize(merge_inv_ss n (ltt_recv p ys) ys1 t1); intros.
          assert(t1 = ltt_recv p ys). apply H; try easy. subst. easy.
        - specialize(mergeCtx_sl n ctxGLis ctxGi ctxG); intros.
          assert(Forall2R (fun u v : option gtt => u = v \/ u = None) ctxGi ctxG). apply H; try easy.
          clear H. clear Hb H2 Htf Hte Hta Htc Htd Ha Htb H12 H7 H18 H4 H3 H0.
          revert H5 H1.
          revert ctxG p q x. clear s s' xs ys ys0 ys1 ctxGLis n g2 t1 s2 g3.
          induction ctxGi; intros; try easy.
          - destruct ctxG; try easy. inversion H1. subst. clear H1. inversion H5. subst. clear H5.
            specialize(IHctxGi ctxG p q x H7 H3). constructor; try easy. clear H7 H3 IHctxGi.
            destruct H4. subst. easy. left. easy.
        - specialize(ishParts_n H3 Hta); try easy.
        - specialize(ishParts_n H4 Hta); try easy.
        left. easy.
      }
      clear H6 H18 H17 H13 H10 H9 H11 H5 H4 H3 H2 H1 H0 H. 
      revert H8 H7. revert ctxG p q ys x. clear s s' xs ys0 ys1.
      induction ctxGLis; intros; try easy.
      - inversion H8. subst. clear H8.
        inversion H7; try easy.
        - subst.
          destruct H1; try easy. destruct H as (ct1,(Ha,Hb)). inversion Ha. subst. easy.
        - subst.
          specialize(IHctxGLis ctxG p q ys x). apply IHctxGLis; try easy.
        - subst.
          specialize(IHctxGLis t p q ys x H2 H5). clear H2 H5.
          clear H7. destruct H1; try easy.
          destruct H as (t1,(Ha,Hb)). inversion Ha. subst. clear Ha.
          revert H4 Hb IHctxGLis. clear ctxGLis. revert p q ys t t1 x. 
          induction ctxG; intros; try easy.
          - inversion H4.
            - subst. easy.
            - subst. easy.
            subst. clear H4. specialize(IHctxG p q ys xa xb x H6).
            inversion Hb. subst. clear Hb. inversion IHctxGLis. subst. clear IHctxGLis.
            specialize(IHctxG H2 H4). constructor; try easy.
            clear H4 H2 H6 IHctxG.
            - destruct H5. destruct H as (Ha,(Hb,Hc)). subst. easy.
            - destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. easy.
            - destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. easy.
            - destruct H as (t,(Ha,(Hb,Hc))). subst. easy.
  apply proj_mon.
Qed.


Lemma canon_rep_s_helper {A B} : forall (ys : list (option (A * B))),
  exists SI, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g, u = Some s /\ v = Some (s, g))) SI ys.
Proof.
  induction ys; intros; try easy.
  exists nil. easy.
  destruct IHys. destruct a. destruct p. exists (Some a :: x). constructor; try easy.
  right. exists a. exists b. easy.
  exists (None :: x). constructor; try easy. left. easy.
Qed.

Lemma canon_rep_s_helper2s : forall n s1 g1 xs ys ys0 ys1 ctxG p q,
    Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys -> 
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) ys ys0 -> 
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) ys ys1 -> 
    onth n xs = Some (s1, g1) -> 
    exists g2 t t',
    onth n ys = Some (s1, g2) /\ typ_gtth ctxG g1 g2 /\
    onth n ys0 = Some t /\ projectionC g2 q t /\
    onth n ys1 = Some t' /\ projectionC g2 p t'.
Proof.
  induction n; intros; try easy.
  - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
    inversion H. inversion H0. inversion H1. subst. clear H H0 H1.
    simpl in H2. subst.
    destruct H6; try easy. destruct H as (s2,(g2,(g3,(Ha,(Hb,Hc))))). inversion Ha. subst.
    destruct H12; try easy. destruct H as (s3,(g4,(t2,(Hd,(He,Hf))))). inversion Hd. subst.
    destruct H18; try easy. destruct H as (s4,(g5,(t3,(Hg,(Hh,Hi))))). inversion Hg. subst.
    pclearbot. simpl. exists g5. exists t2. exists t3. easy.
  - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
    inversion H. inversion H0. inversion H1. subst. clear H H0 H1.
    specialize(IHn s1 g1 xs ys ys0 ys1 ctxG). apply IHn; try easy.
Qed.

Lemma canon_rep_s_helper2 : forall G' G p q PT QT ctxG,
  projectionC G p (ltt_send q PT) -> 
  projectionC G q (ltt_recv p QT) -> 
  typ_gtth ctxG G' G -> 
  (ishParts p G' -> False) -> 
  (ishParts q G' -> False) -> 
  Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg)) ctxG -> 
   wfgC G -> 
  List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g'))) PT QT.
Proof.
  induction G' using gtth_ind_ref; intros; try easy. rename H5 into Ht.
  - inversion H1. subst. clear H1.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))), u = Some g /\ g = gtt_send p q lsg))
       ctxG); intros.
    destruct H1. specialize(H1 H4). clear H4 H5.
    specialize(some_onth_implies_In n ctxG G H7); intros.
    specialize(H1 (Some G) H4). destruct H1; try easy.
    destruct H1 as (g,(lsg,(Ha,Hb))). inversion Ha. subst.
    pinversion H; try easy. subst. pinversion H0; try easy. subst.
    clear H13 H15 H14 H9 H11 H10 Ht H7 H3 H2 H H0 Ha H4. clear ctxG n.
    revert H16 H12. revert p q PT QT.
    induction lsg; intros; try easy.
    - destruct QT; try easy. destruct PT; try easy.
    - destruct QT; try easy. destruct PT; try easy.
      inversion H16. subst. clear H16. inversion H12. subst. clear H12.
      specialize(IHlsg p q PT QT H4 H6); intros. constructor; try easy.
      clear H6 H4 IHlsg.
      destruct H2. destruct H3. left. easy.
      destruct H. subst. destruct H0 as (s1,(g1,(t1,(Ha,Hb)))). easy.
      destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). subst.
      destruct H3; try easy.
      destruct H as (s0,(g0,(t0,(Hd,(He,Hf))))). inversion Hd. subst.
      right. exists s0. exists t0. exists t. easy.
    apply proj_mon.
    apply proj_mon.
  - inversion H2. subst.
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    pinversion H1; try easy. subst. assert False. apply H3. constructor. easy.
    pinversion H0; try easy. subst.
    assert(List.Forall (fun u => u = None \/ (exists lis, u = Some (ltt_recv p lis))) ys0).
    {
      apply Forall_forall; intros.
      destruct x.
      specialize(in_some_implies_onth l ys0 H7); intros. destruct H8 as (n,H8).
      right.
      specialize(merge_onth_recv n p QT ys0 l H19 H8); intros. destruct H9. exists x. subst. easy.
      left. easy.
    }
    assert(List.Forall (fun u => u = None \/ (exists lis, u = Some (ltt_send q lis))) ys1).
    {
      apply Forall_forall; intros.
      destruct x.
      specialize(in_some_implies_onth l ys1 H8); intros. destruct H9 as (n,H9).
      right.
      specialize(merge_onth_send n q PT ys1 l H30 H9); intros. destruct H16. exists x. subst. easy.
      left. easy.
    }
    assert(List.Forall (fun u => u = None \/ 
      (exists s g PT QT, u = Some(s, g) /\ projectionC g p (ltt_send q PT) /\ projectionC g q (ltt_recv p QT) /\
        Forall2
             (fun u0 v : option (sort * ltt) =>
              u0 = None /\ v = None \/
              (exists (s0 : sort) (g0 g' : ltt), u0 = Some (s0, g0) /\ v = Some (s0, g'))) PT QT
      )) ys).
    {
      clear H30 H19 H12 H1 H0 H2.
      specialize(wfgC_after_step_all H10 H6); intros. clear H25 H24 H23 H14 H11 H10 H6.
      clear H26 H15.
      revert H0 H29 H18 H13 H5 H4 H3 H H7 H8.
      revert s s' xs p q ctxG ys0 ys1. clear PT QT.
      induction ys; intros; try easy.
      - destruct xs; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H0. subst. clear H0. inversion H29. subst. clear H29.
        inversion H18. subst. clear H18. inversion H13. subst. clear H13.
        inversion H. subst. clear H. inversion H7. subst. clear H7. inversion H8. subst. clear H8.
        specialize(IHys s s' xs p q ctxG ys0 ys1).
        assert(Forall
         (fun u : option (sort * gtt) =>
          u = None \/
          (exists (s : sort) (g : gtt) (PT QT : seq.seq (option (sort * ltt))),
             u = Some (s, g) /\
             projectionC g p (ltt_send q PT) /\
             projectionC g q (ltt_recv p QT) /\
             Forall2
               (fun u0 v : option (sort * ltt) =>
                u0 = None /\ v = None \/
                (exists (s0 : sort) (g0 g' : ltt), u0 = Some (s0, g0) /\ v = Some (s0, g'))) PT QT)) ys).
      {
        apply IHys; try easy.
        specialize(ishParts_hxs H4); try easy.
        specialize(ishParts_hxs H3); try easy.
      }
      constructor; try easy.
      clear H H18 H16 H13 H17 H15 H12 H9 IHys.
      destruct H11. left. easy. right.
      destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst.
      destruct H14; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,Hf))))). inversion He. subst.
      destruct H6; try easy. destruct H as (s3,(g4,(Hg,Hi))). inversion Hg. subst.
      destruct H1; try easy. destruct H as (lis,Hj). inversion Hj. subst.
      destruct H10; try easy. destruct H as (s5,(g5,(t2,(Hk,(Hl,Hm))))). inversion Hk. subst.
      destruct H7; try easy. destruct H as (lis2,Hn). inversion Hn. subst.
      destruct H2; try easy.
      exists s5. exists g5. exists lis2. exists lis.
      destruct H as (s6,(g6,(Ho,Hp))). inversion Ho. subst. clear Hn Hk He Hg Ho.
      specialize(Hp g5 p q lis2 lis ctxG).
      split. easy. split. destruct Hm; try easy. split. destruct Hc; try easy.
      apply Hp; try easy. destruct Hm; try easy. destruct Hc; try easy.
      specialize(ishParts_x H3); try easy.
      specialize(ishParts_x H4); try easy.
    }
    specialize(wfgC_after_step_all H10 H6); intros.
    clear H25 H24 H23 H14 H11 H10 H13 H12 H6 H5 H4 H3 H0 H1 H2 H H15 H26. clear s s' ctxG.
    assert(List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists lis1 lis2, u = Some (ltt_recv p lis1) /\ v = Some (ltt_send q lis2) /\ 
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t'))) lis2 lis1
    )) ys0 ys1).
    {
      clear H30 H19.
      revert H16 H9 H8 H7 H29 H18. revert p q ys0 ys1. clear xs PT QT.
      induction ys; intros.
      - destruct ys0; try easy. destruct ys1; try easy.
      - destruct ys0; try easy. destruct ys1; try easy.
        inversion H16. subst. clear H16. inversion H9. subst. clear H9.
        inversion H8. subst. clear H8. inversion H7. subst. clear H7.
        inversion H29. subst. clear H29. inversion H18. subst. clear H18.
        specialize(IHys p q ys0 ys1).
        assert(Forall2
         (fun u v : option ltt =>
          u = None /\ v = None \/
          (exists lis1 lis2 : seq.seq (option (sort * ltt)),
             u = Some (ltt_recv p lis1) /\
             v = Some (ltt_send q lis2) /\
             Forall2
               (fun u0 v0 : option (sort * ltt) =>
                u0 = None /\ v0 = None \/
                (exists (s : sort) (t t' : ltt), u0 = Some (s, t) /\ v0 = Some (s, t'))) lis2 lis1)) ys0
         ys1).
      apply IHys; try easy. constructor; try easy.
      clear IHys H2 H4 H6 H9 H12 H14 H.
      - destruct H10. destruct H. subst.
        destruct H11. left. easy.
        destruct H as(s,(g,(t,(Ha,(Hb,Hc))))). easy.
      - destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). subst.
        destruct H11; try easy. destruct H as (s1,(g1,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
        destruct H5; try easy. destruct H as (lis,Hg). inversion Hg. subst.
        destruct H8; try easy. destruct H as (lis2,Hh). inversion Hh. subst.
        destruct H1; try easy. destruct H as (s2,(g2,(Hi,Hj))). inversion Hi. subst.
        destruct H3; try easy. destruct H as (s3,(g3,(PT,(QT,(Hk,(Hl,(Hm,Hn))))))). inversion Hk. subst.
        pclearbot.
        specialize(proj_inj Hj Hc Hl); intros. inversion H. subst.
        specialize(proj_inj Hj Hf Hm); intros. inversion H0. subst.
        clear Hg Hh Hc Hf H H0.
        right. exists QT. exists PT. split. easy. split. easy. easy.
    }
    clear H16 H9 H29 H18 H7 H8.
    clear ys.
    
    specialize(merge_sorts ys0 ys1 p q PT QT); intros. apply H0; try easy.
  apply proj_mon.
  apply proj_mon.
Qed.

Lemma canon_rep_helper2 : forall lsg SI x p,
      Forall2
        (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
         u0 = None /\ v = None \/
         (exists (s : sort) (t : ltt) (g' : gtt),
            u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x ->
      Forall2
        (fun (u : option sort) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (t : ltt), u = Some s /\ v = Some (s, t))) SI x ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option sort) =>
         u = None /\ v = None \/
         (exists (s : sort) (g' : gtt), u = Some (s, g') /\ v = Some s)) lsg SI.
Proof.
  induction lsg; intros; try easy.
  - destruct x; try easy.
    destruct SI; try easy.
  - destruct x; try easy.
    destruct SI; try easy.
    inversion H0. subst. clear H0. inversion H. subst. clear H.
    constructor.
    - destruct H4. left. destruct H. subst. destruct H3; try easy. destruct H. destruct H. destruct H.
      destruct H. destruct H0. easy.
    - destruct H. destruct H. destruct H. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H0. subst. right.
      exists x2. exists x4. split; try easy.
  - apply IHlsg with (x := x) (p := p); try easy.
Qed.

Lemma canon_rep_helper3 : forall n lsg x0 Sk ys q,
    onth n lsg = Some(Sk, x0) -> 
    Forall2
          (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
           u0 = None /\ v = None \/
           (exists (s : sort) (t : ltt) (g' : gtt),
              u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg ys ->
    exists Tq, onth n ys = Some(Sk, Tq) /\ projectionC x0 q Tq.
Proof.
  induction n; intros; try easy.
  - destruct lsg; try easy.
    destruct ys; try easy. simpl in *.
    inversion H0. subst. destruct H4; try easy. 
    destruct H. destruct H. destruct H. destruct H. destruct H1. inversion H. subst.
    exists x1. split; try easy.
  - destruct lsg; try easy.
    destruct ys; try easy. simpl in *.
    inversion H0. subst.
    apply IHn with (lsg := lsg); try easy.
Qed.

Lemma part_after_step_helper2 : forall l x0 q p x G' pt s,
    isgPartsC pt G' -> 
    Some (s, G') = onth l x0 -> 
    gttTC (g_send q p x) (gtt_send q p x0) -> 
    (forall n : fin, exists m : fin, guardG n m (g_send q p x)) ->
    exists G'0 : global, gttTC G'0 (gtt_send q p x0) /\ (forall n : fin, exists m : fin, guardG n m G'0) /\ isgParts pt G'0.
Proof.  
  intros.
  unfold isgPartsC in H. destruct H. destruct H. rename x1 into Gl.
  exists (g_send q p (overwrite_lis l (Some(s, Gl)) x)). 
  split.
  - pinversion H1; try easy. subst.
    pfold. constructor. destruct H3.
    clear H1 H2 H3 H4. revert H5 H0 H. clear q p pt. revert l x G' s Gl.
    induction x0; intros; try easy.
    - destruct l; try easy.
    - destruct x; try easy. inversion H5. subst. clear H5.
    - destruct l; try easy.
      - simpl in H0. subst. destruct H4; try easy.
      destruct H0 as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      inversion Hb. subst.
        constructor; try easy. right. exists s1. exists Gl. exists g2. split. easy. split. easy. left. easy.
      - specialize(IHx0 l x G' s Gl H7 H0 H). constructor; try easy.
    apply gttT_mon.
    split.
    destruct H3. intros. destruct n. exists 0. constructor.
    specialize(H2 (S n)). specialize(H3 n). destruct H3. destruct H2.
    exists (Nat.max x1 x2). constructor. inversion H2. subst. clear H2 H1 H0 H4 H.
    revert H8 H3. revert n x s Gl x1 x2. clear x0 q p G' pt.
    induction l; intros; try easy.
    - destruct x; try easy. constructor; try easy. right. exists s. exists Gl.
      split. easy. specialize(guardG_more n x1 (Nat.max x1 x2) Gl); intros. apply H; try easy.
      apply max_l.
    - inversion H8. subst. clear H8. constructor; try easy. right.
      exists s. exists Gl. split. easy.
      specialize(guardG_more n x1 (Nat.max x1 x2) Gl); intros. apply H; try easy. apply max_l.
    - apply Forall_forall; intros.
      specialize(Forall_forall (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ guardG n x2 g)) x); intros.
      destruct H0. specialize(H0 H2). clear H4 H2. specialize(H0 x0 H). 
      destruct H0. left. easy. destruct H0 as (s1,(g,(Ha,Hb))). subst. right.
      exists s1. exists g. split. easy.
      specialize(guardG_more n x2 (Nat.max x1 x2) g); intros. apply H0; try easy. apply max_r.
    - destruct x; try easy.
      specialize(IHl n nil s Gl x1 x2 H8 H3). constructor; try easy.
      left. easy.
    - inversion H8. subst. clear H8. specialize(IHl n x s Gl x1 x2 H2 H3). constructor; try easy.
      destruct H1. left. easy.
      destruct H as (s1,(g1,(Ha,Hb))). subst. right. exists s1. exists g1. split. easy.
      specialize(guardG_more n x2 (Nat.max x1 x2) g1); intros. apply H; try easy.
      apply max_r.
  - case_eq (eqb pt p); intros.
      assert (pt = p). apply eqb_eq; try easy. subst. constructor.
    - case_eq (eqb pt q); intros.
      assert (pt = q). apply eqb_eq; try easy. subst. constructor.
    - assert (pt <> p). apply eqb_neq; try easy. 
      assert (pt <> q). apply eqb_neq; try easy.
      apply pa_sendr with (n := l) (s := s) (g := Gl); try easy.
      apply overwriteExtract; try easy.
Qed.

Lemma part_after_step_helper3 : forall n x1 ys2 ys ys0 ys1 xs p q l s g ctxG,
      onth n x1 = Some (s, g) -> 
      Forall2
        (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : global) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) x1 ys2 -> 
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' q p l)) ys ys2 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) ys ys0 ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) ys ys1 -> 
      Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys -> 
      exists g' g'' t t' Gl,
      onth n ys2 = Some (s, g') /\ gttTC g g' /\
      onth n ys = Some (s, g'') /\ gttstepC g'' g' q p l /\
      onth n ys0 = Some t /\ projectionC g'' q t /\
      onth n ys1 = Some t' /\ projectionC g'' p t' /\
      onth n xs = Some (s, Gl) /\ typ_gtth ctxG Gl g''.
Proof.
  induction n; intros.
  - destruct x1; try easy. destruct ys2; try easy. destruct ys; try easy.
    destruct ys0; try easy. destruct ys1; try easy. destruct xs; try easy.
    inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. subst. 
    clear H0 H1 H2 H3 H4.
    simpl in H. subst. clear H34 H28 H22 H16 H10.
    destruct H8; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. clear H.
    destruct H14; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H0. subst. clear H0.
    destruct H32; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H0. subst. clear H0.
    destruct H26; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. clear H.
    destruct H20; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. clear H.
    destruct H1; try easy. destruct H2; try easy. destruct H4; try easy. destruct H5; try easy.
    simpl. exists x5. exists x6. exists x8. exists x7. exists x2. 
    easy.
  - destruct x1; try easy. destruct ys2; try easy. destruct ys; try easy.
    destruct ys0; try easy. destruct ys1; try easy. destruct xs; try easy.
    inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. subst. 
    clear H0 H1 H2 H3 H4.
    specialize(IHn x1 ys2 ys ys0 ys1 xs p q l s g ctxG). apply IHn; try easy.
Qed.

Lemma typ_after_step_ctx_loose : forall [ctxG p q l T T' SI],
     Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG ->
      Forall
        (fun u : option gtt =>
         u = None \/
         (exists (g : gtt) (lsg : list (option (sort * gtt))),
            u = Some g /\
            g = gtt_send p q lsg /\
            (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
               onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG.
Proof.
  intros.
  apply Forall_forall; intros.
  specialize(Forall_forall (fun u : option gtt =>
       u = None \/
       (exists (g : gtt) (lsg : list (option (sort * gtt))),
          u = Some g /\
          g = gtt_send p q lsg /\
          (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
             onth l lsg = Some (s', Gjk) /\
             projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
          Forall2
            (fun (u0 : option (sort * gtt)) (v : option sort) =>
             u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s)) lsg
            SI)) ctxG); intros.
  destruct H1. specialize(H1 H). clear H H2.
  destruct x. 
  specialize(H1 (Some g) H0). destruct H1; try easy.
  - destruct H. destruct H. destruct H. destruct H1. destruct H2.
    destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4. destruct H5. destruct H6.
    subst.
    inversion H. subst.
    right. exists (gtt_send p q x0). exists x0. split; try easy. split; try easy.
    exists x1. exists x2. exists x3. exists x4. easy.
  left. easy.
Qed.


Lemma proj_inv_lis_helper : forall n ys s0 g xs ys0 ys1 ctxG p q,
    onth n ys = Some (s0, g) -> 
    Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys ->
    Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys ->
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) ys ys0 ->
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) ys ys1 -> 
    exists g' t t',
    onth n xs = Some(s0, g') /\ typ_gtth ctxG g' g /\
    onth n ys0 = Some t /\ projectionC g q t /\
    onth n ys1 = Some t' /\ projectionC g p t' /\ wfgC g.
Proof.
  induction n; intros; try easy.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy. destruct ys1; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1.
    inversion H2. subst. clear H2. inversion H3. subst. clear H3.
    simpl in H. subst.
    destruct H6; try easy. destruct H as (st,(g1,(Ha,Hb))). inversion Ha. subst. clear Ha.
    destruct H5; try easy. destruct H as (st1,(g2,(t1,(Hc,(Hd,He))))). inversion Hc. subst. clear Hc.
    destruct H4; try easy. destruct H as (st2,(g3,(t2,(Hf,(Hg,Hh))))). inversion Hf. subst. clear Hf.
    destruct H8; try easy. destruct H as (st3,(g4,(g5,(Hi,(Hj,Hk))))). inversion Hj. subst. clear Hj.
    simpl. exists g4. exists t1. exists t2. destruct He; try easy. destruct Hh; try easy.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy. destruct ys1; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1.
    inversion H2. subst. clear H2. inversion H3. subst. clear H3.
    specialize(IHn ys s0 g xs ys0 ys1 ctxG p q). apply IHn; try easy.
Qed.

Lemma typ_after_step_step_helper3 : forall xs ys ctxG,
      SList xs ->
      Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys ->
      SList ys.
Proof.
  induction xs; intros; try easy.
  specialize(SList_f a xs H); intros.
  destruct ys; try easy. inversion H0.
  subst.
  destruct H1; try easy.
  - specialize(IHxs ys ctxG). apply SList_b. apply IHxs; try easy.
  - destruct H1. destruct H2. subst. destruct ys; try easy. destruct H5; try easy.
    destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. subst. easy.
Qed.

Lemma proj_inv_lis_helper2 : forall ys2 ys3 ys4 p q,
          SList ys2 -> 
          Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             u = None /\ v = None \/
             (exists (s : sort) (g : gtt) (t : ltt),
                u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) ys2 ys3 -> 
          Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             u = None /\ v = None \/
             (exists (s : sort) (g : gtt) (t : ltt),
                u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) ys2 ys4 ->
          Forall
             (fun u : option (sort * gtt) =>
              u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys2 -> 
          exists n st g t t', 
          onth n ys2 = Some (st, g) /\ wfgC g /\
          onth n ys3 = Some t /\ projectionC g p t /\
          onth n ys4 = Some t' /\ projectionC g q t'.
Proof.
  induction ys2; intros; try easy.
  destruct ys3; try easy. destruct ys4; try easy.
  inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
  specialize(SList_f a ys2 H); intros.
  specialize(IHys2 ys3 ys4 p q).
  destruct H0. 
  assert (exists (n : fin) (st : sort) (g : gtt) (t t' : ltt),
          onth n ys2 = Some (st, g) /\
          wfgC g /\
          onth n ys3 = Some t /\ projectionC g p t /\ onth n ys4 = Some t' /\ projectionC g q t').
  apply IHys2; try easy. destruct H1. exists (S x). easy.
  destruct H0. destruct H1. subst. clear H4 H9 H8 IHys2 H. exists 0. simpl.
  destruct H6; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
  destruct H3; try easy. destruct H as (s2,(g2,(Hd,He))). inversion Hd. subst.
  destruct H5; try easy. destruct H as (s3,(g3,(t2,(Hf,(Hg,Hh))))).
  inversion Hf. subst.
  exists s3. exists g3. exists t1. exists t2. destruct Hc; try easy. destruct Hh; try easy.
Qed.

Lemma proj_inv_lis_helper3 : forall [l lsg s2 Gjk ys2 ys3 p q],
          onth l lsg = Some (s2, Gjk) ->
          Forall2
          (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
           u = None /\ v = None \/
           (exists (s : sort) (g : gtt) (t : ltt),
              u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g q t)) lsg ys2 -> 
          Forall2
          (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
           u = None /\ v = None \/
           (exists (s : sort) (g : gtt) (t : ltt),
              u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g p t)) lsg ys3 -> 
          exists T T' : sort * ltt, onth l ys3 = Some T /\ onth l ys2 = Some T'.
Proof.
  induction l; intros; try easy.
  - destruct lsg; try easy. destruct ys2; try easy. destruct ys3; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. simpl in H. subst.
    destruct H5; try easy. destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). inversion Ha. subst.
    destruct H4; try easy. destruct H as (s1,(g1,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
    simpl. exists (s1, t1). exists (s1, t). easy.
  - destruct lsg; try easy. destruct ys2; try easy. destruct ys3; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. simpl in H. subst.
    specialize(IHl lsg s2 Gjk ys2 ys3 p q). apply IHl; try easy.
Qed.

Lemma projection_step_label : forall G G' p q l LP LQ,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists LS LS' LT LT', onth l LP = Some(LS, LT) /\ onth l LQ = Some(LS', LT').
Proof.
  intros.
  specialize(canon_rep_11 G p q LP H H0); intros.
  destruct H3. rename x into Gl.
  assert (exists ctxJ : list (option gtt),
       typ_gtth ctxJ Gl G /\
       (ishParts p Gl -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : list (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg)) ctxJ). 
  {
    destruct H3. exists x. destruct H3. destruct H4. split. easy. split. easy.
    clear H4 H3 H2 H1 H0 H. destruct H5 as (H5,H0). clear H0.  clear Gl LQ l. clear G G'.
    revert H5. revert LP p q. induction x; intros; try easy.
    inversion H5. subst. clear H5. specialize(IHx LP p q H2). constructor; try easy. clear H2 IHx.
    destruct H1. left. easy.
    destruct H. destruct H. destruct H. destruct H0. right. exists x0. exists x1. easy.
  } 
  clear H3. rename H4 into H3.
  revert H0 H1 H2 H3. clear H.
  revert G G' p q l LP LQ.
  induction Gl using gtth_ind_ref; intros; try easy.
  - destruct H3. destruct H. destruct H3. inversion H. subst. 
    specialize(some_onth_implies_In n x G H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg)) x); intros.
    destruct H6. specialize(H6 H4). clear H8. specialize(H6 (Some G) H5). clear H5 H4.
    destruct H6; try easy. destruct H4. destruct H4. destruct H4. inversion H4.
    subst.
    pinversion H1; try easy. subst.
    pinversion H2; try easy. subst.
    pinversion H0; try easy. subst.
    clear H16 H20 H19 H15 H14 H17 H10 H12 H11 H7 H3 H H0 H1 H2 H4. clear n x.
    revert H13 H18 H21. revert G' p q LP LQ x1 s.
    induction l; intros; try easy.
    - destruct x1; try easy.
      destruct LP; try easy. destruct LQ; try easy.
      inversion H21. subst. clear H21. inversion H13. subst. clear H13. 
      simpl in *. subst.
      destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H. subst.
      destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2.
      inversion H0. subst.
      exists x3. exists x3. exists x2. exists x5. easy.
    - destruct x1; try easy.
      destruct LP; try easy. destruct LQ; try easy.
      inversion H21. subst. clear H21. inversion H13. subst. clear H13. 
      specialize(IHl G' p q LP LQ x1 s). apply IHl; try easy.
    apply proj_mon.
    apply step_mon. 
    apply proj_mon.
  - destruct H3. destruct H3. destruct H4. 
    rename p into s. rename q into s0. rename p0 into p. rename q0 into q.
    specialize(canon_rep_part x (gtth_send s s0 xs) G p q LP LQ H3 H0 H1 H4); intros.
    inversion H3. subst.
    pinversion H1. subst.
    - assert False. apply H4. constructor. easy.
    pinversion H0; try easy. subst. 
    specialize(SList_to_In xs H12); intros. destruct H7.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G G' : gtt) (p q : string) (l : fin) (LP LQ : list (option (sort * ltt))),
           projectionC G p (ltt_send q LP) ->
           projectionC G q (ltt_recv p LQ) ->
           gttstepC G G' p q l ->
           (exists ctxJ : list (option gtt),
              typ_gtth ctxJ g G /\
              (ishParts p g -> False) /\
              Forall
                (fun u0 : option gtt =>
                 u0 = None \/
                 (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                    u0 = Some g0 /\
                    g0 = gtt_send p q lsg)) ctxJ) ->
           exists (LS LS' : sort) (LT LT' : ltt),
             onth l LP = Some (LS, LT) /\ onth l LQ = Some (LS', LT')))) xs); intros.
    destruct H8. specialize(H8 H). clear H H9.
    specialize(H8 (Some x0) H7). destruct H8; try easy. destruct H. destruct H.
    destruct H. inversion H. subst. clear H. rename x2 into G.
    specialize(in_some_implies_onth (x1, G) xs H7); intros. destruct H. clear H7. rename x0 into n.
    rename x into ctxG.
    pinversion H2; try easy. subst.
    assert(exists g g' t t', onth n ys = Some(x1, g) /\ typ_gtth ctxG G g /\ onth n ys0 = Some t /\ projectionC g q t /\
           onth n ys1 = Some t' /\ projectionC g p t' /\ onth n ys2 = Some (x1, g') /\ gttstepC g g' p q l).
    {
      clear H35 H28 H27 H22 H21 H20 H17 H8 H30 H26 H25 H24 H23 H19 H15 H14 H11 H10 H12 H6 H5 H3 H0 H1 H2 H4.
      clear LP LQ. clear s s0.
      revert H H36 H29 H18 H13. 
      revert xs p q ys ctxG ys0 ys1 x1 G. revert l ys2.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H36. subst. inversion H29. subst. inversion H18. subst. inversion H13. subst.
        clear H36 H29 H18 H13.
        simpl in *. subst.
        destruct H8; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
        destruct H6; try easy. destruct H as (s2,(g3,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
        destruct H2; try easy. destruct H as (s3,(g4,(g5,(Hg,(Hh,Hi))))). inversion Hg. subst.
        destruct H5; try easy. destruct H as (s4,(g6,(t2,(Hj,(Hk,Hl))))). inversion Hj. subst.
        exists g6. exists g5. exists t1. exists t2. pclearbot. easy.
      - destruct xs; try easy.
        destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H36. subst. inversion H29. subst. inversion H18. subst. inversion H13. subst. apply IHn with (xs := xs); try easy.
    }
    destruct H7. destruct H7. destruct H7. destruct H7. destruct H7. destruct H9. destruct H16. destruct H31.
    destruct H32. destruct H33. destruct H34. 
    rename x into G0'. rename x2 into LP0. rename x3 into LQ0. rename x0 into G''.
    specialize(H8 G0' G'' p q l).
    specialize(merge_onth_recv n p LQ ys0 LP0 H19 H16); intros. destruct H38 as [LQ' H38].
    specialize(merge_onth_send n q LP ys1 LQ0 H30 H32); intros. destruct H39 as [LP' H39].
    subst.
    specialize(H8 LP' LQ' H33 H31 H37).
    assert (exists (LS LS' : sort) (LT LT' : ltt), onth l LP' = Some (LS, LT) /\ onth l LQ' = Some (LS', LT')).
    {
      apply H8; try easy.
      exists ctxG. split. easy. split; try easy.
      intros. apply H4.
      - case_eq (eqb p s); intros.
        assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
      - case_eq (eqb p s0); intros.
        assert (p = s0). apply eqb_eq; try easy. subst. apply ha_sendq.
      - assert (p <> s). apply eqb_neq; try easy. 
        assert (p <> s0). apply eqb_neq; try easy.
        apply ha_sendr with (n := n) (s := x1) (g := G); try easy.
    }
    destruct H38. destruct H38. destruct H38. destruct H38. destruct H38. 
    
    specialize(merge_label_send ys1 LP LP' (x, x2) n l q H30 H32 H38); intros.
    destruct H40. 
    specialize(merge_label_recv ys0 LQ LQ' (x0, x3) n l p H19 H16 H39); intros.
    destruct H41. destruct x4. destruct x5.
    exists s1. exists s2. exists l0. exists l1. easy.
  apply step_mon.
  apply proj_mon.
  apply proj_mon.
Qed.

Lemma typ_after_step_step_helper2 : forall xs ys p q l ctxG,
    Forall2
       (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\
           v = Some (s, g') /\
           typ_gtth ctxG g g' /\
           isgPartsC p g' /\ isgPartsC q g' /\ (exists G' : gtt, gttstepC g' G' p q l))) xs
       ys -> 
    exists zs,
    Forall (fun u => (u = None) \/ (exists s g, u = Some(s, g) /\ isgPartsC p g /\ isgPartsC q g)) ys /\ 
    Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ gttstepC g g' p q l)) ys zs.
Proof.
  induction xs; intros; try easy.
  - destruct ys; try easy. exists nil. easy.
  - destruct ys; try easy. inversion H. subst. clear H.
    specialize(IHxs ys p q l ctxG H5). destruct IHxs. rename x into zs.
    clear H5. destruct H. destruct H3.
    - exists (None :: zs). destruct H1. subst.
      split. constructor; try easy. left. easy.
      constructor; try easy. left. easy.
    - destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4. destruct H5.
      destruct H6. exists (Some (x, x2) :: zs). subst. split.
      constructor; try easy. right. exists x. exists x1. easy.
      constructor; try easy. right. exists x. exists x1. exists x2. easy.
Qed.

Lemma typ_after_step_step_helper4 : forall ys zs p q l,
      SList ys ->
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ gttstepC g g' p q l)) ys zs ->
      p <> q.
Proof.
  induction ys; intros; try easy.
  specialize(SList_f a ys H); intros. destruct zs; try easy.
  inversion H0. subst.
  destruct H1.
  specialize(IHys zs p q l H1 H7). easy. destruct H1. destruct H2. subst.
  destruct zs; try easy. clear IHys H7 H0.
  destruct H5; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
  inversion H0. subst.
  pinversion H2; try easy.
  apply step_mon.
Qed. 

Lemma typ_after_step_step_helper5 : forall ys zs p q l,
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt), u = Some (s, g) /\ v = Some (s, g') /\ gttstepC g g' p q l)) ys
        zs ->
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g g' : gtt),
            u = Some (s0, g) /\ v = Some (s0, g') /\ upaco5 gttstep bot5 g g' p q l)) ys zs.
Proof.
  induction ys; intros; try easy.
  - destruct zs; try easy.
  - destruct zs; try easy. inversion H. subst.
    specialize(IHys zs p q l H5).
    constructor; try easy.
    destruct H3. left. easy.
    right. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst.
    exists x. exists x0. exists x1. split. easy. split. easy. left. easy.
Qed.

Lemma typ_after_step_step_helper6 : forall ys p q,
    Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt), u = Some (s, g) /\ isgPartsC p g /\ isgPartsC q g)) ys ->
    exists zs1 zs2, 
    Forall2 
         (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys zs1 /\
    Forall2 
         (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts q g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys zs2.
Proof.
  induction ys; intros.
  - exists nil. exists nil. easy.
  - inversion H. subst. clear H.
    specialize(IHys p q H3). destruct IHys. destruct H. destruct H. rename x into zs1. rename x0 into zs2. clear H3.
    destruct H2.
    - exists (None :: zs1). exists (None :: zs2).
      subst. split. constructor; try easy. left. easy.
      constructor; try easy. left. easy.
    - destruct H1. destruct H1. destruct H1. destruct H2. subst.
      unfold isgPartsC in *. destruct H2. destruct H3.
      exists (Some (x, x1) :: zs1). exists (Some (x, x2) :: zs2).
      split. constructor; try easy. right. exists x. exists x0. exists x1. easy.
      constructor; try easy. right. exists x. exists x0. exists x2.
      easy.
Qed.

Lemma typ_after_step_step_helper7 : forall ys x p,
    Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * global)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (g' : global),
            u = Some (s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys x ->
      Forall2
        (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : global) (g' : gtt),
            u = Some (s0, g) /\ v = Some (s0, g') /\ upaco2 gttT bot2 g g')) x ys.
Proof.
  induction ys; intros.
  - destruct x; try easy.
  - destruct x; try easy. inversion H.
    subst. specialize(IHys x p H5). clear H5 H. constructor; try easy.
    destruct H3. left. easy. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H1.
    subst. right. exists x0. exists x2. exists x1. split. easy. split. easy. left. easy.
Qed.

Lemma typ_after_step_step_helper8 : forall ys x s s' p,
      SList ys ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * global)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (g' : global),
            u = Some (s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys x ->
      (forall n : fin, exists m : fin, guardG n m (g_send s s' x)) /\ isgParts p (g_send s s' x).
Proof.
  induction ys; intros; try easy.
  destruct x; try easy.
  inversion H0. subst. clear H0.
  specialize(SList_f a ys H); intros. destruct H0.
  specialize(IHys x s s' p). 
  specialize(IHys H0 H6). split. 
  destruct IHys. destruct H4. destruct H3. subst. intros. specialize(H1 n). destruct H1.
  exists x0. inversion H1. constructor. subst. constructor; try easy. constructor; try easy. left. easy.
  destruct H3 as (s1,(g,(g',(Ha,(Hb,(Hc,(Hd,He))))))). subst.
  intros. specialize(H1 n). destruct H1. destruct n. exists 0. constructor.
  specialize(He n). destruct He. exists (Nat.max x1 x0); intros.
  constructor. constructor; try easy. right. exists s1. exists g'. split. easy.
  specialize(guardG_more n x1 (Nat.max x1 x0) g'); intros. apply H4; try easy. apply max_l.
  apply Forall_forall; intros.
  inversion H1. subst. specialize(Forall_forall (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ guardG n x0 g)) x); intros.
  destruct H5. specialize(H5 H9). specialize(H5 x2 H4). destruct H5. left. easy.
  destruct H5 as (s3,(g3,(Hta,Htb))). subst. right. exists s3. exists g3.
  split. easy. 
  specialize(guardG_more n x0 (Nat.max x1 x0) g3); intros. apply H5; try easy. apply max_r.
  apply isgParts_xs; try easy.
  destruct H0. destruct H1. subst.
  destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
  inversion H0. subst. split. destruct x; try easy. destruct H3.
  intros. destruct n. exists 0. constructor. specialize(H3 n). destruct H3. exists x.
  constructor. constructor; try easy. right. exists x1. exists x3. split. easy. easy.
  apply isgParts_x; try easy.
Qed.

Lemma typ_after_step_h_helper : forall L1 l S T,
    Forall2R
       (fun u v : option (sort * ltt) =>
        u = None \/
        (exists (s s' : sort) (t t' : ltt),
           u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
       (extendLis l (Some (S, T))) L1 -> 
    exists ST, onth l L1 = Some ST.
Proof.
  intros L1 l. revert L1. induction l; intros.
  - destruct L1; try easy. inversion H. subst. 
    destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
    subst. exists (x0, x2). easy.
  - destruct L1; try easy.
    inversion H. subst. specialize(IHl L1 S T H5). destruct IHl. 
    exists x. easy.
Qed.


Lemma typ_after_step_12_helper : forall ys2 x p,
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgCw g)) ys2 ->
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ (isgPartsC p g -> False))) ys2 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt), u = Some (s, g) /\ v = Some t /\ projectionC g p t))
        ys2 x -> 
      Forall (fun u => u = None \/ u = Some ltt_end) x.
Proof.
  induction ys2; intros; try easy.
  - destruct x; try easy.
  - destruct x; try easy. inversion H. subst. clear H. inversion H0. subst. clear H0.
    inversion H1. subst. clear H1.
    specialize(IHys2 x p).
    assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x).
    apply IHys2; try easy. constructor; try easy.
    destruct H7. destruct H0. left. easy.
    destruct H0 as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst.
    destruct H3; try easy. destruct H0 as (s2,(g2,(Hd,He))). inversion Hd. subst.
    destruct H4; try easy. destruct H0 as (s3,(g3,(Hf,Hg))). inversion Hf. subst.
    pinversion Hc; try easy. right. easy.
    subst. specialize(He H1). easy.
    subst. specialize(He H1). easy.
    subst. specialize(He H3). easy.
    apply proj_mon.
Qed.

Lemma merge_same : forall ys ys0 ys1 p q l LP LQ S T S' T' ctxG SI s s' xs,
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) ys ys0 ->
      isMerge (ltt_send q LP) ys0 ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) ys ys1 ->
      Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG ->
      isMerge (ltt_recv p LQ) ys1 ->
      onth l LP = Some (S, T) ->
      onth l LQ = Some (S', T') ->
      (ishParts p (gtth_send s s' xs) -> False) ->
      (ishParts q (gtth_send s s' xs) -> False) ->
      Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys ->
      Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys ->
      Forall (fun u => u = None \/ (exists s g LP' LQ', u = Some (s, g) /\
          projectionC g p (ltt_send q LP') /\ onth l LP' = Some (S, T) /\
          projectionC g q (ltt_recv p LQ') /\ onth l LQ' = Some (S', T'))) ys.
Proof.
  intros. rename H10 into Ht.
  apply Forall_forall; intros. 
  destruct x.
  - right.
    specialize(in_some_implies_onth p0 ys H10); intros. destruct H11. rename x into n.
    destruct p0.
    assert(exists LP LQ T T', onth n ys0 = Some (ltt_send q LP) /\ projectionC g p (ltt_send q LP) /\ onth n ys1 = Some (ltt_recv p LQ) /\ projectionC g q (ltt_recv p LQ) /\ onth l LP = Some T /\ onth l LQ = Some T' /\ wfgC g).
    {
      clear H10 H6 H5 H4 H1.
      specialize(typ_after_step_ctx_loose H3); intros. clear H3. clear SI S T S' T'. clear LP LQ.
      revert H1 H2 H0 H. revert H9 H8 H7 H11 Ht. revert ys ys0 ys1 p q l ctxG s g. revert s' s0 xs.
      induction n; intros; try easy.
      - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy. destruct xs; try easy.
        inversion H2. subst. inversion H0. subst. inversion H. subst. inversion H9. subst. inversion Ht. subst.
        clear H18 H13 H14 H12 H H0 H2 H9 Ht. simpl in H11. subst.
        destruct H5; try easy. destruct H. destruct H. destruct H. destruct H. destruct H.
        destruct H. destruct H. destruct H0. destruct H2. destruct H3. inversion H. subst.
        destruct H6; try easy. destruct H5. destruct H5. destruct H5. destruct H5. destruct H6.
        inversion H5. subst.
        destruct H10; try easy. destruct H6. destruct H6. destruct H6. destruct H6. destruct H10.
        inversion H6. subst.
        destruct H16; try easy. destruct H10. destruct H10. destruct H10. destruct H10. destruct H12.
        inversion H12. subst.
        destruct H15; try easy. destruct H10 as (st,(g,(Ha,Hb))). inversion Ha. subst.
        pclearbot. simpl. exists x1. exists x2. exists x3. exists x4.
        specialize(ishParts_x H8); intros.
        specialize(ishParts_x H7); intros.
        specialize(proj_inj Hb H0 H11); intros. subst.
        specialize(proj_inj Hb H2 H9); intros. subst. 
        easy.
      - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy. destruct xs; try easy.
        inversion H2. subst. inversion H0. subst. inversion H. subst. inversion H9. subst.
        specialize(IHn s' s0 xs ys ys0 ys1 p q l ctxG s g). apply IHn; try easy.
        specialize(ishParts_hxs H8); try easy.
        specialize(ishParts_hxs H7); try easy.
        inversion Ht; try easy.
    }
    destruct H12. destruct H12. destruct H12. destruct H12. destruct H12. destruct H13. destruct H14. destruct H15. destruct H16.
    exists s0. exists g. exists x. exists x0. destruct x1. destruct x2. split. easy. split. easy.
    destruct H17. 
    specialize(merge_label_recv_s ys1 LQ x0 (s2, l1) n l p H4 H14 H17); intros.
    specialize(merge_label_send_s ys0 LP x (s1, l0) n l q H1 H12 H16); intros.
    specialize(eq_trans (esym H19) H6); intros. inversion H21. subst.
    specialize(eq_trans (esym H20) H5); intros. inversion H22. subst.
    easy.
    left. easy.
Qed.

Lemma typ_after_step_3_helper_h1 : forall l lsg ys s' Gjk s,
      onth l lsg = Some (s', Gjk) -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : gtt) (t : ltt),
            u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g s t)) lsg ys -> 
      exists t, onth l ys = Some t /\ projectionC Gjk s t.
Proof.
  induction l; intros.
  - destruct lsg; try easy. 
    inversion H0. subst. clear H0.
    simpl in H. subst. destruct H3; try easy. destruct H as (s0,(g,(t,(Ha,(Hb,Hc))))).
    subst. exists t. inversion Ha. subst. destruct Hc; try easy.
  - destruct lsg; try easy. 
    inversion H0. subst. clear H0. 
    specialize(IHl lsg l' s' Gjk s). apply IHl; try easy.
Qed.

Lemma typ_after_step_3_helper_h2 : forall [n ys s0 g xs ctxG],
        onth n ys = Some (s0, g) -> 
        Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys -> 
        exists g', onth n xs = Some (s0, g') /\ typ_gtth ctxG g' g.
Proof.
  induction n; intros.
  - destruct ys; try easy. destruct xs; try easy.
    inversion H0. subst. clear H0.
    simpl in H. subst. destruct H4; try easy. destruct H as (s,(g0,(g',(Ha,(Hb,Hc))))).
    inversion Hb. subst.
    exists g0. easy.
  - destruct ys; try easy. destruct xs; try easy.
    inversion H0. subst. clear H0.
    specialize(IHn ys s0 g xs ctxG). apply IHn; try easy.
Qed.

Lemma typ_after_step_3_helper_h3 : forall ys ys2 p q l,
    Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) ys ys2 -> 
    (forall t : string,
      t <> p ->
      t <> q ->
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s' : sort) (g : gtt),
            u = Some (s', g) /\
            (forall (G' : gtt) (T : ltt),
             gttstepC g G' p q l ->
             projectionC g t T -> wfgC G' -> exists T' : ltt, projectionC G' t T' /\ T = T'))) ys) ->
    Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys2 ->
    forall t, t <> p -> t <> q -> Forall2 (fun u v => (u = None /\ v = None) \/ (exists s' g g', u = Some(s', g) /\ v = Some(s', g') /\
      gttstepC g g' p q l /\ (forall T, projectionC g t T -> exists T', projectionC g' t T' /\ T = T'
    ))) ys ys2.
Proof.
  induction ys; intros; try easy.
  - destruct ys2; try easy.
  - destruct ys2; try easy.
    inversion H. subst. clear H. inversion H1. subst. clear H1.
    assert(forall t : string,
     t <> p ->
     t <> q ->
     Forall
       (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s' : sort) (g : gtt),
           u = Some (s', g) /\
           (forall (G' : gtt) (T : ltt),
            gttstepC g G' p q l ->
            projectionC g t T -> wfgC G' -> exists T' : ltt, projectionC G' t T' /\ T = T'))) 
       ys).
    {
      intros. specialize(H0 t0 H H1). inversion H0; try easy.
    }
    specialize(H0 t H2 H3). inversion H0. subst. clear H0.
    specialize(IHys ys2 p q l H9 H H6 t H2 H3). constructor; try easy.
    clear H10 H6 H9 IHys H.
    destruct H7. left. easy.
    destruct H as (s1,(g,(g',(Ha,(Hb,Hc))))). subst.
    destruct H5; try easy. destruct H as (s2,(g2,(Hta,Htb))). inversion Hta. subst. clear Hta.
    destruct H8; try easy. destruct H as (s3,(g3,(Hd,He))). inversion Hd. subst. clear Hd.
    right. exists s3. exists g3. exists g2. split. easy. split. easy.
    split. destruct Hc; try easy.
    intros. specialize(He g2 T). apply He; try easy. destruct Hc; try easy.
Qed.

Lemma typ_after_step_3_helper_h4 : forall l lsg s' Gjk ys s T,
      onth l lsg = Some (s', Gjk) ->  
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : gtt) (t : ltt),
            u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g s t)) lsg ys -> 
      isMerge T ys -> 
      projectionC Gjk s T.
Proof.
  induction l; intros; try easy.
  - destruct lsg; try easy. destruct ys; try easy. 
    inversion H0. subst. clear H0. simpl in H. subst.
    destruct H5; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
    pclearbot.
    inversion H1; try easy. 
  - destruct lsg; try easy. destruct ys; try easy. 
    inversion H0. subst. clear H0. simpl in H. subst.
    specialize(IHl lsg s' Gjk ys s T). apply IHl; try easy.
    inversion H1; try easy. subst. destruct lsg; try easy. destruct l; try easy.
Qed.

Lemma typ_after_step_3_helper_h5 : forall ys ys2 ys3 p q l r,
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s' : sort) (g g' : gtt),
            u = Some (s', g) /\
            v = Some (s', g') /\
            gttstepC g g' p q l /\
            (forall T : ltt, projectionC g r T -> exists T' : ltt, projectionC g' r T' /\ T = T'))) ys ys2 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g r t)) ys ys3 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : gtt) (t : ltt),
            u = Some (s0, g) /\ v = Some (s0, t) /\ upaco3 projection bot3 g r t)) ys2 ys3.
Proof.
  induction ys; intros; try easy.
  - destruct ys2; try easy. destruct ys3; try easy.
  - destruct ys2; try easy.
    inversion H. subst. clear H. inversion H0. subst. clear H0.
    specialize(IHys ys2 ys3 p q l r).
    assert(Forall2
         (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
          u = None /\ v = None \/
          (exists (s0 : sort) (g : gtt) (t : ltt),
             u = Some (s0, g) /\ v = Some (s0, t) /\ upaco3 projection bot3 g r t)) ys2 ys3).
    apply IHys; try easy. constructor; try easy. clear H H7 H6 IHys.
    destruct H3. left. destruct H4. easy. 
    destruct H. subst. destruct H0 as (s1,(g1,(g2,(Ha,Hb)))). easy.
    destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst.
    destruct H4; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,(Hf,Hg)))))). inversion Hd. subst.
    right. exists s2. exists g3. exists t1. 
    specialize(Hg t1).
    assert(exists T', projectionC g3 r T' /\ t1 = T'). apply Hg; try easy.
    destruct Hc; try easy.
    destruct H. subst. split. easy. split. easy. left. destruct H. subst. easy.
Qed.

Lemma typ_after_step_3_helper_h6 : forall ys ys2 ys3 p q l r,
        Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys3 -> 
        Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s' : sort) (g g' : gtt),
            u = Some (s', g) /\
            v = Some (s', g') /\
            gttstepC g g' p q l /\
            (forall T : ltt, projectionC g r T -> exists T' : ltt, projectionC g' r T' /\ T = T'))) ys ys2 ->
        Forall2
          (fun (u : option (sort * gtt)) (v : option ltt) =>
           u = None /\ v = None \/
           (exists (s0 : sort) (g : gtt) (t : ltt),
              u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys2 ys3.
Proof.
  induction ys; intros; try easy.
  - destruct ys2; try easy.
  - destruct ys2; try easy. destruct ys3; try easy.
    inversion H. subst. clear H. inversion H0. subst. clear H0.
    specialize(IHys ys2 ys3 p q l r).
    assert(Forall2
         (fun (u : option (sort * gtt)) (v : option ltt) =>
          u = None /\ v = None \/
          (exists (s0 : sort) (g : gtt) (t : ltt),
             u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys2 ys3).
    apply IHys; try easy.
    constructor; try easy.
    - destruct H3. destruct H0. subst. destruct H4. left. easy.
      destruct H0 as (s1,(g1,(t1,(Ha,Hb)))). easy.
    - destruct H0 as (s1,(g1,(g2,(Ha,(Hb,(Hc,Hd)))))). subst.
      destruct H4; try easy. destruct H0 as (s2,(g3,(t1,(He,(Hf,Hg))))). inversion He. subst.
      right. exists s2. exists g2. exists t1. split. easy. split. easy. left.
      specialize(Hd t1).
      assert(exists T' : ltt, projectionC g2 r T' /\ t1 = T'). apply Hd; try easy.
      destruct Hg; try easy.
      destruct H0. destruct H0. subst. easy.
Qed.

Lemma part_after_step_r_helper : forall n ys s1 g1 ys1 ys0 xs p q l r ctxG,
    onth n ys = Some (s1, g1) -> 
    Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys -> 
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys1 -> 
    Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) ys ys0 ->
    Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys ->
    exists g2 g3 t,
    onth n ys0 = Some (s1, g2) /\ gttstepC g1 g2 p q l /\
    onth n xs = Some (s1, g3) /\ typ_gtth ctxG g3 g1 /\
    onth n ys1 = Some t /\ projectionC g1 r t /\ wfgC g1.
Proof.
  induction n; intros; try easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2. 
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    simpl in H. subst. clear H4 H11 H10 H9.
    destruct H7; try easy. destruct H as (s2,(g2,(g3,(Ha,(Hb,Hc))))). inversion Hb. subst.
    destruct H6; try easy. destruct H as (s3,(g4,(g5,(Hd,(He,Hf))))). inversion Hd. subst.
    destruct H5; try easy. destruct H as (s4,(g6,(t1,(Hg,(Hi,Hj))))). inversion Hg. subst.
    destruct H3; try easy. destruct H as (s5,(g7,(Hk,Hl))). inversion Hk. subst.
    simpl. exists g5. exists g2. exists t1. pclearbot. easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2. 
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    specialize(IHn ys s1 g1 ys1 ys0 xs p q l r ctxG). apply IHn; try easy.
Qed.
