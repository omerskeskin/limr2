From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh src.step src.merge src.projection. 
From SST Require Import lemma.inversion lemma.inversion_expr lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step lemma.projection_helper.

Lemma canon_rep_s : forall G p q PT QT S T S' T' n, 
    wfgC G -> 
    projectionC G p (ltt_send q PT) -> 
    onth n PT = Some(S, T) ->
    projectionC G q (ltt_recv p QT) -> 
    onth n QT = Some (S', T') ->
    exists G' ctxG SI Sn, 
    typ_gtth ctxG G' G /\ 
    (ishParts p G' -> False) /\ (ishParts q G' -> False) /\ 
    List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
      (exists s' Gjk Tp Tq, onth n lsg = Some (s', Gjk) /\ projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g', u = Some(s, g') /\ v = Some s)) lsg SI
    )) ctxG /\ 
    (onth n SI = Some Sn) /\ subsort S Sn /\ subsort Sn S'. 
Proof.
  intros.
  specialize(canon_rep_11 G p q PT H H0); intros.
  destruct H4 as (G',(ctxG,(Ha,(Hb,(Hc,Hd))))). 
  exists G'. exists ctxG.
  specialize(canon_rep_part ctxG G' G p q PT QT Ha H0 H2 Hb); intros.
  specialize(canon_rep_16 G' ctxG G p q QT PT H2 Hc Hd Hb H4 Ha); intros. clear Hc.
  specialize(canon_rep_s_helper PT); intros. destruct H6 as (SI, H6).
  exists SI. exists S. split. easy. split. easy. split. easy.
  specialize(canon_rep_s_helper2 G' G p q PT QT ctxG); intros.
  assert(Forall2
       (fun u v : option (sort * ltt) =>
        u = None /\ v = None \/ (exists (s : sort) (g g' : ltt), u = Some (s, g) /\ v = Some (s, g')))
       PT QT).
  {
    apply H7; try easy.
    apply Forall_forall; intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg PT /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg QT)) ctxG); intros.
    destruct H9. specialize(H9 H5). clear H5 H10.
    specialize(H9 x H8). destruct H9. left. easy.
    destruct H5 as (g,(lsg,(Hta,(Htb,Htc)))). subst. right. exists (gtt_send p q lsg).
    exists lsg. easy.
  }
  clear H7.
  split.
  
  apply Forall_forall; intros.
  specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg PT /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg QT)) ctxG); intros.
  destruct H9. specialize(H9 H5). clear H5 H10. specialize(H9 x H7).
  destruct H9. left. easy. destruct H5 as (g,(lsg,(Hta,(Htb,(Htc,Htd))))).
  subst. right. exists (gtt_send p q lsg). exists lsg.
  split. easy. split. easy.
  split.
  {
    clear H7 H8 H6 H4 Hb Ha H2 H0 H Hd. 
    clear G G' ctxG SI. revert Htd Htc. revert lsg H3 H1. 
    revert p q PT QT S T S' T'.
    induction n; intros; try easy.
    - destruct PT; try easy. destruct QT; try easy. destruct lsg; try easy.
      inversion Htd. subst. clear Htd. inversion Htc. subst. clear Htc.
      simpl in *. subst.
      destruct H4; try easy. destruct H as (s1,(t1,(g1,(Ha,(Hb,Hc))))). inversion Hb. subst.
      destruct H5; try easy. destruct H as (s2,(t2,(g2,(Hd,(He,Hf))))). inversion Hd. inversion He. subst.
      exists s2. exists g2. exists t2. exists t1. easy.
    - destruct PT; try easy. destruct QT; try easy. destruct lsg; try easy.
      inversion Htd. subst. clear Htd. inversion Htc. subst. clear Htc.
      specialize(IHn p q PT QT S T S' T' lsg). apply IHn; try easy.
  }
  - specialize(canon_rep_helper2 lsg SI PT p); intros. apply H5; try easy.
    clear H5 H4 Hb Ha H2 H0 Hd. clear G' H ctxG p q.
    revert H8 H6 H3 H1. revert SI T' S' T S PT QT G.
    induction n; intros; try easy.
    - destruct QT; try easy. destruct PT; try easy. destruct SI; try easy.
      inversion H6. subst. clear H6. inversion H8. subst. clear H8.
      simpl in H3. simpl in H1. subst.
      destruct H4; try easy. destruct H as (s1,(g1,(Ha,Hb))). inversion Hb. subst.
      destruct H5; try easy. destruct H as (s2,(g2,(g3,(Hc,Hd)))). inversion Hc. inversion Hd. subst.
      simpl. split. easy. split. apply srefl. apply srefl.
    - destruct QT; try easy. destruct PT; try easy. destruct SI; try easy.
      inversion H6. subst. clear H6. inversion H8. subst. clear H8.
      specialize(IHn SI T' S' T S PT QT). apply IHn; try easy.
Qed.

Lemma canon_rep_w_s : forall G p q PT QT, 
    wfgC G -> 
    projectionC G p (ltt_send q PT) -> 
    projectionC G q (ltt_recv p QT) ->
    List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some (s, t) /\ v = Some (s, t'))) PT QT.
Proof.
  intros.
  specialize(balanced_to_tree G p H); intros.
  assert(isgPartsC p G).
  {
    pinversion H0; try easy. apply proj_mon.
  }
  specialize(H2 H3).
  destruct H2 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd H3.
  revert Hc Hb Ha H0 H1 H. revert G p q PT QT ctxG.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst. 
    specialize(some_onth_implies_In n ctxG G H4); intros. 
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros. 
    destruct H3.
    specialize(H3 Hc). clear H5 Hc.
    specialize(H3 (Some G) H2). destruct H3; try easy.
    destruct H3 as (r,(lsg,Hd)).
    destruct Hd.
    - inversion H3. subst. pinversion H1; try easy. subst. 
      - pinversion H0; subst; try easy.
        clear H9 H14 H13 H11 H10 H3 H2 H4 H H1 H0 Ha Hb.
        revert H12 H15. revert lsg PT QT. 
        induction lsg; intros.
        - destruct QT; try easy. destruct PT; try easy.
        - destruct QT; try easy. destruct PT; try easy.
          inversion H12. subst. clear H12. inversion H15. subst. clear H15.
          specialize(IHlsg PT QT H4 H6). constructor; try easy.
          destruct H3. destruct H. subst. destruct H2. destruct H. subst. left. easy.
          destruct H as (s1,(g1,(t1,Ha))). easy.
          destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst.
          destruct H2; try easy. destruct H as (s2,(g2,(t2,(Hd,(He,Hf))))). inversion Hd. subst.
          right. exists s2. exists t1. exists t2. easy.
          apply proj_mon.
        - subst. pinversion H0; try easy. apply proj_mon. apply proj_mon.
    - destruct H3. inversion H3. subst. pinversion H1; try easy. subst. pinversion H0; try easy.
      apply proj_mon. apply proj_mon.
    - inversion H3. subst. pinversion H1. apply proj_mon.
  - inversion Ha. subst. clear Ha.
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    pinversion H1; try easy.
    - subst.
      assert False.
      apply Hb. constructor. easy.
    - subst.
      pinversion H0; try easy. subst. clear H12.
      clear H0 H1.
      specialize(wfgC_after_step_all H6 H2); intros.
      clear H2 H11 H17.
      revert H21 H20 H16 H13 H15 H14 H10 H7 H6 H9 H9 H8 Hb Hc H H0.
      revert s s' p q PT QT ctxG ys ys0 ys1.
      induction xs; intros.
      - easy.
      - destruct ys; try easy.
        destruct ys0; try easy. destruct ys1; try easy.
        inversion H1. subst. clear H1. inversion H. subst. clear H. inversion H0. subst. clear H0.
        inversion H14. subst. clear H14. inversion H9. subst. clear H9. inversion H20. subst. clear H20.
        specialize(SList_f a xs H8); intros. clear H8.
        destruct H.
        - clear H9 H14 H2 H12 H3 H4.
          specialize(IHxs s s' p q PT QT ctxG ys ys0 ys1).
          apply IHxs; try easy.
          - inversion H21; try easy. 
            subst. destruct ys; try easy. destruct xs; try easy.
          - inversion H15; try easy.
            subst. destruct ys; try easy. destruct xs; try easy.
          - specialize(ishParts_hxs Hb). easy.
        - destruct H. destruct H0. subst.
          clear H23 H22 H19 H18 H11 H5 IHxs.
          destruct H12; try easy. destruct H as (s1,(g1,(g2,(Hd,(He,Hf))))). 
          inversion Hd. subst.
          destruct H9; try easy. destruct H as (s2,(g3,(t1,(Hg,(Hh,Hi))))).
          inversion Hg. subst.
          destruct H4; try easy. destruct H as (s3,(g4,(Hj,Hk))).
          inversion Hj. subst.
          destruct H14; try easy. destruct H as (s4,(g5,(g6,(Hl,(Hm,Hn))))). 
          inversion Hm. subst. inversion Hl. subst.
          destruct H2; try easy. destruct H as (s5,(g7,(t2,(Ho,(Hp,Hq))))). 
          inversion Ho. subst. clear Hm Hg Hj Ho.
          destruct H3; try easy. destruct H as (s6,(g8,(Hr,Hs))).
          inversion Hr. subst. clear Hr.
          specialize(Hs g7 p q PT QT ctxG).
          pclearbot.
          assert(t1 = (ltt_send q PT)).
          - inversion H21; try easy.
          assert(t2 = (ltt_recv p QT)).
          - inversion H15; try easy.
          subst.
          apply Hs; try easy.
          specialize(ishParts_x Hb); intros. easy.
    - apply proj_mon. apply proj_mon.
Qed.
          
Lemma canon_rep_w : forall G p q PT QT S T S' T' n, 
    wfgC G -> 
    projectionC G p (ltt_send q PT) -> 
    onth n PT = Some(S, T) ->
    projectionC G q (ltt_recv p QT) -> 
    onth n QT = Some (S', T') ->
    S = S'.  
Proof.
  intros.
  specialize(canon_rep_w_s G p q PT QT H H0 H2); intros.
  clear H2 H0 H. revert H4 H3 H1.
  revert S S' T T' PT QT.
  induction n; intros.
  - destruct QT; try easy. destruct PT; try easy.
    inversion H4. subst. clear H4.
    simpl in *. subst.
    destruct H5; try easy. destruct H as (s,(t1,(t2,(Ha,Hb)))).
    inversion Ha. subst. inversion Hb. subst. easy.
  - destruct QT; try easy. destruct PT; try easy.
    inversion H4. subst. clear H4.
    specialize(IHn S S' T T' PT QT). apply IHn; try easy.
Qed.


Lemma part_after_step : forall G G' q p pt l LP LQ,
        wfgC G ->
        wfgC G' -> 
        gttstepC G G' q p l -> 
        projectionC G p (ltt_recv q LQ) ->
        projectionC G q (ltt_send p LP) ->
        isgPartsC pt G' -> 
        isgPartsC pt G.
Proof.
  intros.
  specialize(canon_rep_11 G q p LP H H3); intros.
  destruct H5 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  assert(Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send q p lsg)) ctxG).
  {
    apply Forall_forall; intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send q p lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg LP)) ctxG); intros.
    destruct H6. specialize(H6 Hc). clear Hc H7.
    specialize(H6 x H5). destruct H6. left. easy.
    destruct H6 as (g,(lsg,(Hc,(Hd,He)))). right. exists g. exists lsg. easy.
  }
  clear Hc.
  revert H5 Hb Ha H4 H3 H2 H1 H0 H.
  revert G G' p q pt l LP LQ ctxG.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ctxG G H8); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))), u = Some g /\ g = gtt_send q p lsg))
       ctxG); intros.
    destruct H7. specialize(H7 H5). clear H9 H5.
    specialize(H7 (Some G) H6). destruct H7; try easy.
    destruct H5 as (g1,(lsg,(Hc,Hd))). inversion Hc. subst.
    pinversion H1; try easy. subst.
    clear H11 H12.
    unfold wfgC in H. destruct H. destruct H. rename x into G1.
    unfold isgPartsC. destruct H5. destruct H7.
    specialize(part_after_step_helper G1 q p lsg H H7); intros.
    destruct H10. destruct H10.
    specialize(part_after_step_helper2 l lsg q p x G' pt s); intros. apply H12; try easy.
    apply step_mon.
  - inversion Ha. subst.
    unfold isgPartsC.
    pinversion H2; try easy.
    subst. assert False. apply Hb. constructor. easy.
    subst. pinversion H3; try easy. subst.
    pinversion H1; try easy. subst. clear H10 H11 H14 H16 H17 H20.
    specialize(part_break (gtt_send p q ys2) pt H0 H4); intros.
    destruct H7 as (Gl,(Hc,(Hd,(He,Hf)))).
    destruct Hf.
    - subst. pinversion Hc; try easy.
    - destruct H7 as (p1,(q1,(lis1,Hf))). subst.
      pinversion Hc; try easy. subst.
    clear Hc.
    - specialize(part_break (gtt_send p q ys) p); intros.
      assert(exists Gl : global,
       gttTC Gl (gtt_send p q ys) /\
       isgParts p Gl /\
       (forall n : fin, exists m : fin, guardG n m Gl) /\
       (Gl = g_end \/
        (exists (p q : string) (lis : seq.seq (option (sort * global))), Gl = g_send p q lis))).
      {
        apply H7; try easy.
        apply triv_pt_p; try easy.
      }
      destruct H9 as (Gl1,(Hta,(Htb,(Htc,Htd)))).
      destruct Htd. subst. pinversion Hta; try easy.
      destruct H9 as (p1,(q1,(lsg1,Htd))). subst.
      pinversion Hta. subst.
    - rename p into st. rename q into st'. rename p0 into p. rename q0 into q.
      clear H7 Hta.
      inversion Hd; try easy. 
      - subst. exists (g_send st st' lsg1). split. pfold. constructor. easy. split. easy. constructor.
      - subst. exists (g_send st st' lsg1). split. pfold. constructor. easy. split. easy. constructor.
      subst.
      clear Htb H21 H15 H12 H4 H1 Ha H2 H3.
      specialize(wfgC_after_step_all H23 H0); intros.
      specialize(wfgC_after_step_all H23 H6); intros.
      clear H0 H6 Hd H34.
      specialize(part_after_step_helper3 n lis1 ys2 ys ys1 ys0 xs p q l s g ctxG); intros.
      assert(exists (g' g'' : gtt) (t t' : ltt) (Gl : gtth),
       onth n ys2 = Some (s, g') /\
       gttTC g g' /\
       onth n ys = Some (s, g'') /\
       gttstepC g'' g' q p l /\
       onth n ys1 = Some t /\
       projectionC g'' q t /\
       onth n ys0 = Some t' /\
       projectionC g'' p t' /\ onth n xs = Some (s, Gl) /\ typ_gtth ctxG Gl g'').
      {
        apply H0; try easy.
      }
      clear H0.
      destruct H3 as (g1,(g2,(t1,(t2,(Gl,(Hta,(Htb,(Htk,(Htd,(Hte,(Htf,(Hth,(Hti,(Htj,Htl)))))))))))))).
      specialize(some_onth_implies_In n xs (s, Gl) Htj); intros.
      specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G G' : gtt) (p q pt : string) (l : fin) (LP LQ : seq.seq (option (sort * ltt)))
             (ctxG : seq.seq (option gtt)),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\ g0 = gtt_send q p lsg)) ctxG ->
           (ishParts q g -> False) ->
           typ_gtth ctxG g G ->
           isgPartsC pt G' ->
           projectionC G q (ltt_send p LP) ->
           projectionC G p (ltt_recv q LQ) ->
           gttstepC G G' q p l -> wfgC G' -> wfgC G -> isgPartsC pt G))) xs); intros.
      destruct H3. specialize(H3 H). clear H H4.
      specialize(H3 (Some (s, Gl)) H0). destruct H3; try easy. 
      destruct H as (s1,(g3,(Hma,Hmb))). inversion Hma. subst.
      clear Hma H0.
      specialize(Hmb g2 g1 p q pt l).
      specialize(merge_onth_send n p LP ys1 t1 H25 Hte); intros. destruct H. subst.
      specialize(merge_onth_recv n q LQ ys0 t2 H19 Hth); intros. destruct H. subst.
      specialize(Hmb x x0 ctxG H5).
      assert(isgPartsC pt g2).
      {
        apply Hmb; try easy.
        specialize(ishParts_n Hb Htj); try easy.
        unfold isgPartsC. exists g. split. easy. split; try easy.
        specialize(guard_cont He); intros.
        revert n0. specialize(Forall_prop n lis1 (s1, g) (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) H20 H); intro.
        simpl in H0. destruct H0; try easy. destruct H0 as (st1,(gt1,(Hsa,Hsb))). inversion Hsa; try easy.
        specialize(Forall_prop n ys2 (s1, g1) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Hta H1); intro.
        simpl in H. destruct H; try easy. destruct H as (st1,(gt1,(Hsa,Hsb))). inversion Hsa; try easy.
        specialize(Forall_prop n ys (s1, g2) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Htk H2); intro.
        simpl in H. destruct H; try easy. destruct H as (st1,(gt1,(Hsa,Hsb))). inversion Hsa; try easy.
      }
      
      clear Hmb H2 H1.
      specialize(part_after_step_helper2 n ys st st'); intros.
      specialize(H0 lsg1 g2 pt s1). apply H0; try easy. pfold. constructor. easy.
    apply gttT_mon.
    apply gttT_mon.
    apply step_mon.
    apply proj_mon.
    apply proj_mon. 
Qed.


Lemma proj_inv_lis : forall p q l s s' ys LP LQ S T S' T',
    wfgC (gtt_send s s' ys) ->
    projectionC (gtt_send s s' ys) p (ltt_send q LP) -> 
    onth l LP = Some (S, T) ->
    projectionC (gtt_send s s' ys) q (ltt_recv p LQ) -> 
    onth l LQ = Some (S', T') ->
    (s = p /\ s' = q /\ exists Gk, onth l ys = Some Gk) \/
    (s <> p /\ s' <> q /\ List.Forall (fun u => u = None \/ 
        (exists s g LP' LQ' T T', u = Some(s, g) /\ projectionC g p (ltt_send q LP') /\ projectionC g q (ltt_recv p LQ') /\ 
          onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
Proof.
  intros.
  specialize(canon_rep_s (gtt_send s s' ys) p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H4. destruct H4. destruct H4. destruct H4. destruct H4. destruct H5. destruct H6.
  rename x0 into ctxG. rename x into Gl.
  destruct H7.
  specialize(typ_after_step_ctx_loose H7); intros. clear H7 H8 H3 H1.
  revert H9 H6 H5 H4 H2 H0 H.
  revert p q l s s' ys LP LQ ctxG. clear S T S' T' x1 x2.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion H4. subst. 
    specialize(some_onth_implies_In n ctxG (gtt_send s s' ys) H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG); intros.
    destruct H3. specialize(H3 H9). clear H8 H9.
    specialize(H3 (Some (gtt_send s s' ys)) H1); intros.
    destruct H3; try easy. destruct H3. destruct H3. destruct H3. destruct H8. subst.
    inversion H3. subst. clear H3.
    destruct H9. destruct H3. destruct H3. destruct H3. destruct H3.
    left. split. easy. split. easy. exists (x, x1). easy.
  - inversion H4. subst.
    pinversion H2. subst. assert False. apply H6. constructor. easy.
    subst. clear H14. rename H18 into H14. rename H19 into H18. 
    pinversion H0; try easy. subst. clear H20. rename H23 into H20. rename H24 into H23.
    rename p0 into p. rename q0 into q.
    specialize(wfgC_after_step_all H11 H1); intros. clear H1.
    right. split. easy. split. easy.
    apply Forall_forall; intros. destruct x.
    right. destruct p0. exists s0. exists g.
    specialize(in_some_implies_onth (s0, g) ys H1); intros. destruct H7. rename x into n. clear H1.
    clear H2 H0 H4.
    specialize(proj_inv_lis_helper n ys s0 g xs ys0 ys1 ctxG p q); intros.
    assert(exists (g' : gtth) (t t' : ltt),
       onth n xs = Some (s0, g') /\
       typ_gtth ctxG g' g /\
       onth n ys0 = Some t /\ projectionC g q t /\ onth n ys1 = Some t' /\ projectionC g p t' /\ wfgC g).
    apply H0; try easy. clear H0 H3 H17 H15.
    destruct H1 as (g',(t,(t',(Ha,(Hb,(Hc,(Hd,(He,(Hf,Hg))))))))).
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (p q : string) (l : fin) (s0 s' : string) (ys : list (option (sort * gtt)))
             (LP LQ : list (option (sort * ltt))) (ctxG : list (option gtt)),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
                    onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG ->
           (ishParts q g -> False) ->
           (ishParts p g -> False) ->
           typ_gtth ctxG g (gtt_send s0 s' ys) ->
           projectionC (gtt_send s0 s' ys) q (ltt_recv p LQ) ->
           projectionC (gtt_send s0 s' ys) p (ltt_send q LP) ->
           wfgC (gtt_send s0 s' ys) ->
           s0 = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
           s0 <> p /\
           s' <> q /\
           Forall
             (fun u0 : option (sort * gtt) =>
              u0 = None \/
              (exists (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
               (T T' : sort * ltt),
                 u0 = Some (s1, g0) /\
                 projectionC g0 p (ltt_send q LP') /\
                 projectionC g0 q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys)))
      xs); intros. destruct H0. specialize(H0 H). clear H H1.
      specialize(some_onth_implies_In n xs (s0, g') Ha); intros.
      specialize(H0 (Some (s0, g')) H). clear H.
      destruct H0; try easy. destruct H as (s1,(g1,(H1,H2))).
      specialize(H2 p q l). inversion H1. subst. clear H1.
      
      inversion Hb.
      - subst.
        specialize(some_onth_implies_In n0 ctxG g H); intros.
        specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG); intros.
        destruct H1. specialize(H1 H9). clear H3 H9.
        specialize(H1 (Some g) H0). destruct H1; try easy.
        destruct H1 as (g2,(lsg,(H3,(H4,H8)))). subst. inversion H3. subst. clear H3.
        pinversion Hd; try easy. subst. assert False. apply H1. apply triv_pt_q; try easy. easy.
        subst. clear H15.
        pinversion Hf; try easy. subst. assert False. apply H1. apply triv_pt_p; try easy. easy.
        subst. clear H17.
        exists ys3. exists ys2.
        destruct H8 as (s2,(Gjk,(Tp,(Tq,(Hm,Ht))))). 
        assert(exists T T', onth l ys3 = Some T /\ onth l ys2 = Some T').
        {
          specialize(proj_inv_lis_helper3 Hm H22 H26); intros; try easy.
        }
        destruct H1 as (T,(T',(Ht1,Ht2))). exists T. exists T'. split. easy. split. pfold.
        easy. split. pfold. easy. easy.
      apply proj_mon.
      apply proj_mon.
      - subst. rename p0 into s0. rename q0 into s0'.
        specialize(H2 s0 s0' ys2).
        assert(exists LP' LQ', projectionC (gtt_send s0 s0' ys2) p (ltt_send q LP') /\ projectionC (gtt_send s0 s0' ys2) q (ltt_recv p LQ')).
        {
          specialize(merge_onth_recv n p LQ ys0 t H18 Hc); intros. destruct H1. subst.
          specialize(merge_onth_send n q LP ys1 t' H23 He); intros. destruct H1. subst. exists x0. exists x.
          easy.
        }
        destruct H1 as (LP',(LQ',(Ht1,Ht2))).
        specialize(H2 LP' LQ' ctxG).
        assert(s0 = p /\ s0' = q /\ (exists Gk : sort * gtt, onth l ys2 = Some Gk) \/
           s0 <> p /\
           s0' <> q /\
           Forall
             (fun u0 : option (sort * gtt) =>
              u0 = None \/
              (exists (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
               (T T' : sort * ltt),
                 u0 = Some (s1, g0) /\
                 projectionC g0 p (ltt_send q LP') /\
                 projectionC g0 q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys2).
        {
          apply H2; try easy.
          - specialize(ishParts_n H6 Ha); intros. apply H1; try easy.
          - specialize(ishParts_n H5 Ha); intros. apply H1; try easy.
        }
        exists LP'. exists LQ'. 
        destruct H1.
        - destruct H1 as (Hs1,(Hs2,Hs3)). destruct Hs3. subst.
          assert False. apply H6. apply ha_sendr with (n := n) (s := s1) (g := gtth_send p q xs0); try easy.
          constructor. easy.
        - destruct H1 as (Hs1,(Hs2,Hs3)).
          specialize(typ_after_step_step_helper3 xs0 ys2 ctxG H H0); intros.
          clear H2.
          pinversion Ht1; try easy. subst.
          pinversion Ht2; try easy. subst.
          specialize(wfgC_after_step_all H8 Hg); intros.
          specialize(proj_inv_lis_helper2 ys2 ys3 ys4 p q); intros.
          assert(exists (n : fin) (st : sort) (g : gtt) (t t' : ltt),
       onth n ys2 = Some (st, g) /\
       wfgC g /\ onth n ys3 = Some t /\ projectionC g p t /\ onth n ys4 = Some t' /\ projectionC g q t').
          apply H3; try easy. clear H3.
          destruct H4 as (n',(st,(g3,(t1,(t2,(Hta,(Htb,(Htc,(Htd,(Hte,Htf)))))))))).
          specialize(Forall_forall (fun u0 : option (sort * gtt) =>
         u0 = None \/
         (exists (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u0 = Some (s1, g0) /\
            projectionC g0 p (ltt_send q LP') /\
            projectionC g0 q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys2); intros.
          destruct H3. specialize(H3 Hs3). clear Hs3 H4.
          specialize(some_onth_implies_In n' ys2 (st, g3) Hta); intros.
          specialize(H3 (Some (st, g3)) H4); intros. destruct H3; try easy.
          destruct H3 as (s3,(g0,(LP0',(LQ0',(T,(T',(Hsa,(Hsb,(Hsc,(Hsd,Hse)))))))))). inversion Hsa. subst.
          specialize(proj_inj Htb Htd Hsb); intros. subst. 
          specialize(proj_inj Htb Htf Hsc); intros. subst.
          specialize(merge_label_send ys3 LP' LP0' T n' l q H26 Htc Hsd); intros. destruct H3. exists x.
          specialize(merge_label_recv ys4 LQ' LQ0' T' n' l p H32 Hte Hse); intros. destruct H29. exists x0.
          split. easy. split. pfold. easy. split. pfold. easy. easy.
        apply proj_mon.
        apply proj_mon.
        left. easy.
      apply proj_mon.
      apply proj_mon.
Qed.


Lemma projection_step_label_s : forall G p q l LP LQ ST,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some ST -> 
  projectionC G q (ltt_recv p LQ) ->
  exists LS' LT', onth l LQ = Some(LS', LT').
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
    clear H4 H3 H2 H1 H0 H. destruct H5 as (H5, H0). clear H0. clear Gl LQ l. clear G.
    revert H5. revert LP p q. induction x; intros; try easy.
    inversion H5. subst. clear H5. specialize(IHx LP p q H2). constructor; try easy. clear H2 IHx.
    destruct H1. left. easy.
    destruct H. destruct H. destruct H. destruct H0. right. exists x0. exists x1. easy.
  }
  clear H3. clear H.
  revert H4 H2 H1 H0. revert G p q l LP LQ ST.
  induction Gl using gtth_ind_ref; intros.
  - destruct H4. destruct H. destruct H3.
    inversion H. subst. 
    specialize(some_onth_implies_In n x G H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg)) x); intros.
    destruct H6. specialize(H6 H4 (Some G) H5). clear H4 H8.
    destruct H6; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst.
    pinversion H0; try easy. subst.
    pinversion H2; try easy. subst.
    clear H11 H15 H11 H12 H0 H7 H5 H2 H3 H H4. clear H17 H16 H13. clear n x.
    revert H18 H14 H1. revert p q LP LQ ST x1.
    induction l; intros.
    - destruct LP; try easy. destruct x1; try easy. destruct LQ; try easy.
      inversion H18. inversion H14. subst. clear H18 H14.
      simpl in H1. subst.
      destruct H9; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H0. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H2.
      inversion H. subst. 
      exists x3. exists x5. easy.
    - destruct LP; try easy. destruct x1; try easy. destruct LQ; try easy.
      inversion H18. inversion H14. subst. clear H18 H14.
      specialize(IHl p q LP LQ ST x1). apply IHl; try easy.
    apply proj_mon. 
    apply proj_mon.
  - destruct H4. destruct H3. destruct H4. 
    inversion H3. subst.
    specialize(SList_to_In xs H11); intros. destruct H6.
    specialize(in_some_implies_onth x0 xs H6); intros. destruct H7. rename x1 into n.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G : gtt) (p q : string) (l : fin) (LP LQ : list (option (sort * ltt)))
             (ST : sort * ltt),
           (exists ctxJ : list (option gtt),
              typ_gtth ctxJ g G /\
              (ishParts p g -> False) /\
              Forall
                (fun u0 : option gtt =>
                 u0 = None \/
                 (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                    u0 = Some g0 /\ g0 = gtt_send p q lsg)) ctxJ) ->
           projectionC G q (ltt_recv p LQ) ->
           onth l LP = Some ST ->
           projectionC G p (ltt_send q LP) ->
           exists (LS' : sort) (LT' : ltt), onth l LQ = Some (LS', LT')))) xs); intros.
    destruct H8. specialize(H8 H (Some x0) H6). clear H9 H. destruct H8; try easy.
    destruct H. destruct H. destruct H. inversion H. subst.
    pinversion H0. subst.
    assert False. apply H4. constructor. easy.
    subst.
    pinversion H2; try easy. subst.
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    rename x1 into s0. rename x2 into g. rename x into ctxG.
    clear H H6 H11 H2 H0 H3.
    assert(exists g' t t', onth n ys = Some (s0, g') /\ typ_gtth ctxG g g' /\ onth n ys0 = Some t /\ projectionC g' p t 
          /\ onth n ys1 = Some t' /\ projectionC g' q t').
    {
      clear H27 H23 H22 H19 H18 H21 H17 H16 H15 H14 H8 H1 H5 H4. 
      clear ST LP LQ. clear s s'. clear l.
      revert H26 H20 H12 H7. revert xs p q ctxG ys s0 g ys0 ys1.
      induction n; intros.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H26. inversion H20. inversion H12. subst. clear H26 H20 H12.
        simpl in H7. subst.
        destruct H16; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H9; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
        inversion H. subst. clear H.
        simpl. exists x1. exists x4. exists x5. pclearbot. easy.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H26. inversion H20. inversion H12. subst. clear H26 H20 H12.
        specialize(IHn xs p q ctxG ys s0 g ys0 ys1). apply IHn; try easy.
    }
    destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H2. destruct H3. destruct H6.
    rename x into g'. 
    specialize(merge_onth_recv n p LQ ys1 x1 H27 H6); intros. destruct H10. subst.
    specialize(merge_onth_send n q LP ys0 x0 H21 H2); intros. destruct H10. subst.
    rename x1 into LP'. rename x into LQ'.
    
    specialize(H8 g' p q l LP' LQ' ST).
    specialize(merge_label_sendb ys0 LP LP' ST n l q H21 H2 H1); intros. 
    assert (exists (LS' : sort) (LT' : ltt), onth l LQ' = Some (LS', LT')).
    {
      apply H8; try easy.
      exists ctxG. split; try easy. split; try easy.
      intros. apply H4. apply ha_sendr with (n := n) (s := s0) (g := g); try easy.
      
    }
    destruct H11. destruct H11.
    specialize(merge_label_recv ys1 LQ LQ' (x, x0) n l p H27 H6 H11); intros. destruct H13.
    destruct x1. exists s1. exists l0. easy.
  apply proj_mon.
  apply proj_mon.
Qed.


Lemma typ_after_step_step : forall p q l G L1 L2 S T S' T',
  wfgC G ->
  projectionC G p (ltt_send q L1) -> 
  onth l L1 = Some(S, T) ->
  projectionC G q (ltt_recv p L2) -> 
  onth l L2 = Some(S', T') ->
  (isgPartsC p G /\ isgPartsC q G) /\ exists G', gttstepC G G' p q l. 
Proof.
  intros. 
  specialize(canon_rep_s G p q L1 L2 S T S' T' l H H0 H1 H2 H3); intros.
  destruct H4. rename x into Gl.
  destruct H4. destruct H4. destruct H4. destruct H4. destruct H5. destruct H6. destruct H7. clear H8. rename x into ctxG.
  specialize(typ_after_step_ctx_loose H7); intros. clear H7.
  
  revert H H0 H1 H2 H3 H4 H5 H6 H8. clear x0 x1.
  revert p q l G L1 L2 S T S' T' ctxG.
  induction Gl using gtth_ind_ref; intros.
  - inversion H4. subst.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s'0, Gjk) /\
              projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG); intros.
    destruct H7. specialize(H7 H8). clear H8 H9.
    specialize(some_onth_implies_In n ctxG G H10); intros. 
    specialize(H7 (Some G) H8). destruct H7; try easy. destruct H7. destruct H7. destruct H7. destruct H9.
    destruct H11. destruct H11. destruct H11. destruct H11. destruct H11. destruct H12. inversion H7. subst.
    split.
    - split.
      apply triv_pt_p; try easy.
      apply triv_pt_q; try easy.
    - exists x2. 
      pinversion H0; try easy. subst.
      pinversion H2; try easy. subst.
      pfold. apply steq with (s := x1); try easy.
      apply proj_mon.
      apply proj_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    inversion H5. subst.
    pinversion H1; try easy. subst. 
    assert False. apply H6. constructor. easy. subst.
    pinversion H3; try easy. subst.
    specialize(wfgC_after_step_all H12 H0); intros. rename H0 into Ht.
    specialize(proj_inv_lis p q l s s' ys L1 L2 S T S' T'); intros.
    assert(s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
     s <> p /\
     s' <> q /\
     Forall
       (fun u : option (sort * gtt) =>
        u = None \/
        (exists
           (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
         (T T' : sort * ltt),
           u = Some (s, g) /\
           projectionC g p (ltt_send q LP') /\
           projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T'))
       ys).
    {
      apply H0; try easy. pfold. easy. pfold. easy.
    }
    destruct H10; try easy. destruct H10. destruct H11. clear H10 H11. clear H0 Ht.
    assert(List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\
        typ_gtth ctxG g g' /\
        (isgPartsC p g' /\ isgPartsC q g' /\ (exists G', gttstepC g' G' p q l))
    )) xs ys).
    {
      clear H27 H23 H22 H19 H18 H21 H17 H16 H13 H12 H14 H5 H4 H3 H2 H1.
      revert H24 H9 H15 H8 H H6 H7. clear H20 H26.
      clear ys0 ys1 S T S' T' L1 L2. 
      revert s s' p q l ctxG ys.
      induction xs; intros.
      - destruct ys; try easy.
      - destruct ys; try easy.
        inversion H. inversion H24. inversion H9. inversion H15. clear H H24 H9 H15. subst.
        assert (Forall2
         (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
          u = None /\ v = None \/
          (exists (s0 : sort) (g : gtth) (g' : gtt),
             u = Some (s0, g) /\
             v = Some (s0, g') /\
             typ_gtth ctxG g g' /\
             isgPartsC p g' /\ isgPartsC q g' /\ (exists G' : gtt, gttstepC g' G' p q l))) xs
         ys).
       {
        specialize(IHxs s s' p q l ctxG ys). apply IHxs; try easy.
        specialize(ishParts_hxs H6); try easy.
        specialize(ishParts_hxs H7); try easy.
       }
       constructor; try easy.
       clear H H22 H16 H11 H3 IHxs.
       destruct H20. left. easy.
       destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
       destruct H14; try easy. destruct H. destruct H. destruct H. inversion H. subst. clear H.
       destruct H10; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H.
       inversion H. subst. clear H.
       destruct H2; try easy. destruct H. destruct H. destruct H. inversion H. subst. clear H.
       rename x3 into Gl. rename x1 into G. rename x4 into LQ. rename x5 into LP. destruct x6. destruct x7.
       right. exists x2. exists Gl. exists G. split; try easy. split. easy. split. easy.
       specialize(H2 p q l G LQ LP s0 l0 s1 l1 ctxG). 
       assert((isgPartsC p G /\ isgPartsC q G) /\ (exists G' : gtt, gttstepC G G' p q l)).
       apply H2; try easy. 
       specialize(ishParts_x H6); try easy.
       specialize(ishParts_x H7); try easy.
       destruct H; try easy.
    }
    specialize(typ_after_step_step_helper2 xs ys p q l ctxG H0); intros. destruct H10.
    rename x into zs. destruct H10.
    specialize(typ_after_step_step_helper3 xs ys ctxG H14 H15); intros.
    specialize(typ_after_step_step_helper4 ys zs p q l H25 H11); intros.
    assert((exists G' : gtt, gttstepC (gtt_send s s' ys) G' p q l)).
    {
      exists (gtt_send s s' zs).
      pfold. apply stneq; try easy.
      specialize(typ_after_step_step_helper5 ys zs p q l H11); intros. easy.
    }
    split; try easy.
    apply proj_mon.
    apply proj_mon.
Qed.


Lemma typ_after_step_h : forall p q l G L1 L2 S T xs y,
  wfgC G ->
  projectionC G p (ltt_send q L1) -> 
  subtypeC (ltt_send q (extendLis l (Datatypes.Some(S,T)))) (ltt_send q L1) ->
  projectionC G q (ltt_recv p L2) -> 
  onth l xs = Some y ->
  subtypeC (ltt_recv p xs) (ltt_recv p L2) -> 
  exists G', gttstepC G G' p q l.
Proof.
  intros.
  specialize(typ_after_step_step p q l G L1 L2); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) L1 H1); intros.
  specialize(subtype_recv_inv p xs L2 H4); intros.
  specialize(projection_step_label_s G p q l L1 L2); intros.
  specialize(typ_after_step_h_helper L1 l S T H6); intros. destruct H9.
  specialize(H8 x). 
  assert(exists (LS' : sort) (LT' : ltt), onth l L2 = Some (LS', LT')). apply H8; try easy.
  destruct H10. destruct H10.
  destruct x. 
  specialize(H5 s l0 x0 x1).
  apply H5; try easy. 
Qed.


Lemma typ_after_step_12_helper : forall p q l G G' LP LQ S T S' T',
  wfgC G -> 
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some(S, T) ->
  projectionC G q (ltt_recv p LQ) -> 
  onth l LQ = Some(S', T') ->
  gttstepC G G' p q l -> 
  projectionC G' p T /\ projectionC G' q T'.
Proof.
  intros.
  specialize(canon_rep_s G p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H5. rename x into Gl. rename H into Ht.
  revert H0 H1 H2 H3 H4 H5 Ht. revert p q l G G' LP LQ S S' T T'.
  induction Gl using gtth_ind_ref; intros.
  - destruct H5. destruct H. destruct H. destruct H. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9.
    rename x1 into Sn. rename x0 into SI. rename x into ctxG. 
    inversion H. subst.
    specialize(some_onth_implies_In n ctxG G H13); intros.
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
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG); intros. destruct H12.
    specialize(H12 H7). clear H7 H14. 
    specialize(H12 (Some G) H11). destruct H12; try easy.
    destruct H7. destruct H7. destruct H7. destruct H12. destruct H14.
    destruct H14. destruct H14. destruct H14. destruct H14. destruct H14. destruct H16. destruct H17. destruct H18.
    subst. inversion H7. subst. clear H7.
    pinversion H4; try easy. subst. specialize(eq_trans H24 H14); intros. inversion H7. subst. easy.
    apply step_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10.
    rename x into ctxG. rename x1 into Sn. rename x0 into SI. 
    inversion H5. subst. 
    pinversion H0; try easy. subst.
    assert False. apply H6. constructor. easy.
    pinversion H2; try easy. subst.
    pinversion H4; try easy. subst. 
    
    specialize(proj_inv_lis p q l s s' ys LP LQ S T S' T'); intros.
    assert (s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
      s <> p /\
      s' <> q /\
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
    {
      pclearbot.
      apply H12; try easy. 
      specialize(typ_after_step_ctx_loose H8); try easy.
      pfold. easy. pfold. easy.
    }
    destruct H13; try easy. destruct H13. destruct H14.
    clear H15 H16 H19 H28 H29 H30 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g p T /\ projectionC g q T')) ys2).
    {
      clear H5 H4 H2 H0 H17.
      specialize(wfgC_after_step_all H22 Ht); intros. clear Ht. 
      specialize(merge_same ys ys0 ys1 p q l LP LQ S T S' T' ctxG SI s s' xs H33 H23 H24 H34 H8 H35 H1 H3 H6 H7 H18 H0); intros.
      clear H32 H27 H26 H25 H22 H21 H35 H31 H24 H20 H3 H1 H23 H34.
      clear ys0 ys1 LP LQ.
      revert H2 H0 H40 H18 H11 H10 H9 H8 H7 H6 H. clear H39 H33. 
      revert s s' p q l S S' T T' ys ys2 ctxG SI Sn.
      induction xs; intros; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
        inversion H0. subst. clear H0. inversion H40. subst. clear H40.
        inversion H18. subst. clear H18. inversion H. subst. clear H.
        inversion H2. subst. clear H2.
        specialize(IHxs s s' p q l S S' T T' ys ys2 ctxG SI Sn).
        assert (Forall
         (fun u : option (sort * gtt) =>
          u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ projectionC g p T /\ projectionC g q T')) ys2).
        {
          apply IHxs; try easy.
          - intros. apply H7.
            - case_eq (eqb q s); intros.
              assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb q s'); intros.
              assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (q <> s). apply eqb_neq; try easy. 
              assert (q <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
          - intros. apply H6.
            - case_eq (eqb p s); intros.
              assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb p s'); intros.
              assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (p <> s). apply eqb_neq; try easy. 
              assert (p <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
        }
        constructor; try easy.
        clear H H17 H15 H16 H14 H5 IHxs.
        destruct H12. destruct H. left. easy.
        destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
        destruct H1; try easy. destruct H as (s2,(g3,(LP,(LQ,(Hd,(He,(Hf,(Hg,Hh)))))))). inversion Hd. subst.
        destruct H13; try easy. destruct H as (s3,(g4,(g5,(Hi,(Hj,Hk))))). inversion Hj. subst.
        destruct H4; try easy. destruct H as (s4,(g6,(Hl,Hm))). inversion Hl. subst.
        destruct H3; try easy. destruct H as (s5,(g7,(Hn,Ho))). inversion Hn. subst.
        specialize(Ho p q l g6 g2 LP LQ S S' T T'). 
        right. exists s5. exists g2. split; try easy.
        apply Ho; try easy. destruct Hc; try easy.
        exists ctxG. exists SI. exists Sn. split. easy.
        - split. intros. apply H6. 
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := s5) (g := g7); try easy.
        - split; try easy. intros. apply H7.
          - case_eq (eqb q s); intros.
            assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb q s'); intros.
            assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (q <> s). apply eqb_neq; try easy. 
            assert (q <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := s5) (g := g7); try easy.
    }
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ projectionC g p t)) ys2 ys3 /\ isMerge T ys3).
    {
      clear H33 H39 H32 H26 H25 H22 H21 H35 H34 H31 H24 H23 Ht H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H12 H40 H18 H17. clear H27 H20. revert p T xs ys T'. clear s s' LP LQ S S' SI Sn ys0 ys1.
      revert ctxG q l.
      
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H40. subst. clear H18 H12 H40.
        specialize(SList_f o0 xs H17); intros.
        destruct H.
        - specialize(IHys2 ctxG q l p T xs ys T' H3 H8 H4 H). clear H4 H3 H8.
          destruct IHys2 as (ys3,(Ha,Hb)).
          destruct H6; try easy.
          - destruct H0. subst.
            destruct H2; try easy. destruct H0. subst.
            exists (None :: ys3). 
            split.
            - constructor; try easy. left. easy.
            - constructor. easy.
          - destruct H0 as (s1,(g1,(g2,(Hc,(Hd,He))))). easy.
          - destruct H0 as (s1,(g1,(g2,(Hc,(Hd,He))))). subst.
            destruct H2; try easy. destruct H0 as (s2,(g3,(g4,(Hf,(Hg,Hh))))). inversion Hg. subst.
            destruct H1; try easy. destruct H0 as (s3,(g5,(Hi,(Hj,Hk)))). inversion Hi. subst.
            exists (Some T :: ys3). split. constructor; try easy.
            right. exists s3. exists g5. exists T. easy.
            constructor; try easy.
        - destruct H. destruct H0. subst.
          destruct ys; try easy. destruct ys2; try easy. clear H8 H3 H4 IHys2.
          destruct H2; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
          destruct H6; try easy. destruct H as (s2,(g3,(g4,(Hd,(He,Hf))))). inversion Hd. subst.
          destruct H1; try easy. destruct H as (s3,(g5,(Hh,(Hi,Hj)))). inversion Hh. subst.
          exists [Some T]. split.
          constructor; try easy. right. exists s3. exists g5. exists T. easy. constructor.
    }
    destruct H13. destruct H13. split. pfold.
    specialize(wfgCw_after_step (gtt_send s s' ys) (gtt_send s s' ys2) p q l); intros.
    assert(wfgCw (gtt_send s s' ys2)). apply H15; try easy. pfold. easy.
    clear H15.
    specialize(decidable_isgPartsC_s (gtt_send s s' ys2) p H16); intros.
    unfold Decidable.decidable in H15.
    destruct H15.
    - apply proj_cont with (ys := x); try easy.
      revert H13. apply Forall2_mono; intros. destruct H13. left. easy.
      right. destruct H13 as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
      subst. exists s1. exists g1. exists t1. split. easy. split. easy. left. easy.
    - unfold not in H15.
      specialize(part_cont_false_all_s ys2 s s' p); intros.
      assert(Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ (isgPartsC p g -> False))) ys2).
      apply H19; try easy. clear H19.

      specialize(typ_after_step_12_helper ys2 x p); intros.
      assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x).
      apply H19; try easy.
      specialize(wfgCw_after_step_all H22 H16); try easy.
      specialize(merge_end_s x T H29 H14); intros. subst.
      apply proj_end; try easy.
    clear H13 H14.
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ projectionC g q t)) ys2 ys3 /\ isMerge T' ys3).
    {
      clear H33 H39 H32 H26 H25 H22 H21 H35 H34 H31 H24 H23 Ht H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H12 H40 H18 H17. clear H27 H20. revert p T xs ys T'. clear s s' LP LQ S S' SI Sn ys0 ys1.
      revert ctxG q l.
      
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H40. subst. clear H18 H12 H40.
        specialize(SList_f o0 xs H17); intros.
        destruct H.
        - specialize(IHys2 ctxG q l p T xs ys T' H3 H8 H4 H). clear H4 H3 H8.
          destruct IHys2 as (ys3,(Ha,Hb)).
          destruct H6; try easy.
          - destruct H0. subst.
            destruct H2; try easy. destruct H0. subst.
            exists (None :: ys3). 
            split.
            - constructor; try easy. left. easy.
            - constructor. easy.
          - destruct H0 as (s1,(g1,(g2,(Hc,(Hd,He))))). easy.
          - destruct H0 as (s1,(g1,(g2,(Hc,(Hd,He))))). subst.
            destruct H2; try easy. destruct H0 as (s2,(g3,(g4,(Hf,(Hg,Hh))))). inversion Hg. subst.
            destruct H1; try easy. destruct H0 as (s3,(g5,(Hi,(Hj,Hk)))). inversion Hi. subst.
            exists (Some T' :: ys3). split. constructor; try easy.
            right. exists s3. exists g5. exists T'. easy.
            constructor; try easy.
        - destruct H. destruct H0. subst.
          destruct ys; try easy. destruct ys2; try easy. clear H8 H3 H4 IHys2.
          destruct H2; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
          destruct H6; try easy. destruct H as (s2,(g3,(g4,(Hd,(He,Hf))))). inversion Hd. subst.
          destruct H1; try easy. destruct H as (s3,(g5,(Hh,(Hi,Hj)))). inversion Hh. subst.
          exists [Some T']. split.
          constructor; try easy. right. exists s3. exists g5. exists T'. easy. constructor.
    }
    destruct H13. destruct H13. pfold.
    specialize(wfgCw_after_step (gtt_send s s' ys) (gtt_send s s' ys2) p q l); intros.
    assert(wfgCw (gtt_send s s' ys2)). apply H15; try easy. pfold. easy.
    clear H15.
    specialize(decidable_isgPartsC_s (gtt_send s s' ys2) q H16); intros.
    unfold Decidable.decidable in H15.
    destruct H15.
    - apply proj_cont with (ys := x0); try easy.
      revert H13. apply Forall2_mono; intros. destruct H13. left. easy.
      right. destruct H13 as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
      subst. exists s1. exists g1. exists t1. split. easy. split. easy. left. easy.
    - unfold not in H15.
      specialize(part_cont_false_all_s ys2 s s' q); intros.
      assert(Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ (isgPartsC q g -> False))) ys2).
      apply H19; try easy. clear H19.

      specialize(typ_after_step_12_helper ys2 x0 q); intros.
      assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x0).
      apply H19; try easy.
      specialize(wfgCw_after_step_all H22 H16); try easy.
      specialize(merge_end_s x0 T' H29 H14); intros. subst.
      apply proj_end; try easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma typ_after_step_1 : forall p q l G G' LP LQ S T S' T' xs,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  subtypeC (ltt_send q (extendLis l (Datatypes.Some (S, T)))) (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  onth l xs = Some (S', T') ->
  subtypeC (ltt_recv p xs) (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists L, 
  projectionC G' p L /\ subtypeC T L. 
Proof.
  intros.
  specialize(typ_after_step_12_helper p q l G G' LP LQ); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) LP H1); intros.
  specialize(subtype_recv_inv p xs LQ H4); intros.
  specialize(projection_step_label G G' p q l LP LQ H H0 H2 H5); intros.
  destruct H9. destruct H9. destruct H9. destruct H9. destruct H9.
  rename x into s. rename x0 into s'. rename x1 into t. rename x2 into t'.
  
  specialize(H6 s t s' t' H H0 H9 H2 H10 H5).
  exists t. split; try easy.
  
  clear H10 H8 H6 H5 H4 H3 H2 H1 H0 H. clear s' t' xs T' S' LQ G G' p q.
  revert H9 H7. revert LP S T t s.
  induction l; intros; try easy.
  - destruct LP; try easy. inversion H7. subst.
    destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0.
    destruct H1. inversion H. subst. simpl in H9. inversion H9. subst. easy.
  - destruct LP; try easy. inversion H7. subst. specialize(IHl LP S T t s). apply IHl; try easy.
Qed.

Lemma typ_after_step_2 : forall p q l G G' LP LQ S T S' T' xs,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  subtypeC (ltt_send q (extendLis l (Datatypes.Some (S, T)))) (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  onth l xs = Some (S', T') ->
  subtypeC (ltt_recv p xs) (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists L, 
  projectionC G' q L /\ subtypeC T' L. 
Proof.
  intros.
  specialize(typ_after_step_12_helper p q l G G' LP LQ); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) LP H1); intros.
  specialize(subtype_recv_inv p xs LQ H4); intros.
  specialize(projection_step_label G G' p q l LP LQ H H0 H2 H5); intros.
  destruct H9. destruct H9. destruct H9. destruct H9. destruct H9.
  rename x into s. rename x0 into s'. rename x1 into t. rename x2 into t'.
  
  specialize(H6 s t s' t' H H0 H9 H2 H10 H5).
  exists t'. split; try easy.
  
  clear H9 H7 H6 H5 H4 H2 H1 H0 H.
  clear s t S T LP G G' p q.
  revert H3 H8 H10. revert LQ S' T' xs t' s'.
  induction l; intros.
  - destruct LQ; try easy. destruct xs; try easy.
    inversion H8. subst. simpl in *. subst.
    destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0.
    destruct H1. inversion H0. inversion H. subst. easy.
  - destruct LQ; try easy. destruct xs; try easy. 
    inversion H8. subst. simpl in *. 
    specialize(IHl LQ S' T' xs t' s'). apply IHl; try easy.
Qed.


Lemma part_after_step_r : forall G r p q G' l T,
        wfgC G -> 
        wfgC G' ->
        r <> p -> r <> q ->
        isgPartsC r G -> 
        gttstepC G G' p q l -> 
        projectionC G r T ->
        isgPartsC r G'.
Proof.
  intros.
  rename H0 into Htt. rename H1 into H0. rename H2 into H1. rename H3 into H2.
  rename H4 into H3. rename H5 into H4.
  specialize(wfgC_step_part G G' p q l H H3); intros.
  specialize(balanced_to_tree G p H H5); intros. clear H5.
  destruct H6 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  revert Hc Hb Ha H4 H3 H2 H1 H0 H Htt. revert ctxG T l G' r p q G.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ctxG G H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : list (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
    destruct H6. specialize(H6 Hc). clear H8 Hc.
    specialize(H6 (Some G) H5). destruct H6; try easy.
    destruct H6 as (q1,(lsg,Hd)).
    - destruct Hd. inversion H6. subst. pinversion H3; try easy. subst.
      pinversion H4; try easy. subst. easy. subst. easy. subst.
      assert(exists t, onth l ys = Some t /\ projectionC G' r t).
      {
        clear H21 H17 H14 H13 H11 H12 H15 H5 H7 H H0 H1 H6 H2 H3 H4 Ha Hb Htt.
        revert H20 H16.
        revert G' r lsg s ys.
        induction l; intros; try easy.
        - destruct lsg; try easy. destruct ys; try easy.
          inversion H20. subst. clear H20.
          simpl in H16. subst. destruct H2; try easy. 
          destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
          exists t1. destruct Hc; try easy.
        - destruct lsg; try easy. destruct ys; try easy.
          inversion H20. subst. clear H20.
          specialize(IHl G' r lsg s ys). apply IHl; try easy.
      }
      destruct H8 as (t1,(He,Hf)).
      pinversion Hf; try easy. subst.
      specialize(merge_end_back l ys T He H21); intros. subst.
      assert(projectionC (gtt_send p q lsg) r ltt_end). pfold. easy.
      specialize(pmergeCR (gtt_send p q lsg) r); intros.
      assert(False). apply H10; try easy. easy.
    apply proj_mon. apply proj_mon. apply step_mon.
    - destruct H6. inversion H6. subst. pinversion H3; try easy. apply step_mon.
    - inversion H6. subst. pinversion H3; try easy. apply step_mon.
  - inversion Ha. subst.
    pinversion H3; try easy. subst. assert False. apply Hb. constructor. easy.
    subst. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    clear H21.
    - case_eq (eqb r s); intros.
      assert (r = s). apply eqb_eq; try easy. subst. apply triv_pt_p; try easy.
    - case_eq (eqb r s'); intros.
      assert (r = s'). apply eqb_eq; try easy. subst. apply triv_pt_q; try easy.
    - assert (r <> s). apply eqb_neq; try easy. 
      assert (r <> s'). apply eqb_neq; try easy.
      clear H6 H7.
    specialize(part_cont ys r s s' H2 H8 H17); intros.
    destruct H6 as (n,(s1,(g1,(Hta,Htb)))).
    pinversion H4; try easy. subst. easy. subst. easy. subst.
    specialize(wfgC_after_step_all H10 H5); intros.
    specialize(part_after_step_r_helper n ys s1 g1 ys1 ys0 xs p q l r ctxG); intros.
    assert(exists (g2 : gtt) (g3 : gtth) (t : ltt),
       onth n ys0 = Some (s1, g2) /\
       gttstepC g1 g2 p q l /\
       onth n xs = Some (s1, g3) /\
       typ_gtth ctxG g3 g1 /\ onth n ys1 = Some t /\ projectionC g1 r t /\ wfgC g1).
    {
      apply H7; try easy.
    }
    clear H7. destruct H18 as (g2,(g3,(t1,(Hsa,(Hsb,(Hsc,(Hsd,(Hse,(Hsf,Hsg))))))))).
    specialize(some_onth_implies_In n xs (s1, g3) Hsc); intros.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : list (option gtt)) (T : ltt) (l : fin) (G' : gtt) (r p q : string) (G : gtt),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q0 : string) (lsg : list (option (sort * gtt))),
                 u0 = Some (gtt_send p q0 lsg) \/ u0 = Some (gtt_send q0 p lsg) \/ u0 = Some gtt_end))
             ctxG ->
           (ishParts p g -> False) ->
           typ_gtth ctxG g G ->
           projectionC G r T ->
           gttstepC G G' p q l -> isgPartsC r G -> r <> q -> r <> p -> wfgC G -> wfgC G' -> isgPartsC r G')))
      xs); intros.
    destruct H18. specialize(H18 H). clear H H24.
    specialize(H18 (Some (s1, g3)) H7). destruct H18; try easy.
    destruct H as (s3,(g4,(Hma,Hmb))). inversion Hma. subst.
    specialize(Hmb ctxG t1 l g2 r p q g1).
    assert(isgPartsC r g2).
    {
      apply Hmb; try easy.
      specialize(ishParts_n Hb Hsc); intros. apply H; try easy.
      specialize(wfgC_after_step_all H10 Htt); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
       u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys0); intros.
      destruct H18. specialize(H18 H). clear H24 H.
      specialize(some_onth_implies_In n ys0 (s3, g2) Hsa); intros.
      specialize(H18 (Some (s3, g2)) H). destruct H18; try easy.
      destruct H18 as (st1,(gt1,(Hmc,Hmd))). inversion Hmc. subst. easy.
    }
    apply part_cont_b with (n := n) (s := s3) (g := g2); try easy.
  apply proj_mon.
  apply step_mon.
Qed.

Lemma typ_after_step_3_helper : forall G G' p q s l L1 L2 LS LT LS' LT' T,
      wfgC G ->
      wfgC G' ->
      projectionC G p (ltt_send q L1) ->
      onth l L1 = Some (LS, LT) ->
      projectionC G q (ltt_recv p L2) ->
      onth l L2 = Some (LS', LT') ->
      gttstepC G G' p q l ->
      s <> q ->
      s <> p ->
      projectionC G s T -> 
      exists T', projectionC G' s T' /\ T = T'. 
Proof.
  intros.
  rename H0 into Htt. rename H1 into H0. rename H2 into H1.
  rename H3 into H2. rename H4 into H3. rename H5 into H4. rename H6 into H5.
  rename H7 into H6. rename H8 into H7.
  specialize(canon_rep_s G p q L1 L2 LS LT LS' LT' l H H0 H1 H2 H3); intros. 
  destruct H8. rename x into Gl. rename H into Ht.
  destruct H8 as (ctxG,(SI,(Sn,(Ha,(Hb,(Hc,(Hd,He))))))).
  clear He.
  specialize(typ_after_step_ctx_loose Hd); intros. clear Hd.
  clear SI Sn.
  revert H0 H1 H2 H3 H4 H5 H6 H7 Ha Hb Hc H Ht Htt. revert p q l G G' L1 L2 LS LS' LT LT' s T ctxG.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(Forall_forall (fun u : option gtt =>
       u = None \/
       (exists (g : gtt) (lsg : list (option (sort * gtt))),
          u = Some g /\
          g = gtt_send p q lsg /\
          (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
             onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq)))
      ctxG); intros.
    destruct H8. specialize(H8 H). clear H9 H.
    specialize(some_onth_implies_In n ctxG G H10); intros.
    specialize(H8 (Some G) H). destruct H8; try easy.
    destruct H8 as (g,(lsg,(Hta,(Htb,Htc)))). inversion Hta. subst. clear Hta.
    destruct Htc as (s',(Gjk,(Tp,(Tq,(Hsa,(Hsb,Hsc)))))). 
    pinversion H4; try easy. subst.
    specialize(eq_trans H17 Hsa); intros. inversion H8. subst. clear H8 H14 H13 H17.
    pinversion H7; try easy. 
    - subst. exists ltt_end. split. 
      pfold. apply proj_end; try easy.
      specialize(part_after_step (gtt_send p q lsg) Gjk p q s l L1 L2); intros.
      apply H8. apply H9; try easy. pfold. easy.
      constructor. 
    - subst. easy.
    - subst. easy.
    - subst. exists T. split. pfold. 
      specialize(typ_after_step_3_helper_h4 l lsg s' Gjk ys s T); intros.
      assert(projectionC Gjk s T). apply H8; try easy.
      pinversion H9; try easy. apply proj_mon.
      easy.
    apply proj_mon.
    apply step_mon.
  - inversion Ha. subst.
    rename s into r. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    pinversion H0; try easy. subst.
    assert False. apply Hb. constructor. easy.
    subst.
    pinversion H2; try easy. subst.
    specialize(proj_inv_lis p q l s s' ys L1 L2 LS LT LS' LT'); intros.
    assert(s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
     s <> p /\
     s' <> q /\
     Forall
       (fun u : option (sort * gtt) =>
        u = None \/
        (exists
           (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
         (T T' : sort * ltt),
           u = Some (s, g) /\
           projectionC g p (ltt_send q LP') /\
           projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T'))
       ys). apply H9; try easy. pfold. easy. pfold. easy.
    destruct H10. destruct H10. subst. easy.
    destruct H10 as (H10,(Hsa,Hsb)). clear H10 Hsa H9.
    pinversion H4; try easy. subst. clear H12 H13 H16 H18 H19 H22.
    
    assert(forall t, t <> p -> t <> q -> List.Forall (fun u => u = None \/ (exists s' g, u = Some (s', g) /\ forall G' T, 
        gttstepC g G' p q l -> projectionC g t T -> wfgC G' -> exists T', projectionC G' t T' /\ T = T')) ys).
    {
      intros. apply Forall_forall; intros. rename H9 into Hka. rename H10 into Hkb. rename H11 into H9. destruct x.
      - right. specialize(in_some_implies_onth p0 ys H9); intros. destruct H10 as (n, H10).
        destruct p0. exists s0. exists g. split. easy.
        intros. rename H13 into Htl.
        specialize(typ_after_step_3_helper_h2 H10 H15); intros. destruct H13 as (g', (H13, Hla)).
        specialize(some_onth_implies_In n xs (s0, g') H13); intros.
        specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (p q : string) (l : fin) (G G' : gtt) (L1 L2 : list (option (sort * ltt)))
             (LS LS' : sort) (LT LT' : ltt) (s0 : string) (T : ltt) (ctxG : list (option gtt)),
           projectionC G p (ltt_send q L1) ->
           onth l L1 = Some (LS, LT) ->
           projectionC G q (ltt_recv p L2) ->
           onth l L2 = Some (LS', LT') ->
           gttstepC G G' p q l ->
           s0 <> q ->
           s0 <> p ->
           projectionC G s0 T ->
           typ_gtth ctxG g G ->
           (ishParts p g -> False) ->
           (ishParts q g -> False) ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
                    onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG ->
           wfgC G -> wfgC G' -> exists T' : ltt, projectionC G' s0 T' /\ T = T'))) xs); intros.
        destruct H18. specialize(H18 H). clear H19 H.
        specialize(H18 (Some (s0, g')) H16). destruct H18; try easy. 
        specialize(Forall_forall (fun u : option (sort * gtt) =>
         u = None \/
         (exists
            (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T'))
        ys); intros. destruct H18. specialize(H18 Hsb). clear Hsb H19.
        specialize(H18 (Some (s0, g)) H9). destruct H18; try easy.
        destruct H18 as (s1,(g1,(LP',(LQ',(T1,(T1',(Hma,(Hmb,(Hmc,(Hmd,Hme)))))))))).
        inversion Hma. subst. clear Hma.
        destruct H as (s2,(g2,(Hta,Htb))). inversion Hta. subst.
        specialize(Htb p q l g1 G' LP' LQ').
        destruct T1. destruct T1'. 
        specialize(Htb s0 s1 l0 l1 t T0 ctxG). apply Htb; try easy.
        specialize(ishParts_n Hb H13); intros. apply H. easy.
        specialize(ishParts_n Hc H13); intros. apply H. easy.
        specialize(wfgC_after_step_all H25 Ht); intros.
        specialize(Forall_prop n ys (s2, g1) (fun u : option (sort * gtt) =>
       u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) H10 H); intros.
        simpl in H18. destruct H18; try easy. destruct H18 as (st1,(gt1,(Hba,Hbb))). inversion Hba. subst. easy.
        left. easy.
    }
    pose proof H9 as Hla.
    specialize(H9 s H28 H29).
    specialize(wfgC_after_step_all H25 Htt); intros. rename H10 into Htk.
    specialize(typ_after_step_3_helper_h3 ys ys2 p q l H37 Hla Htk); intros. clear Hla H37.
    pinversion H7. subst.
    - exists ltt_end. split.
      pfold. apply proj_end. intros. apply H11.
      specialize(part_after_step (gtt_send s s' ys) (gtt_send s s' ys2) p q r l L1 L2); intros.
      apply H13; try easy. pfold. easy. pfold. easy. pfold. easy. constructor.
    - subst.
      specialize(wfgC_after_step_all H25 Ht); intros.
      exists (ltt_recv s ys3). split; try easy.
      pfold. constructor; try easy.
      apply triv_pt_q; try easy. 
      specialize(H10 r H30 H31).
      specialize(typ_after_step_3_helper_h5 ys ys2 ys3 p q l r); intros. apply H12; try easy.
    - subst.
      specialize(wfgC_after_step_all H25 Ht); intros.
      exists (ltt_send s' ys3). split; try easy.
      pfold. constructor; try easy.
      apply triv_pt_p; try easy. 
      specialize(H10 r H28 H29).
      specialize(typ_after_step_3_helper_h5 ys ys2 ys3 p q l r); intros. apply H12; try easy.
    - subst. exists T.
      split; try easy. 
      specialize(decidable_isgPartsC (gtt_send s s' ys2) r Htt); intros.
      unfold Decidable.decidable in H11. unfold not in H11.
      destruct H11.
      - pfold. apply proj_cont with (ys := ys3); try easy.
        specialize(H10 r).
        assert(Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s' : sort) (g g' : gtt),
            u = Some (s', g) /\
            v = Some (s', g') /\
            gttstepC g g' p q l /\
            (forall T : ltt, projectionC g r T -> exists T' : ltt, projectionC g' r T' /\ T = T'))) ys ys2). apply H10; try easy. clear H10.
        specialize(typ_after_step_3_helper_h6 ys ys2 ys3 p q l r); intros. apply H10; try easy.
      - specialize(part_after_step_r (gtt_send s s' ys) r p q (gtt_send s s' ys2) l T); intros.
        assert(isgPartsC r (gtt_send s s' ys2)). apply H12; try easy. pfold. easy. pfold. easy.
        specialize(H11 H13). easy.
      apply proj_mon. apply step_mon. apply proj_mon. apply proj_mon.
Qed.


Lemma proj_cont_pq_step : forall G G' p q l,
    wfgC G -> 
    gttstepC G G' p q l -> 
    projectableA G ->
    exists LP LQ S S' T T',
    projectionC G p (ltt_send q LP) /\ 
    projectionC G q (ltt_recv p LQ) /\
    onth l LP = Some(S, T) /\ onth l LQ = Some(S', T').
Proof.
  intros.
  specialize(wfgC_step_part G G' p q l H H0); intros.
  specialize(balanced_to_tree G p H H2); intros. clear H2.
  destruct H3 as (Gl,(ct,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  revert H H0 H1 Ha Hb Hc. revert G G' p q l ct.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ct G H4); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : list (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ct); intros.
    destruct H3. specialize(H3 Hc). clear Hc H5.
    specialize(H3 (Some G) H2). destruct H3; try easy.
    destruct H3 as (q1,(lsg,Hc)). clear H2.
    - destruct Hc. inversion H2. subst.  
      pinversion H0; try easy. subst.
      unfold projectableA in H1. pose proof H1 as Ht.
      specialize(H1 p). destruct H1. pinversion H1; try easy. subst.
      assert False. apply H3. apply triv_pt_p; try easy. easy.
      subst. specialize(Ht q). destruct Ht. pinversion H3; try easy. 
      subst. assert False. apply H5. apply triv_pt_q; try easy. easy. subst.
      exists ys. exists ys0.
      assert(exists (S S' : sort) (T T' : ltt),
        onth l ys = Some (S, T) /\ onth l ys0 = Some (S', T')).
      {
        clear H16 H18 H15 H9 H13 H7 H3 H8 H11 H4 Hb H2 Ha H1 H0 H.
        revert H19 H14 H12.
        revert G' p q lsg ys s ys0. clear n ct.
        induction l; intros.
        - destruct lsg; try easy. 
          destruct ys; try easy. destruct ys0; try easy.
          inversion H19. subst. clear H19. inversion H14. subst. clear H14.
          simpl in H12. subst.
          destruct H2; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
          destruct H3; try easy. destruct H as (s2,(g2,(t2,(Hd,(He,Hf))))). inversion Hd. subst.
          simpl. exists s2. exists s2. exists t2. exists t1. easy.
        - destruct lsg; try easy. 
          destruct ys; try easy. destruct ys0; try easy.
          inversion H19. subst. clear H19. inversion H14. subst. clear H14.
          specialize(IHl G' p q lsg ys s ys0). apply IHl; try easy.
      }
      destruct H5 as (s1,(s2,(t1,(t2,(Hl,Hk))))). exists s1. exists s2. exists t1. exists t2. 
      split. pfold. easy. split. pfold. easy. easy.
    apply proj_mon. apply proj_mon. apply step_mon.
    - destruct H2. inversion H2. subst. pinversion H0; try easy. apply step_mon.
    - inversion H2. subst. pinversion H0; try easy. apply step_mon.
  - inversion Ha. subst.
    clear Ha. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    specialize(proj_forward s s' ys H0 H2); intros. 
    pinversion H1; try easy. subst. assert False. apply Hb. constructor. easy.
    subst.
    specialize(wfgC_after_step_all H10 H0); intros. rename H1 into Htt.
    clear H19.
    unfold projectableA in H2. pose proof H2 as Ht.
    specialize(H2 p). destruct H2 as (T,H2). specialize(Ht q). destruct Ht as (T',Ht).
    specialize(slist_implies_some xs H8); intros.
    destruct H1 as (n,(gl,H1)). destruct gl.
    specialize(Forall2_prop_r n xs ys (s0, g) (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ct g g')) H1 H9); intros.
    destruct H5 as (p1,(Hd,He)). destruct He; try easy.
    destruct H5 as (s1,(g1,(g2,(Hf,(Hg,Hh))))). inversion Hf. subst. clear Hf.
    specialize(Forall_prop n ys (s1, g2) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Hg H4); intros.
    destruct H5; try easy. destruct H5 as (s2,(g3,(Hi,Hj))). inversion Hi. subst. clear Hi.
    clear H9 H4 H8.
    specialize(Forall2_prop_r n ys ys0 (s2, g3) (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) Hg H20); intros.
    destruct H4 as (p1,(Hi,Hk)). destruct Hk; try easy. destruct H4 as (s3,(g4,(g5,(Hl,(Hm,Hn))))).
    inversion Hl. subst. clear Hl H20.
    specialize(Forall_prop n ys (s3, g4) (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ projectableA g)) Hg H3); intros.
    destruct H4; try easy. destruct H4 as (s4,(g6,(Ho,Hp))). inversion Ho. subst. clear H3.
    specialize(some_onth_implies_In n xs (s4, g1) H1); intros.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G G' : gtt) (p q : string) (l : fin) (ct : list (option gtt)),
           wfgC G ->
           gttstepC G G' p q l ->
           projectableA G ->
           typ_gtth ct g G ->
           (ishParts p g -> False) ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q0 : string) (lsg : list (option (sort * gtt))),
                 u0 = Some (gtt_send p q0 lsg) \/ u0 = Some (gtt_send q0 p lsg) \/ u0 = Some gtt_end))
             ct ->
           exists (LP LQ : list (option (sort * ltt))) (S S' : sort) (T T' : ltt),
             projectionC G p (ltt_send q LP) /\
             projectionC G q (ltt_recv p LQ) /\ onth l LP = Some (S, T) /\ onth l LQ = Some (S', T')))) xs); intros. 
    destruct H4. specialize(H4 H). clear H H5.
    specialize(H4 (Some (s4, g1)) H3). destruct H4; try easy.
    destruct H as (s5,(g7,(Hq,Hr))). inversion Hq. subst.
    clear H3.
    specialize(Hr g6 g5 p q l ct).
    assert(exists (LP LQ : list (option (sort * ltt))) (S S' : sort) (T T' : ltt),
       projectionC g6 p (ltt_send q LP) /\
       projectionC g6 q (ltt_recv p LQ) /\ onth l LP = Some (S, T) /\ onth l LQ = Some (S', T')).
    {
      apply Hr; try easy.
      destruct Hn; try easy.
      specialize(ishParts_n Hb H1); intros. apply H; try easy.
    }
    clear Hr. 
    clear Hp Hn Hm Hj Hh Ho H1 Hq. clear g7 g5.
    destruct H as (lp,(lq,(s1,(s2,(t1,(t2,(Hta,(Htb,(Htc,Htd))))))))).
    clear Htt.
    assert(isgPartsC p g6). 
    {
      pinversion Hta; try easy.
      apply proj_mon.
    }
    assert(isgPartsC q g6).
    {
      pinversion Htb; try easy.
      apply proj_mon.
    }
    specialize(part_cont_b n ys s5 g6 p s s' Hg); intros.
    assert(isgPartsC p (gtt_send s s' ys)). apply H3; try easy.
    specialize(part_cont_b n ys s5 g6 q s s' Hg); intros.
    assert(isgPartsC q (gtt_send s s' ys)). apply H5; try easy.
    clear H3 H5.
    pinversion Ht; try easy. subst. pinversion H2; try easy. subst.
    clear H23 H22 H19 H18 H17 H16 H15 H6 H4 H1 H H14 H13 H12 H11 H10 H7 Hc Hb.
    specialize(Forall2_prop_r n ys ys1 (s5, g6) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) Hg H20); intros.
    destruct H as (p1,(Ha,Hb)). destruct Hb; try easy. destruct H as (s3,(g1,(t3,(Hb,(Hc,Hd))))).
    inversion Hb. subst. clear Hb.
    specialize(Forall2_prop_r n ys ys2 (s3, g1) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) Hg H26); intros.
    destruct H as (p2,(He,Hf)). destruct Hf; try easy. destruct H as (s4,(g2,(t4,(Hj,(Hh,Hi))))).
    inversion Hj. subst.
    pclearbot.
    specialize(wfgC_after_step_all H9 H0); intros.
    specialize(Forall_prop n ys (s4, g2) (fun u : option (sort * gtt) =>
       u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Hg H); intros.
    destruct H1; try easy. destruct H1 as (s5,(g3,(Hk,Hl))). inversion Hk. subst.
    specialize(proj_inj Hl Hi Hta); intros. subst.
    specialize(proj_inj Hl Hd Htb); intros. subst.
    clear H H26 H20 Hi Hd.
    specialize(merge_send_T n T ys2 q lp H27 Hh); intros. destruct H as (lp',H). subst.
    specialize(merge_recv_T n T' ys1 p lq H21 Hc); intros. destruct H as (lq',H). subst.
    exists lp'. exists lq'. 
    specialize(merge_label_recv ys1 lq' lq (s2, t2) n l p H21 Hc Htd); intros. destruct H as (ta,H). 
    specialize(merge_label_send ys2 lp' lp (s1, t1) n l q H27 Hh Htc); intros. destruct H1 as (tb,H1).
    destruct ta. destruct tb.
    exists s3. exists s0. exists l1. exists l0.
    split. pfold. easy. split. pfold. easy. easy.
  apply proj_mon.
  apply proj_mon.
  apply step_mon.
Qed.

Lemma proj_cont_pq_step_full : forall G G' p q l,
    wfgC G -> 
    gttstepC G G' p q l -> 
    projectableA G ->
    exists (T T' : ltt), projectionC G' p T /\ projectionC G' q T'.
Proof.
  intros.
  specialize(proj_cont_pq_step G G' p q l H H0 H1); intros.
  destruct H2 as (l1,(l2,(s1,(s2,(t1,(t2,(Ha,(Hb,(Hc,Hd))))))))).
  specialize(typ_after_step_12_helper p q l G G' l1 l2 s1 t1 s2 t2); intros.
  exists t1.
  exists t2. apply H2; try easy.
Qed.

Lemma balanced_step : forall [G G' p q l],
    wfgC G -> 
    gttstepC G G' p q l -> 
    projectableA G ->
    balancedG G'.
Proof.
  intros. pose proof H as Ht.
  unfold wfgC in H. destruct H as (Gl,(Ha,(Hb,(Hc,H)))). clear Ha Hb Hc. clear Gl.
  specialize(wfgC_step_part G G' p q l Ht H0); intros.
  specialize(balanced_to_tree G p Ht H2); intros.
  destruct H3 as (Gl,(ct,(Ha,(Hb,(Hc,Hd))))). clear Hd H2.
  revert Hc Hb Ha Ht H1 H0. clear H.
  revert G G' p q l ct.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ct G H3); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : list (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ct); intros.
    destruct H2. specialize(H2 Hc). clear H4 Hc.
    specialize(H2 (Some G) H). destruct H2; try easy.
    destruct H2 as (q1,(lsg,Hc)).
    - destruct Hc. inversion H2. subst.
      pinversion H0; try easy. subst.
      unfold wfgC in Ht. destruct Ht as (G1,(Hta,(Htb,(Htc,Htd)))).
      specialize(balanced_cont Htd); intros.
      specialize(some_onth_implies_In l lsg (s, G') (esym H12)); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) lsg); intros. 
      destruct H6. specialize(H6 H4). clear H4 H7.
      specialize(H6 (Some (s, G')) H5). destruct H6; try easy.
      destruct H4 as (s1,(g1,(Hsa,Hsb))). inversion Hsa. subst. easy.
      apply step_mon.
    - destruct H2. inversion H2. subst. pinversion H0; try easy.
      apply step_mon.
    - inversion H2. subst. pinversion H0; try easy.
      apply step_mon.
  - inversion Ha. subst. 
    pinversion H0; try easy.
    - subst. assert False. apply Hb. constructor. easy.
    subst. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    assert(Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ balancedG g)) ys0).
    {
      clear Ha H7. 
      specialize(wfgC_after_step_all H6 Ht); intros.
      specialize(proj_forward s s' ys Ht H1); intros. clear H1.
      clear H5 H6 H9 H10 H11 H12 Ht H0 H17.
      revert H3 H2 H18 H8 Hc H Hb. revert s s' xs p q l ct ys.
      induction ys0; intros; try easy.
      destruct ys; try easy. destruct xs; try easy.
      inversion H3. subst. clear H3. inversion H2. subst. clear H2.
      inversion H18. subst. clear H18. 
      inversion H8. subst. clear H8. inversion H. subst. clear H.
      specialize(IHys0 s s' xs p q l ct ys).
      assert(Forall
          (fun u : option (sort * gtt) =>
           u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) ys0).
      {
        apply IHys0; try easy.
        specialize(ishParts_hxs Hb); try easy.
      }
      constructor; try easy.
      clear H H8 H12 H10 H6 H5 IHys0.
      destruct H7. left. easy.
      destruct H as (s1,(g1,(g2,(Hd,(He,Hf))))). subst.
      destruct H3; try easy. destruct H as (s2,(g3,(Hg,Hh))). inversion Hg. subst.
      destruct H4; try easy. destruct H as (s3,(g4,(Hi,Hj))). inversion Hi. subst.
      destruct H9; try easy. destruct H as (s4,(g5,(g6,(Hk,(Hl,Hm))))). inversion Hl. subst.
      destruct H2; try easy. destruct H as (s5,(g7,(Hn,Ho))). inversion Hn. subst.
      right. exists s5. exists g2. split. easy.
      clear Hn Hl Hg Hi. destruct Hf; try easy. 
      specialize(Ho g6 g2 p q l ct). apply Ho; try easy.
      specialize(ishParts_x Hb); try easy.
    }
    clear H18 H17 H8 H7 H.
    unfold balancedG.
    intros.
    destruct w.
    - simpl.
      {
        simpl in *. 
        assert(exists Gl, Gl = (gtth_send s s' xs)). exists (gtth_send s s' xs). easy.
        destruct H4 as (Gl,H4). replace (gtth_send s s' xs) with Gl in *.
        assert(exists G, G = (gtt_send s s' ys)). exists (gtt_send s s' ys). easy.
        destruct H7 as (G,H7). replace (gtt_send s s' ys) with G in *.
        assert(exists G', G' = (gtt_send s s' ys0)). exists (gtt_send s s' ys0). easy.
        - case_eq (eqb p0 p); intros.
          assert (p0 = p). apply eqb_eq; try easy. subst. 
          {
            clear H4 Hc Hb Ha. 
            clear H8 H7 H13.
            assert(gttstepC G (gtt_send s s' ys0) p q l). pfold. easy. clear H0.
            specialize(proj_cont_pq_step_full G (gtt_send s s' ys0) p q l Ht H4 H1); intros.
            destruct H0 as (T,(T1,(Ha,Hb))). clear Hb. clear T1.
            
            specialize(wfgCw_after_step G (gtt_send s s' ys0) p q l Ht H4); intros. 
            
            assert(isgPartsC p (gtt_send s s' ys0)).
            {
              apply word_to_parts with (w' := w') (q0 := q0); try easy.
            }
            assert(Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ isgPartsC p g)) ys0).
            {
              apply Forall_forall; intros.
              destruct x.
              - right. destruct p0. exists s0. exists g. split. easy.
                pinversion Ha; try easy. subst.
                specialize(in_some_implies_onth (s0, g) ys0 H8); intros.
                destruct H13 as (n, H13).
                specialize(Forall2_prop_r n ys0 ys1 (s0, g) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) H13 H22); intros.
                destruct H14 as (p1,(Hta,Htb)). destruct Htb; try easy.
                destruct H14 as (s1,(g1,(t1,(Htb,(Htc,Htd))))). inversion Htb. subst.
                destruct Htd; try easy.
                pinversion H14; try easy. subst.
                specialize(merge_end_back n ys1 T Htc H23); intros. subst.
                specialize(pmergeCR_s (gtt_send s s' ys0) p); intros.
                assert False. apply H20; try easy.
                pfold. easy. easy.
                apply proj_mon. apply proj_mon.
              - left. easy.
            }
            unfold balancedG in H2.
            assert((Forall (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                  exists k : fin,
                    forall w'0 : list fin,
                    gttmap g w'0 None gnode_end \/
                    length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                    exists w2 w0 : list fin,
                      w'0 = w2 ++ w0 /\
                      (exists r : string,
                         gttmap g w2 None (gnode_pq p r) \/
                         gttmap g w2 None (gnode_pq r p))))) ys0).
            {
              apply Forall_forall; intros.
              specialize(Forall_forall  (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall (w w' : list fin) (p q : string) (gn : gnode),
            gttmap g w None gn ->
            gttmap g (seq.cat w w') None (gnode_pq p q) \/ gttmap g (seq.cat w w') None (gnode_pq q p) ->
            exists k : fin,
              forall w'0 : list fin,
              gttmap g (seq.cat w w'0) None gnode_end \/
              length w'0 = k /\ (exists tc : gnode, gttmap g (seq.cat w w'0) None tc) ->
              exists w2 w0 : list fin,
                w'0 = w2 ++ w0 /\
                (exists r : string,
                   gttmap g (seq.cat w w2) None (gnode_pq p r) \/
                   gttmap g (seq.cat w w2) None (gnode_pq r p))))) ys0); intros.
              destruct H14. specialize(H14 H2). clear H15 H2.
              specialize(H14 x H13).
              specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ isgPartsC p g)) ys0); intros.
              destruct H2. specialize(H2 H8). clear H8 H15.
              specialize(H2 x H13).
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Hb,Hc))). subst.
              destruct H14; try easy.
              destruct H2 as (s2,(g2,(Hd,He))). inversion Hd. subst.
              clear H13 Hd.
              right. exists s2. exists g2. split. easy.
              specialize(parts_to_word p g2 Hc); intros.
              destruct H2 as (w1,(r,Hd)).
              specialize(He nil w1 p r).
              specialize(nil_word g2); intros. destruct H2 as (tc,H2).
              specialize(He tc). apply He; try easy. simpl.
              destruct Hd. right. easy. left. easy.
            }
            clear H8 H7 Ha H4 H2.
            assert(exists K, 
                Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt),
            u = Some (s, g) /\
            (exists k : fin, k <= K /\
               forall w'0 : list fin,
               gttmap g w'0 None gnode_end \/
               length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
               exists w2 w0 : list fin,
                 w'0 = w2 ++ w0 /\
                 (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p)))))
        ys0).
            {
              clear H0 H3 H H12 H11 H10 H9 H6 H5 H1 Ht.
              revert H13. revert p. clear s s' xs q l ct Gl ys G w' q0 gn T.
              induction ys0; intros; try easy.
              exists 0. constructor.
              inversion H13. subst. clear H13. specialize(IHys0 p H2).
              destruct IHys0 as (K, Ha). clear H2.
              destruct H1.
              - subst. exists K. constructor; try easy. left. easy.
              - destruct H as (s1,(g1,(Hb,(k,Hc)))). subst.
                exists (Nat.max k K).
                constructor; try easy.
                - right. exists s1. exists g1. split. easy.
                  exists k. split; try easy.
                  apply max_l.
                - revert Ha. clear Hc. clear g1 s1.
                  apply Forall_mono; intros.
                  destruct H. left. easy.
                  destruct H as (s1,(g1,(Ha,(k1,(Hb,Hc))))).
                  right. subst. exists s1. exists g1.
                  split. easy. exists k1. split; try easy.
                  apply leq_trans with (n := K); try easy.
                  apply max_r.
            }
            destruct H2 as (K, H2). clear H13.
            assert(Forall
             (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                    (forall w'0 : list fin,
                     gttmap g w'0 None gnode_end \/
                     length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                     exists w2 w0 : list fin,
                       w'0 = w2 ++ w0 /\
                       (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p))))) ys0).
            {
              revert H2. apply Forall_mono; intros.
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Ha,(k,(Hb,Hc))))).
              subst. right. exists s1. exists g1. split. easy.
              apply cut_further with (k := k); try easy.
            }
            clear H2.
            exists (S K).
            intros. clear H H3. clear gn w' ct Gl. clear ys xs H1 Ht.
            destruct H2.
            - inversion H. subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p))))) H14 H4); intros.
               destruct H1; try easy. destruct H1 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
               specialize(Hb lis).
               assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). left. easy.
               specialize(Hb H1). clear H1.
               destruct Hb as (w2,(w0,(Hc,(r,Hd)))). subst.
               exists (n :: w2). exists w0. split. constructor.
               exists r.
               destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
            - destruct H as (H,(tc,Ha)).
              inversion Ha; try easy. subst. easy.
              subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p))))) H14 H4); intros.
              destruct H1; try easy. destruct H1 as (s1,(g1,(Hb,Hc))). inversion Hb. subst.
              specialize(Hc lis).
              assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). right. split. apply eq_add_S. easy. exists tc. easy.
              specialize(Hc H1). clear H1.
              destruct Hc as (w2,(w0,(Hc,(r,Hd)))). subst.
              exists (n :: w2). exists w0. split. constructor. exists r.
              destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
          }
        - case_eq (eqb p0 q); intros.
          assert (p0 = q). apply eqb_eq; try easy. subst. 
          {
            simpl in *. 
            clear H4 Hc Hb Ha. 
            clear H8 H7 H13 H14.
            assert(gttstepC G (gtt_send s s' ys0) p q l). pfold. easy. clear H0.
            specialize(proj_cont_pq_step_full G (gtt_send s s' ys0) p q l Ht H4 H1); intros.
            destruct H0 as (T1,(T,(Hb,Ha))). clear Hb. clear T1.
            
            specialize(wfgCw_after_step G (gtt_send s s' ys0) p q l Ht H4); intros. 
            
            assert(isgPartsC q (gtt_send s s' ys0)).
            {
              apply word_to_parts with (w' := w') (q0 := q0); try easy.
            }
            assert(Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ isgPartsC q g)) ys0).
            {
              apply Forall_forall; intros.
              destruct x.
              - right. destruct p0. exists s0. exists g. split. easy.
                pinversion Ha; try easy. subst.
                specialize(in_some_implies_onth (s0, g) ys0 H8); intros.
                destruct H13 as (n, H13).
                specialize(Forall2_prop_r n ys0 ys1 (s0, g) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) H13 H22); intros.
                destruct H14 as (p1,(Hta,Htb)). destruct Htb; try easy.
                destruct H14 as (s1,(g1,(t1,(Htb,(Htc,Htd))))). inversion Htb. subst.
                destruct Htd; try easy.
                pinversion H14; try easy. subst.
                specialize(merge_end_back n ys1 T Htc H23); intros. subst.
                specialize(pmergeCR_s (gtt_send s s' ys0) q); intros.
                assert False. apply H20; try easy.
                pfold. easy. easy.
                apply proj_mon. apply proj_mon.
              - left. easy.
            }
            unfold balancedG in H2.
            assert((Forall (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                  exists k : fin,
                    forall w'0 : list fin,
                    gttmap g w'0 None gnode_end \/
                    length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                    exists w2 w0 : list fin,
                      w'0 = w2 ++ w0 /\
                      (exists r : string,
                         gttmap g w2 None (gnode_pq q r) \/
                         gttmap g w2 None (gnode_pq r q))))) ys0).
            {
              apply Forall_forall; intros.
              specialize(Forall_forall  (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall (w w' : list fin) (p q : string) (gn : gnode),
            gttmap g w None gn ->
            gttmap g (seq.cat w w') None (gnode_pq p q) \/ gttmap g (seq.cat w w') None (gnode_pq q p) ->
            exists k : fin,
              forall w'0 : list fin,
              gttmap g (seq.cat w w'0) None gnode_end \/
              length w'0 = k /\ (exists tc : gnode, gttmap g (seq.cat w w'0) None tc) ->
              exists w2 w0 : list fin,
                w'0 = w2 ++ w0 /\
                (exists r : string,
                   gttmap g (seq.cat w w2) None (gnode_pq p r) \/
                   gttmap g (seq.cat w w2) None (gnode_pq r p))))) ys0); intros.
              destruct H14. specialize(H14 H2). clear H15 H2.
              specialize(H14 x H13).
              specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ isgPartsC q g)) ys0); intros.
              destruct H2. specialize(H2 H8). clear H8 H15.
              specialize(H2 x H13).
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Hb,Hc))). subst.
              destruct H14; try easy.
              destruct H2 as (s2,(g2,(Hd,He))). inversion Hd. subst.
              clear H13 Hd.
              right. exists s2. exists g2. split. easy.
              specialize(parts_to_word q g2 Hc); intros.
              destruct H2 as (w1,(r,Hd)).
              specialize(He nil w1 q r).
              specialize(nil_word g2); intros. destruct H2 as (tc,H2).
              specialize(He tc). apply He; try easy. simpl.
              destruct Hd. right. easy. left. easy.
            }
            clear H8 H7 Ha H4 H2.
            assert(exists K, 
                Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt),
            u = Some (s, g) /\
            (exists k : fin, k <= K /\
               forall w'0 : list fin,
               gttmap g w'0 None gnode_end \/
               length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
               exists w2 w0 : list fin,
                 w'0 = w2 ++ w0 /\
                 (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q)))))
        ys0).
            {
              clear H0 H3 H H12 H11 H10 H9 H6 H5 H1 Ht.
              revert H13. revert q. clear s s' xs p l ct Gl ys G w' q0 gn T.
              induction ys0; intros; try easy.
              exists 0. constructor.
              inversion H13. subst. clear H13. specialize(IHys0 q H2).
              destruct IHys0 as (K, Ha). clear H2.
              destruct H1.
              - subst. exists K. constructor; try easy. left. easy.
              - destruct H as (s1,(g1,(Hb,(k,Hc)))). subst.
                exists (Nat.max k K).
                constructor; try easy.
                - right. exists s1. exists g1. split. easy.
                  exists k. split; try easy.
                  apply max_l.
                - revert Ha. clear Hc. clear g1 s1.
                  apply Forall_mono; intros.
                  destruct H. left. easy.
                  destruct H as (s1,(g1,(Ha,(k1,(Hb,Hc))))).
                  right. subst. exists s1. exists g1.
                  split. easy. exists k1. split; try easy.
                  apply leq_trans with (n := K); try easy.
                  apply max_r.
            }
            destruct H2 as (K, H2). clear H13.
            assert(Forall
             (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                    (forall w'0 : list fin,
                     gttmap g w'0 None gnode_end \/
                     length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                     exists w2 w0 : list fin,
                       w'0 = w2 ++ w0 /\
                       (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q))))) ys0).
            {
              revert H2. apply Forall_mono; intros.
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Ha,(k,(Hb,Hc))))).
              subst. right. exists s1. exists g1. split. easy.
              apply cut_further with (k := k); try easy.
            }
            clear H2.
            exists (S K).
            intros. clear H H3. clear gn w' ct Gl. clear ys xs H1 Ht.
            destruct H2.
            - inversion H. subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q))))) H14 H4); intros.
               destruct H1; try easy. destruct H1 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
               specialize(Hb lis).
               assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). left. easy.
               specialize(Hb H1). clear H1.
               destruct Hb as (w2,(w0,(Hc,(r,Hd)))). subst.
               exists (n :: w2). exists w0. split. constructor.
               exists r.
               destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
            - destruct H as (H,(tc,Ha)).
              inversion Ha; try easy. subst. easy.
              subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q))))) H14 H4); intros.
              destruct H1; try easy. destruct H1 as (s1,(g1,(Hb,Hc))). inversion Hb. subst.
              specialize(Hc lis).
              assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). right. split. apply eq_add_S. easy. exists tc. easy.
              specialize(Hc H1). clear H1.
              destruct Hc as (w2,(w0,(Hc,(r,Hd)))). subst.
              exists (n :: w2). exists w0. split. constructor. exists r.
              destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
          }
        - destruct H8 as (G',H8). replace (gtt_send s s' ys0) with G' in *. clear H4 H7 H8.
          assert (p0 <> p). apply eqb_neq; try easy. 
          assert (p0 <> q). apply eqb_neq; try easy.
          {
            pose proof Ht as Htt.
            unfold wfgC in Htt. destruct Htt as (G1,(Hf,(Hg,(Hd,He)))). clear Hf Hg Hd. clear G1.
            clear H13 H14 H H12 H11 H10 H9 H6 H5 Ht.
            assert(gttstepC G G' p q l). pfold. easy. clear H0 H1 H2. clear s s' xs ys ys0.
            unfold balancedG in He. specialize(He nil). simpl in He.
            
            assert(exists k : fin,
       forall w'0 : list fin,
       gttmap G w'0 None gnode_end \/ length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc) ->
       exists w2 w0 : list fin,
         w'0 = w2 ++ w0 /\
         (exists r : string, gttmap G w2 None (gnode_pq p0 r) \/ gttmap G w2 None (gnode_pq r p0))).
            {
              specialize(nil_word G); intros.
              destruct H0 as (tc1,H0).
              destruct H3.
              - specialize(word_step_back_s H H1); intros.
                destruct H2. specialize(He w' p0 q0 tc1). apply He; try easy.
                left. easy.
              - destruct H2 as (w0,(w1,(Hd,Hf))). specialize(He (w0 ++ l :: w1) p0 q0 tc1).
                apply He; try easy.
                left. easy.
              - specialize(word_step_back_s H H1); intros.
                destruct H2. specialize(He w' p0 q0 tc1). apply He; try easy.
                right. easy.
              - destruct H2 as (w0,(w1,(Hd,Hf))). specialize(He (w0 ++ l :: w1) p0 q0 tc1).
                apply He; try easy.
                right. easy.
            }
            clear He H3.
            
            destruct H0 as (k, H0). exists k.
            intros.
            destruct H1.
            - specialize(word_step_back_ss H H1); intros.
              destruct H2.
              - specialize(H0 w'0).
                assert(gttmap G w'0 None gnode_end \/ length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc)).
                {
                  left. specialize(H2 w'0 nil gnode_end). apply H2; try easy.
                  apply esym.
                  apply app_nil_r.
                }
                specialize(H0 H3). clear H3.
                destruct H0 as (w2,(w0,(Hta,(r,Htb)))).
                exists w2. exists w0. split. easy. exists r.
                destruct Htb.
                - specialize(H2 w2 w0 (gnode_pq p0 r)). left. apply H2; try easy.
                - specialize(H2 w2 w0 (gnode_pq r p0)). right. apply H2; try easy.
              - destruct H2 as (w0,(w1,(Hd,(He,(Hf,Hg))))). subst.
                pose proof Hf as Ht.
                specialize(Hf w1 nil gnode_end).
                assert(gttmap G (w0 ++ l :: w1) None gnode_end). apply Hf; try easy.
                apply esym. apply app_nil_r.
                specialize(H0 (w0 ++ l :: w1)).
                assert(gttmap G (w0 ++ l :: w1) None gnode_end \/
     length (w0 ++ l :: w1) = k /\ (exists tc : gnode, gttmap G (w0 ++ l :: w1) None tc)). left. easy.
                specialize(H0 H3). clear H3.
                destruct H0 as (w2,(w3,(Hh,(r,Hi)))).
                clear Hc Hb Ha H H1 H2 Hf.
                specialize(decon_word w2 l w0 w1 w3 Hh); intros.
                - destruct H.
                  subst. destruct Hi.
                  specialize(inj_gttmap Hg H); intros. inversion H0. subst. easy.
                  specialize(inj_gttmap Hg H); intros. inversion H0. subst. easy.
                - destruct H.
                  destruct H as (wi,(wj,Hta)). subst.
                  specialize(He w2 wi wj). exists w2. exists (wi ++ wj :: w1).
                  split.
                  apply stword.
                  exists r. destruct Hi.
                  specialize(He (gnode_pq p0 r)). left. apply He; try easy.
                  specialize(He (gnode_pq r p0)). right. apply He; try easy.
                - destruct H as (wi,(wj,(Hta,Htb))). subst.
                  specialize(Ht wi wj). exists (w0 ++ wi). exists wj. split. 
                  apply app_assoc. exists r.
                  destruct Hi.
                  - left. apply Ht; try easy.
                  - right. apply Ht; try easy.
          - destruct H1 as (H1,(tc,H2)).
            specialize(word_step_back_ss H H2); intros.
            clear Hc Hb Ha H. clear Gl ct. clear w' gn.
            destruct H3.
            - assert(gttmap G w'0 None gnode_end \/
     length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc)).
              {
                right. split. easy. exists tc.
                specialize(H w'0 nil). apply H; try easy.
                apply esym. apply app_nil_r.
              }
              specialize(H0 w'0 H3). clear H3.
              destruct H0 as (w2,(w0,(Ha,(r,Hb)))).
              subst. exists w2. exists w0. split. easy. exists r.
              specialize(H w2 w0). destruct Hb.
              - left. apply H; try easy.
              - right. apply H; try easy.
            - destruct H as (w0,(w1,(Ha,(Hb,(Hc,Hd))))).
              assert(k <= S k). easy.
              specialize(cut_further k (S k) G p0 H H0); intros. clear H H0.
              assert(gttmap G (w0 ++ l :: w1) None tc).
              {
                specialize(Hc w1 nil tc). apply Hc; try easy.
                apply esym. apply app_nil_r; try easy. subst. easy.
              }
              specialize(H3 (w0 ++ l :: w1)).
              assert(gttmap G (w0 ++ l :: w1) None gnode_end \/
               length (w0 ++ l :: w1) = S k /\
               (exists tc : gnode, gttmap G (w0 ++ l :: w1) None tc)).
              {
                right. split. subst.
                clear H H3 Hd Hc Hb H2 H7 H4. clear p q G G' p0 q0 tc.
                revert w1 l. induction w0; intros; try easy.
                simpl in *. apply eq_S. apply IHw0; try easy.
                exists tc. easy.
              }
              specialize(H3 H0). clear H0.
              destruct H3 as (w2,(w3,(He,(r,Hf)))). subst.
              specialize(decon_word w2 l w0 w1 w3 He); intros.
              - destruct H0.
                subst.
                destruct Hf. 
                - specialize(inj_gttmap H0 Hd); intros. inversion H1. subst. easy.
                - specialize(inj_gttmap H0 Hd); intros. inversion H1. subst. easy.
              - destruct H0.
                destruct H0 as (wi,(wj,Hg)). subst.
                specialize(Hb w2 wi wj). exists w2. exists (wi ++ wj :: w1). 
                split. apply stword.
                exists r.
                destruct Hf.
                - left. apply Hb; try easy.
                - right. apply Hb; try easy.
              - destruct H0 as (wi,(wj,(Hg,Hh))). subst.
                specialize(Hc wi wj).
                exists (w0 ++ wi). exists wj. split. apply app_assoc.
                exists r.
                destruct Hf.
                - left. apply Hc; try easy.
                - right. apply Hc; try easy.
            }
      }
    - inversion H. subst.
      specialize(some_onth_implies_In n ys0 (st, gk) H17); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) ys0); intros.
      destruct H7. specialize(H7 H2). clear H8 H2.
      specialize(H7 (Some (st, gk)) H4). destruct H7; try easy.
      destruct H2 as (s1,(g1,(Hta,Htb))). inversion Hta. subst. clear H4 Hta.
      unfold balancedG in Htb.
      specialize(Htb w w' p0 q0 gn H18).
      assert(gttmap g1 (seq.cat w w') None (gnode_pq p0 q0) \/ gttmap g1 (seq.cat w w') None (gnode_pq q0 p0)).
      {
        destruct H3. left. inversion H2; try easy. subst. specialize(eq_trans (esym H16) H17); intros.
        inversion H3. subst. easy.
        right. inversion H2; try easy. subst. specialize(eq_trans (esym H16) H17); intros.
        inversion H3. subst. easy.
      }
      specialize(Htb H2). clear H2 H3.
      destruct Htb. exists x. intros.
      specialize(H2 w'0).
      assert(gttmap g1 (seq.cat w w'0) None gnode_end \/
     length w'0 = x /\ (exists tc : gnode, gttmap g1 (seq.cat w w'0) None tc)).
      {
        destruct H3. left.
        inversion H3. subst. specialize(eq_trans (esym H19) H17); intros. inversion H4. subst.
        easy.
        destruct H3. destruct H4 as (tc, H4).
        right. split; try easy.
        exists tc. inversion H4. subst.
        specialize(eq_trans (esym H20) H17); intros. inversion H3. subst.
        easy.
      }
      specialize(H2 H4).
      destruct H2 as (w2,(w0,(Hsa,Hsb))). exists w2. exists w0.
      split. easy. destruct Hsb as (r, Hsb). exists r.
      {
        destruct Hsb.
        left. apply gmap_con with (st := s1) (gk := g1); try easy.
        right. apply gmap_con with (st := s1) (gk := g1); try easy.
      }
    apply step_mon.
Qed.

Theorem wfgC_after_step : forall G G' p q n, wfgC G -> gttstepC G G' p q n -> projectableA G -> wfgC G'. 
Proof.
  intros. rename H1 into Htt. 
  pose proof H as Ht. unfold wfgC in H.
  destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
  specialize(wfgC_step_part G G' p q n Ht H0); intros.
  specialize(balanced_to_tree G p Ht H); intros. clear Ht H.
  destruct H1 as (Gt,(ctxG,(Hta,(Htb,(Htc,Htd))))).
  clear Htd.
  revert Htc Htb Hta H0 Hd Hc Hb Ha Htt.
  revert G G' p q n Gl ctxG.
  induction Gt using gtth_ind_ref; intros; try easy.
  - inversion Hta. subst.
    specialize(Forall_forall (fun u : option gtt =>
         u = None \/
         (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
            u = Some (gtt_send p q lsg) \/
            u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
    destruct H. specialize(H Htc). clear H1 Htc.
    specialize(some_onth_implies_In n ctxG G H2); intros.
    specialize(H (Some G) H1). destruct H; try easy. destruct H as (r,(lsg,Hsa)). clear H1.
    - destruct Hsa. inversion H. subst. 
      pinversion H0; try easy. subst. clear H6 H.
      specialize(guard_breakG_s2 (gtt_send p q lsg) Gl Hc Hb Ha); intros.
      clear Ha Hb Hc. clear Gl. destruct H as (Gl,(Ha,(Hb,(Hc,He)))).
      destruct Ha. subst. pinversion He. apply gttT_mon.
      destruct H as (p1,(q1,(lis1,H))). subst. pinversion He; try easy. subst.
      inversion Hc. subst.
      specialize(balanced_cont Hd); intros.
      specialize(guard_cont Hb); intros.
      specialize(wfgC_after_step_helper n0 s G' lsg lis1); intros.
      assert(exists G1 : global,
       onth n0 lis1 = Some (s, G1) /\
       gttTC G1 G' /\
       wfG G1 /\ balancedG G' /\ (forall n : fin, exists m : fin, guardG n m G1)).
      apply H4; try easy. clear H4. clear H3 H H7 H1.
      destruct H8 as (G1,(Hsa,(Hsb,(Htc,(Htd,Hte))))). exists G1. easy.
      apply gttT_mon.
      apply step_mon.
    - destruct H. inversion H. subst. pinversion H0; try easy. apply step_mon.
    - inversion H. subst. pinversion H0; try easy. apply step_mon.
  - inversion Hta. subst.
    assert(wfgC (gtt_send p q ys)).
    {
      unfold wfgC. exists Gl. easy.
    }
    rename H1 into Ht.
    pinversion H0; try easy.
    - subst. assert False. apply Htb. constructor. easy.
    subst. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    specialize(guard_breakG_s2 (gtt_send s s' ys) Gl Hc Hb Ha); intros. clear Ha Hb Hc. clear Gl.
    destruct H1 as (Gl,(Ha,(Hb,(Hc,He)))). destruct Ha. subst. pinversion He; try easy. apply gttT_mon.
    destruct H1 as (p1,(q1,(lis,H1))). subst. pinversion He; try easy. subst. inversion Hc. subst.
    specialize(balanced_cont Hd); intros.
    specialize(guard_cont Hb); intros.
    assert(List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ wfgC g)) ys0).
    {
      specialize(proj_forward s s' ys Ht Htt); intros. clear Ht Htt. rename H12 into Ht.
      clear H14 H13 Hb Hc He H16 H11 H10 H9 H8 H5 H4 H6 Hta H0 Hd.
      apply Forall_forall; intros. 
      destruct x.
      - specialize(in_some_implies_onth p0 ys0 H0); intros. destruct H4 as (n0 ,H4). clear H0.
        right. destruct p0. exists s0. exists g. split. easy.
        
        revert H4 H3 H1 H15 H2 H17 H7 Htc H Htb Ht.
        revert g s0 lis ys ys0 ctxG n p q xs s s'.
        induction n0; intros.
        - destruct ys0; try easy. destruct ys; try easy. destruct lis; try easy.
          destruct xs; try easy.
          inversion H3. subst. clear H3. inversion H1. subst. clear H1. inversion H15. subst. clear H15.
          inversion H2. subst. clear H2. inversion H17. subst. clear H17. inversion H7. subst. clear H7.
          inversion H. subst. clear H. inversion Ht. subst. clear Ht.
          clear H8 H9 H10 H14 H15 H17 H7.
          simpl in H4. subst.
          destruct H11; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Hb. subst.
          destruct H13; try easy. destruct H as (s2,(g3,(g4,(Hd,(He,Hf))))). inversion He. subst.
          destruct H12; try easy. destruct H as (s3,(g5,(g6,(Hg,(Hh,Hi))))). inversion Hh. subst.
          destruct H3; try easy. destruct H as (s4,(g7,(Hj,Hk))). inversion Hj. subst.
          destruct H6; try easy. destruct H as (s5,(g8,(Hl,Hm))). inversion Hl. subst.
          destruct H5; try easy. destruct H as (s6,(g9,(Hn,Ho))). inversion Hn. subst.
          destruct H2; try easy. clear Hn Hh He Hj Hl Hb.
          destruct H as (s7,(g10,(Hp,Hq))). inversion Hp. subst.
          destruct H1; try easy. destruct H as (s8,(g11,(Hr,Hs))). inversion Hr. subst.
          specialize(Hq g11 g2 p q n g8 ctxG). unfold wfgC.
          apply Hq; try easy. 
          specialize(ishParts_x Htb); try easy.
          destruct Hc; try easy.
          destruct Hi; try easy. 
        - destruct ys0; try easy. destruct ys; try easy. destruct lis; try easy.
          destruct xs; try easy.
          inversion H3. subst. clear H3. inversion H1. subst. clear H1. inversion H15. subst. clear H15.
          inversion H2. subst. clear H2. inversion H17. subst. clear H17. inversion H7. subst. clear H7.
          inversion H. subst. clear H. inversion Ht. subst. clear Ht.
          specialize(IHn0 g s0 lis ys ys0 ctxG n p q xs s s').
          apply IHn0; try easy.
          specialize(ishParts_hxs Htb); try easy.
        left. easy.
    }
    specialize(wfgC_after_step_helper2 lis ys ys0 n p q H13 H2 H17); intros.
    assert(wfgC (gtt_send s s' ys) /\ gttstepC (gtt_send s s' ys) (gtt_send s s' ys0) p q n). 
    {
      unfold wfgC. split. exists (g_send s s' lis). split. pfold. easy. easy.
      pfold. easy.
    }
    destruct H19.
    specialize(balanced_step H19 H20 Htt); intros. clear H19 H20 Htt Ht. rename H21 into Ht.
    clear H3 H1 H15 H2 Hb Hc He H17 H16 H11 H10 H9 H8 H5 H4 H7 Hta H0 Hd Htb Htc H H6 H13.
    clear p q xs n ctxG ys lis. rename H14 into H. rename H12 into H1.
    assert(exists xs, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ gttTC g g')) xs ys0 /\ 
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ balancedG g)) ys0 /\
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfG g)) xs /\
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ (forall n, exists m, guardG n m g))) xs).
    {
      clear H. revert H1. clear H18. clear Ht. revert ys0. clear s s'.
      induction ys0; intros; try easy.
      - exists nil. easy.
      - inversion H1. subst. clear H1.
        specialize(IHys0 H3). destruct IHys0 as (xs,H).
        destruct H2. 
        - subst. exists (None :: xs).
          split. constructor; try easy. left. easy.
          split. constructor; try easy. left. easy.
          split. constructor; try easy. left. easy.
          constructor; try easy. left. easy.
        - destruct H0 as (s,(g,(Ha,Hb))). subst.
          unfold wfgC in Hb. destruct Hb.
          exists (Some(s, x) :: xs).
          split. constructor; try easy. right. exists s. exists x. exists g. easy.
          split. constructor; try easy. right. exists s. exists g. easy.
          split. constructor; try easy. right. exists s. exists x. easy.
          constructor; try easy. right. exists s. exists x. easy.
    }
    destruct H0 as (xs,(Ha,(Hb,(Hc,Hd)))).
    exists (g_send s s' xs).
    - split. pfold. constructor; try easy.
      revert Ha. apply Forall2_mono; intros; try easy. destruct H0. left. easy.
      destruct H0 as (s0,(g0,(g1,(Hta,(Htb,Htc))))). subst. right. exists s0. exists g0. exists g1. 
      split. easy. split. easy. left. easy.
    - split. constructor; try easy.
      specialize(wfgC_after_step_helper3 ys0 xs H18 Ha); try easy.
    - split.
      apply guard_cont_b; try easy.
    - easy.
    apply gttT_mon.
    apply step_mon.
Qed.