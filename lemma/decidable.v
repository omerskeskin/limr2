From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh.
From SST Require Import lemma.inversion lemma.inversion_expr lemma.substitution_helper lemma.substitution lemma.decidable_helper.

Lemma parts_to_word : forall p G, isgPartsC p G -> exists w r, (gttmap G w None (gnode_pq r p) \/ gttmap G w None (gnode_pq p r)).
Proof.
  intros.
  unfold isgPartsC in H.
  destruct H as (Gl,(Ha,(Hb,Hc))).
  specialize(isgParts_depth_exists p Gl Hc); intros.
  destruct H as (n, H).
  clear Hc Hb.
  revert H Ha. revert Gl G p.
  induction n; intros; try easy.
  - inversion H. subst.
    exists nil. exists q. right. pinversion Ha. subst. constructor.
    apply gttT_mon.
  - subst.
    exists nil. exists p0. left. pinversion Ha. subst. constructor.
    apply gttT_mon.
  - inversion H. subst.
    pinversion Ha. subst.
    specialize(subst_parts_depth 0 0 n p g g Q H2 H1); intros.
    specialize(IHn Q G p). apply IHn; try easy.
    apply gttT_mon.
  - subst.
    pinversion Ha. subst.
    assert(exists gl, onth k ys = Some(s, gl) /\ gttTC g gl).
    {
      clear H4 H2 H1 H Ha IHn.
      revert H8 H3. revert lis ys s g.
      induction k; intros; try easy.
      - destruct lis; try easy.
        destruct ys; try easy.
        inversion H8. subst. clear H8.
        simpl in H3. subst. 
        destruct H2; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
        exists g2. destruct Hc; try easy.
      - destruct lis; try easy.
        destruct ys; try easy.
        inversion H8. subst. clear H8.
        specialize(IHk lis ys s g). apply IHk; try easy.
    }
    destruct H0 as (gl,(Hb,Hc)).
    specialize(IHn g gl p H4 Hc).
    destruct IHn as (w,(r,Hd)).
    exists (k :: w). exists r.
    destruct Hd.
    - left. apply gmap_con with (st := s) (gk := gl); try easy.
    - right. apply gmap_con with (st := s) (gk := gl); try easy.
    apply gttT_mon.
Qed.

Lemma decidable_isgParts : forall G pt, decidable (isgParts pt G).
Proof.
  induction G using global_ind_ref; intros.
  - unfold decidable. right. easy.
  - unfold decidable. right. easy.
  - revert H. induction lis; intros; try easy.
    unfold decidable.
    - case_eq (eqb pt p); intros.
      assert (pt = p). apply eqb_eq; try easy. subst. left. constructor.
    - case_eq (eqb pt q); intros.
      assert (pt = q). apply eqb_eq; try easy. subst. left. constructor.
    - assert (pt <> p). apply eqb_neq; try easy. 
      assert (pt <> q). apply eqb_neq; try easy.
      right. unfold not. intros. inversion H4; try easy. subst. destruct n; try easy.
    inversion H. subst. specialize(IHlis H3). clear H3 H.
    unfold decidable in *.
    destruct IHlis. left. 
    - inversion H. subst. constructor. constructor. subst.
      apply pa_sendr with (n := S n) (s := s) (g := g); try easy.
    - unfold not in *. 
      destruct H2. subst. right. intros. apply H. inversion H0; try easy.
      constructor. constructor. subst.
      destruct n; try easy.
      apply pa_sendr with (n := n) (s := s) (g := g); try easy. 
    - destruct H0 as (s,(g,(Ha,Hb))). subst.
    - case_eq (eqb pt p); intros.
      assert (pt = p). apply eqb_eq; try easy. subst. left. constructor.
    - case_eq (eqb pt q); intros.
      assert (pt = q). apply eqb_eq; try easy. subst. left. constructor.
    - assert (pt <> p). apply eqb_neq; try easy. 
      assert (pt <> q). apply eqb_neq; try easy.
    - specialize(Hb pt). destruct Hb. left. 
      apply pa_sendr with (n := 0) (s := s) (g := g); try easy.
      right. intros. inversion H5; try easy. subst. 
      destruct n. simpl in H12. inversion H12. subst. apply H4. easy.
      apply H.
      apply pa_sendr with (n := n) (s := s0) (g := g0); try easy.
  - unfold decidable. specialize(IHG pt). destruct IHG. left. constructor. easy.
    right. unfold not in *. intros. apply H. inversion H0; try easy.
Qed.

Lemma decidable_isgPartsC_s : forall G pt, wfgCw G -> decidable (isgPartsC pt G).
Proof.
  intros. unfold decidable. pose proof H as Ht.
  unfold wfgCw in H.
  destruct H as (G',(Ha,(Hb,Hc))). 
  specialize(decidable_isgParts G' pt); intros. unfold decidable in H.
  destruct H. left. unfold isgPartsC. exists G'. easy.
  right. unfold not in *. intros. apply H.
  clear H Ht.
  unfold isgPartsC in H0. destruct H0 as (Gl,(He,(Hf,Hg))).
  specialize(isgParts_depth_exists pt Gl Hg); intros. destruct H as (n, H). clear Hg.
  clear Hb. revert Ha Hc He Hf H.
  revert G pt G' Gl.
  induction n; intros.
  - inversion H. subst. pinversion He; try easy. subst.
    - pinversion Ha. subst. constructor. subst. clear H0 H1.
      specialize(guard_breakG G Hc); intros. 
      destruct H0 as (T,(Hta,(Htb,Htc))).
      specialize(gttTC_after_subst (g_rec G) T (gtt_send pt q ys)); intros.
    - assert(gttTC T (gtt_send pt q ys)). apply H0; try easy. pfold. easy. clear H0.
      specialize(part_betaG_b (g_rec G) T pt); intros. apply H0; try easy.
      destruct Htc. subst. pinversion H1; try easy. apply gttT_mon.
      destruct H2 as (p1,(q1,(lis1,Hl))). subst. pinversion H1; try easy. subst.
      constructor.
      apply gttT_mon. apply gttT_mon. apply gttT_mon.
    - subst. 
      pinversion He; try easy. subst.
      pinversion Ha. subst. constructor.
      subst. clear H0 H1.
      specialize(guard_breakG G Hc); intros.
      destruct H0 as (T1,(Hta,(Htb,Htc))).
      specialize(part_betaG_b (g_rec G) T1 pt); intros. apply H0; try easy.
      clear H0.
      specialize(gttTC_after_subst (g_rec G) T1 (gtt_send p pt ys)); intros.
      assert(gttTC T1 (gtt_send p pt ys)). apply H0; try easy. pfold. easy.
      clear H0. 
      destruct Htc. subst. pinversion H1; try easy. apply gttT_mon.
      destruct H0 as (p1,(q1,(lis1,Htc))). subst. pinversion H1; try easy. subst. 
      constructor.
      apply gttT_mon.
      apply gttT_mon. apply gttT_mon.
    - inversion H. 
      - subst.
        pinversion He; try easy. subst.
        specialize(subst_parts_depth 0 0 n pt g g Q H2 H1); intros.
        specialize(IHn G pt G' Q). apply IHn; try easy.
        intros. specialize(Hf n0). destruct Hf. 
        - inversion H4. subst. exists 0. constructor.
        - subst. specialize(subst_injG 0 0 (g_rec g) g Q Q0 H6 H2); intros. subst.
          exists m. easy.
        apply gttT_mon.
      - subst.
        pinversion He; try easy. subst.
        specialize(guard_cont Hf); intros.
        pinversion Ha; try easy.
        - subst.
          specialize(guard_cont Hc); intros.
          specialize(decidable_isgPartsC_helper k lis s g ys xs); intros.
          assert(exists (g' : gtt) (g'' : global),
       onth k ys = Some (s, g') /\
       gttTC g g' /\
       (forall n : fin, exists m : fin, guardG n m g) /\
       onth k xs = Some (s, g'') /\ gttTC g'' g' /\ (forall n : fin, exists m : fin, guardG n m g'')).
          apply H6; try easy. clear H6.
          clear H8 H0 H7 H5. destruct H9 as (g1,(g2,(Hg,(Hh,(Hi,(Hj,(Hk,Hl))))))).
          specialize(IHn g1 pt g2 g).
          assert(isgParts pt g2). apply IHn; try easy.
          apply pa_sendr with (n := k) (s := s) (g := g2); try easy.
        - subst. clear H5 H6. clear Q.
          specialize(guard_breakG G Hc); intros.
          destruct H5 as (T1,(Hta,(Htb,Htc))).
          specialize(gttTC_after_subst (g_rec G) T1 (gtt_send p q ys)); intros.
          assert(gttTC T1 (gtt_send p q ys)). apply H5; try easy. pfold. easy.
          clear H5. destruct Htc. subst. pinversion H6. apply gttT_mon.
          destruct H5 as (p1,(q1,(lis1,Htc))). subst. pinversion H6. subst.
          specialize(part_betaG_b (g_rec G) (g_send p q lis1) pt); intros. apply H5; try easy.
          clear H5 Htb.
          specialize(guardG_betaG (g_rec G) (g_send p q lis1)); intros.
          assert(forall n : fin, exists m : fin, guardG n m (g_send p q lis1)). apply H5; try easy.
          clear H5.
          specialize(guard_cont H9); intros.
          specialize(decidable_isgPartsC_helper k lis s g ys lis1); intros.
          assert(exists (g' : gtt) (g'' : global),
        onth k ys = Some (s, g') /\
        gttTC g g' /\
        (forall n : fin, exists m : fin, guardG n m g) /\
        onth k lis1 = Some (s, g'') /\ gttTC g'' g' /\ (forall n : fin, exists m : fin, guardG n m g'')).
          apply H10; try easy. clear H10.
          destruct H11 as (g1,(g2,(Hg,(Hh,(Hi,(Hj,(Hk,Hl))))))).
          specialize(IHn g1 pt g2 g).
          assert(isgParts pt g2). apply IHn; try easy.
          apply pa_sendr with (n := k) (s := s) (g := g2); try easy.
      apply gttT_mon.
      apply gttT_mon. 
      apply gttT_mon.
Qed.

Lemma decidable_isgPartsC : forall G pt, wfgC G -> decidable (isgPartsC pt G).
Proof.
  intros.
  apply decidable_isgPartsC_s; try easy.
  unfold wfgC in *. unfold wfgCw. 
  destruct H. exists x. easy.
Qed.

Lemma balanced_to_tree : forall G p,
    wfgC G ->
    isgPartsC p G ->
    exists G' ctxG, 
       typ_gtth ctxG G' G /\ (ishParts p G' -> False) /\
       List.Forall (fun u => u = None \/ (exists q lsg, u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some (gtt_end))) ctxG /\ usedCtx ctxG G'.
Proof.
  intros.
  specialize(parts_to_word p G H0); intros.
  destruct H1 as (w,(r,Ha)). pose proof H as Htt.
  unfold wfgC in H. destruct H as (Gl,(Hb,(Hc,(Hd,He)))). clear Hb Hc Hd. clear Gl H0.
  pose proof He as Ht.
  unfold balancedG in He.
  specialize(He nil w p r).
  simpl in He.
  assert(exists gn, gttmap G nil None gn).
  {
    destruct G. exists gnode_end. constructor.
    exists (gnode_pq s s0). constructor.
  }
  destruct H as (gn, H). specialize(He gn H).
  assert(gttmap G w None (gnode_pq p r) \/ gttmap G w None (gnode_pq r p)).
  {
    destruct Ha. right. easy. left. easy.
  }
  specialize(He H0). clear H H0. destruct He as (k, H).
  clear Ha.
  revert H Ht Htt. revert G p. clear w r gn.
  induction k; intros.
  - specialize(H nil).
    assert(exists gn, gttmap G nil None gn).
    {
      destruct G. exists gnode_end. constructor.
      exists (gnode_pq s s0). constructor.
    }
    destruct H0 as (gn, H0). inversion H0; try easy. subst.
    - assert(exists w2 w0 : seq.seq fin,
        [] = w2 ++ w0 /\
        (exists r : string,
           gttmap gtt_end w2 None (gnode_pq p r) \/ gttmap gtt_end w2 None (gnode_pq r p))).
      {
        apply H. left. easy.
      }
      clear H. destruct H1 as (w2,(w0,(Ha,Hb))). destruct w2; try easy. simpl in Ha. subst.
      destruct Hb as (r, Hb).
      destruct Hb. inversion H. inversion H.
    - assert(exists w2 w0 : seq.seq fin,
      [] = w2 ++ w0 /\
      (exists r : string, gttmap G w2 None (gnode_pq p r) \/ gttmap G w2 None (gnode_pq r p))).
      apply H. right. split. easy. exists gn. easy.
      destruct H2 as (w2,(w0,(Ha,Hb))). destruct w2; try easy. simpl in Ha. subst.
      clear H.
      destruct Hb as (r, Hb).
      destruct Hb.
      - inversion H. subst.
        exists (gtth_hol 0). exists [Some (gtt_send p r xs)].
        split.
        - constructor; try easy.
        - split. intros. inversion H1.
        - split. constructor; try easy. right. exists r. exists xs. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send p r xs))) (gtth_hol 0)). constructor.
          simpl in H1. easy.
      - inversion H. subst.
        exists (gtth_hol 0). exists [Some (gtt_send r p xs)].
        split.
        - constructor; try easy.
        - split. intros. inversion H1.
        - split. constructor; try easy. right. exists r. exists xs. right. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send r p xs))) (gtth_hol 0)). constructor.
          simpl in H1. easy.
  - destruct G.
    - exists (gtth_hol 0). exists [Some gtt_end].
      split. constructor. easy.
      split. intros. inversion H0.
      split. constructor; try easy. right. exists p. exists nil. right. right. easy.
      assert(usedCtx (extendLis 0 (Some (gtt_end))) (gtth_hol 0)). constructor. simpl in H0. easy.
    - specialize(balanced_cont Ht); intros.
      - case_eq (eqb p s); intros.
        assert (p = s). apply eqb_eq; try easy. subst.
        exists (gtth_hol 0). exists [Some (gtt_send s s0 l)].
        - split. constructor. easy.
        - split. intros. inversion H2.
        - split. constructor; try easy. right. exists s0. exists l. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send s s0 l))) (gtth_hol 0)). constructor. simpl in H2. easy.
      - case_eq (eqb p s0); intros.
        assert (p = s0). apply eqb_eq; try easy. subst.
        exists (gtth_hol 0). exists [Some (gtt_send s s0 l)].
        - split. constructor. easy.
        - split. intros. inversion H3.
        - split. constructor; try easy. right. exists s. exists l. right. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send s s0 l))) (gtth_hol 0)). constructor. simpl in H2. easy.
      - assert (p <> s). apply eqb_neq; try easy. 
        assert (p <> s0). apply eqb_neq; try easy.
        clear H1 H2.
      assert(Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\
        (forall w' : seq.seq fin,
       gttmap g w' None gnode_end \/
       Datatypes.length w' = k /\ (exists tc : gnode, gttmap g w' None tc) ->
       exists w2 w0 : seq.seq fin,
         w' = w2 ++ w0 /\
         (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p)))
      )) l).
      {
        apply Forall_forall; intros.
        destruct x.
        - specialize(in_some_implies_onth p0 l H1); intros.
          destruct H2 as (n, H2). destruct p0.
          right. exists s1. exists g. split. easy.
          intros.
          specialize(H (n :: w')).
          assert(exists w2 w0 : seq.seq fin,
            (n :: w')%SEQ = w2 ++ w0 /\
            (exists r : string,
               gttmap (gtt_send s s0 l) w2 None (gnode_pq p r) \/
               gttmap (gtt_send s s0 l) w2 None (gnode_pq r p))).
          {
            apply H; try easy.
            destruct H5. left. apply gmap_con with (st := s1) (gk := g); try easy.
            right. destruct H5. split. simpl. apply eq_S. easy.
            destruct H6. exists x.
            apply gmap_con with (st := s1) (gk := g); try easy.
          }
          destruct H6 as (w2,(w0,(Ha,Hb))).
          destruct w2.
          - simpl in *. subst.
            destruct Hb as (r, Hb). destruct Hb. inversion H6. subst. easy.
            inversion H6. subst. easy.
          - inversion Ha. subst.
            exists w2. exists w0. split. easy.
            destruct Hb as (r, Hb). exists r.
            destruct Hb.
            - left. inversion H6. subst. specialize(eq_trans (esym H14) H2); intros.
              inversion H7. subst. easy.
            - right. inversion H6. subst. specialize(eq_trans (esym H14) H2); intros.
              inversion H7. subst. easy.
        - left. easy.
      }
      assert(Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\
        exists (G' : gtth) (ctxG : seq.seq (option gtt)),
        typ_gtth ctxG G' g /\
        (ishParts p G' -> False) /\
        Forall
          (fun u : option gtt =>
           u = None \/
           (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
              u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
        usedCtx ctxG G'
      )) l). 
      {
        clear H Ht.
        assert(s <> s0).
        {
          specialize(wfgC_triv s s0 l Htt); intros. easy.
        }
        specialize(wfgC_after_step_all H Htt); intros. clear H Htt.
        revert H0 IHk H1 H3 H4 H2. revert k s s0 p.
        induction l; intros; try easy.
        inversion H1. subst. clear H1. inversion H0. subst. clear H0. inversion H2. subst. clear H2.
        specialize(IHl k s s0 p).
        assert(Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt),
            u = Some (s, g) /\
            (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
               typ_gtth ctxG G' g /\
               (ishParts p G' -> False) /\
               Forall
                 (fun u0 : option gtt =>
                  u0 = None \/
                  (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
                     u0 = Some (gtt_send p q lsg) \/ u0 = Some (gtt_send q p lsg) \/ u0 = Some gtt_end))
                 ctxG /\ usedCtx ctxG G'))) l).
         apply IHl; try easy.
         constructor; try easy. clear H H9 H8 H7 IHl.
         destruct H5. left. easy.
         destruct H as (s1,(g1,(Ha,Hb))). subst. 
         destruct H1; try easy.
         destruct H as (s2,(g2,(Hc,Hd))). inversion Hc. subst.
         destruct H6; try easy. destruct H as (s3,(g3,(He,Hf))). inversion He. subst.
         specialize(IHk g3 p). right. exists s3. exists g3. split. easy. apply IHk; try easy.
      }
    clear H1 H0 Ht H IHk.
    assert(SList l).
    {
      specialize(wfgC_triv s s0 l Htt); intros. easy.
    }
    clear Htt.
    revert H H2 H3 H4. clear k. revert s s0 p.
    induction l; intros; try easy.
    specialize(SList_f a l H); intros. clear H.
    inversion H2. subst. clear H2.
    destruct H0.
    - specialize(IHl s s0 p).
      assert(exists (G' : gtth) (ctxG : seq.seq (option gtt)),
        typ_gtth ctxG G' (gtt_send s s0 l) /\
        (ishParts p G' -> False) /\
        Forall
          (fun u : option gtt =>
           u = None \/
           (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
              u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
        usedCtx ctxG G').
      {
        apply IHl; try easy.
      }
      clear H6 H IHl.
      destruct H5.
      - subst.
        destruct H0 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
        inversion Ha.
        - subst.
          specialize(some_onth_implies_In n ctxG (gtt_send s s0 l) H); intros.
          specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
          destruct H1. specialize(H1 Hc). clear H2 Hc.
          specialize(H1 (Some (gtt_send s s0 l)) H0). destruct H1; try easy.
          destruct H1 as (q1,(lsg,He)).
          - destruct He. inversion H1. subst. easy.
          - destruct H1. inversion H1. subst. easy.
          - inversion H1. 
        - subst.
          exists (gtth_send s s0 (None :: xs)). exists ctxG.
          - split. constructor; try easy.
            constructor; try easy. left. easy.
          - split. 
            intros. apply Hb. inversion H. subst. easy. subst. easy. subst.
            destruct n; try easy.
            apply ha_sendr with (n := n) (s := s1) (g := g); try easy.
          - split. easy.
          - inversion Hd. subst. apply used_con with (ctxGLis := (None :: ctxGLis)); try easy.
            constructor; try easy.
            constructor; try easy. left. easy.
      - destruct H as (s1,(g1,(Ha,Hb))). subst.
        specialize(ctx_merge s s0 s1 g1 l p); intros. apply H; try easy.
    destruct H as (H1,(a0,H2)). subst. clear H6 IHl.
    destruct H5; try easy.
    destruct H as (s1,(g1,(Ha,Hb))). inversion Ha. subst. clear Ha.
    destruct Hb as (Gl,(ctxG,(Hc,(Hd,(He,Hf))))).
    exists (gtth_send s s0 [Some (s1, Gl)]). exists ctxG.
    - split. constructor; try easy. constructor; try easy.
      right. exists s1. exists Gl. exists g1. easy.
    - split. intros. apply Hd. inversion H. subst. easy. subst. easy. 
      subst. destruct n; try easy.
      - simpl in H8. inversion H8. subst. easy.
      - simpl in H8. destruct n; try easy.
    - split. easy.
    - apply used_con with (ctxGLis := [Some ctxG]); try easy.
      - constructor.
      - constructor; try easy. right. exists ctxG. exists s1. exists Gl. easy.
Qed.