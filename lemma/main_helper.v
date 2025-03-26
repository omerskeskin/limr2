From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh src.step src.merge src.projection src.session.  
From SST Require Import lemma.inversion lemma.inversion_expr lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step lemma.projection_helper lemma.projection.

Lemma typ_after_unfold : forall M M' G, typ_sess M G -> unfoldP M M' -> typ_sess M' G.
Proof.
  intros. revert H. revert G. induction H0; intros; try easy.
  - inversion H0. subst. 
    inversion H4. subst. clear H4. inversion H7. subst. clear H7. 
    apply t_sess; try easy. constructor; try easy. constructor; try easy.
    destruct H5. exists x. split; try easy. destruct H4. split.
    destruct H5 as (H5, H6).
    - specialize(inv_proc_rec (p_rec P) P x nil nil H5 (erefl (p_rec P))); intros.
      destruct H7 as (T,(Ha,Hb)).
      specialize(subst_proc_varf P (p_rec P) T T nil nil Q Ha H); intros.
      specialize(typable_implies_wfC H5); intros.
      apply tc_sub with (t := T); try easy.
      apply H7. apply tc_mu; try easy.
      destruct H5.
      intros. specialize(H6 n). destruct H6.
      inversion H6.
      - subst. exists 0. constructor.
      - subst. 
        specialize(inj_substP H9 H); intros. subst. exists m. easy.
  - inversion H0. subst. inversion H4. subst. clear H4. 
    destruct H6 as (T,(Ha,(Hb,Hc))).
    constructor; try easy.
    constructor; try easy.
    specialize(inv_proc_rec (p_rec P) P T nil nil Hb (erefl (p_rec P))); intros.
    destruct H4 as (T0,(Hd,He)).
    specialize(subst_proc_varf P (p_rec P) T0 T0 nil nil Q); intros. exists T. split. easy.
    split. specialize(typable_implies_wfC Hb); intros.
    apply tc_sub with (t := T0); try easy. apply H4; try easy.
    apply tc_mu; try easy.
    intros. specialize(Hc n). destruct Hc. inversion H5.
    - subst. exists 0. constructor.
    - subst. specialize(inj_substP H7 H); intros. subst. exists m. easy.
  - apply IHunfoldP2. apply IHunfoldP1. easy.
  - inversion H. subst. inversion H3. subst. clear H3.
    apply t_sess; try easy.
    - intros. specialize(H1 pt H3).
      unfold InT in *.
      simpl in *. apply in_swap; try easy.
      apply nodup_swap; try easy.
    - constructor; try easy.
  - inversion H. subst. inversion H3. subst. inversion H6. subst.
    apply t_sess; try easy.
    intros. specialize(H1 pt H4).
    unfold InT in *. 
    simpl in *.
    specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
    replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *.
    easy.
    simpl in *.
    specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
    replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *.
    easy.

    constructor. easy. constructor; try easy.
  - inversion H. subst. inversion H3. subst. clear H3. inversion H6. subst. clear H6.
    constructor; try easy.
    - intros. specialize(H1 pt H3). unfold InT in *. simpl in *.
      apply in_or_app. specialize(in_or ((flattenT M ++ flattenT M')) (flattenT M'') pt H1); intros.
      destruct H4. left. apply in_swap. easy. right. easy.
    - simpl in *.
      apply nodup_swap. specialize(nodup_swap ((flattenT M ++ flattenT M')) (flattenT M'') H2); intros.
      apply nodup_swap2. easy.
    - constructor. constructor. easy. easy. easy.
  - inversion H. subst. inversion H3. subst. clear H3. inversion H6. subst. clear H6.
    inversion H5. subst. clear H5.
    constructor; try easy.
    - intros. specialize(H1 pt H3).
      unfold InT in *. simpl in *.
      apply in_or_app.
      specialize(in_or (((flattenT M ++ flattenT M') ++ flattenT M'')) (flattenT M''') pt H1); intros.
      destruct H4.
      - left.
        specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
        replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *.
        easy.
      - right. easy.
    - simpl in *.
      specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
      replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *.
      easy.
    - constructor. constructor. easy. constructor. easy. easy. easy.
Qed.

Lemma sub_red_1_helper : forall l x1 xs x4 x5 y,
    onth l x1 = Some (x4, x5) ->
    onth l xs = Some y ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: nil) nil p t))
       xs x1 ->
    typ_proc (Some x4 :: nil) nil y x5.
Proof.
  induction l; intros; try easy.
  - destruct x1. try easy. destruct xs. try easy.
    simpl in *. subst.
    inversion H1. subst. destruct H3. destruct H. easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. inversion H. inversion H0. subst. easy.
  - destruct x1; try easy. destruct xs; try easy.
    simpl in *. apply IHl with (x1 := x1) (xs := xs); try easy.
    inversion H1; try easy.
Qed.

Lemma typ_after_step_3_helper_s: forall M p q G G' l L1 L2,
    wfgC G ->
    wfgC G' ->
    projectionC G p (ltt_send q L1) -> 
    projectionC G q (ltt_recv p L2) -> 
    ForallT
  (fun (u : string) (P : process) =>
   exists T : ltt,
     projectionC G u T /\ typ_proc nil nil P T /\ (forall n : fin, exists m : fin, guardP n m P)) M ->
    gttstepC G G' p q l ->
    ~ InT q M ->
    ~ InT p M ->
    ForallT
  (fun (u : string) (P : process) =>
   exists T : ltt,
     projectionC G' u T /\ typ_proc nil nil P T /\ (forall n : fin, exists m : fin, guardP n m P)) M.
Proof.
  intro M. induction M; intros; try easy.
  - unfold InT in *. simpl in H5. simpl in H6.
    specialize(Classical_Prop.not_or_and (s = q) False H5); intros. destruct H7.
    specialize(Classical_Prop.not_or_and (s = p0) False H6); intros. destruct H9.
    clear H5 H6 H8 H10.
    constructor.
    inversion H3. subst. destruct H6 as [T' H6]. destruct H6.
    specialize(projection_step_label G G' p0 q l L1 L2 H H1 H2 H4); intros.
    destruct H8. destruct H8. destruct H8. destruct H8. destruct H8.
    Check projection_step_label.
    specialize(typ_after_step_3_helper G G' p0 q s l L1 L2 x x1 x0 x2 T'); intros.
    assert(exists T'0 : ltt, projectionC G' s T'0 /\ T' = T'0).
    apply H11; try easy.
    clear H11. destruct H12. exists x3. split; try easy. destruct H11. rename x3 into Tl. subst. easy. 
  - inversion H3. subst.
    specialize(noin_cat_and q (flattenT M1) (flattenT M2) H5); intros.
    specialize(noin_cat_and p (flattenT M1) (flattenT M2) H6); intros.
    specialize(Classical_Prop.not_or_and (In q (flattenT M1)) (In q (flattenT M2)) H7); intros.
    specialize(Classical_Prop.not_or_and (In p (flattenT M1)) (In p (flattenT M2)) H8); intros.
    destruct H11. destruct H12.
    unfold InT in *.
    specialize(IHM1 p q G G' l L1 L2 H H0 H1 H2).
    specialize(IHM2 p q G G' l L1 L2 H H0 H1 H2).
    constructor; try easy.
    apply IHM1; easy.
    apply IHM2; easy.
Qed.

Lemma sub_red_helper : forall l xs x1 y,
    onth l xs = Some y ->
    Forall2
        (fun (u : option process) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (p : process) (s : sort) (t : ltt),
            u = Some p /\
            v = Some (s, t) /\ typ_proc (Some s :: nil) nil p t)) xs x1 ->
    exists s t, onth l x1 = Some(s,t) /\ typ_proc (Some s :: nil) nil y t.
Proof.
  induction l; intros.
  - destruct xs; try easy.
    destruct x1; try easy.
    simpl in *.
    inversion H0. subst. destruct H4; try easy. destruct H. destruct H. destruct H. destruct H. destruct H1. 
    inversion H. subst.
    exists x0. exists x2. split; try easy.
  - destruct xs; try easy.
    destruct x1; try easy. 
    inversion H0. subst. apply IHl with (xs := xs); try easy.
Qed.

Lemma sub_red_helper_1 : forall [l LQ SL' TL' x x1 x0 q],
        onth l LQ = Some (SL', TL') -> 
        onth l x = Some (x0, x1) ->
        subtypeC (ltt_recv q x) (ltt_recv q LQ) ->
        subtypeC x1 TL' /\ subsort SL' x0.
Proof.
  intros.
  specialize(subtype_recv_inv q x LQ H1); intros.
  clear H1. revert H2 H0 H. revert q x0 x1 x TL' SL' LQ.
  induction l; intros.
  - destruct x; try easy. destruct LQ; try easy. simpl in *. subst.
    inversion H2. subst. destruct H3; try easy. destruct H. destruct H. destruct H.
    destruct H. destruct H. destruct H0. destruct H1. inversion H. inversion H0. subst. easy.
  - destruct LQ; try easy. destruct x; try easy. 
    inversion H2. subst.
    specialize(IHl q x0 x1 x TL' SL' LQ). apply IHl; try easy.
Qed.

Lemma sub_red_helper_2 : forall [l LP SL TL LT S p],
       subtypeC (ltt_send p (extendLis l (Some (S, LT)))) (ltt_send p LP) ->
       onth l LP = Some (SL, TL) -> 
       subtypeC LT TL /\ subsort S SL.
Proof.
  intros.
  specialize(subtype_send_inv p (extendLis l (Some (S, LT))) LP H); intros.
  clear H. revert H0 H1. revert LP SL TL LT S p.
  induction l; intros.
  - destruct LP; try easy. inversion H1. subst.
    destruct H4; try easy. destruct H. destruct H. destruct H. destruct H. destruct H.
    destruct H2. destruct H3. inversion H. simpl in H0. subst. inversion H2. subst.
    easy.
  - destruct LP; try easy. inversion H1. subst.
    specialize(IHl LP SL TL LT S p). apply IHl; try easy.
Qed. 

Lemma sub_red_helper_3 : forall M G pt,
        In pt (flattenT M) -> 
        ForallT
       (fun (u : string) (P : process) =>
        exists T : ltt,
          projectionC G u T /\ typ_proc nil nil P T /\ (forall n : fin, exists m : fin, guardP n m P))
       M -> 
       exists T : ltt, projectionC G pt T.
Proof.
  induction M; intros; try easy.
  - simpl in H. destruct H; try easy. subst.
    inversion H0. subst. destruct H1 as (T,(Ha,Hb)). exists T. easy.
  - inversion H0. subst.
    specialize(in_or (flattenT M1) (flattenT M2) pt H); intros.
    destruct H1.
    - specialize(IHM1 G pt H1 H3). apply IHM1; try easy.
    - specialize(IHM2 G pt H1 H4). apply IHM2; try easy.
Qed.

Lemma pc_par5 : forall M M' M'', unfoldP (M ||| (M' ||| M'')) ((M ||| M') ||| M'').
Proof.
  intros.
  apply pc_trans with (M' := (M' ||| M'') ||| M). constructor.
  apply pc_trans with (M' := (M' ||| (M'' ||| M))). constructor.
  apply pc_trans with (M' := (M'' ||| M) ||| M'). constructor.
  apply pc_trans with (M' := M'' ||| (M ||| M')). constructor. constructor. 
Qed.

Lemma unf_cont_l : forall M1 M1' M2,
  unfoldP M1 M1' -> 
  unfoldP (M1 ||| M2) (M1' ||| M2).
Proof.
  intros. revert M2.
  induction H; intros.
  - {
      apply pc_trans with (M' := (p <-- p_rec P) ||| (M ||| M2)). apply pc_par2.
      apply pc_trans with (M' := (p <-- Q) ||| (M ||| M2)). constructor. easy.
      apply pc_par5. 
      
    }
  - constructor. easy.
  - apply pc_refl.
  - apply pc_trans with (M' := (M' ||| M2)). apply IHunfoldP1. apply IHunfoldP2.
  - constructor.
  - constructor.
  - {
      apply pc_trans with (M' := (M ||| M') ||| (M'' ||| M2)). constructor.
      apply pc_trans with (M' := (M' ||| M) ||| (M'' ||| M2)). constructor.
      apply pc_par5.
    }
  - {
      apply pc_trans with (M' := (((M ||| M') ||| M'') ||| (M''' ||| M2))). constructor.
      apply pc_trans with (M' := ((M ||| (M' ||| M'')) ||| (M''' ||| M2))). constructor.
      apply pc_par5.
    }
Qed.

Lemma unf_cont_r : forall M1 M2 M2', 
    unfoldP M2 M2' -> 
    unfoldP (M1 ||| M2) (M1 ||| M2').
Proof.
  intros.
  apply pc_trans with (M' := M2 ||| M1). constructor.
  apply pc_trans with (M' := M2' ||| M1). apply unf_cont_l. easy.
  constructor.
Qed.

Lemma unf_cont : forall M1 M1' M2 M2',
    unfoldP M1 M1' -> unfoldP M2 M2' -> 
    unfoldP (M1 ||| M2) (M1' ||| M2').
Proof.
  intros.
  apply pc_trans with (M' := (M1 ||| M2')). apply unf_cont_r. easy.
  apply unf_cont_l. easy.
Qed.

Lemma move_forward_h : forall M,
    forall p : string,
    InT p M ->
    (exists (P : process) (M' : session), unfoldP M ((p <-- P) ||| M')) \/
    (exists P : process, unfoldP M (p <-- P)).
Proof.
  induction M; intros.
  - rename H into H2. unfold InT in H2. simpl in H2. destruct H2; try easy.
    subst. right. exists p. constructor.
  - rename H into H2. unfold InT in *. simpl in *.
    specialize(in_or (flattenT M1) (flattenT M2) p H2); intros.
    destruct H.
    - specialize(IHM1 p H). 
      destruct IHM1.
      - destruct H0 as (P,(M',Ha)).
        left. exists P. exists (M' ||| M2).
        apply pc_trans with (M' := ((p <-- P) ||| M') ||| M2). apply unf_cont_l. easy. 
        constructor.
      - destruct H0 as (P,Ha).
        left. exists P. exists M2. apply unf_cont_l. easy.
    - specialize(IHM2 p H). clear IHM1 H2.
      destruct IHM2.
      - destruct H0 as (P,(M',Ha)).
        left. exists P. exists (M1 ||| M').
        apply pc_trans with (M' := M1 ||| ((p <-- P) ||| M')). apply unf_cont_r. easy.
        apply pc_trans with (M' := (M1 ||| (p <-- P)) ||| M'). apply pc_par5.
        apply pc_trans with (M' := ((p <-- P) ||| M1) ||| M'). constructor. constructor.
      - destruct H0 as (P,Ha).
        left. exists P. exists M1.
        apply pc_trans with (M' := M1 ||| (p <-- P)). apply unf_cont_r. easy.
        constructor.
Qed.

Lemma move_forward : forall p M G, 
    typ_sess M G -> 
    isgPartsC p G -> 
    (exists P M', unfoldP M (p <-- P ||| M')) \/ (exists P, unfoldP M (p <-- P)).
Proof.
  intros. inversion H. subst. clear H1 H3 H4 H.
  specialize(H2 p H0). clear H0.
  revert H2. revert p. clear G.
  apply move_forward_h.
Qed.

Lemma part_after_unf : forall M M' p,
    unfoldP M M' -> 
    InT p M ->
    InT p M'.
Proof.
  intros. revert H0. revert p.
  induction H; intros; try easy.
  - apply IHunfoldP2. apply IHunfoldP1. easy.
  - unfold InT in *.
    simpl in *. apply in_swap. easy.
  - unfold InT in *. simpl in *.
    specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
    replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *. easy.
  - unfold InT in *. simpl in *.
    apply in_or_app. specialize(in_or ((flattenT M ++ flattenT M')) (flattenT M'') p H0); intros.
    destruct H.
    - left. apply in_swap. easy. right. easy.
  - unfold InT in *. simpl in *.
    specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
    replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *. easy.
Qed.

Lemma canonical_glob_nt : forall M p q l,
    typ_sess M (gtt_send p q l) -> 
    (exists M' P Q, unfoldP M ((p <-- P) ||| (q <-- Q) ||| M')) \/ (exists P Q, unfoldP M ((p <-- P) ||| (q <-- Q))).
Proof.
  intros.
  inversion H. subst.
  assert(InT p M). apply H1. apply triv_pt_p. easy.
  assert(InT q M). apply H1. apply triv_pt_q. easy.
  specialize(move_forward_h M p H4); intros.
  specialize(wfgC_triv p q l H0); intros. destruct H7.
  destruct H6.
  - destruct H6 as (P,(M',Ha)). specialize(part_after_unf M ((p <-- P) ||| M') q Ha H5); intros.
    unfold InT in *.
    inversion H6. subst. easy. simpl in H9.
    specialize(move_forward_h M' q); intros.
    unfold InT in H10.
    specialize(H10 H9).
    destruct H10.
    - destruct H10 as (P1,(M'',Hb)). left.
      exists M''. exists P. exists P1.
      apply pc_trans with (M' := ((p <-- P) ||| M')); try easy.
      apply pc_trans with (M' := ((p <-- P) ||| ((q <-- P1) ||| M''))). apply unf_cont_r. easy.
      apply pc_par5.
    - destruct H10 as (P1,Hb).
      right. exists P. exists P1. 
      apply pc_trans with (M' := ((p <-- P) ||| M')); try easy.
      apply unf_cont_r. easy.
  - destruct H6 as (P,H6).
    specialize(part_after_unf M (p <-- P) q H6 H5); intros.
    inversion H9; try easy.
Qed.

Lemma canonical_glob_n : forall M,
    typ_sess M gtt_end -> 
    exists M', unfoldP M M' /\ ForallT (fun _ P => P = p_inact \/ (exists e p1 p2, P = p_ite e p1 p2 /\ typ_proc nil nil (p_ite e p1 p2) ltt_end)) M'.
Proof.
  intros.
  inversion H. subst.
  clear H H1 H2.
  revert H3.
  induction M; intros.
  - inversion H3. subst. clear H3.
    destruct H1 as (T,(Ha,(Hb,Hc))).
    specialize(Hc 1). destruct Hc as (m, Hc).
    revert Hc Hb Ha H0. revert s p T.
    induction m; intros. pinversion Ha. subst.
    - inversion Hc. subst. exists (s <-- p_inact). split.
      apply pc_refl.
      constructor. left. easy.
      subst.
      specialize(inv_proc_send pt l e g (p_send pt l e g) nil nil ltt_end Hb (erefl (p_send pt l e g))); intros.
      destruct H1 as (S1,(T1,(Hd,(He,Hf)))). pinversion Hf.
      apply sub_mon.
      subst.
      specialize(inv_proc_recv p0 lis (p_recv p0 lis) nil nil ltt_end Hb (erefl (p_recv p0 lis))); intros.
      destruct H1 as (STT,(Hd,(He,(Hf,Hg)))). pinversion He. apply sub_mon.
    apply proj_mon.
    pinversion Ha. subst.
    inversion Hc; try easy.
    - subst. exists (s <-- p_inact). split. apply pc_refl. constructor. left. easy.
    - subst.
      specialize(inv_proc_send pt l e g (p_send pt l e g) nil nil ltt_end Hb (erefl (p_send pt l e g))); intros. destruct H1 as (S1,(T1,(Hd,(He,Hf)))). pinversion Hf. apply sub_mon.
    - subst.
      specialize(inv_proc_recv p0 lis (p_recv p0 lis) nil nil ltt_end Hb (erefl (p_recv p0 lis))); intros.
      destruct H1 as (STT,(Hd,(He,(Hf,Hg)))). pinversion He. apply sub_mon.
    - subst.
      specialize(inv_proc_ite (p_ite e P Q) e P Q ltt_end nil nil Hb (erefl (p_ite e P Q))); intros.
      destruct H1 as (T1,(T2,(Hd,(He,(Hf,(Hg,Hh)))))).
      pinversion Hf. subst. pinversion Hg. subst.
      exists (s <-- p_ite e P Q). split. apply pc_refl.
      constructor. right. exists e. exists P. exists Q. easy.
      apply sub_mon. apply sub_mon.
    - subst.
      specialize(IHm s Q ltt_end).
      assert(exists M' : session,
        unfoldP (s <-- Q) M' /\
        ForallT
          (fun (_ : string) (P : process) =>
           P = p_inact \/
           (exists (e : expr) (p1 p2 : process),
              P = p_ite e p1 p2 /\ typ_proc nil nil (p_ite e p1 p2) ltt_end)) M').
      {
        apply IHm; try easy.
        - specialize(inv_proc_rec (p_rec g) g ltt_end nil nil Hb (erefl (p_rec g))); intros.
          destruct H1 as (T1,(Hd,He)). pinversion He. subst.
          specialize(subst_proc_varf g (p_rec g) ltt_end ltt_end nil nil Q); intros.
          apply H1; try easy. apply sub_mon.
        - pfold. easy.
      }
      destruct H1 as (M1,(Hd,He)). exists M1. split; try easy.
      apply pc_trans with (M' := (s <-- Q)); try easy.
      constructor. easy.
      apply proj_mon.
  - inversion H3. subst. clear H3.
    specialize(IHM1 H2). specialize(IHM2 H4). clear H2 H4.
    destruct IHM1 as (M1',(Ha,Hb)).
    destruct IHM2 as (M2',(Hc,Hd)). exists (M1' ||| M2'). 
    split. apply unf_cont; try easy.
    constructor; try easy.
Qed.

Lemma typ_proc_after_betaPr : forall P Q Gs Gt T, 
    multi betaPr P Q ->
    typ_proc Gs Gt P T -> typ_proc Gs Gt Q T.
Proof.
  intros. revert H0. revert T Gt Gs.
  induction H; intros.
  - easy.
  - apply IHmulti. clear IHmulti H0. clear z.
    inversion H. subst.
    specialize(inv_proc_rec (p_rec P) P T Gs Gt H1 (erefl (p_rec P))); intros.
    destruct H2 as (T0,(Ha,Hb)).
    specialize(subst_proc_varf P (p_rec P) T0 T0 Gs Gt y); intros.
    specialize(typable_implies_wfC H1); intros.
    apply tc_sub with (t := T0); try easy.
    apply H2; try easy. apply tc_mu. easy.
Qed.

Lemma betaPr_unfold_h : forall P Q1 Q Q2 p q,
          multi betaPr P Q1 -> 
          multi betaPr Q Q2 ->
          unfoldP (((p <-- P) ||| (q <-- Q))) (((p <-- Q1) ||| (q <-- Q2))).
Proof.
  intros.
  apply pc_trans with (M' := (p <-- Q1) ||| (q <-- Q)).
  - apply unf_cont_l. clear H0. clear Q Q2. 
    induction H; intros. constructor. apply pc_trans with (M' := (p <-- y)); try easy.
    clear IHmulti H0. inversion H. subst. constructor. easy.
  - apply unf_cont_r. clear H. clear P Q1.
    induction H0; intros. constructor. apply pc_trans with (M' := (q <-- y)); try easy.
    clear IHmulti H0. inversion H. subst. constructor. easy.
Qed.

Lemma betaPr_unfold : forall P Q1 Q Q2 p q M',
          multi betaPr P Q1 -> 
          multi betaPr Q Q2 ->
          unfoldP (((p <-- P) ||| (q <-- Q)) ||| M') (((p <-- Q1) ||| (q <-- Q2)) ||| M').
Proof.
  intros. apply unf_cont_l; try easy. apply betaPr_unfold_h; try easy.
Qed.
