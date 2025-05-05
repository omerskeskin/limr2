(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable.
From SST Require Import src.step lemma.step src.assoc.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
From Coq Require Import IndefiniteDescription.

Import ListNotations.

Check balanced_to_tree.

Lemma extendLis_forall {A:Type}: forall (P: option A -> Prop) n x, 
P (Some x) /\ P (None) -> 
Forall P
(extendLis n (Some x)).
Proof.
    induction n;crush.
Qed.

Lemma wfg_proof_princip_ctx: forall (Q:gtt->Prop) p,
(forall ctx gs g, typ_p_gtth gs ctx p g -> usedCtx gs ctx -> Q g) -> 
(forall g, wfgC g -> isgPartsC p g -> Q g).
Proof.
intros.
apply balanced_to_tree with (p:=p) in H0 .
destr_hyps.
specialize H with (ctx:=x) (gs:=x0) (g:=g).
unfold typ_p_gtth in *. all:crush.
Qed.



Lemma typ_gtth_hole_inv: forall p q n gs xs, 
    typ_gtth gs (gtth_hol n) (gtt_send p q xs) -> usedCtx gs (gtth_hol n) ->
    exists gcs, gs=extendLis n (Some(gtt_send p q gcs)).
Proof.
    intros.
    inversion H0.
    destruct G;subst.
    {
        inversion H;subst.
        rewrite extendExtract in H3. crush.
    }
    {
        exists l.
        inversion H;subst. rewrite extendExtract in H3. crush.
    }
Qed.
Lemma extendLis_injective {A:Type}:forall n (a b:A), extendLis n (Some a) =extendLis n (Some b) -> a=b.
Proof. intros; induction n;crush. Qed.
Lemma no_step_from_end: forall G' p q n, gttstepC gtt_end G' p q n -> False.
Proof. intros. pinversion H. apply step_mon. Qed.

Print usedCtx.

Inductive in_hole_ctx: nat -> gtth -> Prop :=
    | in_hole_hol: forall n, in_hole_ctx n (gtth_hol n) 
    | in_hole_send: forall n ct s gcs k p q , in_hole_ctx n ct -> onth k gcs=Some (s,ct) ->
        in_hole_ctx n (gtth_send p q gcs).

Lemma in_hole_ctx_hol :forall n x, in_hole_ctx n (gtth_hol x ) <-> x=n.
Proof. split;intros;[inversion H | ];crush. constructor. Qed.

Lemma in_hole_filled: forall gs ctx g n , typ_gtth gs ctx g -> in_hole_ctx n ctx -> 
    exists gch, onth n gs = Some (gch).
Proof.
    intros.
    generalize dependent n.
    generalize dependent g.
    generalize dependent ctx.
    induction ctx using gtth_ind_ref.
    {
        intros.
        eapply in_hole_ctx_hol in H0;inversion H;exists gc;crush.
    }
    {
        rename H into Ih.
        intros.
        inversion H;subst.
        inversion H0;subst.
        eapply slist_implies_some in H6. destr_hyps.
        eapply Forall_prop with (l:=k) (p:=(s,ct)) in Ih;try easy.
        destruct Ih;try easy. destr_hyps.
        inversion H2;subst. 
        eapply Forall2_prop_r with (l:=k) (p:=(x1,x2)) in H7; try easy.
        destr_hyps. destruct H5;try easy. destr_hyps. crush.
        eapply H3 with (g:=x5); try easy.
    }
Qed.
Check typ_p_gtth.

Lemma strong_grafting_1: forall G G' p q ell gs ctx,
gttstepC G G' p q ell -> typ_p_gtth gs ctx p G->
forall n, in_hole_ctx n ctx -> 
exists q lsg, onth n gs = 
 Some (gtt_send p q lsg).
Proof.
    intros.
    generalize dependent G'.
    generalize dependent G.
    generalize dependent n.
    generalize dependent ctx.
    induction ctx using gtth_ind_ref.
    {
     intros. pose proof H1 as Hinhole. eapply in_hole_ctx_hol in H1;subst.
     pinversion H;subst; try apply step_mon.
     {
        eapply in_hole_filled with (gs:=gs) (g:=(gtt_send p q xs)) in Hinhole.
      inversion H0;subst. inversion H3;subst.
      
      destr_hyps. exists q ,xs. easy. inversion H0;easy.
     }
     {
        inversion H0. inversion H9;subst. destr_hyps.
        eapply Forall_prop with (l:=n0) (p:=(gtt_send r s xs)) in H11; try easy.
        destruct H11;try easy.
        destr_hyps. destruct H11;[inversion H11 | destruct H11;inversion H11];crush.
     }   
    }
    {
     intros.
     pinversion H2;subst;try apply step_mon.
     {
        inversion H0.
        eapply typ_gtth_inv in H5. destr_hyps;inversion H5;subst. 
        exfalso. apply H6. constructor.  
     }
     {
        rename H into Ih.
        inversion H0. eapply typ_gtth_inv in H. destr_hyps. inversion H;subst.
        inversion H1;subst. 
        eapply in_hole_filled with (gs:=gs) (g:=gtt_send p0 q0 x) in H1. destr_hyps.
        eapply Forall_prop with (l:=k) (p:=(s,ct)) in Ih; try easy.
        destruct Ih; try easy. destr_hyps.
        inversion H13;subst.
        rename x1 into s, x2 into ct.
        
        eapply typ_p_gtth_cont2 with (n:=k) (s:=s) (gch:=ct) in H0; try easy.
        destr_hyps.

        eapply Forall2_prop_r with (l:=k) (p:=(s,x1)) in H10; try easy.
        destr_hyps.
        destruct H17;try easy. destr_hyps. inversion H17;subst.
        destruct H20;crush.
        rewrite <- H1.
         eapply H14 with (G:=x4) (G':=x5); try easy.
         inversion H0; try easy.
     }   
    }
Qed.

Lemma wfg_proof_princip3: forall (Q:gtt->Prop) p,
    (forall ctx gs g, wfgC g -> typ_p_gtth gs ctx p g -> Q g) -> 
    (forall g, wfgC g -> isgPartsC p g -> Q g).
Proof.
    intros.
    pose proof H0 as Hwfg.
    apply balanced_to_tree with (p:=p) in H0 .
    destr_hyps.
    specialize H with (ctx:=x) (gs:=x0) (g:=g).
    unfold typ_p_gtth in *. all:crush.
Qed.

Lemma typ_p_gtth_step_inv: forall gs n p  q ell g' g, typ_p_gtth gs (gtth_hol n) p g -> gttstepC g g' p q ell ->
exists xs, onth n gs = Some (gtt_send p q xs).
Proof.
    intros.
    pinversion H0;subst;try apply step_mon.
    {
        inversion H. inversion H3;subst. exists xs. easy.
    }
    {
        inversion H.
        destr_hyps.
        inversion H9. eapply Forall_prop with (l:=n) (p:=(gtt_send r s xs)) in H11; try easy;subst.
        destruct H11;try easy.
        destr_hyps.
        destruct H11;[ | destruct H11];inversion H11;crush.
    }
Qed.

Lemma typ_p_gtth_hole_inv2: forall gs n p g g', typ_p_gtth gs (gtth_hol n) p g -> onth n gs = Some g' -> g=g'.
Proof. intros; inversion H;inversion H1;crush. Qed.



Lemma subproj_simple_send_inv: forall t p q gcs ,
wfgC (gtt_send p q gcs) ->
issubProj t (gtt_send p q gcs) p -> exists xs, t= ltt_send q xs.
Proof.
    intros.
    unfold issubProj in H0. destr_hyps.
    pinversion H0;try apply proj_mon;crush. 
    exfalso. apply H2. apply decidable_helper.triv_pt_p. easy.
    pinversion H1;try apply sub_mon;subst. exists xs. easy.
Qed.

Lemma subproj_simple_recv_inv: forall t p q gcs ,
wfgC (gtt_send p q gcs) ->
issubProj t (gtt_send p q gcs) q -> exists xs, t= ltt_recv p xs.
Proof.
    intros.
    unfold issubProj in H0. destr_hyps.
    pinversion H0;try apply proj_mon;crush.
    
    exfalso. apply H2. apply decidable_helper.triv_pt_q. easy.
    pinversion H1;try apply sub_mon;subst. exists xs. easy.
Qed.

Ltac tac_isParts := match goal with 
    | [ H: isgPartsC ?p (gtt_send ?p ?q ?gcs) -> False |- _ ] => 
        exfalso;apply H;apply decidable_helper.triv_pt_p 
    | [ H: isgPartsC ?q (gtt_send ?p ?q ?gcs) -> False |- _ ] => 
        exfalso;apply H;apply decidable_helper.triv_pt_q
end.

Check Forall2_prop_r.

Lemma Forall2R_prop {A:Type} {B:Type}: forall l (xs :list (option A)) (ys :list (option B)) P p, Forall2R P xs ys -> onth l xs= Some p ->  
    exists p', onth l ys= p' /\ P (Some p) p'.
Proof.
    intros.
    generalize dependent l.
    induction H;intros.
    rewrite onth_nil in H0;easy.
    destruct l;simpl in H1;[ exists y | eapply IHForall2R]; crush.    
Qed.


Definition tctx_wf (g:tctx):= forall p q xs, (M.find p g =Some (ltt_send q xs) -> SList xs)
/\ (M.find p g =Some (ltt_recv q xs) -> SList xs).

Lemma subproj_onth1: forall p q xp gcs s T_k k, 
    wfgC (gtt_send p q gcs) ->    
    issubProj (ltt_send q xp) (gtt_send p q gcs) p -> 
    onth k xp =Some (s,T_k)
    -> exists s' gct, onth k gcs =Some (s', gct).
Proof.
    intros.
    unfold issubProj in H0.
    destr_hyps.
    pinversion H0;subst;try (tac_isParts; easy);crush;try apply proj_mon.
    apply subtype_send_inv in H2.
    eapply Forall2R_prop with (l:=k) (p:=(s,T_k)) in H2;try easy.
    destr_hyps.
    destruct H3;try easy. destr_hyps.
    subst.
    eapply Forall2_prop_l with (l:=k) (p:=(x1,x3)) in H10; try easy.
    destr_hyps. destruct H10; try easy. destr_hyps. subst;exists x4, x5;easy.
Qed.
#[global] Instance RWMTCTXR: Proper ((@M.Equal ltt) ==> (eq) ==> (@M.Equal ltt) ==> (iff)) tctxR.
Proof. unfold "==>". constructor; intros; subst. 
apply Rstruct with (g1:=y) (g2:=y1) (g1':=x) (g2':=x1);crush. 
apply Rstruct with (g1:=x) (g2:=x1) (g1':=y) (g2':=y1);crush.
Qed.
Lemma context_red_simple_comm: forall k xq xp p q gamma' s s'' Tp_k Tq_k, 
    p <> q ->
    onth k xq = Some (s'', Tq_k) ->
    onth k xp = Some (s, Tp_k) ->
    M.find p gamma'= None ->
    M.find q gamma'=None ->
    subsort s s'' ->
    tctxR (M.add p (ltt_send q xp) (M.add q (ltt_recv p xq) gamma'))
    (lcomm p q k) (M.add p Tp_k (M.add q Tq_k gamma')).
Proof.
    intros.
    assert(Hd1: forall Ttp Ttq,
    MF.Disjoint (M.add p Ttp (M.add q Ttq M.empty) )
    gamma').
    {
     unfold MF.Disjoint in *. unfold not. intros.
     destruct(Nat.eq_dec p k0);destruct (Nat.eq_dec q k0);crush.
     rewrite  <- MF.not_in_find in H2; try easy.
     rewrite  <- MF.not_in_find in H3; try easy.
     rewrite MF.in_find in H6. apply opt_lem1 in H6. destr_hyps.
     Check M.add_spec2.
     rewrite M.add_spec2 in H5;try easy.
     rewrite M.add_spec2 in H5;try easy.
    }
    assert(H_eq: forall Ttp Ttq Hdd, M.Equal ((M.add p Ttp (M.add q Ttq
    gamma'))) (disj_merge (M.add p Ttp (M.add q Ttq
    M.empty)) gamma' Hdd)).
    {
     unfold M.Equal. intros.
     unfold disj_merge. rewrite MF.merge_spec1mn;crush.
     destruct (Nat.eq_dec p y); destruct (Nat.eq_dec q y);crush.
     + rewrite M.add_spec1. rewrite M.add_spec1. easy.
     + rewrite M.add_spec2. rewrite M.add_spec1. rewrite M.add_spec2.
     rewrite M.add_spec1. 1-3: try easy.
     + repeat rewrite M.add_spec2;try easy. rewrite M.empty_spec. 
     destruct (M.find y gamma') eqn:Hyg;crush.   
    }
    Ltac Hdeq t1 t2 H_eq Hd1:= setoid_rewrite (H_eq t1 t2 (Hd1 t1 t2)).
    Hdeq (ltt_send q xp) (ltt_recv p xq) H_eq Hd1.
    Hdeq Tp_k Tq_k H_eq Hd1.
    apply tctxR_weakening.
    assert(Heq1: forall Ttp Ttq Hdd, M.Equal (M.add p Ttp
    (M.add q Ttq M.empty)) (disj_merge (M.add p Ttp M.empty) (M.add q Ttq M.empty) Hdd)).
    {
     intros.
     unfold M.Equal; intros. unfold disj_merge. rewrite MF.merge_spec1mn;
     destruct (Nat.eq_dec p y);destruct (Nat.eq_dec q y);crush.
     + rewrite M.add_spec1. rewrite M.add_spec1. rewrite M.add_spec2. rewrite M.empty_spec.
     crush. easy.     
     + rewrite M.add_spec2. rewrite M.add_spec1. rewrite M.add_spec2. rewrite M.empty_spec.
     crush. easy. easy.
     + repeat rewrite M.add_spec2; try repeat rewrite M.empty_spec;try easy.     
    }
    assert(Hd2: forall (Ttp Ttq:ltt), MF.Disjoint (M.add p Ttp M.empty) (M.add q Ttq M.empty)).
    {
     unfold MF.Disjoint. unfold not. intros. destruct (Nat.eq_dec p k0);
     destruct (Nat.eq_dec q k0);try repeat rewrite MF.in_find in *;
     crush.
     + rewrite M.add_spec2 in H7;try easy.
     + rewrite M.add_spec2 in H6;try easy.
     + rewrite M.add_spec2 in H6;try easy.    
    }
    intros.
    Hdeq (ltt_send q xp) (ltt_recv p xq) Heq1 Hd2.
    Hdeq Tp_k Tq_k Heq1 Hd2.
    eapply Rcomm with (s:=s) (s':=s''); try easy.
    apply Rsend;try easy.
    apply Rrecv;try easy.
Qed.

Lemma subproj_after_cont_send: forall x p q r gcs s gk ls k,
    SList ls ->
    wfgC (gtt_send p q gcs) ->
    issubProj (ltt_send x ls) (gtt_send p q gcs) r -> 
    r <> p -> r<> q ->
    isgPartsC r (gtt_send p q gcs) ->
    onth k gcs=Some (s,gk) -> issubProj (ltt_send x ls) gk r.
Proof.
    intros.
    apply subproj_inv_send in H1;try easy.
    destruct H1;crush.
    inversion H6;subst. rename x0 into p, x1 into q, x2 into gcs.
    unfold subproj_cont_cond in H9.
    eapply Forall_prop with (l:=k) (p:=(s,gk)) in H9; try easy.
    destruct H9;try easy. destr_hyps. inversion H8;subst. easy.
Qed.
    
Lemma subproj_after_cont_recv: forall x p q r gcs s gk ls k,
    SList ls ->
    wfgC (gtt_send p q gcs) ->
    issubProj (ltt_recv x ls) (gtt_send p q gcs) r -> 
    r <> p -> r<> q ->
    isgPartsC r (gtt_send p q gcs) ->
    onth k gcs=Some (s,gk) -> issubProj (ltt_recv x ls) gk r.
Proof.
    intros.
    apply subproj_inv_recv in H1;try easy.
    destruct H1;crush.
    inversion H6;subst. rename x0 into p, x1 into q, x2 into gcs.
    unfold subproj_cont_cond in H9.
    eapply Forall_prop with (l:=k) (p:=(s,gk)) in H9; try easy.
    destruct H9;try easy. destr_hyps. inversion H8;subst. easy.
Qed.

Lemma part_parent: forall p q gcs G_k k r s, wfgC (gtt_send p q gcs) ->
    onth k gcs=Some (s,G_k) -> isgPartsC r G_k -> isgPartsC r (gtt_send p q gcs).
Proof.
    intros.
    destruct(Nat.eq_dec p r);destruct (Nat.eq_dec q r);subst;
    [
    apply same_rec_send_not_wfg in H| 
    apply decidable_helper.triv_pt_p|
    apply decidable_helper.triv_pt_q|
    eapply decidable_helper.part_cont_b with (n:=k) (s:=s) (g:=G_k)];easy.
Qed.

Lemma assoc_implies_projectable: forall gamma g, wfgC g -> assoc gamma g -> projectableA g.
Proof.
    unfold projectableA. intros.
    destruct(decidable_isgPartsC g pt); try easy;
    unfold assoc in H0;
    specialize (H0 pt); destr_hyps.
    { 
        apply H0 in H1. destr_hyps. 
        unfold issubProj in *. destr_hyps. exists x0. easy.
    }
    {
        exists ltt_end.
        pfold. constructor. easy.      
    }
Qed.

Search SList.
Locate wfgC_triv.
Lemma wfg_implies_slis: forall p q gcs, wfgC (gtt_send p q gcs) -> SList gcs.
Proof.
    intros.
    apply wfgC_triv in H. easy.
Qed.

Lemma not_part_proj: forall p G, ~ isgPartsC p G -> projectionC G p ltt_end.
Proof.
    intros.
    pfold. constructor. easy.
Qed.

Lemma assoc_cont_not_part_send : forall p q gcs k g_k s xs, wfgC (gtt_send p q gcs) -> SList xs ->
issubProj  (ltt_send q xs) (gtt_send p q gcs) p  ->
onth k gcs= Some (s,g_k) -> ( ~ isgPartsC p g_k) -> onth k xs=None \/ exists s', onth k xs =Some (s',ltt_end).
Proof.
    intros.
    apply subproj_inv_send in H1;try easy.
    destruct H1;crush.
    destruct (onth k xs) eqn:Hkxs. right. unfold send_cond in *.
    eapply Forall2R_prop with (l:=k) (p:=p0) in H5;try easy. destr_hyps.
    destruct H4;try easy; destr_hyps.
    rewrite H2 in H1. subst.
    inversion H5;subst. apply eq_sym in H4;inversion H4;subst.
    exists x1. 
    destruct x2;[easy | |];
    (
        unfold issubProj in H7; destr_hyps;
        apply not_part_proj in H3;
        eapply continuation_wfgC with (p:=p) (q:=q) in H2; try easy;
        eapply proj_inj with (t:=ltt_end) in H1; subst;
        pinversion H7;try apply sub_mon;crush
    ).
    left. easy.
Qed.

Lemma assoc_cont_not_part_recv : forall p q gcs k g_k s xs, wfgC (gtt_send p q gcs) -> SList xs ->
issubProj  (ltt_recv p xs) (gtt_send p q gcs) q  ->
onth k gcs= Some (s,g_k) -> ( ~ isgPartsC q g_k) ->  exists s', onth k xs =Some (s',ltt_end).
Proof.
    intros.
    apply subproj_inv_recv in H1;try easy.
    destruct H1;crush.
    destruct (onth k xs) eqn:Hkxs.  unfold recv_cond in *.
    eapply Forall2R_prop with (l:=k) (p:=(s,g_k)) in H5; try easy.
    destr_hyps. destruct H4;try easy. destr_hyps. subst. rewrite H5 in Hkxs.
    inversion Hkxs;subst. exists x1.
    destruct x2;[easy | |];
     (   unfold issubProj in H7; destr_hyps;
     apply not_part_proj in H3;
     inversion H4;subst;
     eapply continuation_wfgC with (p:=p) (q:=q) in H2; try easy;
        eapply proj_inj with (t:=ltt_end) in H1; subst;
        pinversion H7;try apply sub_mon;crush).

    unfold recv_cond in H5.
    eapply Forall2R_prop with (l:=k) (p:=(s,g_k)) in H5; try easy.
    destr_hyps. crush.
Qed.

Search isgPartsC.

Lemma projection_implies_slist_send : 
    forall q g r xs,    wfgC g -> projectionC g r (ltt_send q xs) ->
    SList xs.
Proof.
    admit. 
Admitted.


Lemma projection_implies_slist_recv : 
    forall q g r xs,    wfgC g -> projectionC g r (ltt_recv q xs) ->
    SList xs.
Proof.
    admit. 
Admitted.

Definition create_gamma_k s t Gks Gkt (gamma:tctx) := 
M.add s Gks (M.add t Gkt (M.remove s (M.remove t gamma))).

Lemma gamma_k_props: forall k s' gamma s t g_k gcs Gks Gkt,
    tctx_wf gamma ->
    wfgC (gtt_send s t gcs) ->
    wfgC (g_k) ->
    assoc gamma (gtt_send s t gcs) ->
    projectionC g_k s Gks ->
    projectionC g_k t Gkt ->
    onth k gcs = Some (s',g_k) -> 
    tctx_wf (create_gamma_k s t Gks Gkt gamma) /\ assoc (create_gamma_k s t Gks Gkt gamma) g_k.
Proof.
    intros.
    Ltac rewr1 H6:=rewrite M.add_spec1 in H6.
        Ltac rewr2 H6:=
        rewrite M.add_spec2 in H6;try rewrite M.add_spec1 in H6;try easy.
        Ltac rewr3 H6 := rewrite M.add_spec2 in H6;try rewrite M.add_spec2 in H6;
        try rewrite M.remove_spec2 in H6; try rewrite M.remove_spec2 in H6;
        try easy.
    set (gamma_k:= M.add s Gks (M.add t Gkt (M.remove s (M.remove t gamma)))).
    unfold create_gamma_k in *. fold gamma_k.
    split.
    {
        unfold tctx_wf; intros;
        destruct (Nat.eq_dec p s); 
        destruct (Nat.eq_dec p t);crush;
        try (apply same_rec_send_not_wfg in H0; easy);
        unfold gamma_k in *;
        try rewr1 H6;try rewr2 H6;try rewr3 H6;
        try inversion H6;subst; 
        [apply projection_implies_slist_send in H3 | 
        apply projection_implies_slist_recv in H3|
        apply projection_implies_slist_send in H4  |
        apply projection_implies_slist_recv in H4 | | ];try easy;
        (unfold tctx_wf in H; specialize (H p q xs); destr_hyps);
        [apply H | apply H7];try easy.
    }
    {
        Ltac rewr1g := rewrite M.add_spec1.
        Ltac rewr2g :=
        rewrite M.add_spec2;try rewrite M.add_spec1;try easy.
        Ltac rewr3g := rewrite M.add_spec2;try rewrite M.add_spec2;
        try rewrite M.remove_spec2; try rewrite M.remove_spec2;
        try easy.
        unfold assoc. intros.
        split.
        {
            intros.
            destruct (Nat.eq_dec p s); 
            destruct (Nat.eq_dec p t);crush;
            try (apply same_rec_send_not_wfg in H0; easy);
            unfold gamma_k in *;
            try rewr1g;try rewr2g ;try rewr3g;subst.
            {
                exists Gks. unfold assoc in H2. unfold issubProj. crush. 
                exists Gks. crush. apply stRefl. 
            }
            {
                exists Gkt. unfold assoc in H2. unfold issubProj. crush. 
                exists Gkt. crush. apply stRefl. 
            }
            {
                Check part_parent.
                eapply part_parent with (p:=s) (q:=t) (k:=k) (gcs:=gcs) (s:=s') in H6; try easy.
                unfold assoc in H2. specialize (H2 p). destr_hyps. pose proof H6 as Hisparts.
                apply H2 in H6. destr_hyps.
                exists x. split;try easy.
                Search issubProj.
                destruct x.
                {
                    eapply subproj_inv_end in H8; try easy.   
                }
                {
                    eapply subproj_after_cont_recv with (p:=s) (q:=t) 
                    (gcs:=gcs) (k:=k) (s:=s');try easy.   
                    unfold tctx_wf in H. specialize (H p n1 l).
                    destr_hyps. apply H9; easy.
                }   
                {
                    eapply subproj_after_cont_send with (p:=s) (q:=t) 
                    (gcs:=gcs) (k:=k) (s:=s');try easy.   
                    unfold tctx_wf in H. specialize (H p n1 l).
                    destr_hyps. apply H; easy.
                }   
            }
        }
        {
            intros.
            destruct (Nat.eq_dec p s);
            destruct (Nat.eq_dec p t);crush;
            try (apply same_rec_send_not_wfg in H0; easy);
            unfold gamma_k in *;
            try rewr1 H7;try rewr2 H7 ;try rewr3 H7;inversion H7;subst.
            {
                eapply not_part_proj in H6. eapply proj_inj with (t:=Tpx) in H6;try easy.
            }
            {
                eapply not_part_proj in H6. eapply proj_inj with (t:=Tpx) in H6;try easy.
            }
            {
                assert(isgPartsC p (gtt_send s t gcs) -> False).
                {
                    intros.
                    Search isgPartsC gttstepC.
                    apply H6.
                    unfold assoc in H2. specialize (H2 p). destr_hyps.
                    pose proof H8 as Hpp.
                    apply H2 in H8. destr_hyps. unfold issubProj in H11. destr_hyps.  
                    eapply part_after_step_r with 
                    (G:=gtt_send s t gcs) (p:=s) (q:=t) (l:= k) (T:=x0);try easy.
                    pfold. eapply steq with (s:=s');try easy.
                    destruct(Nat.eq_dec s t);try easy.
                    subst;apply same_rec_send_not_wfg in H0. easy.
                }
                unfold assoc in H2. specialize (H2 p). destr_hyps.
                eapply H10 with (Tpx:=Tpx) in H8; easy.
            }   
        }
    }
Qed.

Definition soundness_pred p q G gamma ell':= fun u => match u with 
    | (gamma', G'') => gttstepC G G'' p q ell' /\ assoc gamma' G'' /\ 
    tctxR gamma (lcomm p q ell') gamma'
     end.


Definition decorate_proof {A:Type} (k:nat) (xs:list (option A)) : 
    {exists a, onth k xs =Some a} + {onth k xs =None}.
Proof.
    destruct (onth k xs). left. exists a. reflexivity.
    right. reflexivity.
Defined.

Definition eqlenSeq {A:Type} (x:list A) := seq 0 (List.length x).

Definition extract_some_ind k gcs_og (H:exists a: sort*gtth, onth k gcs_og =Some a): sort*gtth.
Proof.
    destruct (constructive_indefinite_description _ H). exact x. Defined.


Lemma assoc_soundness: forall G G' gamma  p q ell xs, p <> q -> wfgC G -> isgPartsC p G ->
tctx_wf gamma -> M.find p gamma =Some (ltt_send q xs) ->
assoc gamma G -> 
gttstepC G G' p q ell -> 
forall ell', onth ell' xs <> None ->
exists gamma' G'',
gttstepC G G'' p q ell' /\ assoc gamma' G'' /\ tctxR gamma (lcomm p q ell') gamma'.
Proof.
    intros.
    pose proof H4 as Hprojectable. apply assoc_implies_projectable in Hprojectable.
    rename H3 into Hmfindp, H4 into H3, H5 into H4.
    generalize dependent G'.
    revert H2 H3 Hmfindp.
    generalize dependent xs.
    revert gamma.
    revert ell'.
    rename H into Hpq_neq, H0 into H, H1 into H0.
    revert Hprojectable.
    eapply wfg_proof_princip3 with (g:=G) (p:=p); try easy.
    induction ctx using gtth_ind_ref.
    {
        intros.
        rename H6 into Hellsome.
        pose proof H4 as Hassoc.
        pose proof H2 as Htyp.
        eapply typ_p_gtth_step_inv with (g':=G') (q:=q) (ell:=ell) in H2; try easy.
        destruct H2.
        eapply typ_p_gtth_hole_inv2 with (g':= (gtt_send p q x)) in Htyp;try easy;subst.
        rename x into gcs.
        unfold assoc in H4. specialize (H4 p) as Hsocp. specialize (H4 q) as Hsocq.
        destr_hyps.
        clear H9 H7.
        set (trivp:=decidable_helper.triv_pt_p p q gcs H1).
        set (trivq:=decidable_helper.triv_pt_q p q gcs H1).
        apply  H8 in trivp. apply H6 in trivq. clear H6 H8.
        destr_hyps.  rename x0 into Tp, x into Tq.
        pose proof H8 as Hsubq.
        pose proof H9 as Hsubp.
        apply subproj_simple_send_inv in H9;try easy.
        apply subproj_simple_recv_inv in H8;try easy.
        destruct H9 as [xp].
        destruct H8 as [xq].
        subst. pose proof H7 as Hpgamma. pose proof H6 as Hqgamma.
        pose proof H3 as Htctx_wf.
        unfold tctx_wf in H3.  eapply H3 in H7. eapply H3 in H6.
        pose proof Hsubp as Hsims.
        eapply lem_6_16_simul_subproj with (xq:=xq) in Hsims; try apply decidable_helper.triv_pt_p; try easy.
        pose proof H7 as xpSlist. pose proof H6 as xqSlist.
        rewrite Hpgamma in Hmfindp. apply eq_sym in Hmfindp;inversion Hmfindp. subst.
        apply opt_lem1 in Hellsome.
        destruct Hellsome as [T_k Hellsome]. 
        rename ell' into k. destruct T_k as [s T_k].
        assert(exists s' gct, onth k gcs=Some (s',gct) /\ gttstepC (gtt_send p q gcs) gct p q k).
        {
        unfold issubProj in Hsubq. destr_hyps. pinversion H8;subst; try tac_isParts;try easy.
        eapply subproj_onth1 with (k:=k) (s:=s) (T_k:=T_k) in Hsubp;try easy;try apply proj_mon.
        destr_hyps. exists x, x0. crush.
        pfold. eapply steq with (s:=x);crush. try apply proj_mon.
        }
        destruct H8 as [s' [G_k Hprog]].
        pose proof Hsims as Honthq.
        eapply Forall2R_prop with (l:=k) (p:=(s,T_k)) in Honthq;try easy. 
        destr_hyps. destruct H9;try easy. destr_hyps;subst. 
        apply eq_sym in H9. inversion H9. subst.  clear H9. 
        rename x2 into s'', x3 into Tq_k, T_k into Tp_k.
        assert(Hwfgk:wfgC G_k).
        {
            eapply continuation_wfgC with (p:=p) (q:=q) in H10; try easy.
        } 
        set (gamma':=M.add p Tp_k (M.add q Tq_k (M.remove p (M.remove q gamma)))).
        assert (Heqdom: M.Eqdom gamma gamma').
        {
            unfold M.Eqdom.
            intros.
            unfold gamma'.
            split.
            {    
                intros.   
                rewrite MF.in_find in *.
                destruct (Nat.eq_dec p y);
                destruct (Nat.eq_dec q y);crush.
                rewrite M.add_spec1 in H9. easy.
                rewrite M.add_spec2 in H9;try easy;rewrite M.add_spec1 in H9; try easy.
                rewrite M.add_spec2 in H9;rewrite M.add_spec2 in H9;try easy.
                rewrite M.remove_spec2 in H9;rewrite M.remove_spec2 in H9; try easy.
            }
            {
             intros. 
             rewrite MF.in_find in *. apply opt_lem1 in H8. destr_hyps.
             destruct(Nat.eq_dec p y);destruct(Nat.eq_dec q y);crush.
             rewrite M.add_spec2 in H8;try  rewrite M.add_spec2 in H8;
             try rewrite M.remove_spec2 in H8; try rewrite M.remove_spec2 in H8; crush.
            }
        }

        exists gamma', G_k. crush.
        {
            unfold assoc.
            intros.
            pose proof Hwfgk as Hgkdec. 
            apply decidable_isgPartsC with (pt:= p0) in Hgkdec.
            destruct (Hgkdec) as [Hgpart | Hgpart].
            {
                destruct (Nat.eq_dec p0 p);
                destruct (Nat.eq_dec p0 q);
                crush.
                {
                    exists Tp_k. split. unfold gamma'. rewrite M.add_spec1. easy.
                    apply subproj_inv_send in Hsubp;try easy.
                    destruct (Hsubp).
                    {
                        destr_hyps.
                        inversion H9;subst. rename x into gcs.
                        unfold send_cond in H14.
                        eapply Forall2R_prop with (l:=k) (p:=(s,Tp_k)) in H14; try easy.
                        destr_hyps.
                        destruct H15;try easy.
                        destr_hyps.
                        inversion H16;subst.
                        rewrite H15 in H10. inversion H10;subst. easy.
                    }
                    {
                        destr_hyps. inversion H9;crush.
                    }
                }
                {
                    exists Tq_k. split. unfold gamma'. 
                    rewrite M.add_spec2; try rewrite M.add_spec1; easy.   
                    apply subproj_inv_recv in Hsubq;try easy.
                    destruct (Hsubq).
                    {
                        destr_hyps.
                        inversion H9;subst. rename x into gcs.
                        unfold recv_cond in H14.
                        eapply Forall2R_prop with (l:=k) (p:=(s',G_k)) in H14; try easy.
                        destr_hyps.
                        destruct H15;try easy.
                        destr_hyps.
                        inversion H16;subst.
                        rewrite H16 in H12. inversion H12;subst. 
                        inversion H15;subst.  easy.
                    }
                    {
                        destr_hyps. inversion H9;crush.
                    }
                }
                {
                    assert(Hpart_parent:isgPartsC p0 (gtt_send p q gcs)).
                    {
                        eapply part_parent with (p:=p) (q:=q) (gcs:=gcs) (k:=k) (s:=s') in H8;easy.
                    }
                    assert(Hrg: forall r, r<> p -> r <> q -> M.find r gamma' =M.find r gamma).
                    {
                        intros.
                        unfold gamma'. try rewrite M.add_spec2;
                        try rewrite M.add_spec2;
                        try rewrite M.remove_spec2;
                        try rewrite M.remove_spec2;easy.   
                    }
                    {
                        unfold assoc in Hassoc.
                        specialize (Hassoc p0).
                        destr_hyps.
                        pose proof Hpart_parent as Hpp.
                        apply H9 in Hpart_parent.
                        destr_hyps.
                        pose proof n0 as Hp0p.
                        apply Hrg in Hp0p; try easy.
                        exists x.
                        rewrite Hp0p. split. easy.
                        destruct x;
                        [apply subproj_inv_end in H16|
                        eapply subproj_after_cont_recv with (k:=k) (s:=s') (gk:=G_k) in H16|
                        eapply subproj_after_cont_send with (k:=k) (s:=s') (gk:=G_k) in H16];
                        try easy;
                        unfold tctx_wf in Htctx_wf;
                        specialize (Htctx_wf p0 n2 l);
                        crush.
                    }
                }
            }
            {
                crush.
                destruct (Nat.eq_dec p0 p);
                destruct (Nat.eq_dec p0 q);subst.
                {
                    crush.
                }
                {
                     eapply assoc_cont_not_part_send with (q:=q) (xs:=xp) (gcs:=gcs) (k:=k) (s:=s') 
                     in Hgpart; try easy.
                     destruct Hgpart;crush.
                     rewrite H14 in Hellsome.
                     inversion Hellsome;subst.
                     unfold gamma' in H9.
                     rewrite M.add_spec1 in H9. inversion H9;easy.
                }
                {
                    eapply assoc_cont_not_part_recv with (p:=p) (xs:=xq) (gcs:=gcs) (k:=k) (s:=s') 
                     in Hgpart; try easy.
                     destruct Hgpart;crush.
                     rewrite H14 in H12.
                     inversion H12;subst.
                     unfold gamma' in H9.
                     rewrite M.add_spec2 in H9;try easy; rewrite M.add_spec1 in H9. inversion H9;easy.
                }
                {
                    Search isgPartsC.
                    assert(Hnotpart: ~ isgPartsC p0 (gtt_send p q gcs)).
                    {
                        unfold not.
                        intros.
                        specialize (Hprojectable p0). destr_hyps.
                        eapply part_after_step_r with (T:=x) (p:=p) (q:=q) (l:=k) (G':=G_k) in H14; 
                        try easy.
                    }
                    unfold assoc in Hassoc.
                    Check conj.
                    destruct (M.find p0 gamma) eqn:Hyg1;
                    [eapply (proj2 (Hassoc p0)) with (Tpx:=l) in Hnotpart;try easy | ];
                        unfold gamma' in H9;
                        try rewrite M.add_spec2 in H9;
                        try rewrite M.add_spec2 in H9;
                        try rewrite M.remove_spec2 in H9;
                        try rewrite M.remove_spec2 in H9; crush.
                }
            }
        }
        {
            set (gamma_justpq := M.add p (ltt_send q xp) (M.add q (ltt_send p xq) M.empty)).
            set (gamma_nopq := M.remove p (M.remove q gamma)).
            set (gamma'_justpq:=M.add p Tp_k (M.add q Tq_k M.empty)).
            fold gamma_nopq in gamma'.
            assert(Heq_gamma: M.Equal gamma (M.add p (ltt_send q xp)
            (M.add q (ltt_recv p xq) gamma_nopq))).
            {
                unfold M.Equal. intros. unfold gamma_nopq.
                destruct (Nat.eq_dec p y);destruct (Nat.eq_dec q y);crush.
                + rewrite M.add_spec1. easy.
                + rewrite M.add_spec2;try easy. rewrite M.add_spec1. easy.
                +   rewrite M.add_spec2. rewrite M.add_spec2.
                rewrite M.remove_spec2. rewrite M.remove_spec2. all:easy.
            }
            unfold gamma'.
            setoid_rewrite Heq_gamma.
            eapply context_red_simple_comm with (s:=s) (s'':=s'');try easy;unfold gamma_nopq.
            apply M.remove_spec1. rewrite M.remove_spec2. rewrite M.remove_spec1.
            easy. easy. 
        }
    }
    {
        intros. rename p0 into s, q0 into t, H1 into Ih.
        pose proof H3 as Htyp. eapply typ_p_gtth_inv in Htyp. destr_hyps;subst.
        inversion H3.
        assert (Hneq: p <>s /\ q <> t).
        {
         split.
         {
            destruct (Nat.eq_dec p s); try easy. destr_hyps. subst.
            assert(ishParts s (gtth_send s t xs)). constructor.
            easy.   
         }
         {
          destruct (Nat.eq_dec q t); try easy.
          pinversion H7;crush. apply H19. constructor. apply step_mon.  
         }
        }
        destr_hyps.
        pose proof H7 as Hstep.
        pinversion H7;try apply step_mon;crush.
        rename xs into ghs, ys into gcs', x into gcs.
        
        assert(gamma_k_props_2:forall s4 k g_k k' xs Gks Gkt, onth k gcs = Some (s4,g_k) -> 
        projectionC g_k s Gks ->
        projectionC g_k t Gkt ->
        M.find p (create_gamma_k s t Gks Gkt gamma)=Some (ltt_send q xs) -> onth k' xs <> None ->
        exists (gamma' : tctx) (G'' : gtt),
        gttstepC g_k G'' p q k' /\
        assoc gamma' G'' /\ tctxR (create_gamma_k s t Gks Gkt gamma) (lcomm p q k') gamma').
        {
            intros.
            assert(Hwfgk: wfgC g_k). eapply continuation_wfgC with (p:=s) (q:=t) in H12;try easy.
            eapply gamma_k_props with (k:=k) (gcs:=gcs) (s':=s4) (s:=s) (Gks:=Gks) (gamma:= gamma) in H14;
            try easy.
            destr_hyps.
            rename H14 into Htcwf.
            pose proof H12 as Hc2.
            eapply typ_gtth_cont1 with (gs:=gs) (p:=s) (q:=t) (gcs:=ghs) in H12; try easy.
            destr_hyps.
            eapply Forall_prop with (l:=k) (p:=(s4,x)) in Ih; try easy.
            destruct Ih;try easy.
            destr_hyps.
            inversion H24;subst.
            rename H27 into Ih.
            eapply Forall2_prop_r with (l:=k) (p:=(x0,g_k)) in H26;try easy.
            destr_hyps.
            destruct H27;try easy. destr_hyps. inversion H27; subst. clear H27.
            
            destruct H29;crush.
            rename x3 into g_k, x4 into gk', H24 into Hstepk.
            eapply Ih with (gs:=gs) (G':=gk') (xs:=xs); try easy.
            {
                unfold typ_p_gtth. crush. Search ishParts. rename x1 into ghco.
                assert(ishParts p (gtth_send s t ghs)).
                {
                    eapply ha_sendr with (g:=ghco) (n:=k) (s:=x2);try easy.   
                }
                apply H8 in H27. easy.
            }
            {
                apply proj_forward in Hprojectable;try easy.
                eapply Forall_prop with (l:=k) (p:=(x2,g_k)) in Hprojectable;try easy.
                destruct Hprojectable;try easy. destr_hyps. inversion H21. subst.
                apply assoc_implies_projectable in H23;
                try easy.
            }
        }
        assert(Hpsame:forall Gks Gkt, M.find p (create_gamma_k s t Gks Gkt gamma) = M.find p gamma).
        {
            intros.
            unfold create_gamma_k.
            try rewrite M.add_spec2;try rewrite M.add_spec2;try rewrite M.remove_spec2;
            try rewrite M.remove_spec2;try easy.   
        }
        Check gamma_k_props_2.
        assert(Hchild_proj_1: forall k s4 g_k, onth k gcs=Some (s4,g_k) -> 
        projectableA g_k).
        {
            intros.
            apply assoc_implies_projectable in H5;try easy.
            eapply proj_forward in H5;try easy.
            eapply Forall_prop with (l:=k) (p:=(s4,g_k)) in H5;destruct H5; try easy. destr_hyps.
            inversion H5;easy.  
        }
        assert(gamma_props_simple: forall k  s4 g_k, 
        onth k gcs=Some (s4,g_k) -> 
        exists (Gks:ltt) (Gkt:ltt) (gamma' : tctx) (G'' : gtt),
        projectionC g_k s Gks /\
        projectionC g_k t Gkt /\
        M.find p (create_gamma_k s t Gks Gkt gamma)=Some (ltt_send q xs0) /\
        gttstepC g_k G'' p q ell' /\
        assoc gamma' G'' /\ tctxR (create_gamma_k s t Gks Gkt gamma) (lcomm p q ell') gamma').
        {
            intros.
            pose proof H12 as Honthk. 
            specialize (Hchild_proj_1 k s4 g_k). apply Hchild_proj_1 in H12.
            unfold projectableA in H12. specialize (H12 s) as Hchilds.
            specialize (H12 t) as Hchildt. destr_hyps.
            rename x0 into Gks, x into Gkt.
            exists Gks, Gkt.
            eapply gamma_k_props_2 with (k:=k) (s4:=s4) (g_k:=g_k) (Gks:= Gks)
             (Gkt:=Gkt) (k':=ell') (xs:=xs0) in Honthk;
            try easy.
            destr_hyps. exists x, x0. crush.
            rewrite Hpsame. easy.
        }
        assert(extract_gamma_props_simple:forall s4 k g_k, onth k gcs = Some (s4,g_k) -> 
        {u:  (ltt*ltt*tctx* gtt) |
        (fun u=> match u with 
        | (Gks,Gkt,gamma',G'')=>
        projectionC g_k s Gks /\
        projectionC g_k t Gkt /\
        M.find p (create_gamma_k s t Gks Gkt gamma)=Some (ltt_send q xs0) /\
        gttstepC g_k G'' p q ell' /\
        assoc gamma' G'' /\ tctxR (create_gamma_k s t Gks Gkt gamma) (lcomm p q ell') gamma'
        end) u}).
        {
            intros.
            eapply gamma_props_simple in H12. 
            destruct (constructive_indefinite_description _ H12).
            destruct (constructive_indefinite_description _ (e)).
            destruct (constructive_indefinite_description _ (e0)).
            destruct (constructive_indefinite_description _ (e1)).
            exists (x,x0,x1,x2). easy. 
        }
        Search SList.
        Definition verified_indexing_helper (gcs_og:list (option (sort*gtt))) 
        (gcs:list (option (sort*gtt))) (k_now:nat): list(
            {u : (nat*option (sort*gtt)) |
            match u with | (k,None) =>True
                         | (k, Some (s,g)) => onth k gcs_og=Some (s,g) end
            } 
        ).
        Proof.
            induction gcs.
            {
             exact [].   
            }
            {
                destruct (onth k_now gcs_og) eqn:Heq.
                {
                    destruct p.
                    assert(Hr: {u : (nat*option (sort*gtt)) |
                    match u with | (k,None) =>True
                                 | (k, Some (s,g)) => onth k gcs_og=Some (s,g) end
                    }).
                    {
                        exists (k_now, Some (s,g)). assumption.   
                    }
                    exact (Hr :: IHgcs).   
                }
                {
                    assert(Hr: {u : (nat*option (sort*gtt)) |
                    match u with | (k,None) =>True
                                 | (k, Some (s,g)) => onth k gcs_og=Some (s,g) end
                    }). exists (k_now,None). easy.
                    exact(Hr::IHgcs).
                }
            }
        Defined.

        Definition populate_indices (gcs:list(option(sort*gtt))) :=verified_indexing_helper gcs gcs 0.
        
        Print sig.

        Definition create_gcs'' (gcs:list (option (sort*gtt))) p q ell' s t
        (Hps : p<>s ) (Hqt: q <>t) 
        (Hwfg:wfgC (gtt_send s t gcs))
        (P: forall s4 k g_k,
        onth k gcs =Some (s4,g_k) -> {u:gtt| gttstepC g_k u p q ell'})
        :{gcs'':list (option (sort*gtt)) | gttstepC (gtt_send s t gcs) (gtt_send s t gcs'') p q ell' }.
        Proof.
            set (indexed_gcs:=populate_indices gcs).
            set (indexed_gcs_mapped:= map (fun u=> 
                match u with 
                    | exist (k,None) _ => None
                    | exist (k,Some (s,g)) H => match (P s k g H) with 
                                | exist v _ => Some (s,v) end
                    end
            ) indexed_gcs).
            Check indexed_gcs_mapped.
            exists indexed_gcs_mapped.
            pfold. constructor;try easy.
            Check indexed_gcs.
        Defined.
        
        assert(extract_just_gtt: forall s4 k g_k, onth k gcs = Some (s4,g_k) -> 
        {u:gtt| gttstepC g_k u p q ell'}).
        {
            intros.
            apply extract_gamma_props_simple in H12.
            destruct H12.
            destruct x as [[[d1 d2] d3] d4].
            exists d4. easy.
        }
        set(gcs'':=create_gcs'' gcs (eqlenSeq gcs) 
        extract_just_gtt).

        assert(gttstepC (gtt_send s t gcs) 
        (gtt_send s t gcs'') p q ell').
        {
            generalize dependent gcs.
            induction gcs;intros.
            {
                apply empty_not_wfg in H2. easy.
            }
            {
                destruct a.
                {
                    simpl in gcs''.
                    admit.
                }  
                {
                    unfold gcs''.
                    simpl in gcs''. simpl.
                    pfold. constructor;try easy. constructor;try easy. left. easy.

                }
            }
            intros.
            pfold. constructor;try easy. 
            
        }
        assert ({gcs'' : (list (option (sort*gtt))) | 
            forall k, ((onth k gcs=None -> onth k gcs'' =None) /\ 
            (exists s4 g_k, onth k gcs=Some (s4,g_k) -> exists G'', 
            onth k gcs'' =Some (s4,G'') /\ gttstepC g_k G'' p q ell'))}).
        assert (exists gcs'',
            forall k, 
                (forall (Hknone:onth k gcs=None), onth k gcs'' =None) /\
                (forall s4 g_k (Hksome:onth k gcs=Some (s4, g_k)),
                    exists G'', onth k gcs'' =Some (s4,G'') /\
                    gttstepC g_k G'' p q ell'
                )
        ).
        {
            intros.
            exists gcs''.
            intros.
            split.
            {
                admit.   
            }
            {
                intros.
                Compute  
                eapply gamma_props_simple with (k':=k') in Hksome; try easy.
                destr_hyps.
                exists x0. split;try easy.
            }   
        }
        set (G'':= (gtt_send s t (map_fun gcs))).
        assert(Hg'':exists g'', gttstepC (gtt_send s t gcs) g'' p q ell').
        {

        }

    }
Qed. 