(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From live_mpst.STBase Require Import src.expr src.header src.local
src.global src.projection src.part  src.balanced src.merge  src.gttreeh
lemma.projection lemma.projection_helper lemma.decidable src.step lemma.step.
From live_mpst.STLive Require Import src.wfltt src.lcontext src.assoc.
From live_mpst.cpdtlib Require Import CpdtTactics.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.

Import ListNotations.
(*
Create HintDb mmaps. 
Hint Rewrite ( @M.add_spec1 ) ( @M.add_spec2) ( @M.remove_spec1)
    ( @M.remove_spec2) ( @M.empty_spec) using easy : mmaps.*)


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
(*Check typ_p_gtth.*)

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

(*Check Forall2_prop_r.*)

Lemma Forall2R_prop {A:Type} {B:Type}: forall l (xs :list (option A)) (ys :list (option B)) P p, Forall2R P xs ys -> onth l xs= Some p ->  
    exists p', onth l ys= p' /\ P (Some p) p'.
Proof.
    intros.
    generalize dependent l.
    induction H;intros.
    rewrite onth_nil in H0;easy.
    destruct l;simpl in H1;[ exists y | eapply IHForall2R]; crush.    
Qed.



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

(*
#[export] Instance RWMTCTXR: 
    Proper ((@M.Equal ltt) ==> (eq) ==> (@M.Equal ltt) ==> (iff)) tctxR.
Proof. unfold "==>". constructor; intros; subst. 
apply Rstruct with (g1:=y) (g2:=y1) (g1':=x) (g2':=x1);crush. 
apply Rstruct with (g1:=x) (g2:=x1) (g1':=y) (g2':=y1);crush.
Qed.
*)
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

(*Search SList.*)
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

Lemma assoc_cont_not_part_send : forall p q gcs k g_k s xs, wfgC (gtt_send p q gcs) -> 
SList xs ->
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

Lemma assoc_cont_not_part_recv : forall p q gcs k g_k s xs, wfgC (gtt_send p q gcs) -> 
SList xs ->
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

Lemma projection_wf_helper:forall xs ys r, SList xs -> Forall2
(fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
u = None /\ v = None \/
(exists (s : sort) (g : gtt) (t : ltt),
u = Some (s, g) /\
v = Some (s, t) /\ upaco3 projection bot3 g r t)) xs ys -> SList ys.
Proof.
    intros.
    generalize dependent xs.
    revert r.
    generalize dependent ys.
    induction ys.
    {
        intros;
        inversion H0;crush.   
    }
    {
        intros.
        inversion H0;subst.
        destruct H4;destr_hyps;subst.
        {
            simpl in H.
            assert (SList ys). eapply IHys with (r:=r) (xs:=l);try easy.
            simpl. easy.
        }
        {
            simpl in H. destruct l. inversion H5;crush.   
            assert (SList ys). eapply IHys with (r:=r) (xs:= (o::l)); try easy.
            simpl. destruct ys;crush.
        }
    }
Qed.


Lemma projection_implies_wf : 
    forall g r t,    wfgC g -> projectionC g r t ->
    wflttC t.
Proof.
    (*Search projectionC SList.*)
    pcofix CIH.
    intros g pt t Hwfg Hproj.
    destruct (decidable_isgPartsC g pt);try easy.
    {
        destruct g;
        [pinversion Hproj;try apply proj_mon;subst; easy|].
        rename n into p, n0 into q, l into gcs.
        pose proof H as Hgraft.
        eapply balanced_to_tree in Hgraft;try easy.
        destruct Hgraft as [ctx [gs [Hgraft1 [Hgraft2 [Hgraft3 Hgraft4]]]]].
        clear Hgraft4.        
        clear H.
        assert(H:True). constructor.
        generalize dependent p.
        generalize dependent q.
        generalize dependent gcs.
        generalize dependent gs.
        generalize dependent ctx.
        
        induction ctx using gtth_ind_ref.
        {
            intros.
            inversion Hgraft1;subst.
            eapply Forall_prop with (l:= n) (p:=(gtt_send p q gcs)) in Hgraft3;try easy.
            
            destruct Hgraft3;try easy.
            destruct H0 as [q' [gcs']].
            destruct H0.
            {
                inversion H0;subst.
                pinversion Hproj;try apply proj_mon;crush;pfold;constructor.
                
                eapply projection_wf_helper with (xs:=gcs') (r:=pt);
                    [apply wfg_implies_slis in Hwfg | ];easy.
                eapply Forall_forall;
                intros;
                destruct x as [p0 | ];try (left;easy);
                destruct p0 as [s1 t1];
                right;
                apply in_some_implies_onth in H1;
                destruct H1 as [n' Honth];
                exists s1, t1;
                split;try easy;
                right;
                eapply Forall2_prop_l with (l:=n') (p:=(s1,t1)) in H9;try easy.
                destr_hyps. destruct H3;try easy; destr_hyps. inversion H4;subst.
                eapply CIH with (g:=x1) (r0:=pt).
                eapply continuation_wfgC with (p:=pt) (q:=q') (xs:=gcs') (n:=n') (s:=x0);try easy.
                destruct H7;crush.
            }
            destruct H0.
            {
                inversion H0;subst.
                pinversion Hproj;try apply proj_mon;crush;pfold;constructor.
                eapply projection_wf_helper with (xs:=gcs') (r:=pt);
                    [apply wfg_implies_slis in Hwfg | ];easy.
                eapply Forall_forall;
                intros;
                destruct x as [p0 | ];try (left;easy);
                destruct p0 as [s1 t1];
                right;
                apply in_some_implies_onth in H1;
                destruct H1 as [n' Honth];
                exists s1, t1;
                split;try easy;
                right;
                eapply Forall2_prop_l with (l:=n') (p:=(s1,t1)) in H9;try easy.
                destr_hyps. destruct H3;try easy; destr_hyps. inversion H4;subst.
                eapply CIH with (g:=x1) (r0:=pt).
                eapply continuation_wfgC with (q:=pt) (p:=q') (xs:=gcs') (n:=n') (s:=x0);try easy.
                destruct H7;crush.
            }
            {
                easy.   
            }    
        }
        {
            intros.
            (*Search typ_gtth "inv".*)
            pose proof Hgraft1 as Htyp.
            eapply typ_gtth_inv in Hgraft1. destr_hyps.
            apply eq_sym in H1;inversion H1;subst;clear H1.
            pinversion Hproj;try apply proj_mon;subst.
            pfold;constructor.
            exfalso;apply Hgraft2; constructor.
            exfalso;apply Hgraft2; constructor.
            pose proof Hwfg as Hslis.
            apply wfg_implies_slis in Hslis.
            apply slist_implies_some in Hslis.
            destr_hyps.
            destruct x0 as [s1 g1].
            rename x into n.
            pose proof H1 as Honth.
            eapply typ_gtth_cont1 with (p:=p0) (q:=q0) (gs:=gs) (gcs:=xs) in H1;try easy.
            eapply Forall2_prop_r with (l:=n) (p:=(s1,g1)) in H10;try easy.
            destr_hyps.
            (*Search typ_gtth "cont".*)
            eapply Forall_prop with (l:=n) (p:=(s1,x)) in H0;try easy.
            destruct H0;try easy.
            destr_hyps.
            inversion H0;subst.
            destruct H8;try easy. destr_hyps.
            inversion H2;subst.
            eapply merge_inv_ss with (T:=t) in H8;try easy;subst.
            rename x0 into gc, x into s1, x2 into gh1, xs into ghs.
            destruct gc.
            {
                destruct H10.
                pinversion H8;subst;try easy;try apply proj_mon. pfold. constructor.
                inversion H8.
            }
            {
                rename n0 into p, n1 into q, l into gcs'.
                eapply H9 with (gs:=gs) (p:=p) (q:=q) (gcs:=gcs');try easy.
                (*Search ishParts onth.*)
                eapply decidable_helper.ishParts_n with (s:=p0) (s':=q0) (xs:=ghs) (s0:=s1) (n:=n);try easy.
                eapply continuation_wfgC with (p:=p0) (q:=q0) (xs:=gcs) (s:=s1) (n:=n);try easy.
                destruct H10;try easy.
            }
        }
    }
    {
        pinversion Hproj;subst;try apply proj_mon;crush.
        pfold;constructor.
    }
Qed.

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
    set (gamma_k:= M.add s Gks (M.add t Gkt (M.remove s (M.remove t gamma)))).
    unfold create_gamma_k in *. fold gamma_k.
    split.
    {
        unfold tctx_wf; intros;
        destruct (Nat.eq_dec p s); 
        destruct (Nat.eq_dec p t);crush;
        try (apply same_rec_send_not_wfg in H0; easy);
        unfold gamma_k in *;
        autorewrite with mmaps in H6;
        try inversion H6;subst;
        [apply projection_implies_wf in H3 | 
        apply projection_implies_wf in H4  | ];try easy.
        (unfold tctx_wf in H; specialize (H p); destr_hyps);
        apply H;try easy.
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
            Ltac shl1 Gks H2:= exists Gks; unfold assoc in H2; unfold issubProj; crush; 
                exists Gks; crush; apply stRefl.
            intros.
            destruct (Nat.eq_dec p s); 
            destruct (Nat.eq_dec p t);crush;
            try (apply same_rec_send_not_wfg in H0; easy);
            unfold gamma_k in *;
            autorewrite with mmaps;[shl1 Gks H2| shl1 Gkt H2 |].
            {
                eapply part_parent with (p:=s) (q:=t) (k:=k) (gcs:=gcs) (s:=s') in H6; try easy.
                unfold assoc in H2. specialize (H2 p). destr_hyps. pose proof H6 as Hisparts.
                apply H2 in H6. destr_hyps.
                exists x. split;try easy.
                destruct x;try (eapply subproj_inv_end in H8;  easy);
                    [eapply subproj_after_cont_recv with (p:=s) (q:=t) 
                    (gcs:=gcs) (k:=k) (s:=s') | 
                    eapply subproj_after_cont_send with (p:=s) (q:=t) 
                    (gcs:=gcs) (k:=k) (s:=s')];
                    try easy;   
                    unfold tctx_wf in H; [
                        specialize (H p (ltt_recv n1 l)) |
                        
                        specialize (H p (ltt_send n1 l))];destr_hyps;
                        [eapply wfltt_slist_recv | eapply wfltt_slist_send]; apply H;easy.
                        
            }
        }
        {
            intros.
            destruct (Nat.eq_dec p s);
            destruct (Nat.eq_dec p t);crush;
            try (apply same_rec_send_not_wfg in H0; easy);
            unfold gamma_k in *;
            autorewrite with mmaps in H7;inversion H7;subst.
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

(*Search projectionC Forall. *)
Lemma proj_implies_subproj : forall g p t, projectionC g p t -> issubProj t g p.
Proof.
    intros. unfold issubProj. exists t;split;try apply stRefl;try easy.
Qed.
(*Print SList.*)

Lemma proj_cont_implies_proj_parent:forall p s t Tp gcs'' k g_k s4, 
wfgC (gtt_send s t gcs'' ) ->
projectableA (gtt_send s t gcs'') -> 
isgPartsC p (gtt_send s t gcs'') ->
p <> s  -> p<> t -> s<> t->
onth k gcs''=Some (s4,g_k) ->
projectionC g_k p Tp->
projectionC  (gtt_send s t gcs'') p Tp.
{
    intros.
    assert (Hwfgk: wfgC g_k). eapply continuation_wfgC with (p:=s) (q:=t) in H5;try easy.
    assert (Hstep:gttstepC (gtt_send s t gcs'') g_k s t k).
    {
        intros.  
        pfold. eapply steq with (s:=s4);try easy. 
    }
    assert (Hgkpart: isgPartsC p g_k).
    {
        (*Search isgPartsC gttstepC.*)
        unfold projectableA in H0. specialize (H0 p). 
        destr_hyps.
        eapply part_after_step_r with (G:=(gtt_send s t gcs'')) (p:=s) (q:=t) (l:=k) (T:=x);try easy.
    }
    unfold projectableA in H0;specialize (H0 p). destr_hyps.
    pinversion H0;try apply proj_mon;crush.
    eapply Forall2_prop_r with (l:=k) (p:=(s4,g_k)) in H16;try easy.
    destr_hyps. destruct H8;try easy.
    destr_hyps.
    inversion H8;subst.
    destruct H14;crush.
    (*Search isMerge onth.*)
    eapply merge_inv_ss with (T:=x) in H9;subst;try easy.
    change (paco3 projection bot3 x2 p x) with (projectionC x2 p x) in H7.
    eapply proj_inj with (t:=x) in H6; subst;try easy. 
    pfold. easy.
}
Qed. 

Lemma subproj_cont_implies_subproj_parent: forall p s t Tp gcs'' k g_k s4, 
wfgC (gtt_send s t gcs'' ) ->
projectableA (gtt_send s t gcs'') -> 
isgPartsC p (gtt_send s t gcs'') ->
p <> s  -> p<> t -> s<> t->
onth k gcs''=Some (s4,g_k) ->
issubProj Tp g_k p->
issubProj Tp (gtt_send s t gcs'') p.
Proof.
    intros.
    unfold issubProj in *. destr_hyps.
    exists x.
    split;try easy.
    eapply proj_cont_implies_proj_parent with (k:=k) (s4:=s4) (g_k:=g_k);try easy.
Qed.

Lemma subproj_after_step_r: forall G G' r p q ell' x, 
wfgC G -> wfgC G' -> projectableA G -> 
issubProj x G r -> r <> p -> r <> q ->
    gttstepC G G' p q ell' -> issubProj x G' r.
Proof.
    intros.
    (*Search "proj" "cont".*)
    unfold issubProj in *. destr_hyps.
    pose proof H5 as Hstep.
    eapply proj_cont_pq_step in H5;try easy.
    destr_hyps. 
    (*Search "typ_after_step_3".*)
    eapply typ_after_step_3_helper with (q:=q) (p:=p) (G':=G')
    (l:=ell') (L1:=x1) (L2:=x2) (LS:=x3) (LS':=x4) (LT':=x6) (LT:=x5)
     in H2 ; try easy.
     destr_hyps;subst. exists x7. split;easy.
Qed.


Lemma subproj_after_step1 : forall G G' p q ell'  xsp xsq s1 s2 Tp Tq, 
wfgC G -> wfgC G' -> projectableA G -> 
issubProj (ltt_send q xsp) G p ->
issubProj (ltt_recv p xsq) G q -> 
onth ell' xsp =Some (s1, Tp) ->
onth ell' xsq =Some (s2, Tq) ->
    gttstepC G G' p q ell' -> (issubProj Tp G' p /\ issubProj Tq G' q).
Proof.
    (*Check projection.typ_after_step_12_helper.*)
    intros.
    pose proof H6 as Hstep.
    eapply proj_cont_pq_step in H6;try easy. destr_hyps. 
    unfold issubProj in *. destr_hyps.
    eapply proj_inj with (t:=x6) in H6;try easy;subst.
    eapply proj_inj with (t:=x5) in H7;try easy;subst.
    rename x into xsp', x0 into xsq',x3 into Tp', x4 into Tq'.
    (*Check typ_after_step_3_helper.*)
    
    eapply projection.typ_after_step_12_helper 
    with (LP:=xsp') (LQ:=xsq') (S:=x1) (S':=x2) (T:=Tp') (T':=Tq') in Hstep;try easy.
    split.
    {
        exists Tp'.
        pose proof H11 as Hsubp.
        pose proof H10 as Hsubq.
        apply subtype_send_inv in H11.
        eapply Forall2R_prop with (l:=ell') (p:=(s1,Tp)) in H11;try easy.
        destr_hyps. destruct H12;try easy. destr_hyps.
        apply eq_sym in H12;inversion H12;subst.
        rewrite H13 in H8;inversion H8;subst. easy.
    }
    {
        exists Tq'.
        pose proof H11 as Hsubp.
        pose proof H10 as Hsubq.
        apply subtype_recv_inv in H10.
        eapply Forall2R_prop with (l:=ell') (p:=(x2,Tq')) in H10;try easy.
        destr_hyps. destruct H12;try easy. destr_hyps.
        apply eq_sym in H12;inversion H12;subst.
        rewrite H13 in H5;inversion H5;subst. easy.
    }
Qed.

Lemma assoc_inv_find : forall gamma g p Tp, wfgC g -> assoc gamma g -> M.find p gamma=Some Tp -> issubProj Tp g p.
Proof.
    intros.
    unfold assoc in H0. specialize (H0 p). destr_hyps.
    (*Check decidable_isgPartsC.*)
    apply decidable_isgPartsC with (pt:=p) in H.
    destruct H.
    {
        apply H0 in H. destr_hyps. rewrite H in H1;inversion H1;subst;try easy.
    }
    {
        pose proof H as Hnotin.
        apply H2 with (Tpx:=Tp) in H ;subst;try easy.
        unfold issubProj. exists ltt_end. apply not_part_proj in Hnotin. split;try (apply stRefl);try easy.   
    }
Qed.

Lemma not_part_step : forall g g' p q k r, wfgC g -> projectableA g ->
gttstepC g g' p q k -> ~isgPartsC r g -> ~ isgPartsC r g'.
Proof.
    unfold not in *;intros.
    apply H2.
    pose proof H1 as Hstep.
    apply proj_cont_pq_step in H1;try easy.
    destr_hyps.
    eapply part_after_step with (G':=g') (q:=p) (p:=q) (l:=k) (LP:=x) (LQ:=x0);try easy.
    eapply wfgC_after_step with (G:=g) (p:=p) (q:=q) (n:=k);try easy.
Qed.


Lemma subtype_send_inv2: forall x q xs, subtypeC x (ltt_send q xs) -> exists ys, x=(ltt_send q ys).
Proof.
    intros.
    destruct x; pinversion H;try apply sub_mon.
    subst;
    exists l;easy.
Qed.

Lemma subtype_recv_inv2: forall x q xs, subtypeC x (ltt_recv q xs) -> 
exists ys, x=(ltt_recv q ys).
Proof.
    intros.
    destruct x; pinversion H;try apply sub_mon.
    subst;
    exists l;easy.
Qed.

Ltac tac_wfl_to_slist := match goal with | 
    [ H: wflttC (ltt_send _ ?a) |- SList ?a] =>
    apply wfltt_slist_send in H;easy
    | [ H: wflttC (ltt_recv _ ?a) |- SList ?a] =>
    apply wfltt_slist_recv in H;easy
    end.

Lemma step_assoc_inv: forall g g' p q ell' s1 gamma xs Tp, 
wfgC g->
gttstepC g g' p q ell'  -> assoc gamma g -> 
M.find p gamma = Some (ltt_send q xs) -> onth ell' xs =Some (s1, Tp) -> tctx_wf gamma -> 
(
    exists ys s2 Tq, M.find q gamma = Some (ltt_recv p ys) /\ onth ell' ys =Some (s2,Tq) /\
    subsort s1 s2
).
Proof.
    intros.
    rename H4 into Htcwf.
    pose proof H1 as Hassoc.
    pose proof H1 as Hprojectable.
    apply assoc_implies_projectable in Hprojectable;try easy.
    pose proof H as Hwfg.
    pose proof H0 as Hstep.
    unfold assoc in Hassoc. specialize (Hassoc p) as Hasp. specialize (Hassoc q) as Hasq.
    assert (Hp:isgPartsC p g).
    {
           eapply wfgC_step_part with (G':=g') (q:=q) (n:=ell');try easy.
    } 
    assert (Hq:isgPartsC q g).
    {
        pinversion Hstep;try apply step_mon;subst.
        apply decidable_helper.triv_pt_q;try easy.
        pose proof Hwfg as Hwfg2.
        apply wfg_implies_slis in Hwfg. apply slist_implies_some in Hwfg.
        destr_hyps.
        eapply Forall_prop with (l:=x) (p:=x0) in H10;try easy.
        destruct H10;try easy.
        destr_hyps.
        inversion H10;subst.
        eapply part_parent with (k:=x) (s:=x1) (G_k:=x2);try easy.   
    }
    apply proj_cont_pq_step in Hstep;try easy.
    destr_hyps.
    pose proof Hp as Hp2.
    apply H7 in Hp. destr_hyps.
    rewrite H2 in H12;inversion H12;subst.
    pose proof Hq as Hq2.
    apply H5 in Hq. destr_hyps.
    clear H5 H6 H7 H8.
    unfold issubProj in H15. destr_hyps.
    apply proj_inj with (t:=x6) in H9;subst;try easy.
    apply subtype_recv_inv2 in H6. destr_hyps;subst.
    unfold tctx_wf in Htcwf.
    specialize (Htcwf p (ltt_send q xs)) as Slis1.
    specialize (Htcwf q (ltt_recv p x6)) as Slis2.
    destr_hyps.
    assert (Hslis1: SList xs ) by  (eapply wfltt_slist_send;apply Slis1;easy).
    assert (Hslis2: SList x6 ) by  (eapply wfltt_slist_recv;apply Slis2;easy).
    pose proof H2 as H22.
    eapply assoc_inv_find with (g:=g) in H2;try easy.
    pose proof H14 as H214.
    eapply assoc_inv_find with (g:=g) in H14;try easy.
    eapply simul_subproj with (xp:=xs) in H14;try easy.
    eapply Forall2R_prop with (l:=ell') (p:=(s1,Tp)) in H14;try easy.
    destr_hyps.
    destruct H7;try easy.
    destr_hyps. inversion H7;subst.
    exists x6, x9, x10. easy.
Qed.

Lemma projectable_after_step : forall g g' p q ell, wfgC g -> projectableA g -> gttstepC g g' p q ell -> projectableA g'.
Proof.
    unfold projectableA; intros.
    pose proof H0 as Hproj.
    assert ( p <> q) by (pinversion H1;crush;apply step_mon).   
    specialize (H0 pt);destr_hyps.
    (*Search projectionC gttstepC.*)
    destruct (Nat.eq_dec p pt);
    destruct (Nat.eq_dec q pt);crush.
    eapply proj_cont_pq_step_full in H1;crush; exists x0; easy.
    eapply proj_cont_pq_step_full in H1;crush; exists x1; easy.
    pose proof H1 as Hstep.
    
    pose proof Hstep as Hstep'. eapply proj_cont_pq_step in Hstep';try easy.
    destr_hyps.
    apply wfgC_after_step in H1;try easy.
    eapply typ_after_step_3_helper with (s:=pt) (T:=x) (L1:=x0) (L2:= x1)
    (LS:=x2) (LT:=x4) (LS':= x3) (LT':=x5) in Hstep;try easy.
    destr_hyps. exists x6;try easy.
Qed.

Lemma Forall_onth: forall (gcs1:list (option(sort*gtt))), 
Forall (fun u=> u=None \/ exists k, onth k gcs1=u) gcs1.
Proof.
    induction gcs1;constructor.
    destruct a; [right; exists  0 | left ];crush.
    set (P:=(fun u : option (sort * gtt) =>
u = None \/ (exists k : opt_lbl, onth k gcs1 = u))).
    eapply Forall_impl with (P:=P); unfold P in *;crush.
    destruct (onth x gcs1) eqn:Hyg;[
    eapply Forall_prop with (l:=x) (p:=p) in IHgcs1|];crush.
    right; exists (S x0); crush.
Qed.


Lemma assoc_soundness': forall G G' gamma  p q ell xs, p <> q -> wfgC G -> isgPartsC p G ->
tctx_wf gamma -> M.find p gamma =Some (ltt_send q xs) ->
assoc gamma G -> 
gttstepC G G' p q ell -> 
forall ell', onth ell' xs <> None ->
exists gamma' G'',
gttstepC G G'' p q ell' /\ assoc gamma' G'' /\ tctxR gamma (lcomm p q ell') gamma'.
Proof.
    intros * Hpq Hwf Hispartsp Htwf Hfindp Hassoc Hstep * Honth.
    assert(Hprojable: projectableA G) by (eapply assoc_implies_projectable in Hassoc;try easy).
    assert(Hslist: SList xs).
    {
        specialize (Htwf p _ Hfindp).
        pinversion Htwf;try easy.   
    }
    assert(exists xsp, projectionC G p (ltt_send q xsp)).
    {
        eapply proj_cont_pq_step in Hstep;try easy;destr_hyps.
        exists x. easy.   
    }
    destruct H as [xsp Hprojp].
    
    assert(exists xsq, projectionC G q (ltt_recv p xsq)).
    {
        eapply proj_cont_pq_step in Hstep;try easy;destr_hyps.
        exists x0. easy.   
    }
    destruct H as [xsq Hprojq].
    
    eapply assoc_inv_find in Hassoc as Hinf;try exact Hfindp;try easy.
    red in Hinf;destr_hyps.
    eapply proj_inj in H;try exact Hprojp;try easy;subst.
    eapply subtype_send_inv in H0.
    eapply opt_lem1 in Honth;destr_hyps.
    eapply Forall2R_prop in H0;try exact H;destr_hyps.
    destruct H1;try easy;destr_hyps;subst.
    inversion H1;subst;clear H1.
    eapply projection_step_label_s in Hprojq as Honth3;try exact Hprojp;
    try exact H2;try easy. destr_hyps.
    eapply typ_after_step_step in Hwf as Hstep2;try exact Hprojp;
    try exact Hprojq;try exact H2;try exact H0;destr_hyps.
    clear H1. rename H6 into Hispartsq, x5 into G''.
    pose proof Hassoc as Hassoc'.
    specialize (Hassoc q) as [Hsq0 _];specialize (Hsq0 Hispartsq).
    destruct Hsq0 as [Tq [Hfindq Hsubq]].
    red in Hsubq;destr_hyps;try easy. eapply proj_inj in H1;try exact Hprojq;subst;try easy.
    eapply subtype_recv_inv2 in H6 as ?H;destr_hyps;subst.
    eapply subtype_recv_inv in H6;try easy.
    eapply Forall2R_prop in H6;try exact H0;try easy.
    destr_hyps. destruct H6;try easy. destr_hyps. inversion H6;subst. clear H6.
    assert(Hsubs: subsort x2 x7).
    {
        (*Search subsort onth gtt_send.*)
        eapply canon_rep_s in Hwf;try exact Hprojp;try exact Hprojq;try exact H0;try exact H2;
        destr_hyps.
        eapply sstrans;try exact H13;easy.
    }
    eapply context_red_simple_comm with (p:=p) (q:=q) (gamma' := 
    M.remove p (M.remove q gamma)
    ) in H as Hcr;try exact H7;try easy;
    try solve [autorewrite with mmaps;easy
        | eapply sstrans; try exact H3; eapply sstrans;try exact Hsubs;try easy
    ].
    assert(Hwfg'' : wfgC G'') by (eapply wfgC_after_step;try exact H5;try easy).
    exists (M.add p x3 (M.add q x10 (M.remove p (M.remove q gamma)))), (G'').
    split;try easy.
    split.
    {
        red;intros;split;intros Hp0 *.
        {
            destruct (Nat.eq_dec p p0);   
            destruct (Nat.eq_dec q p0);subst;try easy.
            {
                autorewrite with mmaps. exists x3;split;try easy.
                red.
                eapply projection.typ_after_step_12_helper in H5;try exact Hprojp;try exact Hprojq;try exact H2;try exact H0;
                try easy. destr_hyps.
                exists x4.
                split;try easy.
            }
            {   
                autorewrite with mmaps. exists x10;split;try easy.
                red.
                eapply projection.typ_after_step_12_helper in H5;try exact Hprojp;try exact Hprojq;try exact H2;try exact H0;
                try easy. destr_hyps.
                exists x9.
                split;try easy.
            }
            {
                
                assert (Hisparts2: isgPartsC p0 G).
                {
                    destruct (decidable.decidable_isgPartsC G p0);try easy.
                    eapply not_part_step with (g':=G'') (g:=G) in Hp0;try exact H5;try easy.
                }
                

                specialize (Hassoc' p0) as [Hsc _].
                specialize (Hsc Hisparts2);destr_hyps.
                red in H6;destr_hyps.
                eapply typ_after_step_3_helper with (G':=G'') (s:=p0) in Hwf as Hr;try 
                exact Hprojp;try exact Hprojq; try exact H0;try exact H2;
                try exact H1;try exact H6;try easy.
                destr_hyps;subst. 
                autorewrite with mmaps.
                exists x. split;try easy.
                
                red;intros. exists x6. split;easy.   
            }
        }
        {
            destruct (Nat.eq_dec p p0);   
            destruct (Nat.eq_dec q p0);subst;try easy;autorewrite with mmaps;intros;
            inversion H1;subst;clear H1.
            {
                eapply projection.typ_after_step_12_helper in H5;try exact Hprojp;try exact Hprojq;try exact H2;try exact H0;
                try easy. destr_hyps.
                pinversion H1;try apply proj_mon;subst;try easy.
                eapply subtype_end_inv in H4. easy. 
            }
            {
                eapply projection.typ_after_step_12_helper in H5;try exact Hprojp;try exact Hprojq;try exact H2;try exact H0;
                try easy. destr_hyps.
                pinversion H5;try apply proj_mon;subst;try easy.
                eapply subtype_end_inv in H9. easy. 
            }
            {
                destruct (decidable.decidable_isgPartsC G p0);try easy.
                specialize (Hprojable p0) as Hprojp0;destr_hyps.
                eapply part_after_step_r with (r:=p0) in H5 as Hisp2;try exact H6;
                try easy.
                specialize (Hassoc' p0).
                destr_hyps. specialize (H11 H1). eapply H11;easy.
            }
        }
    }
    {
        eapply Rstruct;try exact Hcr;try easy.
        red;intros;destruct (Nat.eq_dec y p);destruct (Nat.eq_dec y q);subst;
        autorewrite with mmaps;try easy.
    }
Qed.


Lemma assoc_soundness : forall G G' gamma  p q ell, p <> q -> wfgC G -> 
tctx_wf gamma ->
assoc gamma G -> 
gttstepC G G' p q ell -> 
exists gamma' G'' ell',
gttstepC G G'' p q ell' /\ assoc gamma' G'' /\ tctxR gamma (lcomm p q ell') gamma'.
Proof.
    intros G G' gamma p q ell H H0 H2 H3 H4.
    assert (H1: isgPartsC p G) by 
    (eapply wfgC_step_part with (G':=G') (q:=q) (n:=ell);try easy).
    pose proof H1 as Hisparts.
    pose proof H2 as Hwf.
    pose proof H4 as Hstep.
    pose proof H3 as Hassoc.
    apply assoc_implies_projectable in Hassoc;try easy.
    apply proj_cont_pq_step in H4;try easy.
    destr_hyps.
    unfold assoc in H3. specialize (H3 p) as Hap.
    destr_hyps.
    apply H8 in H1.
    destr_hyps.
    unfold issubProj in H10.
    destr_hyps.
    eapply proj_inj with (t:=x6) in H4; try easy;subst.
    apply subtype_send_inv2 in H11.
    destr_hyps;subst.
    unfold tctx_wf in H2. specialize (H2 p (ltt_send q x6)).
    destr_hyps.
    pose proof H1 as H12.
    apply H2 in H1.
    apply wfltt_slist_send in H1.
    apply slist_implies_some in H1.
    destr_hyps.
    rename x6 into xss, x5 into ell'.
    apply opt_lem2 in H1.
    eapply assoc_soundness' with (ell':=ell') (xs:=xss) (gamma:=gamma) in Hstep;try easy.
    destruct Hstep as [gamma' [G'' Hstep]].
    exists gamma', G'', ell'. easy.
Qed.
