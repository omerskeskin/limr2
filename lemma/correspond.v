(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.wfltt src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable.
From SST Require Import src.step lemma.step src.assoc.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
From Coq Require Import IndefiniteDescription.

Import ListNotations.

Create HintDb mmaps. 
Hint Rewrite (@M.add_spec1 ) (@M.add_spec2) (@M.remove_spec1)
    (@M.remove_spec2) (@M.empty_spec) using easy : mmaps.


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


Definition tctx_wf (g:tctx):= forall p l, 
(M.find p g = Some l -> wflttC l).

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

(*
Lemma projection_implies_slist_helper : forall xs xs0 r, Forall2
(fun (u : option (sort * gtt))
(v : option (sort * ltt)) =>
u = None /\ v = None \/
(exists (s : sort) (g : gtt) (t : ltt),
u = Some (s, g) /\
v = Some (s, t) /\
upaco3 projection bot3 g r t)) xs0 xs -> SList xs0 -> SList xs.
Proof.
    induction xs.
    {
        intros.
        eapply slist_implies_some in H0;inversion H;crush.
        destruct x;crush.
    }
    {
        intros.
        destruct xs0.
        + inversion H0.
        + inversion H;subst.
        destruct o. .
        {
            destruct H4;try easy.
            destruct xs0. inversion H6;subst. crush.
            assert (SList xs).
            {
                eapply IHxs with (r:=r) (xs0:=xs0).
                simpl in H0.   
            }   
        }
        destruct a;destruct o;crush.   
    }
Qed.
*)
Lemma projection_implies_wf : 
    forall g r t,    wfgC g -> projectionC g r t ->
    wflttC t.
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

Search projectionC Forall. 
Lemma proj_implies_subproj : forall g p t, projectionC g p t -> issubProj t g p.
Proof.
    intros. unfold issubProj. exists t;split;try apply stRefl;try easy.
Qed.
Print SList.

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
        Search isgPartsC gttstepC.
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
    Search isMerge onth.
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
    Search "proj" "cont".
    unfold issubProj in *. destr_hyps.
    pose proof H5 as Hstep.
    eapply proj_cont_pq_step in H5;try easy.
    destr_hyps. 
    Search "typ_after_step_3".
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
    Check projection.typ_after_step_12_helper.
    intros.
    pose proof H6 as Hstep.
    eapply proj_cont_pq_step in H6;try easy. destr_hyps. 
    unfold issubProj in *. destr_hyps.
    eapply proj_inj with (t:=x6) in H6;try easy;subst.
    eapply proj_inj with (t:=x5) in H7;try easy;subst.
    rename x into xsp', x0 into xsq',x3 into Tp', x4 into Tq'.
    Check typ_after_step_3_helper.
    
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
    Check decidable_isgPartsC.
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
    eapply lem_6_16_simul_subproj with (xp:=xs) in H14;try easy.
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
    Search projectionC gttstepC.
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
    intros.
    pose proof H4 as Hprojectable. apply assoc_implies_projectable in Hprojectable;try easy.
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
        Search SList ltt.
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
                    apply subproj_inv_send in Hsubp;try easy;try tac_wfl_to_slist.
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
                    apply subproj_inv_recv in Hsubq;try easy;try tac_wfl_to_slist.
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
        (*construct gcs'', together with the proof, inductively*)

        assert(extract_just_gtt: forall s4 k g_k, onth k gcs = Some (s4,g_k) -> 
            {u:gtt| gttstepC g_k u p q ell'}).
        {
            intros.
            apply extract_gamma_props_simple in H12.
            destruct H12.
            destruct x as [[[d1 d2] d3] d4].
            exists d4. easy.
        }
       
        Print projection.
        Search SList projectionC.
        assert(create_gcs'' : forall gcs1 
        (Hsubset: Forall (fun u=> u=None \/ exists k, onth k gcs=u) gcs1), 
        exists gcs'' ,
            Forall2
            (fun u v : option (sort * gtt) =>
            u = None /\ v = None \/
            (exists (s0 : sort) (g g' : gtt),
            u = Some (s0, g) /\
            v = Some (s0, g') /\
            upaco5 gttstep bot5 g g' p q ell')) gcs1 gcs'' 
            /\ 
            (
            forall xsp xsq Tp Tq s1 s2, M.find p gamma=Some (ltt_send q xsp) ->
            M.find q gamma=Some (ltt_recv p xsq) ->
            onth ell' xsp= Some (s1, Tp) ->
            onth ell' xsq =Some (s2, Tq) ->
            Forall (fun u=> u=None \/ 
            (exists s4 g_k, u=Some (s4,g_k)  /\ issubProj Tp g_k p /\ issubProj Tq g_k q)) gcs'')
            /\
            (forall r, r <> p  -> r <> q ->  
            Forall2 (fun u v=> u=None /\ v=None \/ exists s4 g_k g_k', u=Some (s4,g_k) /\
            v=Some(s4,g_k') /\ (~isgPartsC r g_k' -> ~isgPartsC r g_k) /\
            forall gr, (issubProj gr g_k r ->issubProj gr g_k' r))
            gcs1 gcs'') 
            /\
            (forall xsp xsq, M.find p gamma=Some (ltt_send q xsp) ->
            M.find q gamma=Some (ltt_recv p xsq) ->
            Forall2 (fun u v=> u=None /\ v=None \/ exists s4 g_k g_k', u=Some (s4,g_k) /\
            v=Some(s4,g_k') /\ (~isgPartsC p g_k' -> onth ell' xsp=None \/  exists s5, onth ell' xsp= Some (s5,ltt_end)) /\
            (~isgPartsC q g_k' -> onth ell' xsq=None \/ exists s5, onth ell' xsq= Some (s5,ltt_end)))
            gcs1 gcs'')
            /\ (forall r, r<>p -> r <> q  -> 
            Forall2 (fun u v=> u=None /\ v=None \/ exists s4 g_k g_k', u=Some (s4,g_k) /\
            v=Some(s4,g_k') /\ 
            (~isgPartsC r g_k' -> ~ isgPartsC r g_k))
            gcs1 gcs''
            )
        ).
        {
            intros.
            induction gcs1.
            {
                exists [].
                repeat (try split); try intros;try constructor.
            }
            {
                pose proof Hsubset as Hsubset'.
                inversion Hsubset;subst.
                apply IHgcs1 in H21.
                clear gamma_k_props_2 gamma_props_simple Hpsame Hchild_proj_1 IHgcs1.
                destruct a.
                {
                    destruct H14;try easy.
                    destruct H12 as [k Honthk].
                    
                    destruct p0 as [s4 g_k].
                    pose proof Honthk as Honthk'.
                    eapply extract_gamma_props_simple in Honthk.
                    destruct Honthk.
                    destruct x as [ [[ext_s ext_t] ext_tcx] ext_g].
                    destruct H21 as [grest [Hrest]].
                    
                    assert(Hwfg_gk: wfgC g_k).
                    {
                        eapply continuation_wfgC with (p:=s) (q:=t) (xs:=gcs) (n:=k) (s:=s4);try easy.   
                    }
                    assert(Hproj_gk: projectableA g_k). 
                    {
                        pose proof Hprojectable as Hprj.
                        eapply proj_forward in Hprj;try easy.
                        eapply Forall_prop with (l:=k) (p:=(s4,g_k)) in Hprj;try easy.
                        destruct Hprj;try easy.
                        destr_hyps.
                        inversion H13;subst;easy.
                    }
                    assert(Hwfg_ext: wfgC ext_g).
                    {
                        destr_hyps.
                        eapply wfgC_after_step in H27;try easy.
                    } 

                    assert (Hgamma_k_same: forall Gks Gkt p, 
                    p <> s -> p <> t ->
                    M.find p (create_gamma_k s t Gks Gkt gamma) =M.find p gamma).
                    {
                        intros.
                        unfold create_gamma_k. rewrite M.add_spec2;try 
                        rewrite M.add_spec2;try rewrite M.remove_spec2;try rewrite M.remove_spec2;try easy.
                    }
                    
                    assert(Hproj_p_same: forall xs, M.find p gamma = Some (ltt_send q xs) -> issubProj (ltt_send q xs) g_k p).
                    {
                        (*this can also be proven via subproj_cont lemma*)
                        intros.
                        assert (SList xs).
                        {
                            unfold tctx_wf in H4. Check H4. specialize H4 with (p:=p) (q:=q) (xs:=xs). destr_hyps.
                            
                            apply H4. easy.
                        }
                        eapply assoc_inv_find with (g:=(gtt_send s t gcs)) in H13; try easy.
                        eapply subproj_after_cont_send with (p:=s) (q:=t) (gcs:=gcs) (s:=s4) (k:=k);try easy.
                        Search wfgC gcs.
                        pose proof H2 as Hwfg.
                        apply decidable.decidable_isgPartsC with (pt:=p) in Hwfg.
                        destruct (Hwfg);try easy.
                        apply not_part_proj in H21.
                        unfold issubProj in H13.
                        destr_hyps.
                        apply subtype_send_inv1 in H22. destr_hyps. subst. 
                        apply proj_inj with (t:=ltt_end) in H13; try easy.
                    }
                    assert(Hproj_q_same: forall xs, M.find q gamma = Some (ltt_recv p xs) -> issubProj (ltt_recv p xs) g_k q).
                    {
                        (*this can also be proven via subproj_cont lemma*)
                        intros.
                        assert (SList xs).
                        {
                            unfold tctx_wf in H4. Check H4. specialize H4 with (p:=q) (q:=p) (xs:=xs). destr_hyps.
                            
                            apply H31. easy.
                        }
                        eapply assoc_inv_find with (g:=(gtt_send s t gcs)) in H13; try easy.
                        Check subproj_after_cont_send.
                        eapply subproj_after_cont_recv with (p:=s) (q:=t) (gcs:=gcs) (s:=s4) (k:=k);try easy.
                        Search wfgC gcs.
                        pose proof H2 as Hwfg.
                        apply decidable.decidable_isgPartsC with (pt:=q) in Hwfg.
                        destruct (Hwfg);try easy.
                        apply not_part_proj in H21. 
                        unfold issubProj in H13.
                        destr_hyps.
                        apply subtype_recv_inv1 in H22. destr_hyps. subst. 
                        apply proj_inj with (t:=ltt_end) in H13; try easy.
                    }
                    destr_hyps.
                    pose proof H27 as Hgk_extg_step.
                    eapply proj_cont_pq_step in Hgk_extg_step;try easy.
                    destruct Hgk_extg_step as [LP [LQ Hgk_projs]].
                    destr_hyps. 
                    
                    exists (Some (s4,ext_g)::grest).
                    repeat (try split).
                    {
                        constructor.
                        right. exists s4,g_k, ext_g.
                        split; split;try easy.
                        unfold upaco5.
                        left. destr_hyps. assumption.
                        assumption.
                    }
                    {
                        intros.
                        constructor.
                        {
                            right. exists s4, ext_g.
                            split;try easy.
                            
                            eapply subproj_after_step1 with (ell':= ell') (xsp:=xsp) (xsq:=xsq) (G:=g_k) (s1:=s1) (s2:=s2); try easy.
                            apply Hproj_p_same in H34; try easy. 
                            apply Hproj_q_same in H35; try easy.
                            
                        }
                        {
                            eapply H12 with (xsp:=xsp) (xsq:=xsq) (s1:=s1) (s2:=s2);try easy.
                        }
                    }
                    {
                        intros.
                        constructor.
                        {
                            right. exists s4, g_k, ext_g. split;try split;try easy.
                            split.
                            {
                                unfold not.
                                intros.
                                apply H36.
                                unfold projectableA in Hproj_gk.
                                specialize (Hproj_gk r). destr_hyps.
                                eapply part_after_step_r with (p:=p) (q:=q) (G:=g_k) (l:=ell') (T:=x3); try easy.
                            }
                            {
                                intros.   
                                unfold issubProj in H36.
                                unfold issubProj. destr_hyps. exists x3.
                                split;try easy.
                                Search gttstepC projectionC.
                                pose proof H27 as Hgk_extg_step.
                                eapply typ_after_step_3_helper with (s:=r) (T:=x3) (L1:=LP) (L2:=LQ) (LS:=x)
                                (LS':=x0) (LT:=x1) (LT':=x2)
                                in Hgk_extg_step; try easy.
                                destr_hyps. 
                                subst.
                                easy.
                            }
                        }
                        {
                            eapply H13;try easy.   
                        }
                    }
                    {
                        intros.
                        constructor.
                        {
                            right. exists s4, g_k, ext_g. split;try split;try easy.
                            split.
                            {
                                intros.
                                pose proof H28 as Hex_assoc.   
                                pose proof H29 as Hex_red.
                                destruct (onth ell' xsp) eqn:Hyg1.
                                {
                                    right.
                                    destruct p0 as (s5,lct).
                                    exists s5.
                                    assert (lct=ltt_end).
                                    {
                                        apply lem_6_11c_tctx_comm_invert in Hex_red.
                                        destr_hyps.
                                        rewrite Hgamma_k_same in H37;try easy.
                                        unfold assoc in Hex_assoc.
                                        specialize (Hex_assoc p).
                                        destr_hyps.
                                        eapply H45 with (Tpx:=x6) in H36;try easy.
                                        crush.
                                    }
                                    rewrite H37;easy.   
                                }
                                left. easy.
                            }   
                            {
                                intros.
                                pose proof H28 as Hex_assoc.   
                                pose proof H29 as Hex_red.
                                destruct (onth ell' xsq) eqn:Hyg1.
                                {
                                    right.
                                    destruct p0 as (s5,lct).
                                    exists s5.
                                    assert (lct=ltt_end).
                                    {   
                                        apply lem_6_11c_tctx_comm_invert in Hex_red.
                                        destr_hyps.
                                        rewrite Hgamma_k_same in H38;try easy.
                                        unfold assoc in Hex_assoc.
                                        specialize (Hex_assoc q).
                                        destr_hyps.
                                        eapply H45 with (Tpx:=x8) in H36;try easy.
                                        crush.
                                    }
                                    rewrite H37;easy.   
                                }
                                left. easy.
                            }
                        }
                        eapply H14;try easy.
                    }
                    {
                        intros.
                        constructor.
                        {
                            right. exists s4, g_k, ext_g.
                            split;try split;try easy. intros.
                            unfold not. intros. apply H36.
                            Search gttstepC isgPartsC.
                            unfold projectableA in Hproj_gk. specialize (Hproj_gk r). 
                            destruct Hproj_gk as [TT Hproj_gk].
                            eapply part_after_step_r with (G:=g_k) (p:=p) (q:=q) (l:=ell') (T:=TT);try easy.
                        }
                        eapply H21;try easy.   
                    }
                }
                {
                    destruct H21 as [grest [Hrest1 [Hrest2 [Hrest3 [Hrest4 Hrest5]]]]].
                    exists (None::grest).
                    repeat (try split).
                    {
                        constructor. left. easy.
                        destr_hyps.
                        assumption.
                    }
                    {
                        intros.
                        constructor. left. easy.
                        eapply Hrest2 with (xsp:=xsp) (xsq:=xsq) (s1:=s1) (s2:=s2);try easy.
                    }
                    {
                        intros. constructor. left. easy.   
                        eapply Hrest3; try easy.
                    }
                    {
                        intros. constructor. left. easy.
                        eapply Hrest4;try easy.   
                    }
                    {
                        intros. constructor. left. easy.
                        eapply Hrest5;try easy.
                    }
                }
            }
        }
        
        set (gcs'':= create_gcs'' gcs (Forall_onth gcs)).
        destruct gcs'' as [gcs'' [Hgcs''_1 [Hgcs''_2 [Hgcs''_3  [Hgcs''_4 Hgcs''_5]]]]].
        assert(gcs''_step : gttstepC (gtt_send s t gcs) (gtt_send s t gcs'') p q ell').
        {
            pfold. constructor;try easy.
        }
        assert(gcs''_wfg: wfgC (gtt_send s t gcs'')).
        {
            eapply wfgC_after_step with (G:=(gtt_send s t gcs)) (p:=p) (q:=q) (n:=ell');
            try easy.
        }
        assert (Hgcs''_nonemp: exists k s4 g_k, onth k gcs'' =Some (s4,g_k)).
        {
            apply wfg_implies_slis in gcs''_wfg.
            apply slist_implies_some in gcs''_wfg.
            destr_hyps. destruct x0. exists x, s0, g. easy.   
        }
        destruct Hgcs''_nonemp as [k [s4 [g_k Honthk]]].
        assert (projectableA (gtt_send s t gcs'')). eapply projectable_after_step with (g:=(gtt_send s t gcs)) (p:=p) (q:=q) (ell:=ell');try easy.
        (*by proj_cont_step_pq*)
        assert(exists xsp xsq s1 s2 Tp Tq, M.find p gamma = Some (ltt_send q xsp) /\ 
        M.find q gamma =Some (ltt_recv p xsq)
            /\ onth ell' xsp=Some (s1,Tp) /\
            onth ell' xsq=Some (s2,Tq) /\ 
            subsort s1 s2 
            /\ tctxR gamma (lcomm p q ell') (create_gamma_k p q Tp Tq gamma)
        ). 
        {
            Check step_assoc_inv.
            Search onth ell'.
            pose proof H6 as Hellnone. apply opt_lem1 in Hellnone.
            destruct Hellnone as [[s6 g1]].
            eapply step_assoc_inv with (gamma:=gamma) (xs:=xs0) (s1:=s6) (Tp:=g1) 
            in gcs''_step; try easy.
            destruct gcs''_step as [ys [s2 [Tq gcs''_step]]].
            exists xs0,ys,s6,s2,g1, Tq. repeat (try split);try easy.
            set (gamma_justpq := M.add p (ltt_send q xs0) (M.add q (ltt_recv p ys) M.empty)).
            set (gamma_nopq := M.remove p (M.remove q gamma)).
            set (gamma'_justpq:=M.add p g1 (M.add q Tq M.empty)).
            unfold create_gamma_k.
            fold gamma_nopq.
            assert(Heq_gamma: M.Equal gamma (M.add p (ltt_send q xs0)
            (M.add q (ltt_recv p ys) gamma_nopq))).
            {
                unfold M.Equal. intros. unfold gamma_nopq.
                destruct (Nat.eq_dec p y);destruct (Nat.eq_dec q y);crush.
                + rewrite M.add_spec1. easy.
                + rewrite M.add_spec2;try easy. rewrite M.add_spec1. easy.
                +   rewrite M.add_spec2. rewrite M.add_spec2.
                rewrite M.remove_spec2. rewrite M.remove_spec2. all:easy.
            }
            setoid_rewrite Heq_gamma.
            eapply context_red_simple_comm with (s:=s6) (s'':=s2);try easy;unfold gamma_nopq.
            apply M.remove_spec1. rewrite M.remove_spec2. rewrite M.remove_spec1.
            easy. easy. 
        }
        destr_hyps.
        rename x into xsp, x0 into xsq, x1 into s1, x2 into s2, x3 into Tp, x4 into Tq.
        assert(assoc (create_gamma_k p q Tp Tq gamma) (gtt_send s t gcs'')).
        {
            unfold assoc. intros r. split.
            {
                intros.
                destruct (Nat.eq_dec r p);   
                destruct (Nat.eq_dec r q);subst;try easy.
                {
                    exists Tp.
                    unfold create_gamma_k.
                    rewrite M.add_spec1.
                    split;try easy.
                    (*get proof from the extraction*)
                    eapply Hgcs''_2 with (xsp:=xsp) (xsq:=xsq)
                    (Tp:=Tp) (Tq:=Tq) (s1:=s1)
                    in H22;try easy.
                    
                    eapply Forall_prop  with (l:=k) (p:=(s4,g_k)) in H22;try easy.
                    destruct H22;try easy.
                    destr_hyps.
                    inversion H22;subst.
                    eapply subproj_cont_implies_subproj_parent with
                    (g_k:=x0) (k:=k) (s4:=x);try easy.
                    (*eapply subproj_cont_implies_subproj_parent with (s:=s) (t:=t) in H22 ;try easy. 
                *)
                }
                {
                    exists Tq.
                    unfold create_gamma_k.
                    rewrite M.add_spec2;try rewrite M.add_spec1;try easy.
                    split;try easy.
                    (*get proof from the extraction*)
                    eapply Hgcs''_2 with (xsp:=xsp) (xsq:=xsq)
                    (Tp:=Tp) (Tq:=Tq) (s1:=s1)
                    in H22;try easy.
                    (*eapply subproj_cont_implies_subproj_parent with (s:=s) (t:=t) in H22 ;try easy.*)
                    
                    eapply Forall_prop  with (l:=k) (p:=(s4,g_k)) in H22;try easy.
                    destruct H22;try easy.
                    destr_hyps.
                    inversion H22;subst.
                    eapply subproj_cont_implies_subproj_parent with (p:=q) 
                    (g_k:=x0) (k:=k) (s4:=x);try easy.
                }
                {
                    Search r.
                    assert (Hisparts: isgPartsC r (gtt_send s t gcs)).
                    {
                        Check part_after_step.
                        pose proof gcs''_step as gcs''_step2.
                        Search gttstepC projectionC.
                        eapply proj_cont_pq_step in gcs''_step2;try easy.
                        destr_hyps.
                        eapply part_after_step with 
                        (G:=(gtt_send s t gcs)) (G':= (gtt_send s t gcs'')) (LQ:=x0) (LP:=x) (p:=q) (q:=p) (l:=ell');try easy.   
                    }
                    pose proof H5 as Hassoc.
                    unfold assoc in Hassoc.
                    specialize (Hassoc r).
                    destr_hyps.
                    apply H28 in Hisparts.
                    destr_hyps.
                    exists x.
                    unfold create_gamma_k.
                    rewrite M.add_spec2;try rewrite M.add_spec2;try rewrite M.remove_spec2;
                    try rewrite M.remove_spec2;try easy.
                    split;try easy.
                    eapply subproj_after_step_r with (r:=r) (x:=x) in gcs''_step;try easy.
                }
            }
            {
                intros.
                destruct (Nat.eq_dec r p);
                destruct (Nat.eq_dec r q);subst;try easy.
                {
                    unfold create_gamma_k in H28;rewrite M.add_spec1 in H28; inversion H28;subst.
                    eapply Hgcs''_4 with (xsq:=xsq) in H13;try easy.
                    eapply Forall2_prop_l with (l:=k) (p:=(s4,g_k)) in H13;try easy.
                    destr_hyps.
                    destruct H29;try easy. destr_hyps.
                    apply eq_sym in H30;inversion H30;subst.
                    assert (~isgPartsC p g_k). 
                    {
                        eapply not_part_step with (g:=gtt_send s t gcs'') (p:=s) (q:=t) (k:=k);try easy.
                        pfold. eapply steq with (s:=s4); try easy.
                    }
                    apply H31 in H13.
                    destruct H13;destr_hyps; rewrite H21 in H13;try easy.
                    inversion H13;easy.
                }

                {
                    unfold create_gamma_k in H28;
                    rewrite M.add_spec2 in H28;try  rewrite M.add_spec1 in H28;try easy. 
                    inversion H28;subst; try easy.
                    eapply Hgcs''_4 with (xsp:=xsp) in H14;try easy.
                    eapply Forall2_prop_l with (l:=k) (p:=(s4,g_k)) in H14;try easy.
                    destr_hyps.
                    destruct H29;try easy. destr_hyps.
                    apply eq_sym in H30;inversion H30;subst.
                    assert (~isgPartsC q g_k).
                    {
                        eapply not_part_step with (g:=gtt_send s t gcs'') (p:=s) (q:=t) (k:=k);try easy.
                        pfold. eapply steq with (s:=s4); try easy.
                    }
                    apply H32 in H14.
                    destruct H14;destr_hyps; rewrite H22 in H14;try easy.
                    inversion H14;easy.
                }
                {
                    specialize (Hgcs''_5 r n n0).
                    eapply Forall2_prop_l with (l:=k) (p:=(s4,g_k)) in Hgcs''_5;try easy.
                    destr_hyps.
                    destruct H30;try easy. destr_hyps.
                    assert(~ isgPartsC r g_k).
                    {
                        eapply not_part_step with (g:=gtt_send s t gcs'') (p:=s) (q:=t) (k:=k);try easy.
                        pfold. eapply steq with (s:=s4); try easy.
                    }  
                    apply eq_sym in H31;inversion H31;subst.
                    apply H32 in H33.
                    assert (~isgPartsC r (gtt_send s t gcs)).
                    {
                        unfold not.
                        destruct (Nat.eq_dec r s);
                        destruct (Nat.eq_dec r t);subst;try easy.
                        exfalso. apply H27. apply decidable_helper.triv_pt_p;try easy.
                        
                        exfalso. apply H27. apply decidable_helper.triv_pt_q;try easy.
                        intros. unfold not in H33.
                        apply H33.
                        unfold projectableA in Hprojectable. specialize (Hprojectable r). destr_hyps.
                        eapply part_after_step_r with (G:=gtt_send s t gcs) (p:=s) (q:=t) (l:=k) (T:=x);try easy.
                        eapply continuation_wfgC with (p:=s) (q:=t) (xs:=gcs) (n:=k) (s:=s4);try easy.
                        pfold. eapply steq with (s:=s4);try easy.
                    }
                    Search assoc gcs.
                    pose proof H5 as Hassoc.
                    unfold assoc in Hassoc. specialize (Hassoc r). destr_hyps.
                    eapply H35 with (Tpx:=Tpx) in H29. easy.
                    unfold create_gamma_k in H28; try rewrite M.add_spec2 in H28;
                    try rewrite M.add_spec2 in H28;
                    try rewrite M.remove_spec2 in H28;
                    try rewrite M.remove_spec2 in H28;try easy.
                }   
            }   
        }
        exists (create_gamma_k p q Tp Tq gamma), (gtt_send s t gcs'').
        destr_hyps. auto.
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
    unfold tctx_wf in H2. specialize (H2 p q x6).
    destr_hyps.
    pose proof H1 as H12.
    apply H2 in H1.
    apply slist_implies_some in H1.
    destr_hyps.
    rename x6 into xss, x5 into ell'.
    apply opt_lem2 in H1.
    eapply assoc_soundness' with (ell':=ell') (xs:=xss) (gamma:=gamma) in Hstep;try easy.
    destruct Hstep as [gamma' [G'' Hstep]].
    exists gamma', G'', ell'. easy.
Qed.
