(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.wfltt src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable lemma.soundness.
From SST Require Import src.step lemma.step src.assoc.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.

Import ListNotations.


Ltac tac_use_assoc Hassoc p Hisparts := 
    let Ha1:=fresh "Hassoc" in let Ha2:=fresh "Hassoc" in 
    let Ha3:=fresh "Hassoc" in
    pose proof Hassoc as Ha3;
    unfold assoc in Ha3;
specialize (Ha3 p); 
    destruct Ha3 as [Ha1 Ha2];
    let Har:=fresh "Hassoc_u" in 
try (specialize (Ha1 Hisparts) as Har;clear Ha2 Ha1);try (specialize (Ha2 Hisparts) as Har;clear Ha1 Ha2).


Section AssocCompletenessHelpers.
Variables (gamma: tctx) (g:gtt).
Hypothesis Hwfg : wfgC g.
Hypothesis Hassoc: assoc gamma g.

Lemma assoc_m : forall gamma', M.Equal gamma gamma' -> assoc gamma' g.
Proof.
    intros.
    unfold assoc in *.
    intros;split;intros;
    unfold assoc in Hassoc; specialize (Hassoc p) as Hap; 
    destruct Hap as [Hap0 Hap1];
    [
    apply Hap0 in H0;  destr_hyps;
    unfold M.Equal in H; specialize (H p); exists x
    | eapply Hap1 in H0 ];crush.
Qed.
Check Proper.



Lemma assoc_weakening: forall p, (~ isgPartsC p g) 
    -> assoc (M.add p ltt_end gamma) g.
Proof.
    intros * Hparts.
    unfold assoc in *.
    intros.
    destruct (Nat.eq_dec p p0);subst.
    split;crush;autorewrite with mmaps in H0;crush.
    split.
    {
        specialize (Hassoc p0) as Hap0. destruct Hap0 as [Hap01 Hap02].
        intros. apply Hap01 in H. destruct H as [Tp H]. destr_hyps.
        exists Tp. split;autorewrite with mmaps;easy.   
    }
    {
        intros. specialize (Hassoc p0) as Hap0. destruct Hap0 as [Hap01 Hap02].
        eapply Hap02 in H. exact H. autorewrite with mmaps in H0. easy.   
    }
Qed.

Lemma assoc_context_not_in_global_not_in : forall p, M.find p gamma = None ->
    ~isgPartsC p g.
Proof.
    intros * Hisfind.
    destruct (decidable.decidable_isgPartsC g p);try easy.
    unfold assoc in Hassoc. specialize (Hassoc p) as Hap. destruct Hap as [Hap0 Hap1].
    apply Hap0 in H. destr_hyps. crush.
Qed.

Lemma assoc_remove_none : forall p, M.find p gamma= None ->
assoc (M.remove p gamma) g.
Proof.
    intros p Hnone.
    unfold assoc. intros. split;intros;destruct (Nat.eq_dec p0 p);subst.
    {
        unfold assoc in Hassoc. specialize (Hassoc p) as Hap. destruct Hap as [Hap0 Hap1].
        apply Hap0 in H. crush.
    }
    {
        unfold assoc in Hassoc. specialize (Hassoc p0) as Hap. destruct Hap as [Hap0 Hap1].
        apply Hap0 in H. destr_hyps.
        autorewrite with mmaps. exists x. easy.
    }
    {
        autorewrite with mmaps in H0;easy.   
    }
    {
        unfold assoc in Hassoc. specialize (Hassoc p0) as Hap. destruct Hap as [Hap0 Hap1].
        autorewrite with mmaps in H0.
        apply Hap1 with (Tpx:=Tpx) in H;easy.
    }
Qed.

Lemma assoc_remove_end : forall p, M.find p gamma= Some ltt_end ->
assoc (M.remove p gamma) g.
Proof.
    intros p Hnone.
    unfold assoc; split; intros; destruct (Nat.eq_dec p0 p);subst;try easy.
    {
        eapply assoc_inv_find with (g:=g) in Hnone;try easy.
        red in Hnone.
        destr_hyps.
        eapply subtype_end_inv2 in H1;subst.
        eapply pmergeCR_s in H0;easy.
    }
    {
        tac_use_assoc Hassoc p0 H. 
        autorewrite with mmaps. easy.
    }
    {
        tac_use_assoc Hassoc p H. autorewrite with mmaps in H0. crush.   
    }
    {
        tac_use_assoc Hassoc p0 H. autorewrite with mmaps in H0. crush.   
           
    }
Qed.

Lemma assoc_remove_not_part : forall p, ~isgPartsC p g ->
assoc (M.remove p gamma) g.
Proof.
    intros p Hpart.
    unfold assoc; split; intros; destruct (Nat.eq_dec p0 p);subst;try easy.
    {
        tac_use_assoc Hassoc p0 H. destr_hyps. exists x. autorewrite with mmaps. crush.
    }
    {
        autorewrite with mmaps in H0. easy.
    }
    {
        tac_use_assoc Hassoc p0 H. autorewrite with mmaps in H0. crush.   
    }
Qed.
End AssocCompletenessHelpers.

Instance EqMEQ {A: Type} : Equivalence ( @M.Equal A).
Proof. apply MF.Equal_equiv. Qed.

#[export] Instance ASSMEQ {A: Type}: Proper (M.Equal ==> eq ==> (iff)) assoc.
Proof. unfold "==>"; red; intros;subst; split;intros; [ | symmetry in H];

eapply assoc_m with (g:=y0) in H;try easy.
Qed.

Definition partial_assoc (gamma:tctx) (g:gtt) :=
    forall p Tp, M.find p gamma = Some Tp -> issubProj Tp g p.
(*assoc = largest partial assoc*)

Lemma partial_assoc_strengthening: forall gamma p Tp g, wfgC g ->
M.find p gamma = None ->
partial_assoc (M.add p Tp gamma) g -> partial_assoc gamma g.
Proof.
    red. intros * Hwfg Hnone Hassoc. red in Hassoc. intros. specialize (Hassoc p0 Tp0).
    destruct (Nat.eq_dec p p0);subst; autorewrite with mmaps in Hassoc;crush.
Qed.

Lemma assoc_is_partial_assoc : forall gamma g,
wfgC g -> assoc gamma g -> partial_assoc gamma g.
Proof.
    intros * Hwfg Hassoc. red;intros. 
    specialize (Hassoc p). destruct (decidable_isgPartsC g p);try easy.
    {
        destr_hyps. specialize (H1 H0). crush.   
    }
    {
        destr_hyps. specialize (H2 H0 Tp). crush. red. exists ltt_end.
        split;[apply not_part_proj;easy|apply stRefl].   
    }
Qed.

Lemma assoc_to_partial_assoc_add : forall gamma p Tp g,
wfgC g->
M.find p gamma = None -> 
assoc (M.add p Tp gamma) g -> partial_assoc gamma g.
Proof.
    red. intros * Hwfg Hnone Hassoc *. red in Hassoc. specialize (Hassoc p0).
    destr_hyps. 
    destruct (decidable_isgPartsC  g p0);try easy.
    apply H in H1. destr_hyps. intros.
    destruct (Nat.eq_dec p p0);subst;autorewrite with mmaps in *;crush.
    intros.
    destruct (Nat.eq_dec p p0);subst;autorewrite with mmaps in *;crush.
    eapply H3 in H2;subst. red. exists ltt_end. split.
    apply not_part_proj;easy. apply stRefl.
Qed. 

Lemma partial_assoc_to_assoc : forall gamma g, wfgC g ->
partial_assoc gamma g -> (forall p, isgPartsC p g -> M.In p gamma) ->
assoc gamma g.
Proof.
    intros * Hwfg Hpassoc Hsubset.
    red. intros;split;intros.
    {
        red in Hpassoc.
        specialize (Hsubset p H). rewrite MF.in_find in Hsubset. apply opt_lem1 in Hsubset. destr_hyps.
        exists x. specialize (Hpassoc p x H0). easy.   
    }
    {
        red in Hpassoc.
        specialize (Hpassoc p Tpx H0). apply not_part_proj in H. red in Hpassoc. destr_hyps.
        eapply proj_inj in H;try exact H1;try easy;subst. apply subtype_end_inv in H2. easy.   
    }
Qed.

Lemma part_after_step_redux : forall g g' p q ell r, wfgC g -> projectableA g -> gttstepC g g' p q ell -> isgPartsC r g' 
-> isgPartsC r g.
Proof.
    intros.
    Search isgPartsC gttstepC.
    pose proof H1 as Hstep. eapply proj_cont_pq_step in Hstep;try easy.
    destr_hyps.
    eapply part_after_step with (G':=g') (q:=p) (p:=q) (l:=ell) (LP:=x) (LQ:=x0);try easy.
    
    eapply wfgC_after_step in H1;easy.
Qed.

#[export] Instance PASSMEQ {A: Type}: Proper (M.Equal ==> eq ==> (iff)) partial_assoc.
Proof. unfold "==>"; red; intros;subst; split;intros; [ | symmetry in H]; 
    red; intros; red in H0; specialize (H0 p Tp); apply H0;
    red in H; crush.    
Qed.

Lemma partial_assoc_extend: forall gamma g p T, partial_assoc gamma g -> M.find p gamma =None -> issubProj T g p -> 
partial_assoc (M.add p T gamma) g.
Proof. 
    intros * Hpassoc Hnone Hsubproj; red;intros;
    destruct (Nat.eq_dec p p0);subst; autorewrite with mmaps in H;crush.
Qed. 

Lemma partial_assoc_inv_send: forall p q xs gamma G,
wfgC G ->
SList xs ->
partial_assoc gamma G ->
M.find p gamma =Some  (ltt_send q xs)  ->
(exists ys : list (option (sort * gtt)), G = gtt_send p q ys /\ send_cond xs ys p) \/
(exists (s t : opt_lbl) (ys : list (option (sort * gtt))),
G = gtt_send s t ys /\ p <> s /\ p <> t /\ subproj_cont_cond (ltt_send q xs) ys p).
Proof.
    intros.
    pose proof H as Hwfg.
    apply decidable_isgPartsC with (pt:= p) in H.
    specialize (H1 p).
    
    destr_hyps.
    destruct H.
    eapply H1 in H2.
    apply subproj_inv_send in H2;crush.
    specialize (H1 _ H2).
    red in H1. destr_hyps. apply not_part_proj in H. 
    eapply proj_inj with (t:=ltt_end)in H1;try easy;subst.
    pinversion H3;apply sub_mon.
Qed.

Lemma partial_assoc_inv_recv: forall p q xs gamma G,
wfgC G ->
SList xs ->
partial_assoc gamma G ->
M.find p gamma =Some  (ltt_recv q xs)  ->(exists ys : list (option (sort * gtt)),
G = gtt_send q p ys /\ recv_cond xs ys p) \/
(exists (s t : opt_lbl) (ys : list (option (sort * gtt))),
G = gtt_send s t ys /\
p <> s /\ p <> t /\ subproj_cont_cond (ltt_recv q xs) ys p).
Proof.
    intros.
    pose proof H as Hwfg.
    apply decidable_isgPartsC with (pt:= p) in H.
    specialize (H1 p).
    
    destr_hyps.
    destruct H.
    eapply H1 in H2.
    apply subproj_inv_recv in H2;crush.
    specialize (H1 _ H2).
    red in H1. destr_hyps. apply not_part_proj in H. 
    eapply proj_inj with (t:=ltt_end)in H1;try easy;subst.
    pinversion H3;apply sub_mon.
Qed.

Lemma partial_assoc_simul_inv: 
    forall gamma g p q xp xq, 
    tctx_wf gamma ->
    wfgC g ->
    partial_assoc gamma g ->
    M.find p gamma = Some (ltt_send q xp) -> 
    M.find q gamma = Some (ltt_recv p xq) ->
    (
        exists xg, g=gtt_send p q xg /\
        send_cond xp xg p  /\
        recv_cond
        xq xg q
    )
    \/
    (
        exists s t xg, g=gtt_send s t xg /\
        p <> s /\ q <> t /\ 
        Forall (fun u=> u=None \/ exists s g, u=Some (s,g) /\ issubProj (ltt_send q xp) g p
        /\ issubProj (ltt_recv p xq) g q
        ) xg
    )
    .
Proof.
    intros * Htctx_wf Hwfg Hassoc Hfindp Hfindq.
    
    tac_tctx_wf_to_slist xp Htctx_wf Hfindp q.
    tac_tctx_wf_to_slist xq Htctx_wf Hfindq p.
    eapply  partial_assoc_inv_send with (G:=g) in Hfindp;try easy.
    eapply  partial_assoc_inv_recv with (G:=g) in Hfindq; try easy.
    destruct Hfindp;destruct Hfindq;crush.
    {

        left.
        exists x0. crush. 
        (*follows from the assumptions*)    
    }
    {
        right. rename x2 into s, x3 into t, x4 into xg. 
        exists s, t, xg. crush.
        eapply Forall_forall.
        intros.
        destruct x2;crush.
        right.
        destruct p0 as [s0 g].
        exists s0, g.
        Check Forall_forall.
        Search In onth.
        apply in_some_implies_onth in H7. destruct H7 as [n].
        split;try easy.   
        unfold subproj_cont_cond in H6, H8.
        inversion H3;subst;clear H3.
        split;
        [eapply Forall_prop with (l:=n) (p:=(s0,g)) in H8 |
        eapply Forall_prop with (l:=n) (p:=(s0,g)) in H6]; crush.
    }
Qed.
Lemma subproj_after_cont_wfltt: forall p q r gcs s gk Tp k,
    wflttC Tp ->
    wfgC (gtt_send p q gcs) ->
    issubProj Tp (gtt_send p q gcs) r -> 
    r <> p -> r<> q ->
    onth k gcs=Some (s,gk) -> issubProj Tp gk r.
Proof.
    intros.
    destruct (decidable_isgPartsC (gtt_send p q gcs) r);try easy.
    destruct Tp;
    [eapply subproj_inv_end in H1
    | apply wfltt_slist_recv in H; 
    eapply subproj_after_cont_recv with (p:=p) (q:=q) (gcs:=gcs) (k:=k) (s:=s)
    |apply wfltt_slist_send in H; 
    eapply subproj_after_cont_send with (p:=p) (q:=q) (gcs:=gcs) (k:=k) (s:=s)]; try easy.
    assert(isgPartsC r gk -> False) by 
    (intros; eapply part_parent with (k:=k) (gcs:=gcs) (p:=p) (q:=q) (s:=s) in H6;
    try easy).
    red in H1. destr_hyps. apply not_part_proj in H5. 
    eapply proj_inj with (t:=x) in H5;try easy;subst.
    apply subtype_end_inv in H7;subst.
    apply not_part_proj in H6. exists ltt_end. split;try easy;try apply stRefl.
Qed.

Lemma local_step_implies_global_step: forall g gamma gamma' p q ell,
    wfgC g -> projectableA g -> tctx_wf gamma -> partial_assoc gamma g -> tctxR gamma (lcomm p q ell) gamma' ->
    exists g', gttstepC g g' p q ell.
Proof.
    intros * Hwfg Hproj Hwflt Hassoc Hred.
    destr_hyps.
    eapply tctx_comm_invert in Hred.
    
    destruct Hred as [s [s' [Hred1 Hred2]]].
    destr_hyps.
    rename x into xsp, x1 into xsq, x0 into Tp, x2 into Tq.
     assert(Hsxsp: SList xsp).
        {

            eapply wfltt_slist_send with (p:=q).
            red in Hwflt.
            specialize (Hwflt p (ltt_send q xsp) H). easy.
        }
        assert(Hsxsq : SList xsq).
        {
            eapply wfltt_slist_recv with (p:=p).
            red in Hwflt.
            specialize (Hwflt q _ H0). easy.   
        }
    rename H into Hfindp, H0 into Hfindq.
    (*projection_step_label_s*)
    specialize (Hassoc p _ Hfindp) as Hsubp.
    specialize (Hassoc q _ Hfindq) as Hsubq.
    pose proof Hsubp as Hsubp1.
    pose proof Hsubq as Hsubq1.
    red in Hsubp, Hsubq. destr_hyps.
    eapply subtype_send_inv1 in H7 as Hs1. eapply subtype_recv_inv1 in H6 as Hs2. destr_hyps;subst.
    assert(exists ss Tt, onth ell x2=Some (ss,Tt)).
    {
        apply subtype_send_inv in H7.
        eapply Forall2R_prop with (l:=ell) (p:=(s,Tp)) in H7.
        destr_hyps.
        destruct H8;try easy. destr_hyps. inversion H8;subst. exists x3, x5.
        all:easy.
    }
    destr_hyps.
    eapply (projection_step_label_s) with (l:=ell) (LP:=x2) (ST:=(x,x0)) in H as Hpp;try easy.
    destr_hyps.
    eapply typ_after_step_step with (L1:=x2) (L2:=x1) (S:=x) (T:=x0) (S':=x3) (T':=x4);try easy.
Qed.
    
Theorem assoc_completeness' : forall p q ell gamma gamma' g, partial_assoc gamma g ->
wfgC g -> projectableA g -> tctx_wf gamma ->
tctxR gamma (lcomm p q ell) gamma' ->
exists g', partial_assoc gamma' g' /\ gttstepC g g' p q ell. 
Proof.
    intros * Hassoc Hwfg Hproj Hwfltt Hred.
    pose proof Hred as Hredinv.
    eapply tctx_comm_invert in Hredinv.
    destr_hyps.
    rename x into s, x0 into s', x1 into xsp, x2 into Tp, x3 into xsq, x4 into Tq.
    Search gttstepC projectionC ltt_send ltt_recv.
    assert (exists g', gttstepC g g' p q ell).
    {
        eapply local_step_implies_global_step with (g:=g) (gamma:=gamma) (gamma':=gamma');easy.
        
    }
    destruct H6 as [g' Hpstep].
    exists g'.
    split;try easy.
    assert(Hwfg' : wfgC g') by (apply wfgC_after_step in Hpstep;try easy).
    
    eapply dom_preservation_6_9 in Hred as Heqdom. red;intros.
    apply opt_lem2 in H6 as Hin. rewrite <- MF.in_find in Hin. apply Heqdom in Hin.
    rewrite MF.in_find in Hin. apply opt_lem1 in Hin. destr_hyps. rename Tp0 into Tp0',
    x into Tp0.
    destruct (Nat.eq_dec p0 p);destruct (Nat.eq_dec p0 q);crush
    ;[rewrite H5 in H6 | rewrite H3 in H6 |];
    try(
    symmetry in H6;inversion H6;subst;
        eapply subproj_after_step1 with  (xsp:=xsp)(xsq:=xsq) (s1:=s) (Tp:=Tp) 
        (s2:=s') (Tq:=Tq) in Hpstep as Hsastep;try easy;
        red in Hassoc;
        [
        specialize (Hassoc p _ H)|
        specialize (Hassoc q _ H0)];try easy).
    eapply lem_6_10 with (r:=p0) in Hred as Hrelv;[| crush].
    specialize (Hassoc p0 _ H7) as Hassocp0. rewrite H7 in Hrelv. rewrite H6 in Hrelv. inversion Hrelv;subst.
    clear Hrelv. 
    eapply subproj_after_step_r with (x:=Tp0') (r:=p0)in Hpstep;easy.
Qed.

Theorem assoc_completeness: forall p q ell gamma gamma' g, assoc gamma g ->
    wfgC g ->
    tctx_wf gamma ->
    tctxR gamma (lcomm p q ell) gamma' ->
    exists g', assoc gamma' g' /\ gttstepC g g' p q ell.
Proof.
    intros * Hassoc Hwfg Hwfltt Hred.
    pose proof Hred as Heqdom.
    pose proof Hassoc as Ha1.
    eapply assoc_is_partial_assoc in Hassoc;try easy. 
    eapply assoc_completeness' with (g:=g) in Hred;try easy.
    destr_hyps.
    exists x.
    split;try easy.
    eapply partial_assoc_to_assoc;try easy.
    apply wfgC_after_step in H0;try easy. apply assoc_implies_projectable in Ha1;try easy.
    
    intros.
    assert (isgPartsC p0 g).
    {
        eapply part_after_step_redux with (r:=p0)in H0;try easy.
        apply assoc_implies_projectable in Ha1;try easy.   
    }
    eapply dom_preservation_6_9 in Heqdom.
    tac_use_assoc Ha1 p0 H2. destr_hyps. apply opt_lem2 in H3. rewrite  <- MF.in_find in H3.
    apply Heqdom in H3. easy.
    apply assoc_implies_projectable with (gamma:=gamma);easy.
Qed.