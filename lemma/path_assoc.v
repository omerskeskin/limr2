(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.wfltt src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable lemma.liveness_helpers lemma.soundness.
From SST Require Import src.step lemma.step src.assoc lemma.completeness  src.ltth src.path_props.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.

Lemma eventually_if {A:Type}: 
forall (P Q : coseq A -> Prop) (xs:coseq A), eventually P xs -> 
(forall ys, P ys -> eventually Q ys) -> eventually Q xs.
Proof.
    intros.
    induction H;[crush|].

    constructor 2. easy.
Qed.


Definition xs_height_map_fn := fun u : option (sort * gtth) =>
match u with
| Some (_, x) => gtth_height x
| None => 0
end.

Lemma gtth_height_fold : forall p q xs, 
gtth_height (gtth_send p q xs) =
seq.foldr ( fun g a => Init.Nat.max (xs_height_map_fn g + 1) a) 1 xs.
Proof.
    intros * .
    induction xs.
    { 
        simpl;easy.   
    }
    {
        destruct a. 
        destruct p0. rewrite gtth_height_unfold_once_some.
        simpl seq.foldr. rewrite IHxs;easy.
        rewrite gtth_height_unfold_once_none. simpl seq.foldr.
        rewrite <- IHxs.
        rewrite Nat.max_0_l.
        
        destruct (gtth_height (gtth_send p q xs)) eqn:Hyg;try easy.
        eapply gtth_height_0_means_hol_general in Hyg;destr_hyps;easy.
    }
Qed.


Variant coseq_bisimI {A:Type} (R: coseq A -> coseq A -> Prop): 
coseq A -> coseq A -> Prop :=
    | coseq_bis_nil : coseq_bisimI R conil conil
    | coseq_bis_cons: forall xs ys x y, 
    R xs ys -> coseq_bisimI R (cocons x xs) (cocons y ys).

Definition coseq_bisimC {A:Type}:= paco2 ( @coseq_bisimI A) bot2.



Variant path_assoc (R:local_path -> global_path -> Prop): local_path -> global_path -> Prop :=
   | path_assoc_nil : path_assoc R conil conil
   | path_assoc_xs : forall g gamma l xs ys, assoc gamma g ->
    R xs ys ->
   path_assoc R (cocons (gamma, l) xs) (cocons (g, l) ys)
   .

Lemma path_assoc_mon : monotone2 path_assoc.
Proof. red;intros. inversion IN;subst;constructor;try tauto. apply LE;easy. Qed.
   
Definition path_assocC := paco2 path_assoc bot2.

Definition conj_props (P:tctx -> Prop) (Q: gtt -> Prop) := forall gamma g,

assoc gamma g -> (P gamma <-> Q g).

Definition tctxREN_comm p q g := exists n, (tctxRE (lcomm p q n) g). 


Definition tctxREN_send p q g := exists n s, (tctxRE (lsend p q s n) g).

Definition tctxREN_recv p q g := exists n s, (tctxRE (lrecv p q s n) g).

Print alwaysG.

Definition wfg_global_path := alwaysCG (to_path_prop (fun a=> wfgC a /\ projectableA a) True).
Definition wf_local_path := alwaysCG (to_path_prop tctx_wf True).
Lemma global_path_always_wf : forall g l xs, wfgC g -> projectableA g -> global_valid_pathC (cocons (g,l) xs) -> 
wfg_global_path (cocons (g,l) xs).
Proof.
    pcofix CIH.
    intros * Hwfg Hprojable Hvalid.
    pfold. constructor. simpl;easy.
    destruct xs. left. pfold. constructor. easy.
    right. destruct p.  pinversion Hvalid;subst;try apply valid_path_mon;try easy.
    eapply CIH;
    
    red in H5; destruct l0;try tauto.
    inversion Hvalid;subst.
    eapply wfgC_after_step;try exact H5;try easy. eapply projectable_after_step;try exact H5;try easy.
Qed.


Lemma local_path_always_wf : forall g l xs, tctx_wf g -> local_valid_pathC (cocons (g,l) xs) -> 
wf_local_path (cocons (g,l) xs).
Proof.
    pcofix CIH.
    intros * Hwfg  Hvalid.
    pfold. constructor. simpl;easy.
    destruct xs. left. pfold. constructor. easy.
    right. destruct p.  pinversion Hvalid;subst;try apply valid_path_mon;try easy.
    eapply CIH;
    
    red in H5; destruct l0;try tauto.
    inversion Hvalid;subst.
    eapply tctx_wf_after_red_comm;try exact H5;try easy.
Qed.

Lemma eventually_and {A:Type} P Q : forall (xs:coseq A),
            eventually ( P /1\ Q) xs <-> eventually (Q /1\ P) xs.
            Proof. split;intros; induction H; 
            try solve [constructor; easy | constructor 2; easy].  Qed.
            
Lemma path_assoc_eventually_enabled : forall xs ys P Q, wfg_global_path ys -> wf_local_path xs -> path_assocC xs ys -> 
conj_props P Q -> eventually (to_path_prop  P False) xs -> eventually (to_path_prop  Q False) ys.
Proof.
    intros * Hwfgp Hwfgl Hpassoc Hconj Hevp.
    generalize dependent ys.
    induction Hevp.
    {
        intros. constructor. red in H. destruct xs;try easy.
        pinversion Hpassoc;try apply path_assoc_mon;subst.
        red.
        eapply Hconj with (gamma:=gamma); easy. 
    }
    {
     intros.
     pinversion Hpassoc;try apply path_assoc_mon;subst.
     constructor 2.
     eapply IHHevp.
     pinversion Hwfgl;try apply always_mon;subst;easy.
     pinversion Hwfgp;try apply always_mon;subst;easy.
     easy.   
    }
Qed.
Lemma path_assoc_preserves_fairness_helper : forall xs p q ys, path_assocC xs ys ->
eventually (headComm p q) xs -> eventually (headComm_global p q) ys.
Proof.
    intros * Hpassoc Hevp.
    generalize dependent ys. induction Hevp.
    {
        intros. red in H. destruct xs as [ | [t l]];try easy.
        destruct l;try tauto;destruct l;try tauto.
        destruct (Nat.eq_dec p n);destruct (Nat.eq_dec q n0);try tauto;subst;clear H.
        pinversion Hpassoc;try apply path_assoc_mon;subst. constructor.  simpl. tauto.
    }
    {
        intros * Hpassoc. pinversion Hpassoc;try apply path_assoc_mon;subst.
        constructor 2.
        eapply IHHevp. easy.  
    }
Qed.


Lemma global_comm_enabled_assoc_local_comm_enabled: forall p q n gamma g, wfgC g ->
tctx_wf gamma -> global_comm_enabled p q n g -> 
assoc gamma g -> exists n', tctxRE (lcomm p q n') gamma.
Proof.
    intros * Hwfg Hwft Hgce Hassoc. 
    red in Hgce. destr_hyps. eapply assoc_soundness with (gamma:=gamma) in H;try easy.
    destr_hyps. exists x2. red. exists x0;easy.
    pinversion H;subst;try apply step_mon;easy.
Qed.

Lemma wfg_global_path_head: forall g l ys, wfg_global_path (cocons (g,l) ys) -> wfgC g.
Proof.
    intros. pinversion H;try apply always_mon;subst. red in H2. tauto.
Qed.

Lemma projable_global_path_head: forall g l ys, wfg_global_path (cocons (g,l) ys) -> projectableA g.
Proof.
    intros. pinversion H;try apply always_mon;subst. red in H2. tauto.
Qed.

Lemma wf_local_path_head: forall g l ys, wf_local_path (cocons (g,l) ys) -> tctx_wf g.
Proof.
    intros. pinversion H;try apply always_mon;subst. red in H2. tauto.
Qed.

Lemma always_tail {A:Type}: forall (g:A) (l:option label) xs P, alwaysCG P (cocons (g,l) xs) -> alwaysCG P xs.
Proof. intros. pinversion H;try apply always_mon;subst. easy. Qed.


    
Lemma path_assoc_preserves_fairness : forall lp gp, wfg_global_path gp -> wf_local_path lp ->
path_assocC lp gp ->
fair_path lp -> fair_path_global gp.
Proof.
    pcofix CIH.
    intros * Hwfgp Hwflp Hpassoc Hfairl.
    pfold.
    pinversion Hpassoc;try apply path_assoc_mon;subst.
    {
        constructor. red. intros. simpl in H. easy.
    }
    constructor.
    { 
        red. intros.
        pinversion Hfairl;subst;try apply always_mon.
        red in H4.
        simpl in H1.
        
        eapply global_comm_enabled_assoc_local_comm_enabled in H1 as Hlc;try exact Hassoc;try easy;
        try solve [
        apply wfg_global_path_head in Hwfgp;easy | apply wf_local_path_head in Hwflp;easy].
        destruct Hlc as [n' Hr].
        
        specialize (H4 p q n').
        simpl in H4. 
        specialize (H4 Hr). inversion H4;subst.
        {  
            simpl in H2.
            destruct l;try tauto.
            destruct l; destruct (Nat.eq_dec p n0);destruct (Nat.eq_dec q n1);subst;try tauto.
            constructor 1. simpl. tauto.
        }
        {
            constructor 2. eapply path_assoc_preserves_fairness_helper;try exact H3;try easy.
        }   
    }
    {
        right. eapply CIH with (lp := xs);
        eapply always_tail in Hwfgp, Hwflp, Hfairl;try easy.
    }
Qed.

Lemma local_send_enabled_global_send_enabled : forall g p q s n gamma, wfgC g -> tctx_wf gamma ->
        assoc gamma g -> tctxRE (lsend p q (Some s) n) gamma ->
        exists s' n', global_label_enabled (lsend p q (Some s') n') g.
Proof.
    intros * Hwfg Hwf Hassoc Hre.
    destruct Hre as [t' Hre].
    eapply lem_6_11a_tctx_send_invert in Hre. destr_hyps. 
    
    eapply assoc_inv_find in H as Hinvf;try exact Hassoc;try easy.
    red in Hinvf. destr_hyps. eapply subtype_send_inv1 in H3 as Hst. destr_hyps;subst. 
    eapply subtype_send_inv in H3. eapply Forall2R_prop in H3;try exact H0;tac_sanitize.
    exists x4, n.
    red. exists x2, x6. tauto.
Qed.

Lemma local_recv_enabled_global_recv_enabled : forall g p q s n gamma, wfgC g -> tctx_wf gamma ->
    assoc gamma g -> tctxRE (lrecv p q (Some s) n) gamma ->
    exists s' n', global_label_enabled (lrecv p q (Some s') n') g.
Proof.
    intros * Hwfg Hwf Hassoc Hre.
    destruct Hre as [t' Hre].
    eapply lem_6_11b_tctx_recv_invert in Hre. destr_hyps. 
    
    eapply assoc_inv_find in H as Hinvf;try exact Hassoc;try easy.
    red in Hinvf. destr_hyps. eapply subtype_recv_inv1 in H3 as Hst. destr_hyps;subst.
    
    eapply projection_implies_wf in H2 as Hwfp;try easy.
    eapply wfltt_slist_recv in Hwfp as Hslist. eapply slist_implies_some in Hslist.
    destr_hyps. destruct x3. exists s0,x1.
    red. exists x2, l. tauto.
Qed.

Lemma path_assoc_reflects_liveness_helper : forall xs p q ys, path_assocC xs ys ->
eventually (headComm_global p q) ys -> eventually (headComm p q) xs.
Proof.
    intros * Hpassoc Hevp.
    generalize dependent xs. induction Hevp.
    {
        intros. red in H. destruct xs as [ | [t l]];try easy.
        destruct l;try tauto;destruct l;try tauto.
        destruct (Nat.eq_dec p n) ;destruct (Nat.eq_dec q n0);try tauto;subst;clear H.
        pinversion Hpassoc;try apply path_assoc_mon;subst. constructor. simpl. tauto.
    }
    {
        intros * Hpassoc. pinversion Hpassoc;try apply path_assoc_mon;subst.
        constructor 2.
        eapply IHHevp. easy.  
    }
Qed.

Lemma path_assoc_reflects_liveness : forall lp gp, wfg_global_path gp -> wf_local_path lp ->
path_assocC lp gp ->
live_path_global gp -> live_path lp.
Proof.
    pcofix CIH.
    intros * Hwfgp Hwflp Hpassoc Hfairl.
    pfold.
    pinversion Hpassoc;try apply path_assoc_mon;subst.
    {
        constructor. red;split; intros; simpl in H; easy.
    }
    constructor.
    { 
        red;split; intros;
        pinversion Hfairl;subst;try apply always_mon;
        red in H4;
        simpl in H1;

        [eapply local_send_enabled_global_send_enabled in H1 as Hlc 
        | eapply local_recv_enabled_global_recv_enabled in H1 as Hlc];
        try exact Hassoc;try easy;
        try solve [
        apply wfg_global_path_head in Hwfgp;easy | apply wf_local_path_head in Hwflp;easy];
        destruct Hlc as [s' [n' Hr]];
        
        specialize (H4 p q s' n'); destruct H4 as [Hlv1 Hlv2];
        [
        assert(Hevg: eventually (headComm_global p q) (cocons (g,l) ys)) by (eapply Hlv1;easy)
        |
        assert(Hevg: eventually (headComm_global p q) (cocons (g,l) ys)) by (eapply Hlv2;easy)];
        eapply path_assoc_reflects_liveness_helper with (ys:=(cocons (g,l) ys));try easy;
        pfold;easy.
    }
    {
        right. eapply CIH with (gp := ys);
        eapply always_tail in Hwfgp, Hwflp, Hfairl;try easy.
    }
Qed.

(*
Definition g_by_gamma_trans : forall t p q ell g t', wfgC g -> tctx_wf t -> assoc t g ->
tctxR t (lcomm p q ell) t' ->
{g' | assoc t' g' /\ gttstepC g g' p q ell}.
Proof.
    intros. eapply assoc_completeness with (g:=g) in H0;try exact H2;try easy.
    destruct (constructive_indefinite_description _ H0) as [g' Hg'].
    exists g'. easy.
Defined.


Lemma valid_local_path_valid_trans: forall t p q ell xs,
valid_local_path (cocons (t, Some (lcomm p q ell)) xs) ->
{s| match s with (t',l,ys) => 
xs= cocons (t',l) ys /\ tctxR t (lcomm p q ell) t' end}.
Proof.
    intros. 
    refine (
        (match xs as m return xs =m -> {s| match s with (t',l,ys) => 
xs= cocons (t',l) ys /\ tctxR t (lcomm p q ell) t' end} with 
    |conil => _
    | cocons (t',l) ys => _ end
) (eq_refl)).
    {
        intros. subst.
        assert(False).
        {
            pinversion H;try apply valid_path_mon.   
        }
        exists (M.empty, None, conil). easy.   
    }
    {
        intros. subst. exists (t', l, ys).
        split. easy.
        pinversion H;subst;try apply valid_path_mon. easy.   
    }
Defined.


Lemma valid_local_path_dilemma: forall t l xs, valid_local_path (cocons (t,l) xs) ->
{ s & match s with (p,q,ell) => {l=Some (lcomm p q ell)} + {l=None} end }.
Proof.
    intros.
    destruct l;try tauto.
    {
        assert(Hrec: { s | match s with (p,q,ell) => l=lcomm p q ell end}).
        {
                refine ((match l as m return 
                (l=m -> { s | match s with (p,q,ell) => l=lcomm p q ell end}) with 
                | lsend a b c d => _
                | lrecv a b c d => _
                
                | lcomm p q ell => _ end) (eq_refl));intros;subst;
                try (
                assert(False) by
                (
                    pinversion H;subst;try apply valid_path_mon; inversion H4  
                );
                exists (0,0,0); easy).
                exists (p,q,ell). reflexivity.
        }
        destruct Hrec. destruct x as [[p q] ell]. subst. exists (p,q,ell). tauto.
    }
    {
        exists (0,0,0). right. easy.   
    }
Defined.
(*
Ltac indef_destruct H := let tth := type of H in match tth with 
     | ex _  => let nx := fresh "x" in let nh:= fresh "H" in  
    destruct (constructive_indefinite_description _ H) as [nx nh];try indef_destruct nh;clear H end.
*)   
CoFixpoint conj_path : forall t g l  xs, wfgC g -> tctx_wf t -> assoc t g ->
    valid_local_path (cocons (t, l) xs) ->
    global_path.
Proof.
    intros * Hwfg Htxt Hassoc Hvalid.
    eapply valid_local_path_dilemma in Hvalid as Hdl.
    destruct Hdl as [[[p q] ell] Hdd].
    destruct Hdd.
    {
        subst.
        eapply valid_local_path_valid_trans in Hvalid as Htrans.
        destruct Htrans as [[[t' l] ys] H1].
        
        destruct H1;subst. 
        set (seq_hd := (g,Some (lcomm p q ell))).
        eapply g_by_gamma_trans with (g:=g) in H0 as Ht2;try easy.
        destruct Ht2.
        rename  x into g'.
        destruct a as [Ha0 Ha1].
        assert(Hwft': tctx_wf t').
        {
            eapply tctx_wf_after_red_comm;try exact H0;try easy.   
        }
        assert(Hwfg': wfgC g').
        {

            eapply wfgC_after_step;try exact Ha1;try easy.
            eapply assoc_implies_projectable;try exact Hassoc;try easy.   
        }
        assert(Hvlxs: valid_local_path (cocons (t', l) ys)).
        {
            pinversion Hvalid;try apply valid_path_mon;tauto.   
        }
        
        specialize (conj_path t' g' l ys Hwfg' Hwft' Ha0 Hvlxs) as vxs.
        exact (cocons seq_hd vxs).
    }
    subst. exact (cocons (g, None) conil).
Defined.


Lemma conj_path_recur : forall (t:tctx) (g:gtt) (l:option label) (xs:local_path) 
 (Hwfg : wfgC g) (Htxwf : tctx_wf t) (Hassoc: assoc t g) 
(Hvalid : valid_local_path (cocons (t,l) xs)), exists ys,
(conj_path _ _ _ _ Hwfg Htxwf Hassoc Hvalid) = cocons (g,l) ys.
Proof.
    intros.
    destruct l.
    {
           destruct l;
        pose proof Hvalid as Hvalid'; pinversion Hvalid'; try apply valid_path_mon;try tauto;subst.
        rewrite (coseq_eq (conj_path _ _ _ _ _ _ _ _   )). simpl.

        destruct (g_by_gamma_trans t n n0 n1 g x Hwfg Htxwf Hassoc) (eqn:Hyg).
        Check eq_rec_r.

    }
    {
        rewrite (coseq_eq (conj_path _ _ _ _ _ _ _ _   )). simpl. exists conil;easy.
    }
    

Lemma conj_path_path_assoc : forall (t:tctx) (g:gtt) (l:option label) (xs:local_path) 
 (Hwfg : wfgC g) (Htxwf : tctx_wf t) (Hassoc: assoc t g) 
(Hvalid : valid_local_path (cocons (t,l) xs)),

path_assocC (cocons (t,l) xs) 
(conj_path _ _ _ _ Hwfg Htxwf Hassoc Hvalid).
Proof.
    pcofix CIH.
    intros.
    destruct l.
    {
        destruct l;
        pose proof Hvalid as Hvalid'; pinversion Hvalid'; try apply valid_path_mon;try tauto;subst.

        rewrite (coseq_eq (conj_path _ _ _ _ _ _ _ _   )).
        pfold.
           
            
    }
    {
        Search valid_path_GC conil.
        eapply valid_path_none_next_nil in Hvalid as Hv2;subst.
        pfold.
        assert(conj_path t g None conil Hwfg Htxwf Hassoc Hvalid = cocons (g,None) conil).
        {
            rewrite (coseq_eq (conj_path _ _ _ _ _ _ _ _   )).
            simpl. reflexivity.
        }
        rewrite H. constructor;try tauto.
        left. pfold. constructor.     
    }
*)

Lemma conj_path_exists: forall g gamma xs l, wfgC g -> tctx_wf gamma -> assoc gamma g ->
    exists ys, path_assocC (cocons (gamma,l) xs) (cocons (g, l) ys).
Proof.
Admitted.

Lemma assoc_completeness_multistep: forall gamma gamma' g, wfgC g ->
projectableA g ->
tctx_wf gamma ->
assoc gamma g -> 
tctxRtc gamma gamma' -> exists g', gttstepRtc g g' /\ assoc gamma' g'.
Proof.
    intros * Hwfg Hprojable Hwft Hassoc Hrtc.
    generalize dependent g.
    induction Hrtc;intros.
    {
        red in H. destr_hyps.
        eapply assoc_completeness in H;try exact Hassoc;try easy.
        destr_hyps. exists x3. split;try easy. constructor. 
        red. exists x0, x1, x2. easy.
    }
    {
        exists g. split;try easy. constructor 2.   
    }
    {
        assert (Hwtf2: tctx_wf y) by 
        (eapply tctx_wf_after_rtc in Hrtc1;try easy).
        specialize (IHHrtc1 Hwft g Hwfg Hprojable Hassoc).
        destr_hyps.
        assert (Hwfg2: wfgC x0 /\ projectableA x0) by
        (eapply gttstep_preserves_wfg in H; try easy).  destr_hyps.
        specialize (IHHrtc2 Hwtf2 _ H1 H2 H0). destr_hyps.
        exists x1;split;try tauto.
        econstructor 3;try exact H;try exact H3.
    }
Qed. 

Lemma live_global_type_assoc_live_context : forall gamma g, 
wfgC g -> projectableA g -> tctx_wf gamma ->
live_type_global g -> assoc gamma g -> 
liveCtx gamma.
Proof.
    intros * Hwfg Hprojable Htwf Hlivet Hassoc.
    red;intros;red;intros. 
    eapply assoc_completeness_multistep with (g:=g) in H;try easy.
    rename g' into gamma'.
    destruct H as [g' [Hstep' Hassoc']].
    eapply gttstep_preserves_wfg in Hstep' as Hwfg';try easy.
    destruct Hwfg' as [Hwfg' Hprojable'].
    eapply conj_path_exists with (xs:=xs) (l:=l) in Hwfg' as Hconj_path;
    try exact Hassoc;try easy.
    2:admit.
    destruct Hconj_path as [ys Hconj_path].
    eapply path_assoc_reflects_liveness with (gp:=(cocons (g',l) ys));try easy.
    1-2:admit.
    red in Hlivet. specialize (Hlivet g' Hstep'). red in Hlivet.
    eapply Hlivet. admit.
    eapply path_assoc_preserves_fairness;try exact Hconj_path;try easy.
    all:admit.
Admitted.
