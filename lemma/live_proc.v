Require Import List String Coq.Arith.PeanoNat Coq.Program.Equality Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local 
src.global src.balanced src.typecheck src.part src.gttreeh src.path_props src.step src.merge src.projection src.session src.lcontext.  
From SST Require Import lemma.inversion lemma.path_assoc lemma.inversion_expr lemma.completeness lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step 
lemma.projection_helper lemma.subj_red_prog_fid lemma.projection lemma.subj_red_helpers lemma.soundness 
lemma.liveness_helpers lemma.liveness.

Definition typable M := exists gamma, typ_sess M gamma. 

Definition proc_path_valid_criteria := (fun x1 (l:label)  x2  =>
  match (x1,l,x2) with 
    | (g1,(lcomm p q ell), g2) => betaP_lbl g1 (lcomm p q ell) g2 /\ typable g1
    | _=> False
  end).

  From Coq Require Import IndefiniteDescription.

Definition proc_valid_pathC := valid_path_GC proc_path_valid_criteria.

Definition betaRtc := clos_refl_trans session betaP.

Print path_assoc.

Search "local" "path".

Variant typ_path  (R: coseq (session * option label) -> coseq (tctx * option label) -> Prop) :  coseq (session * option label) -> coseq (tctx * option label) -> Prop :=
    | typ_nil : typ_path R conil conil
    | typ_cocons : forall M gamma ms gs l, typ_sess  M gamma ->  R ms gs ->
        typ_path R (cocons (M,l) ms) (cocons (gamma,l) gs).

Definition gamma_by_betaP : forall M gamma p q ell M' l' xs, typ_sess M gamma -> proc_valid_pathC (cocons (M, Some (lcomm p q ell)) (cocons (M',l') xs)) ->
{gamma' | typ_sess M' gamma' /\ tctxR gamma (lcomm p q ell) gamma' /\ proc_valid_pathC (cocons (M',l') xs)}.
Proof.
    intros * Htyp Hvalid.
    assert(Hbeta: betaP_lbl M (lcomm p q ell) M').
    {
      pinversion Hvalid;try apply valid_path_mon;subst;red in H5;easy. 
    }
	Search betaP_lbl.
	eapply sub_red_strong_labelled in Hbeta as Hsub;try exact Htyp.
	destruct (constructive_indefinite_description _ Hsub) as [gamma' Hg'].
    destruct Hg' as [Hassoc' Hstep].
    exists gamma'. split;try easy. split;try easy.	
	pinversion Hvalid;subst;try apply valid_path_mon. easy.
Qed.

CoFixpoint get_typ_path : forall M gamma l xs, typ_sess M gamma ->
    proc_valid_pathC (cocons (M, l) xs) ->
    local_path.
Proof.
    intros * Htyp Hvalid.
    refine ((match l as m return 
    (l =m -> local_path)
    with 
        | None =>  fun u=> (cocons (gamma, None) conil)
        | Some (lcomm p q ell) => 
        fun u=> (cocons (gamma,(Some (lcomm p q ell))) _)
        | _ => fun u=> conil 
    end
    ) (eq_refl)).
    {
        destruct xs. exact conil.
        subst. destruct p0. eapply gamma_by_betaP with (gamma:=gamma) in Hvalid;try easy.
        destruct Hvalid as [gamma' [Hsess' [Hstep' Hvalid' ]]].
        exact (get_typ_path s gamma' o xs Hsess'  Hvalid').
    }
Defined.


Search path_assocC.

Definition typ_pathC := paco2 typ_path bot2.

Definition head_comm_enabled_proc p q ell (xs: coseq (session * option label)) := match xs with 
  | cocons (M,_) xs => exists M', betaP_lbl M (lcomm p q ell) M'
  | _ => False end.
  
Definition head_trans_proc p q ell (xs:coseq (session * option label)) := match xs with 
  | cocons (_, Some (lcomm p' q' ell')) _ => p=p' /\ q=q' /\ ell =ell'
  | _ => False end.

Definition fairness_proc_inner xs := forall p q ell, head_comm_enabled_proc p q ell xs ->
eventually (head_trans_proc p q ell) xs.

Definition fair_path_proc := alwaysCG fairness_proc_inner.

Lemma get_typ_path_types : forall M gamma l xs
 (Htyp : typ_sess M gamma) 
(Hvalid : proc_valid_pathC (cocons (M,l) xs)),
typ_pathC (cocons (M,l) xs) 
(get_typ_path _ _ _ _ Htyp Hvalid).
Proof.
    pcofix CIH.
    intros.
    destruct l.
    {
        
        destruct l;
        pose proof Hvalid as Hvalid'; pinversion Hvalid'; try apply valid_path_mon;try tauto;subst.

        rewrite (coseq_eq (get_typ_path _ _ _ _ _ _   )).
        simpl.
        pfold.
        constructor;try easy.
        unfold eq_rect_r. simpl.
		Check gamma_by_betaP.
        set (gnext:= gamma_by_betaP M gamma n n0 n1 x l' xs0 Htyp  Hvalid).
        destruct gnext.
        destruct a. destr_hyps.
        right. eapply CIH.            
    }
    {   
        pose proof Hvalid as Hvalid'.
        pinversion Hvalid';subst;try apply valid_path_mon;try easy. 
        
        rewrite (coseq_eq (get_typ_path _ _ _ _ _ _   )). simpl. 
        pfold. constructor;try easy. left;pfold; constructor;try easy.
    }
Qed.

Lemma get_typ_path_valid : forall M gamma l xs
 (Htyp : typ_sess M gamma) 
(Hvalid : proc_valid_pathC (cocons (M,l) xs)),
local_valid_pathC  
(get_typ_path _ _ _ _ Htyp Hvalid).
Proof.
    pcofix CIH.
    intros.
    destruct l.
    {
        
        destruct l;
        pose proof Hvalid as Hvalid'; pinversion Hvalid'; try apply valid_path_mon;try tauto;subst.
        destruct l'.
        {
            destruct l;
            pose proof H1 as Hvalid3;
            pinversion Hvalid3;subst;try apply valid_path_mon;try easy.
            rewrite (coseq_eq (get_typ_path _ _ _ _ _ _   )). simpl.
            unfold eq_rect_r;simpl.   
            set (gnext' := gamma_by_betaP M gamma n n0 n1 x (Some (lcomm n2 n3 n4))
(cocons (x0, l') xs) Htyp Hvalid).
            destruct gnext'. destr_hyps. pfold.
            assert (Hfold: exists x2 w0 t1 , 
			((get_typ_path x x1 (Some (lcomm n2 n3 n4)) (cocons (x0, l') xs) t p))
			 = (cocons (x1, Some (lcomm n2 n3 n4)) (get_typ_path x0 x2 l' xs w0 t1 ))).
            {
                 rewrite (coseq_eq (get_typ_path _ _  _ _ _ _   )). simpl.
            
            unfold eq_rect_r. simpl.
            set (gnext'' := gamma_by_betaP x x1 n2 n3 n4 x0 l' xs t p).
            destruct gnext''. destr_hyps.
            exists x2,  t1,  p0. easy.

            }
            destr_hyps.
            rewrite H.
            constructor;try solve [red;easy].
            rewrite <- H.
            right. eapply CIH.
        }
        rewrite (coseq_eq (get_typ_path _ _ _ _ _ _ )). simpl.
        unfold eq_rect_r. simpl.
        
        set (gnext' := gamma_by_betaP M gamma n n0 n1 x None xs0 Htyp
Hvalid).
        destruct gnext';destr_hyps.
        

        rewrite (coseq_eq (get_typ_path _ _ _ _ _ _ )). simpl.
        unfold eq_rec_r. simpl.
        pfold. constructor. left. pfold. constructor.
        red;easy.            
    }
    {   
        pose proof Hvalid as Hvalid'.
        pinversion Hvalid';subst;try apply valid_path_mon;try easy. 
        
        rewrite (coseq_eq (get_typ_path _ _ _ _ _ _   )). simpl. 
        pfold. constructor;try easy. 
    }
Qed.

Lemma typ_path_mon : monotone2 typ_path.
Proof.
	red;intros;induction IN;try constructor;try easy;eapply LE;easy.
Qed.

Hint Resolve typ_path_mon :paco.

Lemma typ_path_preserves_fairness_helper : forall xs ys p q ell, typ_pathC xs ys -> eventually (head_trans_proc p q ell) xs ->
eventually (headComm p q) ys.
Proof.
	intros * Htyp Hev. generalize dependent ys.
	induction Hev;intros.
	destruct xs;try easy. destruct p0. destruct o;try easy. destruct l;try easy. red in H;destr_hyps;subst.
	pinversion Htyp;subst. constructor. simpl;tauto.
	
	pinversion Htyp;subst. specialize (IHHev _ H3). constructor 2. easy.
Qed.
	

Lemma typ_path_preserves_fairness : forall xs ys, proc_valid_pathC xs -> fair_path_proc xs -> typ_pathC xs ys ->
fair_path ys.
Proof.
	pcofix CIH.
	intros * Hvalid Hfair Htyp. pfold. 
	pinversion Htyp;subst. constructor. red;intros. inversion H.	
	constructor. red;intros. simpl in H1. red in H1;destr_hyps.
	eapply sess_fidelity in H1 as Hfid;try exact H;try easy;destr_hyps.
	red in Hfair.
	pinversion Hfair;subst. red in H7. specialize (H7 p q x2). 
	eapply typ_path_preserves_fairness_helper with (xs:=cocons (M,l) ms) (ell:=x2). pfold. easy.
	eapply H7;red. exists x1;easy.
	right. eapply CIH with (xs:=ms). pinversion Hvalid;try eapply valid_path_mon;subst;try easy. pfold. constructor.
	pinversion Hfair;subst. easy.
	easy.
Qed.
	
Definition extends_to_fair M := exists l xs, coseq_head xs = Some (M,l) /\ proc_valid_pathC xs /\ fair_path_proc xs.

Definition fairness_feasible := forall M, extends_to_fair M.

Lemma typ_path_exists: forall M gamma xs l, typ_sess M gamma -> proc_valid_pathC (cocons (M,l) xs) ->
    exists ys,  typ_pathC (cocons (M,l) xs) ys
    /\ local_valid_pathC ys /\ coseq_head ys= Some (gamma,l) .
Proof.
    intros * Hsess Hvalid.
     exists (get_typ_path _ _ _ _ Hsess Hvalid). split;[|split];
     try solve [eapply (get_typ_path_types) | eapply get_typ_path_valid].
     pose proof Hvalid as Hvalid'.    
    destruct l.
    {
        destruct l;pinversion Hvalid';subst;try apply valid_path_mon;try easy.
    }
    easy.
Qed.


Definition live_sess Mp := forall M, betaRtc Mp M -> (forall p q ell e P' M', p <>q -> unfoldP M ( (p <-- p_send q ell e P') ||| M') -> exists M'',
betaRtc M ((p <-- P')|||M''))
/\
(forall p  q llp M', p <>q -> unfoldP M ( (p <-- p_recv q llp) ||| M') -> exists M'' P' k,
onth k llp = Some P' /\
betaRtc M ((p <-- P')|||M'')).

Lemma path_to_betaRtc : forall xs M M' (lb:option label), coseq_head xs = Some (M,lb) -> 
proc_valid_pathC xs ->
eventually (fun u=> match u with cocons (a,_)_ => a=M' | _ => False end) xs ->
	betaRtc M M'.
Proof.
	intros * Hhead Hvalid Hev.  generalize dependent lb. generalize dependent M. induction Hev.
	destruct xs;try easy. destruct p;subst. intros. simpl in Hhead. inversion Hhead;subst. constructor 2.

	intros. destruct x;try easy. simpl in Hhead. inversion Hhead;subst;clear Hhead.
	pinversion Hvalid;try apply valid_path_mon;subst. inversion Hev;try easy.
	specialize (IHHev H1 x).
	econstructor 3 with (y:=x).
	red in H3. destruct l;try easy. econstructor 1. exists (lcomm n n0 n1). easy.

	eapply IHHev. simpl. reflexivity.
Qed.



Lemma sub_red_Rtc : forall M M' gamma, typ_sess M gamma -> betaRtc M M' -> exists gamma', typ_sess M' gamma'.
Proof.
	intros. generalize dependent gamma. induction H0.
	intros. eapply sub_red in H0;try exact H. destr_hyps. exists x0;easy.
	intros. exists gamma. easy.
	intros. specialize (IHclos_refl_trans1 _ H). destr_hyps. 
	eapply IHclos_refl_trans2;try exact H0.
Qed.

Ltac destruct_forallT := match goal with 
                 | [ H: ForallT _ (?p <-- ?P)|- _] => inversion_clear H
                | [ H: ForallT _ (?M ||| ?M' ) |- _] => inversion_clear H
                end.

Definition proc_path_head_is x (xs : coseq (session *option label)) := 
match xs with (cocons (M,_) _) => M = x
| _ => False
end.

Definition proc_path_head_scong_send p q ell e P' (xs : coseq (session *option label)):= 
match xs with (cocons (M,_) _) => exists M', scong M  (p<-- p_send q ell e P' |||M')
    | _ => False
end.
Definition proc_path_head_unfolds_to_send p q (xs : coseq (session *option label)) := 
match xs with (cocons (M,_) _) => exists M' ell e P, unfoldP M ((p <-- p_send q ell e P) |||M')
| _ => False
end.

Lemma betaP_lbl_invert : forall M M' p q ell gamma,
typ_sess M gamma -> betaP_lbl M (lcomm p q ell) M' ->
exists M'' P' llp e, unfoldP M ((p <-- p_send q ell e P' )|||(q <-- p_recv p llp) |||M'').
Proof.
    intros * Hsess Hbeta.
    generalize dependent gamma.
    dependent induction Hbeta.
    {
        exists M, Q, xs, e. eauto with procs.
    }
    {
        intros.
        assert(Hsess2 : typ_sess M1' gamma).
        {
            eapply typ_after_unfold in Hsess;try exact H;easy.
        }
        eapply IHHbeta in Hsess2 as IH_use;try reflexivity.
        destr_hyps.
        exists x, x0, x1, x2.
        eauto with procs.
    }
Qed.

Lemma betaP_lbl_send_unique : forall M M' M'' gamma p q ell ell' q', 
typ_sess M gamma ->
betaP_lbl M (lcomm p q ell) M' -> betaP_lbl M (lcomm p q' ell') M'' ->
q = q'.
Proof.
    intros * Hsess Hbeta1 Hbeta2.
    eapply betaP_lbl_invert in Hbeta1;try exact Hsess.
    
    eapply betaP_lbl_invert in Hbeta2;try exact Hsess.
    destr_hyps.
    eapply typ_after_unfold in H0 as Ht1;try exact Hsess.

    eapply typ_after_unfold in H as Ht2;try exact Hsess.
    inversion Ht1;inversion Ht2;subst.
    
    repeat destruct_forallT;destr_hyps.
    assert(x9 =x7) by congruence;subst.
    eapply inv_proc_send in H15, H19;try reflexivity.
    destr_hyps. pinversion H28;subst;pinversion H26;subst;try apply sub_mon. easy.
Qed.

Lemma proc_same_after_distinct_trans: 
    forall M M' M'' p q p' q' ell ell' e P',
    typable M ->
    scong M ((p<-- p_send q ell e P')|||M') ->
    betaP_lbl M (lcomm p' q' ell') M'' ->
    p' <> p -> q' <> p ->
    exists M''' ell' e' P'', scong M'' ((p<-- p_send q ell' e' P'')|||M''').
    Proof.
        intros * Htyp Hunf Hbeta Hpp Hqp.
        destruct Htyp as [gamma Htyp].
        eapply sub_red_strong_labelled in Hbeta as Hbeta';try exact Htyp;destr_hyps.
        eapply lem_6_10 with (r:=p) in H0.
        Search typ_sess scong.
        eapply typ_after_unfold in Hunf as Htyp';try exact Htyp. inversion Htyp';subst.
        repeat destruct_forallT. destr_hyps.
        eapply inv_proc_send in H7;try reflexivity;destr_hyps.
        eapply betaP_lbl_invert in Hbeta;destr_hyps;try exact Htyp.
        pinversion H11;subst;try apply sub_mon.
        rewrite H4 in H0.
        inversion H;subst.
        eapply move_forward with (p:=p) in H as Hmf;
        try solve [red;exists (ltt_send q ys);easy].
        destr_hyps. eapply typ_after_unfold in H18 as Ht1;try exact H.
        inversion Ht1;subst. repeat destruct_forallT. destr_hyps.
        assert(x10= ltt_send q ys) by congruence;subst.
        eapply typ_proc_inv_send in H27;try easy.
        destr_hyps.
        exists x8, x10, x12, x13.
        eauto with procs.
        red; intros;simpl;auto. simpl in H1. destruct H1;subst;try easy.
    Qed.

Lemma live_proc_helper2 : forall p q P ell e xs,
        p <> q ->
        proc_valid_pathC xs ->
        proc_path_head_scong_send p q ell e P xs -> 
        weak_untilC ((fun u=> 
        match u with | conil => True
        | x => proc_path_head_scong_send p q ell e P x
         end)) 
        (fun u=>  proc_path_head_scong_send p q ell e P u /\ 
        exists ell',  head_trans_proc p q ell' u) xs. 
Proof. 
    intros * Hpq.  revert xs. pcofix CIH.
    intros * Hvalid Hphead. pfold.
    destruct xs;try easy. destruct p0;try easy.
    pinversion Hvalid;subst;try apply valid_path_mon.
    {
        econstructor 2. simpl in Hphead. destr_hyps. simpl. exists x. easy. 
        left.  
        pfold. econstructor 3. easy.    
    }
    {
        destruct l;try easy. red in H3.
        destruct H3 as [Htab Htypable].
        destruct (Nat.eq_dec n p);destruct (Nat.eq_dec n0 q);subst;try easy.
        {
            econstructor 1. simpl in Hphead. simpl. destr_hyps. 
            split. exists x0; tauto.
            exists n1;tauto.
        }
        {
            simpl in Hphead.
            Lemma unfold_beta_unique_send : 
            forall M M' M'' p q ell e P' q' ell' gamma, typ_sess M gamma ->
            unfoldP M ((p <-- p_send q ell e P')|||M'') ->
            betaP_lbl M (lcomm p q' ell') M' -> q=q'.
            Proof.
                intros * Hsess Hunf Hbet.
                eapply typ_after_unfold in Hsess as Hsess';try exact Hunf.
                inversion Hsess';subst. repeat destruct_forallT. destr_hyps.
                eapply inv_proc_send in H5;try reflexivity;destr_hyps.
                eapply betaP_lbl_invert in Hbet as Hbinv;try exact Hsess.
                destr_hyps.
                eapply typ_after_unfold in Hsess as Hsess'';try exact H10.
                inversion Hsess'';subst. repeat destruct_forallT. destr_hyps.
                assert(x=x7) by congruence;subst.
                eapply inv_proc_send in H18;try reflexivity;destr_hyps.
                pinversion H24;pinversion H9;subst;try apply sub_mon;congruence. 
            Qed.
            red in Htypable. destr_hyps.
            eapply unfold_beta_unique_send with (q:=q) (ell:=ell) (e:=e) (P':=P) (M'':=x1)  in Htab as Hunfq; 
            try exact H;subst;try easy.
            eapply unfoldB_to_unfoldP. inversion H;try easy.
            econstructor 1. econstructor 2. easy.
        }
        {
            econstructor 2. easy.
            right. eapply CIH;try easy.
            simpl in Hphead.  destr_hyps.
            simpl. exists x0.  
            eapply proc_same_after_distinct_trans in Htab as Hd.
            try exact H;try easy.
        }
        {
            econstructor 2. easy.
            right. eapply CIH;try easy.
            simpl in Hphead. destr_hyps.  
            eapply proc_same_after_distinct_trans in Htab as Hd;try exact H;try easy.
            red;intros;subst.
            destruct Htypable as [gamma Htyp].
            eapply betaP_lbl_invert in Htab as Hinv;destr_hyps;try exact Htyp.
            
            eapply typ_after_unfold in H0 as Ht2;try exact Htyp.
            eapply typ_after_unfold in H as Ht3;try exact Htyp.
            inversion_clear Ht3.
            inversion_clear Ht2.
            repeat destruct_forallT.
            destr_hyps.
            assert(x8=x10) by congruence;subst.
            eapply inv_proc_send in H15;try reflexivity.
            eapply inv_proc_recv in H19;try reflexivity.
            destr_hyps.
            pinversion H27;pinversion H23;subst;try apply sub_mon;try easy.
        }
    }
Qed.


Definition is_p_send P:=exists q ell e P', P=p_send q ell e P'.    

Lemma p_send_no_tau : forall P Q, is_p_send P -> tauRtc P Q -> P=Q.
    Proof.
        intros. revert H. induction H0;
        intros. red in H0;destr_hyps;subst. inversion H;inversion H0.
        easy.
        eapply IHclos_refl_trans1 in H as H';subst.
        tauto.
    Qed.
Lemma unfold_p_unique : forall p P M' M'',
is_p_send P ->
typable ((p <-- P) ||| M') ->
unfoldP ((p <-- P) ||| M')
M'' ->  exists M''', unfoldP M'' ((p <-- P) ||| M''').
Proof.
    intros * Hse Htyp Hunf.
    red in Htyp;destruct Htyp as [gamma Htyp].
    assert(Hinp: InT p M'' ). 
    {
        eapply part_after_unf with (p:=p) in Hunf;try easy. red;simpl;tauto.
    }
    eapply move_forward_h in Hinp;destr_hyps.
    assert (tauRtc P x).
    {
        assert(unfoldP ((p <-- P) ||| M') ((p <-- x) ||| x0)) by eauto with procs.
        eapply unfoldP_to_unfoldB in H0 as Hb.
        eapply unfoldB_p_unique in Hb. easy.
        inversion Htyp. red;easy.   
    }
    eapply p_send_no_tau in H0;subst;try easy. exists x0;easy.
Qed.

Theorem sess_fidelity_strong : forall M gamma M' e p q ell ell' P' gamma', 
typ_sess M gamma -> tctxR gamma (lcomm p q ell) gamma' ->
unfoldP M ((p <-- p_send q ell' e P') |||M') ->
exists M'', betaP_lbl M (lcomm p q ell') M'' /\ 
exists M''', unfoldP M'' ((p <-- P')|||M''').
Proof.
	intros * Hsess Hgstep Hunf.
	eapply typ_after_unfold in Hunf as Hsess';try exact Hsess.
	eapply lem_6_11c_tctx_comm_invert in Hgstep as Hinvert;destr_hyps.
	
	assert(Hinp: InT p M) by (
		inversion Hsess;subst;eapply H7; red;exists (ltt_send q x1);split;try easy).

	assert(Hinq: InT q M) by (inversion Hsess;subst;eapply H7; red;exists (ltt_recv p x3);split;try easy).
	assert(Hpq : p<> q) by (red;intros;subst;congruence).
    inversion Hsess;destr_hyps;subst.
   	eapply assoc_inv_find in H as Hsub1;try exact H13;try easy.
	eapply assoc_inv_find in H0 as Hsub2;try exact H13;try easy.
	assert(Hpartp :isgPartsC p x5).
	{
		red in Hsub1;destr_hyps. pinversion H11;try apply sub_mon;subst.
        
		eapply multigrafting.proj_contains_q_implies_part_send in H10;destr_hyps;try easy.
		eapply assoc_implies_projectable in H13;try easy.	
	}
	assert(Hslist1: SList x1).
	{
		red in H6. specialize (H6 _ _ H). pinversion H6;try apply wfltt.wfltt_mon;try easy.
	}
	assert(Hslist2 : SList x3).
	{
		red in H6. specialize (H6 _ _ H0). pinversion H6;try apply wfltt.wfltt_mon;try easy.
	}
	eapply assoc.lem_6_16_simul_subproj in Hsub1 as Hsim;try exact Hsub2;try easy.
	Lemma unfold_ooo_lemma : forall p q P M M', InT q M -> unfoldP M ((p<-- P) |||M') ->
    p=q \/ InT q M'.
    Proof.
        intros * Hinq Hunf.
        eapply part_after_unf in Hunf;try exact Hinq. red in Hunf. simpl in Hunf.
        destruct Hunf;try tauto.
    Qed. 
    eapply unfold_ooo_lemma in Hinq as Hinq';try exact Hunf.
    destruct Hinq';try easy.
    eapply move_forward_h in H10. destr_hyps.
    assert (Hunf1: unfoldP M ((p <-- p_send q ell' e P') ||| ((q <-- x6) ||| x7))) by
    eauto with procs.
    eapply typ_after_unfold in Hsess as Hsess2;try exact Hunf1.    
    
    inversion Hsess2;subst.
    repeat destruct_forallT.
    destr_hyps;subst.
    assert(x8=(ltt_recv p x3)) by congruence;subst.
    assert(x9=(ltt_send q x1)) by congruence;subst.
    eapply typ_proc_inv_recv in H20 as Hdr;try easy.
    destr_hyps. eapply typ_after_tauRtc in H25 as Ht;try exact H20.
    eapply inv_proc_recv in Ht;try reflexivity.
    destr_hyps.
    eapply subtype_recv_inv in H27.
    eapply inv_proc_send in H22 as Ht2;try reflexivity.
    destr_hyps.
    eapply subtype_send_inv in H32. 
    assert(onth ell' (extendLis ell' (Some (x11,x12)))=(Some (x11,x12))) by (rewrite extendExtract;easy).
	eapply Forall2R_prop in H32;try exact H33;tac_sanitize.
    eapply Forall2R_prop in Hsim;try exact H35;tac_sanitize.
    eapply Forall2R_prop in H27;try exact H38;tac_sanitize. 
    eapply Forall2_prop_l in H28;try exact H34;tac_sanitize.
    eapply expr_eval_ss in H30;destr_hyps.
    assert(betaP_lbl (((q <-- (p_recv p x8)) ||| (p <-- p_send q ell' e P') ||| x7)) (lcomm p q ell') 
        ( ((q <-- subst_expr_proc x18 (e_val x11) 0 0) ||| (p <-- P') ||| x7))).
    {
        eapply r_comm;try easy.   
    }
    assert (Hunfx1 : unfoldP M 
    ((p <-- p_send q ell' e P') ||| ((q <-- (p_recv p x8)) ||| x7)))
    by eauto with procs.

    assert(unfoldP M  ((q <-- p_recv p x8) ||| (p <-- p_send q ell' e P')
||| x7)) by eauto with procs.
    exists (((q <-- subst_expr_proc x18 (e_val x11) 0 0) ||| (p <-- P')) ||| x7).
    split.
    eapply r_struct with (M2':= (((q <-- subst_expr_proc x18 (e_val x11) 0 0) ||| (p <-- P'))
||| x7));try exact H32;try easy.
    eauto with procs.
    exists (((q <-- subst_expr_proc x18 (e_val x11) 0 0))
||| x7).
eauto with procs.
Qed.

Lemma live_proc_helper : forall p q xs ys, 
eventually (headComm p q) xs -> 
typ_pathC  ys xs -> exists ell,
eventually (head_trans_proc p q ell) ys.
Proof.
    intros * Hev Htyp. generalize dependent ys. induction Hev.
    {
        intros. destruct xs;try easy. destruct p0. destruct o;try easy.
        destruct l;try easy. simpl in H;destr_hyps;subst.
        pinversion Htyp;subst. exists n1;simpl. constructor. easy. 
    }
    {
        intros.
        pinversion Htyp;subst. specialize (IHHev ms H3). 
        destr_hyps. exists x. constructor 2. easy.   
    }
Qed.

Lemma extends_to_fair_implies_live : fairness_feasible -> forall M gamma, typ_sess M gamma -> live_sess M.
Proof. 
	intros Ax_fairness * Hsess. red. intros. split.
	{
		intros * Hpq H0.
        
        
		specialize (Ax_fairness ((p <-- p_send q ell e P') ||| M')). red in Ax_fairness. destr_hyps.
		destruct x0;try easy. destruct p0;try easy. simpl in H1;inversion H1;subst;clear H1.
		eapply sub_red_Rtc in Hsess;try exact H.
		destruct Hsess as [gamma' Hsess].
		eapply typ_path_exists in H2 as Htypp;try exact Hsess. destr_hyps.
		assert(Hlive: liveCtx gamma').
		{
            inversion Hsess;destr_hyps.
			eapply liveness with (g:=x2);try easy. 
            eapply assoc_implies_projectable in H12;try easy.  	
		}
        assert(Hlive_path: all_fair_live gamma').
        {
            eapply Hlive. constructor 2.   
        }
                    destruct x1;try easy. destruct p0. simpl in H5;inversion H5;subst;clear H5.

        assert(Hev_local_trans: eventually (headComm p q) (cocons (gamma', x) x1)).
        {
            red in Hlive_path.
            eapply typ_path_preserves_fairness in H3 as Hfair_local;try exact H1;try easy.
            eapply Hlive_path in Hfair_local;try exact H4.
            pinversion Hfair_local;subst. red in H7.
            assert(exists s  xsp Tp', M.find p gamma' = Some (ltt_send q xsp) 
            /\ onth ell xsp = Some (s,Tp')).
            {
                eapply typ_after_unfold in H0;try exact Hsess. inversion H0;subst. inversion_clear H10.
                inversion_clear H11. destr_hyps.  
                eapply inv_proc_send in H13;try reflexivity. destr_hyps. 
                pose proof H17 as Hsub.
                pinversion H17;subst;try apply sub_mon.
                Search "sub" "inv" "send".
                eapply subtype_send_inv in Hsub.
                eapply Forall2R_prop with (l:=ell) (p:=(x4,x5)) in Hsub;
                try solve [rewrite extendExtract;try easy]; tac_sanitize.
                exists x7, ys, x9.
                repeat split;try easy.
            }
            destr_hyps.
            assert(tctxRE (lsend p q (Some x2) ell) gamma').
            red. exists (m_update p x4 gamma').
            eapply simple_red_send;try exact H6;try easy.
            specialize (H7 p q x2 ell).
            destr_hyps.
            eapply H7. simpl. easy.
        }
        Check typ_path_preserves_fairness_helper.
        
        eapply live_proc_helper in Hev_local_trans as Hlpr;try exact H1.
        destruct Hlpr as [ell' Hlpr].
        eapply  live_proc_helper2 with (p:=p) (q:=q) in H2 as Hweak;try easy;
        try solve [simpl; exists M', ell, e, P';  easy].
        eapply weak_untilC_to_until in Hweak as Hunt;
        try solve[
        rewrite eventually_P_iff_P_suffix in Hlpr; destr_hyps;
        rewrite eventually_P_iff_P_suffix; exists x2; split;try easy; exists ell'; easy].
        eapply until_suf in Hunt.
        Check until_suf.
        destruct Hunt.
        {
            destr_hyps. clear H5. rename H6 into H5. destruct x;try easy. destruct l;try easy. simpl in H5;destr_hyps;subst.
            pinversion H2;subst;try apply valid_path_mon. red in H9;destr_hyps.   
            destruct H6 as [gamma'' Hty].
            eapply sub_red_strong_labelled in H5 as Hss;try exact Hty.
            destr_hyps.
            eapply sess_fidelity_strong with (ell':=ell) in Hty;try exact H8;
            try solve [
            econstructor 2].
            destr_hyps.
            exists x3.
            econstructor 1.
            red.
            exists (lcomm n n0 ell).
            eapply r_struct;try exact H9;try easy.
        }
        {
            destr_hyps.
            destruct x2. 
            assert(Hbet1 : betaRtc  ((p <-- p_send q ell e P') ||| M') s).
            {
                eapply path_to_betaRtc with (xs:=cocons ((p <-- p_send q ell e P') ||| M', x) x0);try easy.
                eapply eventually_P_iff_P_suffix. exists (cocons (s, o) x3).
                split;try easy.
            }
            Lemma unfoldP_to_betaRtc : forall M M' M'', unfoldP M M' -> betaRtc M' M'' ->
             (betaRtc M M'' \/ unfoldP M M'').
             Proof.
                intros. generalize dependent M. induction H0.
                {
                    intros. left.  econstructor 1. red in H. destr_hyps. exists x0.
                    eapply r_struct;try exact H0;try exact H. constructor 2.
                }
                {
                    intros. tauto.
                }
                {
                    intros.   
                    specialize (IHclos_refl_trans1 _ H).
                    destruct IHclos_refl_trans1.
                    left. econstructor 3;try exact H0;easy.
                    specialize (IHclos_refl_trans2 _ H0).
                    destruct IHclos_refl_trans2;try easy;try tauto.
                }
             Qed.

             Lemma valid_suffix_valid_proc : forall xs ys, proc_valid_pathC xs ->
             is_suffix ys xs -> proc_valid_pathC ys.
             Proof.
                intros. induction H0;try easy.
                pinversion H;subst;try apply valid_path_mon. inversion H0;subst. pfold;constructor.
                eapply IHis_suffix. easy.
             Qed.
             assert(Hv:proc_valid_pathC (cocons (s,o) x3)).
             {
                eapply valid_suffix_valid_proc in H5;try easy.
             }
             destruct x3;try easy.
             destruct p0.
             pinversion Hv;try apply valid_path_mon;try easy;subst.

             simpl in H7;simpl in H8.
             destruct o0;try easy.
             destruct l0;try easy.
             destr_hyps;subst.
             destruct l;try easy.
             pinversion H11;subst;try easy;try eapply valid_path_mon.
             red in H15.
             red in H13.
             destr_hyps.
             destruct H9 as [gamma_0 Htyp0].
             eapply sub_red_strong_labelled in H8;try exact Htyp0;destr_hyps.
             eapply sess_fidelity_strong in H9;try exact Htyp0;try exact H7.
             destr_hyps.
             destruct l;try easy.
             red in H14.
             red in H12. destr_hyps.
             destruct H8 as [gamma_s0 Hts0].
             eapply sub_red_strong_labelled in H7 as Hsbr;try exact Hts0.
             destr_hyps.
             eapply sess_fidelity_strong in H13.
             
             destruct l;try easy.
             simpl in H6.
             destr_hyps.
             red in H14.
             destr_hyps.
             destruct H9 as [gamma_s Htyps].
             eapply sub_red_strong_labelled in H8;try exact Htyps.
             destr_hyps.
             
             red in H14.


             
             destruct o;try easy.

            assert(Hbet2: betaRtc M0 s \/ unfoldP M0 s).
            {
                eapply unfoldP_to_betaRtc with (M:=M0) in Hbet1;try easy.
            }
            des
            red in H7.
        }
        destruct xs.
        eapply eventually_P_iff_P_suffix in Hev;destr_hyps.

    }

