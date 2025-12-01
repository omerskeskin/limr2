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

Search gttstepH.
Locate graft_height_after_step.
Definition typable M := exists gamma, typ_sess M gamma. 

Definition proc_path_valid_criteria := (fun x1 (l:label)  x2  =>
  match (x1,l,x2) with 
    | (g1,(lcomm p q ell), g2) => betaP_lbl g1 (lcomm p q ell) g2 /\ typable g1
    | _=> False
  end).
From Coq Require Import IndefiniteDescription.

Locate constructive_indefinite_description.

Definition proc_valid_pathC := valid_path_GC proc_path_valid_criteria.

Definition betaRtc := clos_refl_trans session betaP.

Print path_assoc.


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

Print live_path_inner.

Definition fairness_proc_inner xs := forall p q ell, head_comm_enabled_proc p q ell xs ->
exists ell',eventually (head_trans_proc p q ell') xs.

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
    Print fair_path_local_inner.
    assert(Hra : head_comm_enabled_proc p q x2 (cocons (M, l) ms)) by 
    (red;simpl;exists x1;easy).
    specialize (H7 Hra). destr_hyps. 
	eapply typ_path_preserves_fairness_helper with (xs:=cocons (M,l) ms) (ell:=x3). 
    pfold. easy.
    easy. 
	right. eapply CIH with (xs:=ms). pinversion Hvalid;try eapply valid_path_mon;subst;try easy. pfold. constructor.
	pinversion Hfair;subst. easy.
	easy.
Qed.
	
Definition extends_to_fair M := exists l xs, coseq_head xs = Some (M,l) /\ proc_valid_pathC xs /\ fair_path_proc xs.

Definition fairness_feasible := forall M, typable M -> extends_to_fair M.


(*
Definition trans_with_p_enabled p M := exists q ell M', 
betaP_lbl M (lcomm p q ell) M' \/ betaP_lbl M (lcomm q p ell) M.

Definition max_part (M:session) := list_max (flattenT M).

Theorem trans_p_lem : forall p M, {trans_with_p_enabled p M} + {~ trans_with_p_enabled p M}.
Admitted.
(*
Theorem trans_p_dec : forall p M, {trans_with_p_enabled p M} + {~ trans_with_p_enabled p M}.
Admitted.
*)



*)

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


Definition live_sess Mp := forall M, betaRtc Mp M -> 
(forall p q ell e P' M', p <>q -> unfoldP M ( (p <-- p_send q ell e P') ||| M') -> exists M'',
betaRtc M ((p <-- P')|||M''))
/\
(forall p  q llp M', p <>q -> unfoldP M ( (p <-- p_recv q llp) ||| M') -> 
    exists M'' P' e k,
    onth k llp = Some P' /\
     
    betaRtc M ((p <-- subst_expr_proc P' e 0 0)|||M'')).

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

Definition proc_path_head_scong_recv p q llp (xs : coseq (session *option label)):= 
match xs with (cocons (M,_) _) => exists M', scong M  (p<-- p_recv q llp |||M')
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

Lemma betaP_lbl_recv_unique : forall M M' M'' gamma p q ell ell' p', 
typ_sess M gamma ->
betaP_lbl M (lcomm p q ell) M' -> betaP_lbl M (lcomm p' q ell') M'' ->
p = p'.
Proof.
    intros * Hsess Hbeta1 Hbeta2.
    eapply betaP_lbl_invert in Hbeta1;try exact Hsess.
    
    eapply betaP_lbl_invert in Hbeta2;try exact Hsess.
    destr_hyps.
    eapply typ_after_unfold in H0 as Ht1;try exact Hsess.
    eapply typ_after_unfold in H as Ht2;try exact Hsess.
    inversion Ht1;inversion Ht2;subst.
    repeat destruct_forallT;destr_hyps.
    assert(x10 =x8) by congruence;subst.
    eapply inv_proc_recv in H17, H21;try reflexivity.
    destr_hyps. pinversion H28;subst;pinversion H25;subst;try apply sub_mon. easy.
Qed.

Lemma typ_after_scong : forall M M' G, typ_sess M G -> scong M M' -> typ_sess M' G.
Proof.
  intros * Hsess Hcong.
  generalize dependent G. induction Hcong;intros;try easy;try tauto;inversion Hsess;subst;
  econstructor;try solve [
    intros; eapply H0 in H3;
    eapply scong_preserves_part;try exact H3; eauto with brocs |
        eapply scong_preserves_noDup_zero;try exact H1; eauto with brocs    
    ];try easy;repeat destruct_forallT;try solve [repeat constructor;try easy].
    eapply scong_preserves_forallT;try exact H2;try easy.
    constructor;try easy.
    eapply scong_preserves_forallT;try  exact H3;try easy. eauto with brocs.
    assert(Hsessmg : typ_sess M G) by
      (constructor;try easy).
    eapply IHHcong1 in Hsessmg.
    eapply IHHcong2 in Hsessmg.
    inversion Hsessmg;try easy.
Qed.


Lemma scong_cong_r : forall M1 M2 M2', scong M2 M2' -> scong (M1 ||| M2') (M1 ||| M2').
Proof.
    intros.
    eauto with brocs.
Qed.

Lemma scong_cont : forall M1 M2 M1' M2',
scong M1 M1' -> scong M2 M2' ->  scong (M1 ||| M2) (M1' ||| M2').
Proof.
    intros. eauto 6 with brocs.
Qed.

Hint Resolve scong_cong_r scong_cont :brocs.


Lemma sess_map_empty_implies_scong_zero : forall M, noDupSess M -> 
M.Equal M.empty (sess_to_map M) ->
    scong M s_zero.
Proof.
    intros * Hnd H.
    induction M.
    red in H;simpl in H;specialize (H n). autorewrite with mmaps in H;easy.
    assert(scong (s_zero|||s_zero) s_zero). eauto with brocs.
    Search noDupSess MF.Disjoint.
    eapply sess_to_map_noDup_to_disj in Hnd as Hdisj.
    rewrite sess_to_map_disj_merge with (Hdisj:=Hdisj) in H;try easy.
    unfold disj_merge in H. 
    assert(Hem1  :M.Equal M.empty (sess_to_map M1)).
    {
        red;intros;specialize (H y). 
        rewrite MF.merge_spec1mn in H;try easy. autorewrite with mmaps in H.
        destruct (M.find y (sess_to_map M1)) eqn:Hg1;destruct (M.find y (sess_to_map M2)) eqn:Hg2;
        simpl in H;try easy.
        red in Hdisj. specialize (Hdisj y). eapply opt_lem2 in Hg1, Hg2. rewrite <- MF.in_find in Hg1, Hg2.
        tauto.
    }
    assert(Hem2  :M.Equal M.empty (sess_to_map M2)).
    {
        red;intros;specialize (H y). 
        rewrite MF.merge_spec1mn in H;try easy. autorewrite with mmaps in H.
        destruct (M.find y (sess_to_map M1)) eqn:Hg1;destruct (M.find y (sess_to_map M2)) eqn:Hg2;
        simpl in H;try easy.
        red in Hdisj. specialize (Hdisj y). eapply opt_lem2 in Hg1, Hg2. rewrite <- MF.in_find in Hg1, Hg2.
        tauto.
    }
    eapply noDupSess_par in Hnd as Hnp;destr_hyps.
    eapply IHM1 in Hem1;
    eapply IHM2 in Hem2;try easy. eauto with brocs.
    eauto with brocs.
Qed.

Create HintDb brocs_pres.
Hint Rewrite scong_preserves_forallT
scong_preserves_noDup_zero scong_preserves_part  :brocs_pres.
Hint Resolve noDupSess_par :brocs_pres.


Ltac subtac_nodup_par:= match goal with 
[H: noDupSess (?a ||| ?b)|- noDupSess ?a ] => 
eapply noDupSess_par in H;destruct H;try easy
| [H: noDupSess (?a ||| ?b)|- noDupSess ?b ] => 
eapply noDupSess_par in H;destruct H;try easy end.


Lemma map_equal_implies_scong : forall M M' Mp Mp', noDupSess M -> 
noDupSess M' ->
M.Equal Mp  (sess_to_map M) ->
M.Equal Mp' (sess_to_map M') ->
M.Equal Mp Mp' ->scong M M'.
Proof.
    intros * Hnd Hnd' Hs1 Hs2 Heq. generalize dependent M'.
    generalize dependent Mp'.
    generalize dependent M. 

    induction Mp using MF.map_induction;intros.
    {
        assert(Heqm1: M.Equal M.empty Mp').
        {
            red;intros. red in Hs2, Heq, Hs1.
            autorewrite with mmaps. 
            specialize (Hs2 y).
            specialize (Heq y). specialize (Hs1 y).
            assert(M.find y (sess_to_map M)=None).
            red in H.
            destruct (M.find y (sess_to_map M)) eqn:Hg;try easy.
            specialize (H y p).
            rewrite <- M.find_spec in H. easy.
            congruence.               
        }
        assert(Heqm2: M.Equal M.empty Mp).
        {
            red;intros. red in Hs2, Heq, Hs1.
            autorewrite with mmaps. 
            specialize (Hs2 y).
            specialize (Heq y). specialize (Hs1 y).
            assert(M.find y (sess_to_map M)=None).
            red in H.
            destruct (M.find y (sess_to_map M)) eqn:Hg;try easy.
            specialize (H y p).
            rewrite <- M.find_spec in H. easy.
            congruence.   
        }
        
        subst.
        rewrite Hs1 in Heqm2.
        rewrite Hs2 in Heqm1.
        eapply sess_map_empty_implies_scong_zero in Heqm1, Heqm2;try easy.
        eauto with brocs.
    }
    {
        subst.
        red in H0.
        assert(InT x M).
        {
            eapply sess_map_inT_to_in;try easy.
            specialize (H0 x). autorewrite with mmaps in H0.
            eapply opt_lem2 in H0. rewrite MF.in_find;try easy.
            rewrite <- Hs1. easy.   
        }
        assert(M.In x Mp').
        {
            rewrite MF.in_find. 
            specialize (H0 x).
            specialize (Hs1 x).
            specialize (Hs2 x).
            autorewrite with mmaps in *.
            assert(M.find x Mp' =Some e) by congruence.
            eapply opt_lem2 in H2;try easy.   
        }
        assert(InT x M').
        {
            eapply sess_map_inT_to_in;try easy.
            rewrite <- Hs2. easy.  
        }

        
        eapply move_forward_h_scong in H1;destr_hyps.
        eapply scong_trans;try exact H1.
        
        specialize (IHMp1 x1).
        eapply move_forward_h_scong in H3;destr_hyps.

        assert(Hnd1: noDupSess ((x <--x0)|||x1)) by
                (eapply scong_preserves_noDup_zero in H1;
                rewrite H1 in Hnd;easy). 
            assert(Hnd2: noDupSess ((x <--x2)|||x3)) by
                (eapply scong_preserves_noDup_zero in H3;
                rewrite H3 in Hnd';easy).
            assert(Hinf1: ~ InT x x1 ). 
            {
                red;intros. red in H4. red in Hnd1. simpl in Hnd1. 
                inversion Hnd1;try easy.   
            }
            assert(Hinf2: ~ InT x x3 ). 
            {
                red;intros. red in H4. red in Hnd2. simpl in Hnd2. 
                inversion Hnd2;try easy.   
            }
        assert(Hsx: scong x1 x3).
        {
            
            eapply IHMp1;try easy;
            try solve subtac_nodup_par.
            red;intros.
            eapply scong_to_map in H1;try easy.
            
            destruct (Nat.eq_dec x y);subst.
            {
                rewrite sess_map_inT_to_in in Hinf1.
                
                rewrite MF.not_in_find in H.
                rewrite MF.not_in_find in Hinf1. congruence. subtac_nodup_par.         
            }
            {
                specialize (H1 y).
                simpl in H1. rewrite MF.merge_spec1mn in H1.
                autorewrite with mmaps in H1.
                specialize (H0 y). autorewrite with mmaps in H0.
                specialize (Hs1 y).
                destruct (M.find y (sess_to_map x1)) eqn:Hg;simpl in H1;try congruence.
                1-2:easy.   
            }
            red;intros.
            eapply scong_to_map in H3;try easy.
            destruct (Nat.eq_dec x y);subst.
            {
                rewrite sess_map_inT_to_in in Hinf2.
                
                rewrite MF.not_in_find in H.
                rewrite MF.not_in_find in Hinf2. congruence. subtac_nodup_par.         
            }
            {
                specialize (H3 y).
                simpl in H3. rewrite MF.merge_spec1mn in H3.
                autorewrite with mmaps in H3.
                specialize (H0 y). autorewrite with mmaps in H0.
                specialize (Hs1 y). specialize (Heq y). specialize (Hs2 y).
                destruct (M.find y (sess_to_map x3)) eqn:Hg;simpl in H3;try congruence.
                1-2:easy.   
            }
        }   
        assert(x0=x2).
        {
            eapply scong_to_map in H1;
            eapply scong_to_map in H3;try easy.
            repeat 
            (match goal with [H: M.Equal _ _ |-  _ ]=> specialize (H x) end).
            simpl in H1. simpl in H3.
            rewrite MF.merge_spec1mn in *;try easy.
            autorewrite with mmaps in *.
            rewrite sess_map_inT_to_in in Hinf1 , Hinf2;try subtac_nodup_par.
            rewrite MF.in_find in Hinf1, Hinf2.
            destruct (M.find x (sess_to_map x1)) eqn:Hg1;
            destruct (M.find x (sess_to_map x3)) eqn:Hg2;
            red in Hinf1, Hinf2;
            try solve 
            [exfalso;eapply Hinf1;easy | exfalso;eapply Hinf2;easy].
            simpl in H1, H3. congruence.
        }
        subst.
        eauto with brocs.
    }
Qed.

Lemma scong_par_elim : forall M M' p P Q, noDupSess (((p <--P) ||| M)) ->
 scong ((p <--P) ||| M)
 ((p <--Q) ||| M') -> scong M M'.
Proof.
    intros * Hd ?Hs.
    assert(Hd2 : noDupSess ((p<--Q) |||M')). eapply scong_sym in Hs; 
    eapply scong_preserves_noDup_zero;try exact Hs;try easy.
    assert(Hinp1: ~InT p M). red in Hd;simpl in Hd;inversion Hd;subst;red;intros;easy.
    assert(Hinp2: ~InT p M'). red in Hd2;simpl in Hd2;inversion Hd2;subst;red;intros;easy.
    rewrite sess_map_inT_to_in in Hinp1, Hinp2;try subtac_nodup_par.
    rewrite MF.not_in_find in Hinp1, Hinp2.
    eapply scong_to_map in Hs;try easy.
    eapply map_equal_implies_scong with (Mp:=sess_to_map M);try subtac_nodup_par;try easy.
    red;intros;specialize (Hs y).
    destruct (Nat.eq_dec y p);subst.
    {
        congruence.   
    }
    {
        simpl in Hs;autorewrite with mmaps in Hs.
        do 2 rewrite MF.merge_spec1mn in Hs;try easy.
        autorewrite with mmaps in Hs.
        destruct (M.find y (sess_to_map M)) eqn:Hg;   
        destruct (M.find y (sess_to_map M')) eqn:Hg';
        simpl in Hs;try easy.
    }
Qed.

Lemma unfoldB_preserves_noDup : forall M M', unfoldB M M' -> noDupSess M  <-> noDupSess M'.
Proof.
    intros; induction H;try tauto; eapply unfoldB_preserves_noDup_single in H; easy.
Qed.

Lemma scong_unfold_send_still_same : forall M p M' q ell e P' M'', 
noDupSess M ->
scong M (( p <-- p_send q ell e P') ||| M' ) ->
unfoldP M M'' -> exists M''', scong M'' (( p <-- p_send q ell e P') ||| M''' ).
Proof.
    intros * Hnd Hscong Hunf.
    revert Hscong.
    revert p q ell e P'.
    generalize dependent M'.
    eapply unfoldP_to_unfoldB in Hunf.
    dependent induction Hunf.
    {
        inversion H;subst.
        intros.   
        assert(Hinp: InT p M').
        {
            eapply scong_preserves_part with (p:=p) in Hscong as Hpr.
            unfold InT in Hpr;simpl in Hpr. 
            assert(p0=p \/ In p (flattenT M')) by tauto.
            destruct H1;subst;try easy.
            eapply scong_p_unique in Hscong;try easy;subst. inversion H0;subst;inversion H1.        
        }
        eapply move_forward_h_scong in Hinp. destr_hyps.
        exists ((p <-- Q)|||x0).
        assert(Hs2 : scong ((p <-- P) ||| M)
        ((p0 <-- p_send q ell e P') ||| ((p <-- x) ||| x0))). eauto with brocs.

        assert(Hs3 : scong ((p <-- P) ||| M)
        ( (p <-- x) ||| ((p0 <-- p_send q ell e P') ||| x0))). eauto with brocs.
        Hint Resolve scong_p_unique :brocs. 
        assert(P=x). eauto with brocs.
        subst. 
        eapply scong_par_elim in Hs3;try easy.
        eauto with brocs.
        intros. eauto with brocs.           
    }
    {
        intros. exists M'. easy.   
    }
    {
        intros.
        eapply IHHunf1 in Hscong as IHu;destr_hyps;try easy.
        eapply IHHunf2 in H. easy.
        
        eapply unfoldB_preserves_noDup in Hunf1. tauto.
    }
Qed.

Lemma scong_unfold_recv_still_same : forall M p M' q llp M'', 
noDupSess M ->
scong M (( p <-- p_recv q llp) ||| M' ) ->
unfoldP M M'' -> exists M''', scong M'' (( p <-- p_recv q llp) ||| M''' ).
Proof.
    intros * Hnd Hscong Hunf.
    revert Hscong.
    revert p q llp.
    generalize dependent M'.
    eapply unfoldP_to_unfoldB in Hunf.
    dependent induction Hunf.
    {
        inversion H;subst.
        intros.   
        assert(Hinp: InT p M').
        {
            eapply scong_preserves_part with (p:=p) in Hscong as Hpr.
            unfold InT in Hpr;simpl in Hpr. 
            assert(p0=p \/ In p (flattenT M')) by tauto.
            destruct H1;subst;try easy.
            eapply scong_p_unique in Hscong;try easy;subst. inversion H0;subst;inversion H1.        
        }
        eapply move_forward_h_scong in Hinp. destr_hyps.
        exists ((p <-- Q)|||x0).
        assert(Hs2 : scong ((p <-- P) ||| M)
        ((p0 <-- p_recv q llp) ||| ((p <-- x) ||| x0))). eauto with brocs.

        assert(Hs3 : scong ((p <-- P) ||| M)
        ( (p <-- x) ||| ((p0 <-- p_recv q llp) ||| x0))). eauto with brocs.
        Hint Resolve scong_p_unique :brocs. 
        assert(P=x). eauto with brocs.
        subst. 
        eapply scong_par_elim in Hs3;try easy.
        eauto with brocs.
        intros. eauto with brocs.           
    }
    {
        intros. exists M'. easy.   
    }
    {
        intros.
        eapply IHHunf1 in Hscong as IHu;destr_hyps;try easy.
        eapply IHHunf2 in H. easy.
        
        eapply unfoldB_preserves_noDup in Hunf1. tauto.
    }
Qed.

Lemma noDup_after_unf : forall M M', unfoldP M M' -> 
    noDupSess M <-> noDupSess M'.
Proof.
    intros. eapply unfoldP_to_unfoldB in H.
    eapply unfoldB_preserves_noDup;easy.
Qed.

Lemma noDup_after_beta: forall M M', betaP M M' -> noDupSess M <-> noDupSess M'.
Proof.
    intros. red in H. destr_hyps. induction H.
    unfold noDupSess;simpl. easy.
    eapply noDup_after_unf in H. eapply noDup_after_unf in H0. tauto.
Qed.

Lemma proc_same_after_distinct_trans_send: 
    forall M M' M'' p q p' q' ell ell' e P',
    noDupSess M ->    
    scong M ((p<-- p_send q ell e P')|||M') ->
    betaP_lbl M (lcomm p' q' ell') M'' ->
    p' <> p -> q' <> p -> p' <> q' ->
    exists M''', scong M'' ((p<-- p_send q ell e P')|||M''').
Proof.
    intros * Hnd  Hscong Hbeta Hpp Hqp Hpqp.
    generalize dependent M'.    
    dependent induction Hbeta;intros.
    {
        assert(Hinp: InT p M). {
            eapply scong_preserves_part with (p:=p) in Hscong. unfold InT at 2 in Hscong.
            simpl in Hscong. 
            assert(InT p (((q' <-- p_recv p' xs) ||| (p' <-- p_send q' ell' e0 Q))
            ||| M)). tauto.
            red in H1. simpl in H1. tauto.
        } 
        eapply move_forward_h_scong in Hinp. destr_hyps.
        assert(Hinp: InT p' M'). {
            eapply scong_preserves_part with (p:=p') in Hscong.
            unfold InT at 1 in Hscong. simpl in Hscong.
            assert(InT p' ((p <-- p_send q ell e P') ||| M')). tauto.
            red in H2;simpl in H2. destruct H2;subst;try easy.
        }
        eapply move_forward_h_scong in Hinp.  destr_hyps.
        assert(Hinq: InT q' x2).
        { 
            eapply scong_preserves_part with (p:=q') in Hscong.
            unfold InT at 1 in Hscong. simpl in Hscong.  
            assert(InT q' ((p <-- p_send q ell e P') ||| M')) by tauto.
            red in H3;simpl in H3;destruct H3;subst;try easy.
            eapply scong_preserves_part with (p:=q') in H2. 
            rewrite H2 in  H3.
            red in H3;simpl in H3;destruct H3;subst;easy.
        } 
        eapply move_forward_h_scong in Hinq. destr_hyps.
        assert(Hst1: scong ((q' <-- p_recv p' xs) ||| ((p' <-- p_send q' ell' e0
        Q) ||| ((p <-- x) ||| x0))) ((p <-- p_send q ell e P') ||| M')). eauto with brocs.

        assert(Hst2: scong M' ((p' <-- x1)||| ((q' <--x3) |||x4))). eauto with brocs.
        clear Hscong.
        assert(Hst3: scong (((q' <-- p_recv p' xs) ||| (p' <-- p_send q' ell' e0 Q)) ||| ((p <-- x) ||| x0)) 
        ((p <-- p_send q ell e P') ||| ((p' <-- x1) ||| ((q' <-- x3) ||| x4)))
        ). eauto with brocs.
        exists (((q' <-- subst_expr_proc y (e_val v) 0 0) ||| (p' <-- Q))
        ||| x0).
        assert(x=p_send q ell e P').
        {   assert(
            scong     
            ((p <-- x)  ||| ((q' <-- p_recv p' xs) ||| (p' <-- p_send q' ell' e0 Q) ||| x0))
            ((p <-- p_send q ell e P') ||| ((p' <-- x1)
            ||| ((q' <-- x3) ||| x4)))).
            eauto with brocs.
            eapply scong_p_unique in H4. try easy.
            
            assert(
            scong (((q' <-- p_recv p' xs) ||| (p' <-- p_send q' ell' e0 Q)) ||| M)
             (((q' <-- p_recv p' xs) ||| (p' <-- p_send q' ell' e0 Q))
        ||| (p <-- x ||| x0))). eauto with brocs.
            red;simpl.
        eapply scong_preserves_noDup_zero in H5.
        rewrite H5 in Hnd. red in Hnd;simpl in Hnd.
        move Hnd at bottom.
            inversion Hnd;subst. inversion H9;subst.
            inversion H11;subst.
            repeat (try constructor);try easy;
            red;intros. inversion H6;try easy.
            inversion H7;try easy.


            inversion H6;try easy.
            eapply H8. constructor 2. constructor 2. easy.
            
            eapply H10. constructor 2. easy.
        }
        subst.
        eauto with brocs.
    }
    {
        assert(noDupSess M1'). eapply noDup_after_unf in H;try tauto.
        assert (Hnd2: noDupSess M2'). 
        {
            assert(Hb:betaP M1' M2') by (red;exists (lcomm p' q' ell');easy).
            eapply noDup_after_beta in Hb;tauto. 
        }
        assert (Hnd3: noDupSess M2). 
        {
            eapply noDup_after_unf in H0;try tauto.
        }
        eapply scong_unfold_send_still_same in H as Hs2;try exact Hscong;try easy.
        destr_hyps.
        eapply IHHbeta in H2 as Ht1;try reflexivity;try easy.
        destr_hyps.
        eapply IHHbeta in H1;try reflexivity;try easy;try exact H2.
        eapply scong_unfold_send_still_same in H0;try exact H3;try easy.
    }
Qed.

Lemma proc_same_after_distinct_trans_recv: 
    forall M M' M'' p q p' q' ell' llp,
    noDupSess M ->    
    scong M ((p<-- p_recv q llp)|||M') ->
    betaP_lbl M (lcomm p' q' ell') M'' ->
    p' <> p -> q' <> p -> p' <> q' ->
    exists M''', scong M'' ((p<-- p_recv q llp)|||M''').
Proof.
    intros * Hnd  Hscong Hbeta Hpp Hqp Hpqp.
    generalize dependent M'.    
    dependent induction Hbeta;intros.
    {
        assert(Hinp: InT p M). {
            eapply scong_preserves_part with (p:=p) in Hscong. unfold InT at 2 in Hscong.
            simpl in Hscong. 
            assert(InT p (((q' <-- p_recv p' xs) ||| (p' <-- p_send q' ell' e Q))
            ||| M)). tauto.
            red in H1. simpl in H1. tauto.
        } 
        eapply move_forward_h_scong in Hinp. destr_hyps.
        assert(Hinp: InT p' M'). {
            eapply scong_preserves_part with (p:=p') in Hscong.
            unfold InT at 1 in Hscong. simpl in Hscong.
            assert(InT p' ((p <-- p_recv q llp) ||| M')). tauto.
            red in H2;simpl in H2. destruct H2;subst;try easy.
        }
        eapply move_forward_h_scong in Hinp.  destr_hyps.
        assert(Hinq: InT q' x2).
        { 
            eapply scong_preserves_part with (p:=q') in Hscong.
            unfold InT at 1 in Hscong. simpl in Hscong.  
            assert(InT q' ((p <-- p_recv q llp) ||| M')) by tauto.
            red in H3;simpl in H3;destruct H3;subst;try easy.
            eapply scong_preserves_part with (p:=q') in H2. 
            rewrite H2 in  H3.
            red in H3;simpl in H3;destruct H3;subst;easy.
        } 
        eapply move_forward_h_scong in Hinq. destr_hyps.
        assert(Hst1: scong ((q' <-- p_recv p' xs) ||| ((p' <-- p_send q' ell' e
        Q) ||| ((p <-- x) ||| x0))) ((p <-- p_recv q llp) ||| M')). eauto with brocs.

        assert(Hst2: scong M' ((p' <-- x1)||| ((q' <--x3) |||x4))). eauto with brocs.
        clear Hscong.
        assert(Hst3: scong (((q' <-- p_recv p' xs) ||| (p' <-- p_send q' ell' e Q)) ||| ((p <-- x) ||| x0)) 
        ((p <-- p_recv q llp) ||| ((p' <-- x1) ||| ((q' <-- x3) ||| x4)))
        ). eauto with brocs.
        exists (((q' <-- subst_expr_proc y (e_val v) 0 0) ||| (p' <-- Q))
        ||| x0).
        assert(x=p_recv q llp).
        {   assert(
            scong     
            ((p <-- x)  ||| ((q' <-- p_recv p' xs) ||| (p' <-- p_send q' ell' e Q) ||| x0))
            ((p <-- p_recv q llp) ||| ((p' <-- x1)
            ||| ((q' <-- x3) ||| x4)))).
            eauto with brocs.
            eapply scong_p_unique in H4. try easy.
            
            assert(
            scong (((q' <-- p_recv p' xs) ||| (p' <-- p_send q' ell' e Q)) ||| M)
             (((q' <-- p_recv p' xs) ||| (p' <-- p_send q' ell' e Q))
        ||| (p <-- x ||| x0))). eauto with brocs.
            red;simpl.
        eapply scong_preserves_noDup_zero in H5.
        rewrite H5 in Hnd. red in Hnd;simpl in Hnd.
        move Hnd at bottom.
            inversion Hnd;subst. inversion H9;subst.
            inversion H11;subst.
            repeat (try constructor);try easy;
            red;intros. inversion H6;try easy.
            inversion H7;try easy.


            inversion H6;try easy.
            eapply H8. constructor 2. constructor 2. easy.
            
            eapply H10. constructor 2. easy.
        }
        subst.
        eauto with brocs.
    }
    {
        assert(noDupSess M1'). eapply noDup_after_unf in H;try tauto.
        assert (Hnd2: noDupSess M2'). 
        {
            assert(Hb:betaP M1' M2') by (red;exists (lcomm p' q' ell');easy).
            eapply noDup_after_beta in Hb;tauto. 
        }
        assert (Hnd3: noDupSess M2). 
        {
            eapply noDup_after_unf in H0;try tauto.
        }
        eapply scong_unfold_recv_still_same in H as Hs2;try exact Hscong;try easy.
        destr_hyps.
        eapply IHHbeta in H2 as Ht1;try reflexivity;try easy.
        destr_hyps.
        eapply IHHbeta in H1;try reflexivity;try easy;try exact H2.
        eapply scong_unfold_recv_still_same in H0;try exact H3;try easy.
    }
Qed.

Lemma betaP_lbl_pq : forall M M' p q ell, noDupSess M -> betaP_lbl M (lcomm p q ell) M' ->
    p <> q.
Proof.
    intros. dependent induction H0.
    {
        red;intros;subst;red in H;simpl in H;inversion H;subst. eapply H4.
        constructor. easy.   
    }
    {
        eapply IHbetaP_lbl;try reflexivity.
        eapply noDup_after_unf in H2;try easy. tauto.   
    }
Qed.

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

Lemma unfold_beta_unique_recv : 
forall M M' M'' p q llp q' ell' gamma, typ_sess M gamma ->
unfoldP M ((p <-- p_recv q llp)|||M'') ->
betaP_lbl M (lcomm q' p ell') M' -> q=q'.
Proof.
    intros * Hsess Hunf Hbet.
    eapply typ_after_unfold in Hsess as Hsess';try exact Hunf.
    inversion Hsess';subst. repeat destruct_forallT. destr_hyps.
    eapply inv_proc_recv in H5;try reflexivity;destr_hyps.
    eapply betaP_lbl_invert in Hbet as Hbinv;try exact Hsess.
    destr_hyps.
    eapply typ_after_unfold in Hsess as Hsess'';try exact H11.
    inversion Hsess'';subst. repeat destruct_forallT. destr_hyps.
    assert(x=x7) by congruence;subst.
    eapply inv_proc_recv in H21;try reflexivity;destr_hyps.
    pinversion H24;pinversion H8;subst;try apply sub_mon;congruence. 
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

Lemma unfold_ooo_lemma : forall p q P M M', InT q M -> unfoldP M ((p<-- P) |||M') ->
    p=q \/ InT q M'.
    Proof.
        intros * Hinq Hunf.
        eapply part_after_unf in Hunf;try exact Hinq. red in Hunf. simpl in Hunf.
        destruct Hunf;try tauto.
    Qed. 

Theorem sess_fidelity_strong : forall M gamma M' e p q ell ell' P' gamma', 
typ_sess M gamma -> tctxR gamma (lcomm p q ell) gamma' ->
unfoldP M ((p <-- p_send q ell' e P') |||M') ->
exists M'', betaP_lbl M (lcomm p q ell') M'' /\ 
exists M''', unfoldP M'' ((p <-- P')|||M''').
Proof.
	intros * Hsess Hgstep Hunf.
	eapply typ_after_unfold in Hunf as Hsess';try exact Hsess.
	eapply tctx_comm_invert in Hgstep as Hinvert;destr_hyps.
	
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
	eapply assoc.simul_subproj in Hsub1 as Hsim;try exact Hsub2;try easy.
	
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

Theorem sess_fidelity_strong_recv : forall M gamma M' llp p q ell  gamma', 
typ_sess M gamma -> tctxR gamma (lcomm q p ell) gamma' ->
unfoldP M ((p <-- p_recv q llp) |||M') ->
exists M'' ell', betaP_lbl M (lcomm q p ell') M'' /\ 
exists M''' e P', onth ell' llp = Some P' /\ 
unfoldP M'' ((p <-- subst_expr_proc P' e 0 0)|||M''').
Proof.
	intros * Hsess Hgstep Hunf.
	eapply typ_after_unfold in Hunf as Hsess';try exact Hsess.
	eapply tctx_comm_invert in Hgstep as Hinvert;destr_hyps.
	
	assert(Hinp: InT p M) by (
		inversion Hsess;subst;eapply H7; red;exists (ltt_recv q x3);split;try easy).

	assert(Hinq: InT q M) by 
    (inversion Hsess;subst;eapply H7; red;exists (ltt_send p x1);split;try easy).
	assert(Hpq : p<> q) by (red;intros;subst;congruence).
    inversion Hsess;destr_hyps;subst.
   	eapply assoc_inv_find in H as Hsub1;try exact H13;try easy.
	eapply assoc_inv_find in H0 as Hsub2;try exact H13;try easy.
	assert(Hpartp :isgPartsC q x5).
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
    Check assoc.simul_subproj.
	eapply assoc.simul_subproj in Hsub1 as Hsim;try exact Hsub2;try easy.
	
    eapply unfold_ooo_lemma in Hinq as Hinq';try exact Hunf.
    destruct Hinq';try easy.
    eapply move_forward_h in H10. destr_hyps.
    assert (Hunf1: unfoldP M ((p <-- p_recv q llp) ||| ((q <-- x6) ||| x7))) by
    eauto with procs.
    eapply typ_after_unfold in Hsess as Hsess2;try exact Hunf1.    
    
    inversion Hsess2;subst.
    repeat destruct_forallT.
    destr_hyps;subst.
    assert(x8=(ltt_send p x1)) by congruence;subst.
    assert(x9=(ltt_recv q x3)) by congruence;subst.
    eapply typ_proc_inv_send in H20 as Hdr;try easy.
    destr_hyps. eapply typ_after_tauRtc in H25 as Ht;try exact H20.
    eapply inv_proc_send in Ht;try reflexivity.
    destr_hyps.
    eapply subtype_send_inv in H28.
    eapply inv_proc_recv in H22 as Ht2;try reflexivity.
    destr_hyps.
    eapply subtype_recv_inv in H30. 
    assert(onth x8 (extendLis x8 (Some (x12,x13)))=(Some (x12,x13))) by (rewrite extendExtract;easy).
	eapply Forall2R_prop in H28;try exact H33;tac_sanitize.
    eapply Forall2R_prop in Hsim;try exact H35;tac_sanitize.
    eapply Forall2R_prop in H30;try exact H38;tac_sanitize. 
    eapply Forall2_prop_l in H31;try exact H34;tac_sanitize.
    eapply expr_eval_ss in H26;destr_hyps.
    assert(betaP_lbl (((p <-- (p_recv q llp)) ||| (q <-- p_send p x8 x9 x11) ||| x7)) 
    (lcomm q p x8) 
        ((p <-- subst_expr_proc x20 (e_val x12) 0 0) ||| (q <-- x11) ||| x7)).
    {
        eapply r_comm;try easy.   
    }
    
    assert (Hunfx1 : unfoldP M
    ((p <-- p_recv q llp) ||| (q <-- x6) ||| x7))
    by eauto with procs.
    
    assert(Hunfx2: unfoldP M  ((p <-- p_recv q llp) ||| (q <-- p_send p 
    x8 x9 x11)
    ||| x7)). eauto with procs.
    exists (((p <-- subst_expr_proc x20 (e_val x12) 0 0) ||| (q <-- x11) ||| x7)), x8.
        
    split.
    eapply r_struct with (M2':= ((p <-- subst_expr_proc x20 (e_val x12) 0 0) ||| (q <-- x11) ||| x7));
    try exact Hunfx2;try easy.
    eauto with procs.
    exists ((q <-- x11 ||| x7)), (e_val x12), x20.
    split;try easy.
    eauto with procs.
Qed.

Lemma live_proc_helper_send : forall p q ell e P xs ys, 
proc_path_head_scong_send p q ell e P ys->
proc_valid_pathC ys ->
eventually (headComm p q) xs -> 
typ_pathC  ys xs -> 
eventually (fun u=>  proc_path_head_scong_send p q ell e P u /\ 
        exists ell',  head_trans_proc p q ell' u) ys.
Proof.
    intros * Head Hvalid Hev Htyp. generalize dependent ys. induction Hev.
    {
        intros. destruct xs;try easy. destruct p0. destruct o;try easy.
        destruct l;try easy. simpl in H;destr_hyps;subst.
        pinversion Htyp;subst. constructor. split;try easy. exists n1;simpl. constructor; easy. 
    }
    {
        intros.
        pinversion Hvalid;subst;try apply valid_path_mon.
        {
            pinversion Htyp.   
        }
        {
            pinversion Htyp;subst. pinversion H5;subst. inversion Hev;subst. simpl in H. easy.   
        }
        {
            destruct l;try easy.
            destruct (Nat.eq_dec n p);subst.
            {
                simpl in Head.
                red in H0;destr_hyps.
                destruct H2 as [gamma Htyp2].
                Check unfold_beta_unique_send.
                eapply scong_to_unfoldP in H1 as Hunf.
                destr_hyps.
                eapply unfold_beta_unique_send in H2;try exact H0;try exact Htyp2.
                subst.
                constructor.
                split;simpl. exists x1. easy.
                exists n1. tauto.
                inversion Htyp2;easy.
            }
            destruct (Nat.eq_dec n0 p);subst.
            {
                simpl in Head.
                red in H0. destr_hyps.
                
                destruct H2 as [gamma Htyp2].
                eapply betaP_lbl_invert in H0;try exact Htyp2.
                destr_hyps.
                eapply typ_after_unfold in Htyp2 as Hty3;try exact H0.
                eapply scong_to_unfoldP in H1 as Ht.
                destr_hyps.
                eapply typ_after_unfold in Htyp2 as Hty4; try exact H2.
                inversion Hty4;inversion Hty3;subst.
                repeat destruct_forallT. destr_hyps. 
                assert(x6=x8) by congruence;subst.
                eapply inv_proc_send in H17;try reflexivity.
                eapply inv_proc_recv in H21;try reflexivity.
                destr_hyps.
                pinversion H25;subst;try apply sub_mon.
                pinversion H29;try apply sub_mon.
                inversion Htyp2;easy.   
            }
            
            red in H0;destr_hyps.
            assert(n <> n0). eapply betaP_lbl_pq in H0;try easy. inversion H1. inversion H2;easy.
            simpl in Head. destr_hyps.
            eapply proc_same_after_distinct_trans_send in H0;try exact H3;try easy.
            destr_hyps.
            econstructor 2.
            eapply IHHev. simpl. exists x2. easy.
            easy. pinversion Htyp. easy.
            inversion H1. inversion H4;try easy.
        }
    }
Qed.

Lemma live_proc_helper_send2 : forall p q P ell e xs,
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
            simpl.   
            eapply proc_same_after_distinct_trans_send in Htab as Hd;
            try exact H;try easy.
            inversion Htypable. inversion H0. easy.
            eapply betaP_lbl_pq in Htab;try easy. inversion Htypable;inversion H0;easy.
        }
        {
            econstructor 2. easy.
            right. eapply CIH;try easy.
            assert(Hnodup: noDupSess s) by (inversion Htypable; inversion H;easy).
            simpl in Hphead. destr_hyps.  
            eapply proc_same_after_distinct_trans_send in Htab as Hd;try exact H;try easy.
            red;intros;subst.
            destruct Htypable as [gamma Htyp].
            eapply betaP_lbl_invert in Htab as Hinv;destr_hyps;try exact Htyp.
            
            eapply typ_after_unfold in H0 as Ht2;try exact Htyp.
            eapply typ_after_scong in H as Ht3;try exact Htyp.
            inversion_clear Ht3.
            inversion_clear Ht2.
            repeat destruct_forallT.
            destr_hyps.
            assert(x5=x7) by congruence;subst.
            eapply inv_proc_send in H15;try reflexivity.
            eapply inv_proc_recv in H19;try reflexivity.
            destr_hyps.
            pinversion H27;pinversion H23;subst;try apply sub_mon;try easy.
            eapply betaP_lbl_pq in Htab;easy.
        }
    }
Qed.

Lemma live_proc_helper_recv : forall p q llp xs ys, 
proc_path_head_scong_recv p q llp ys->
proc_valid_pathC ys ->
eventually (headComm q p) xs -> 
typ_pathC  ys xs -> 
eventually (fun u=>  proc_path_head_scong_recv p q llp u /\ 
        exists ell',  head_trans_proc q p ell' u) ys.
Proof.
    intros * Head Hvalid Hev Htyp. generalize dependent ys. induction Hev.
    {
        intros. destruct xs;try easy. destruct p0. destruct o;try easy.
        destruct l;try easy. simpl in H;destr_hyps;subst.
        pinversion Htyp;subst. constructor. split;try easy. exists n1;simpl. constructor; easy. 
    }
    {
        intros.
        pinversion Hvalid;subst;try apply valid_path_mon.
        {
            pinversion Htyp.   
        }
        {
            pinversion Htyp;subst. pinversion H5;subst. inversion Hev;subst. simpl in H. easy.   
        }
        {
            destruct l;try easy.
            destruct (Nat.eq_dec n p);subst.
            {
                simpl in Head.
                red in H0. destr_hyps.
                
                destruct H2 as [gamma Htyp2].
                eapply betaP_lbl_invert in H0;try exact Htyp2.
                destr_hyps.
                eapply typ_after_unfold in Htyp2 as Hty3;try exact H0.
                eapply scong_to_unfoldP in H1 as Ht.
                destr_hyps.
                eapply typ_after_unfold in Htyp2 as Hty4; try exact H2.
                inversion Hty4;inversion Hty3;subst.
                repeat destruct_forallT. destr_hyps. 
                assert(x6=x7) by congruence;subst.
                eapply inv_proc_recv in H17;try reflexivity.
                eapply inv_proc_send in H19;try reflexivity.
                destr_hyps.
                pinversion H26;subst;try apply sub_mon.
                pinversion H27;try apply sub_mon.
                inversion Htyp2;easy.   
            }
            destruct (Nat.eq_dec n0 p);subst.
            {
                 simpl in Head.
                red in H0;destr_hyps.
                destruct H2 as [gamma Htyp2].
                eapply scong_to_unfoldP in H1 as Hunf.
                destr_hyps.
                eapply unfold_beta_unique_recv in H2;try exact H0;try exact Htyp2.
                subst.
                constructor.
                split;simpl. exists x1. easy.
                exists n1. tauto.
                inversion Htyp2;easy. 
            }
            
            red in H0;destr_hyps.
            assert(n <> n0). eapply betaP_lbl_pq in H0;try easy. inversion H1. inversion H2;easy.
            simpl in Head. destr_hyps.
            eapply proc_same_after_distinct_trans_recv in H0;try exact H3;try easy.
            destr_hyps.
            econstructor 2.
            eapply IHHev. simpl. exists x2. easy.
            easy. pinversion Htyp. easy.
            inversion H1. inversion H4;try easy.
        }
    }
Qed.


Lemma live_proc_helper_recv2 : forall p q llp xs,
        p <> q ->
        proc_valid_pathC xs ->
        proc_path_head_scong_recv p q llp xs -> 
        weak_untilC ((fun u=> 
        match u with | conil => True
        | x => proc_path_head_scong_recv p q llp x
         end)) 
        (fun u=>  proc_path_head_scong_recv p q llp u /\ 
        exists ell',  head_trans_proc q p ell' u) xs. 
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
        destruct (Nat.eq_dec n0 p);destruct (Nat.eq_dec n q);subst;try easy.
        {
            econstructor 1. simpl in Hphead. simpl. destr_hyps. 
            split. exists x0; tauto.
            exists n1;tauto.
        }
        {
            simpl in Hphead.
            
            red in Htypable. destr_hyps.
            eapply unfold_beta_unique_recv with (q:=q) (llp:=llp) (M'':=x1)  in Htab as Hunfq; 
            try exact H;subst;try easy.
            eapply unfoldB_to_unfoldP. inversion H;try easy.
            econstructor 1. econstructor 2. easy.
        }
        {
            econstructor 2. easy.
            right. eapply CIH;try easy.
            simpl in Hphead.  destr_hyps.
            simpl.   
            eapply proc_same_after_distinct_trans_recv in Htab as Hd;
            try exact H;try easy.
            inversion Htypable. inversion H0. easy.
            eapply betaP_lbl_pq in Htab;try easy. inversion Htypable;inversion H0;easy.
        }
        {
            econstructor 2. easy.
            right. eapply CIH;try easy.
            assert(Hnodup: noDupSess s) by (inversion Htypable; inversion H;easy).
            simpl in Hphead. destr_hyps.  
            eapply proc_same_after_distinct_trans_recv in Htab as Hd;
            try exact H;try easy.
            red;intros;subst.
            destruct Htypable as [gamma Htyp].
            eapply betaP_lbl_invert in Htab as Hinv;destr_hyps;try exact Htyp.
            
            eapply typ_after_unfold in H0 as Ht2;try exact Htyp.
            eapply typ_after_scong in H as Ht3;try exact Htyp.
            inversion_clear Ht3.
            inversion_clear Ht2.
            repeat destruct_forallT.
            destr_hyps.
            assert(x5=x6) by congruence;subst.
            eapply inv_proc_send in H17;try reflexivity.
            eapply inv_proc_recv in H15;try reflexivity.
            destr_hyps.
            pinversion H27;pinversion H23;subst;try apply sub_mon;try easy.
            eapply betaP_lbl_pq in Htab;easy.
        }
    }
Qed.

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

Lemma extends_to_fair_implies_live : fairness_feasible -> forall M gamma, typ_sess M gamma -> live_sess M.
Proof. 
	intros Ax_fairness * Hsess. red. intros. split.
	{
		intros * Hpq H0.
		specialize (Ax_fairness ((p <-- p_send q ell e P') ||| M')). red in Ax_fairness.
        assert(Htypr : typable ((p <-- p_send q ell e P') ||| M')).
        {
            red. eapply sub_red_Rtc in H;
            try exact Hsess;destr_hyps. eapply typ_after_unfold in H0;try exact H. exists x;easy.   
        }
        specialize (Ax_fairness Htypr). destr_hyps.
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
        eapply live_proc_helper_send with (ell:=ell) (e:=e)
        (P:=P') in Hev_local_trans as Hlpr;try exact H1;try easy.
        eapply  live_proc_helper_send2 with (p:=p) (q:=q) (ell:=ell) (e:=e) (P:=P') in H2 as Hweak;try easy;
        try solve [simpl; exists M'; eauto with brocs].
        eapply weak_untilC_to_until in Hweak as Hunt;
        try solve[
        rewrite eventually_P_iff_P_suffix in Hlpr; destr_hyps;
        rewrite eventually_P_iff_P_suffix; exists x2; split;try easy; exists ell'; easy].
        eapply until_suf in Hunt.
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
             assert(Hnd1 : noDupSess s). {inversion H13; inversion H14;try easy. }
             
             assert(Hnd2 : noDupSess s0). {inversion Htyp0; easy. }
            eapply scong_to_unfoldP in H7;try easy.
            destruct H7 as [H7 _].
             eapply sess_fidelity_strong in H9;try exact Htyp0;try exact H7.
             destr_hyps.
            assert(Hbets0: betaP_lbl s0 (lcomm n n0 ell) ((n <-- P') ||| x6)).
            eapply r_struct;try exact H9;eauto with procs.
             assert(Hbet2: betaRtc M0 s \/ unfoldP M0 s).
            {
                eapply unfoldP_to_betaRtc with (M:=M0) in Hbet1;try easy.
            }
            assert(Hbetr: betaRtc s ((n <-- P') ||| x6)). {
                econstructor 3 with (y:=s0).
                econstructor 1. exists (lcomm n2 n3 n4). easy.
                econstructor 1. exists (lcomm n n0 ell). easy.
            }
            destruct Hbet2 as [Hbet2 | Hbet2].
            {
                exists x6. econstructor 3;try exact Hbet2;try easy.   
            }
            {
                exists x6.
                assert(Hbet3 : betaP M0 s0).
                exists (lcomm n2 n3 n4).
                econstructor 2;try exact Hbet2;try exact H12;eauto with procs.
                econstructor 3 with (y:=s0);try easy.
                econstructor 1;easy.
                econstructor 1. exists (lcomm n n0 ell). easy.
            }
        }
        easy.
        simpl. exists M';eauto with brocs.
        eapply typ_after_unfold in Hsess;try exact H0. easy.
    }
    {
		intros * Hpq H0.
		specialize (Ax_fairness ((p <-- p_recv q llp) ||| M')). red in Ax_fairness. 
        assert(Htypr : typable ((p <-- p_recv q llp) ||| M')).
        {
            red. eapply sub_red_Rtc in H;
            try exact Hsess;destr_hyps. eapply typ_after_unfold in H0;try exact H. exists x;easy.   
        }
        specialize (Ax_fairness Htypr). destr_hyps.
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

        assert(Hev_local_trans: eventually (headComm q p) (cocons (gamma', x) x1)
        ).
        {
            red in Hlive_path.
            eapply typ_path_preserves_fairness in H3 as Hfair_local;try exact H1;try easy.
            eapply Hlive_path in Hfair_local;try exact H4.
            pinversion Hfair_local;subst. red in H7.
            assert(exists s ell xsp Tp', 
            M.find p gamma' = Some (ltt_recv q xsp) 
            /\ onth ell xsp = Some (s,Tp')).
            {
                eapply typ_after_unfold in H0;try exact Hsess. inversion H0;subst. inversion_clear H10.
                inversion_clear H11. destr_hyps.  
                eapply inv_proc_recv in H13;try reflexivity. destr_hyps.
                 
                pose proof H16 as Hsub.
                pinversion H16;subst;try apply sub_mon.
                specialize (H5 _ _ H10).
                pinversion H5;subst;try apply wfltt.wfltt_mon.
                eapply slist_implies_some in H21.
                destr_hyps.
                destruct x5.
                exists s, x2, ys, l.
                repeat split;try easy.
            }
            destr_hyps.
            assert(tctxRE (lrecv p q (Some x2) x3) gamma').
            red. exists (m_update p x5 gamma').
            eapply simple_red_recv ;try exact H5;try easy.
            specialize (H7 p q x2 x3).
            destr_hyps.
            eapply H10. simpl. easy.
        }
        eapply live_proc_helper_recv with (llp:=llp) in Hev_local_trans as Hlpr;try exact H1;try easy.
        eapply  live_proc_helper_recv2 with (p:=p) (q:=q) (llp:=llp) in H2 as Hweak;try easy;
        try solve [simpl; exists M'; eauto with brocs].
        eapply weak_untilC_to_until in Hweak as Hunt;
        try solve[
        rewrite eventually_P_iff_P_suffix in Hlpr; destr_hyps;
        rewrite eventually_P_iff_P_suffix; exists x2; split;try easy; exists ell'; easy].
        eapply until_suf in Hunt.
        destruct Hunt.
        {
            destr_hyps. clear H5. rename H6 into H5. destruct x;try easy. destruct l;try easy. simpl in H5;destr_hyps;subst.
            pinversion H2;subst;try apply valid_path_mon. red in H9;destr_hyps.   
            destruct H6 as [gamma'' Hty].
            eapply sub_red_strong_labelled in H5 as Hss;try exact Hty.
            destr_hyps.
            eapply sess_fidelity_strong_recv in Hty;try exact H8;
            try solve [
            econstructor 2].
            destr_hyps.
            exists x4, x6,x5,x3.
            split;try easy.
            econstructor 1.
            red.
            exists (lcomm n n0 x3).
            eapply r_struct;try exact H9;try easy.
        }
        {
            destr_hyps.
            destruct x2. 
            assert(Hbet1 : betaRtc  ((p <-- p_recv q llp) ||| M') s).
            {
                eapply path_to_betaRtc with (xs:=cocons ((p <-- p_recv q llp) ||| M', x) x0);try easy.
                eapply eventually_P_iff_P_suffix. exists (cocons (s, o) x3).
                split;try easy.
            }
            
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
             assert(Hnd1 : noDupSess s). {inversion H13; inversion H14;try easy. }
             
             assert(Hnd2 : noDupSess s0). {inversion Htyp0; easy. }
            eapply scong_to_unfoldP in H7;try easy.
            destruct H7 as [H7 _].
             eapply sess_fidelity_strong_recv in H9;try exact Htyp0;try exact H7.
             destr_hyps.
            assert(Hbets0: betaP_lbl s0 (lcomm n n0 x6) ((n0 <-- subst_expr_proc x9 x8 0 0) ||| x7)).
            eapply r_struct;try exact H9;eauto with procs.
             assert(Hbet2: betaRtc M0 s \/ unfoldP M0 s).
            {
                eapply unfoldP_to_betaRtc with (M:=M0) in Hbet1;try easy.
            }
            assert(Hbetr: betaRtc s ((n0 <-- subst_expr_proc x9 x8 0 0) ||| x7)). {
                econstructor 3 with (y:=s0).
                econstructor 1. exists (lcomm n2 n3 n4). easy.
                econstructor 1. exists (lcomm n n0 x6). easy.
            }
            destruct Hbet2 as [Hbet2 | Hbet2].
            {
                exists x7, x9, x8, x6. split;try easy. econstructor 3;try exact Hbet2;try easy.   
            }
            {
                exists x7, x9, x8, x6.
                assert(Hbet3 : betaP M0 s0).
                exists (lcomm n2 n3 n4).
                econstructor 2;try exact Hbet2;try exact H12;eauto with procs.
                split;try easy.
                econstructor 3 with (y:=s0);try easy.
                econstructor 1;easy.
                econstructor 1. exists (lcomm n n0 x6). easy.
            }
        }
        easy.
        simpl. exists M';eauto with brocs.
        eapply typ_after_unfold in Hsess;try exact H0. easy.
    }
Qed.
