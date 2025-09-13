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
    unfoldP M ((p<-- p_send q ell e P')|||M') ->
    betaP_lbl M (lcomm p' q' ell') M'' ->
    p' <> p -> q' <> p ->
    exists M''' ell' e' P'', unfoldP M'' ((p<-- p_send q ell' e' P'')|||M''').
    Proof.
        intros * Htyp Hunf Hbeta Hpp Hqp.
        destruct Htyp as [gamma Htyp].
        eapply sub_red_strong_labelled in Hbeta as Hbeta';try exact Htyp;destr_hyps.
        eapply lem_6_10 with (r:=p) in H0.
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

Lemma live_proc_helper2 : forall p q  xs,
        p <> q ->
        proc_valid_pathC xs ->
        proc_path_head_unfolds_to_send p q xs -> 
        weak_untilC ((fun u=> 
        match u with | conil => True
        | x => proc_path_head_unfolds_to_send p q x 
         end)) 
        (fun u=> exists ell', head_trans_proc p q ell' u) xs. 
Proof.
    intros * Hpq.  generalize dependent xs. pcofix CIH. 
    intros * Hvalid Hphead. pfold.
    destruct xs;try easy. destruct p0;try easy.
    pinversion Hvalid;subst;try apply valid_path_mon.
    {
        econstructor 2. simpl in Hphead. destr_hyps. simpl. exists x, x0, x1, x2. easy. 
        left.  
        pfold. econstructor 3. easy.    
    }
    {
        destruct l;try easy. red in H3.
        destruct H3 as [Htab Htypable].
        destruct (Nat.eq_dec n p);destruct (Nat.eq_dec n0 q);subst;try easy.
        {
            econstructor 1. simpl. exists n1; tauto.
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
            eapply unfold_beta_unique_send in Htab as Hunfq;try exact Hphead;
            subst;try exact H0; try exact H;subst.
            easy.
        }
        {
            econstructor 2. easy.
            right. eapply CIH;try easy.
            simpl in Hphead. destr_hyps.  
            eapply proc_same_after_distinct_trans in Htab as Hd;try exact H;try easy.
        }
        {
            econstructor 2. easy.
            right. eapply CIH;try easy.
            simpl in Hphead. destr_hyps.  
            eapply proc_same_after_distinct_trans in Htab as Hd;try exact H;try easy.
            admit.
        }
    }
Admitted.


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
			Check liveness_global.
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
        eapply live_proc_helper in Hev_local_trans as Hlpr;try exact H1.
        destruct Hlpr as [ell' Hlpr].
        eapply  live_proc_helper2 with (p:=p) (q:=q) in H2 as Hweak;try easy;
        try solve [simpl; exists M', ell, e, P';  easy].
        eapply weak_untilC_to_until in Hweak as Hunt;
        try solve[
        rewrite eventually_P_iff_P_suffix in Hlpr; destr_hyps;
        rewrite eventually_P_iff_P_suffix; exists x2; split;try easy; exists ell'; easy].
        eapply until_suf in Hunt.
        destruct Hunt.
        {
            destr_hyps. destruct x;try easy. destruct l;try easy. simpl in H5;destr_hyps;subst.
            pinversion H2;subst;try apply valid_path_mon. red in H9;destr_hyps.   

            
            Lemma betaP_lbl_send_unique_comm : forall p q ell e P' M' ell' x, 
            typable ((p <-- p_send q ell e P') ||| M') ->
            betaP_lbl ((p <-- p_send q ell e P') ||| M') (lcomm p q ell') x ->
            exists M'', betaP_lbl ((p <-- p_send q ell e P') ||| M') (lcomm p q ell) 
            ((p <-- P') ||| M'').
            Proof.
                intros * Htyp Hbeta. destruct Htyp as [gamma Htyp]. 

                eapply betaP_lbl_invert in Hbeta as Hbinv;destr_hyps;try exact Htyp.
                Print unfoldP.
        Inductive scong : session -> session -> Prop :=
            | scong_refl : forall M, scong M M
            | scong_par_com : forall M1 M1' , scong (M1 ||| M1') (M1' ||| M1)
            | scong_par_ass: forall M1 M2 M3 , 
            scong (M1 ||| (M2 ||| M3))
            ((M1 ||| M2)|||M3)
            | scong_zero: forall M, scong M (M ||| s_zero)
            | scong_sym: forall M M', scong M M' -> scong M' M
            | scong_cong: forall M M' M'', scong M M' -> scong (M|||M'') (M' ||| M'').
            
        Lemma scong_implies_unfold : forall M M', scong M M' -> unfoldP M M'.
        Proof.
            intros. induction H;eauto 2 with procs.
            
                Lemma unfold_squeeze : forall p P M Q M',
                is_p_send P ->
                unfoldP ((p <-- P )|||M) M0 ->
                unfoldP M0 ((p <-- Q )|||M') ->

                Lemma unfoldP_split : forall p P M Q M', 
                typable ((p <-- P )|||M) ->
                unfoldP ((p <-- P )|||M) ((p<--Q) |||M') ->
                unfoldP (p <-- P) (p <-- Q) /\ unfoldP M M'.
                Proof.
                    intros * Htyp Hunf1.
                    
                    dependent induction Hunf1.
                    {
                        intros.
                        split; eauto with procs.
                    }
                    {
                        split;eauto with procs.   
                    }
                    {
                           
                    }
                    split. Print unfoldP. econstructor 3.

                    Search unfoldP.
                Definition is_p_send P:=exists q ell e P', P=p_send q ell e P'.    
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
                    generalize dependent gamma.
                    dependent induction Hunf;subst;try easy;intros.
                    red in Hse;destr_hyps;subst;inversion H;subst;inversion H0.
                    exists M';try constructor 2.
                    eapply IHHunf1 in Hse as Hse1;try reflexivity;try exact Htyp.
                    assert(Hinp: InT p M'0 ). 
                    {
                        eapply part_after_unf with (p:=p) in Hunf1;try easy. red;simpl;tauto.
                    }
                    eapply move_forward_h in Hinp;destr_hyps.
                    assert(Hunf3: unfoldP ((p <-- P) ||| M') ((p <-- x) ||| x0)) by eauto with procs.
                    eapply IHHunf1 in Hse.
                    admit.
                    inversion Htyp;subst. simpl in H1. inversion H1;subst. 
                    exfalso;eapply H5;simpl;tauto.
                Admitted.
                Search unfoldP.
                evar (Ms : session). exists Ms.
                econstructor 2 with (M1':=((p <-- p_send q ell e P') ||| M')) (M2':=(p <-- P') ||| Ms).
                constructor 2. constructor 2.
                dependent induction Hbeta.
        }
        destruct xs.
        eapply eventually_P_iff_P_suffix in Hev;destr_hyps.

    }

