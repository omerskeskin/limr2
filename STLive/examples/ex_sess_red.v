(* From mathcomp Require Import all_boot. *)
Require Import List String Coq.Arith.PeanoNat Coq.Program.Equality Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From live_mpst.STBase Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh src.step src.merge src.projection.  
From live_mpst.STBase Require Import lemma.inversion lemma.inversion_expr lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step
lemma.projection_helper  lemma.projection. 
From live_mpst.STLive Require Import src.lcontext src.session lemma.subj_red_helpers lemma.subj_red_prog_fid lemma.live_proc lemma.fairness_feasible.

Require Import Lia.
Definition pt_s := 0.
Definition pt_c := 1.
Definition pt_a := 2.
Definition msg_login:=0.
Definition msg_auth:=1.
Definition msg_cancel:=2.
Definition msg_pwd:=3.
Definition msg_quit:=4.
(*Print process.*)
Notation " # e #":= (e_val (vnat e)) (at level 85).
Definition val_from_nm x:= (e_val (vnat x)).
(*Print Grammar.*)



Definition p_sum P Q := p_ite (e_det (e_val (vbool true) ) (e_val (vbool false) )) P Q.

Notation "P |+ Q" := (p_sum P Q) (at level 100).

Definition P_s := p_rec ( (p_send pt_c msg_login (val_from_nm 0)
     (p_recv pt_a [None;Some (p_var 0)])) |+ (p_send pt_c msg_cancel (val_from_nm 0) p_inact)).

Definition P_c pwd_val := p_rec 
    (p_recv pt_s [Some (p_send pt_a msg_pwd (val_from_nm pwd_val) (p_var 0));None;
    Some (p_send pt_a msg_quit (val_from_nm 0) p_inact)]).

Definition P_a pwd_correct := p_rec 
    (p_recv pt_c [None;None;None;
    Some (p_ite (e_gt (e_var 0) (val_from_nm pwd_correct)) 
    (p_send pt_s msg_auth (e_val (vbool true)) (p_var 0)) 
    
    (p_send pt_s msg_auth (e_val (vbool false)) (p_var 0))
    );
    Some p_inact]).

Definition M := (pt_c <-- P_c 30) ||| (pt_s <-- P_s) ||| (pt_a <-- P_a 40).

Lemma M_nodup: noDupSess M.
Proof.
  cbv. (repeat constructor); try (red;intros;inversion_clear H as [Ht | Ht];
  inversion_clear Ht; try easy);red;intros. inversion H.
Qed. 

Definition M_zero :=  (pt_c <-- p_inact) ||| (pt_s <-- p_inact) ||| (pt_a <-- p_inact).

Lemma scong_to_unfoldP_single : forall M M', noDupSess M -> scong M M' -> unfoldP M M'.
Proof.
  intros. eapply scong_to_unfoldP in H0;try easy.
Qed.

Lemma onth_above_length_none {A:Type}: forall k (xs:list (option A)), length xs <= k -> onth k xs = None.
Proof.
  induction k;intros.
  destruct xs;simpl;try easy.
  destruct xs. eapply onth_nil.
  simpl. eapply IHk. simpl in H.
 lia.
Qed.

Definition P_s_cont := (p_recv pt_a
        [None;
        Some
          (p_rec
          (p_send pt_c msg_login (val_from_nm 0)
            (p_recv pt_a [None; Some (p_var 0)])))]).

Lemma M_may_terminate1 : betaP M ((pt_c <-- p_send pt_a msg_quit (val_from_nm 0) p_inact) ||| (pt_s <-- p_inact) ||| (pt_a <-- P_a 40)).
Proof.
    exists (lcomm pt_s pt_c msg_cancel).
    
    set (P_c_unf := (fun pwd_val => 
    (p_recv pt_s [Some (p_send pt_a msg_pwd (val_from_nm pwd_val) 
      (p_rec 
      (p_recv pt_s [Some (p_send pt_a msg_pwd (val_from_nm pwd_val) (p_var 0));None;
      Some (p_send pt_a msg_quit (val_from_nm 0) p_inact)])));
      None;
    Some (p_send pt_a msg_quit (val_from_nm 0) p_inact)]))).
    set (P_s_unf := (p_send pt_c msg_login (val_from_nm 0)
    (p_recv pt_a [None; Some (p_rec
        (p_send pt_c msg_login (val_from_nm 0)
        (p_recv pt_a [None; Some (p_var 0)])
        |+ p_send pt_c msg_cancel (val_from_nm 0) p_inact))])
    |+ p_send pt_c msg_cancel (val_from_nm 0) p_inact)).

        set (P_s_ifb :=p_send pt_c msg_cancel (val_from_nm 0) p_inact).
    econstructor 2 with 
    (M1':=   (pt_c <-- P_c_unf 30) ||| (pt_s <-- P_s_ifb)  ||| (pt_a <-- P_a 40))
    (M2':= (pt_s <-- p_inact) ||| (pt_c <-- p_send pt_a msg_quit (val_from_nm 0 ) p_inact)
    |||  (pt_a <-- P_a 40)).
    {
        unfold M.
        assert(Hz0 : unfoldP
        (((pt_c <-- P_c 30) ||| (pt_s <-- P_s))
        ||| (pt_a <-- P_a 40))
        (((pt_s <-- P_s) ||| (pt_c <-- P_c 30))
        ||| (pt_a <-- P_a 40))) by 
          eapply pc_par1m.
          (*Print P_s.*)
        eapply pc_trans with (M':=(((pt_s <-- P_s) ||| (pt_c <-- P_c 30))
        ||| (pt_a <-- P_a 40)));try easy.
        assert(unfoldP
          (((pt_s <-- P_s) ||| (pt_c <-- P_c 30)) ||| (pt_a <-- P_a 40))
          (((pt_c <-- P_c 30)) ||| (pt_s <-- P_s) |||  (pt_a <-- P_a 40))) by 
          eauto with procs.
          eapply pc_trans;try exact H.
        eapply unf_cont_l.
        eapply unf_cont.
        {
          assert(Hz1: unfoldP (pt_c <-- P_c 30) (pt_c <-- P_c 30||| s_zero)) by eauto with procs.
          assert(Hz2: unfoldP (pt_c <-- P_c 30||| s_zero) (pt_c <-- P_c_unf 30||| s_zero)).
          {
            econstructor 1. constructor.  constructor.
            unfold P_c_unf. econstructor.
            eapply assoc.Forall2_forall;simpl;try easy.
            intros.
            destruct(3 <=? k) eqn:Hnk.
            {
              left.
              rewrite onth_above_length_none;
              try rewrite onth_above_length_none; try easy;simpl;
              eapply leb_complete in Hnk;easy.
            }
            {
              destruct(Nat.eq_dec k 0);   
              destruct(Nat.eq_dec k 1);   
              destruct(Nat.eq_dec k 2);subst;try easy;simpl.
              {
                right.
                exists (p_send pt_a msg_pwd (val_from_nm 30 ) (p_var 0)).
                exists (p_send pt_a msg_pwd (val_from_nm 30 )
                (p_rec
                (p_recv pt_s
                [Some (p_send pt_a msg_pwd (val_from_nm 30 ) (p_var 0)); None;
                Some (p_send pt_a msg_quit (val_from_nm 0 ) p_inact)]))).
                repeat split;try easy.
                constructor. constructor.
              }
              {
                left. easy. 
              }
              {
                right. exists (p_send pt_a msg_quit (val_from_nm 0 ) p_inact), (p_send pt_a msg_quit (val_from_nm 0 ) p_inact).
                repeat split;try easy. constructor. constructor.
              }
              {
                (*Search "<=?".*)
                rewrite leb_iff_conv in Hnk. lia.
              }
            }  
          }
          eauto with procs.
        }
        {
          assert(Hz1: unfoldP (pt_s <-- P_s) (pt_s <-- P_s ||| s_zero)) by eauto with procs.
          assert(Hz2: unfoldP (pt_s <-- P_s ||| s_zero) (pt_s <-- P_s_unf ||| s_zero)).
          {
            econstructor 1. constructor.  constructor.
            unfold P_s_unf;do 3 constructor.
             
            eapply assoc.Forall2_forall;simpl;try easy.
            intros.
            destruct(3 <=? k) eqn:Hnk.
            {
              left.
              
              rewrite onth_above_length_none;
              try rewrite onth_above_length_none; try easy;simpl;
              eapply leb_complete in Hnk;lia.
            }
            {
              destruct(Nat.eq_dec k 0);   
              destruct(Nat.eq_dec k 1);   
              destruct(Nat.eq_dec k 2);subst;try easy;simpl.
              {
                left;tauto.
              }
              {
                
                right.
                evar (kp:process). evar (kl :process).
                exists kp, kl.
                split;try split;unfold kp,kl;try  f_equal.
                constructor.
              }
              {
                left;try tauto.
              }
              {
                rewrite leb_iff_conv in Hnk. lia.
              }
            }  
          }
          assert(Hz3: unfoldP ((pt_s <-- P_s_unf) ||| s_zero) ((pt_s <-- P_s_ifb) ||| s_zero)).
          {
            constructor. econstructor 2. constructor.
            (*Print stepE.*)
            eapply ec_detr. constructor.
          }
          eauto with procs.
        }   
    }
    {
      eauto with procs. 
    }
    {
      econstructor 2 with (M1':= (((pt_c <-- P_c_unf 30) ||| (pt_s <-- P_s_ifb))
      ||| (pt_a <-- P_a 40))) 
      (M2':= ((pt_c <-- p_send pt_a msg_quit (val_from_nm 0) p_inact)
      |||(pt_s <-- p_inact)
      ||| (pt_a <-- P_a 40))) ;try solve [eauto with procs].
      
      assert(Hsub: subst_expr_proc (p_send pt_a msg_quit (val_from_nm 0) p_inact) (e_val (vnat 0)) 0 0 = p_send pt_a msg_quit (val_from_nm 0) p_inact).
      {
        easy.
      }
      rewrite <- Hsub.
      econstructor 1. cbv;simpl;try easy.
      constructor.
    }
Qed.