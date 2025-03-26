From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global.

(* global trees with context holes *)
Inductive gtth: Type :=
  | gtth_hol    : fin -> gtth
  | gtth_send   : part -> part -> list (option (sort * gtth)) -> gtth.

Section gtth_ind_ref.
  Variable P : gtth -> Prop.
  Hypothesis P_hol : forall n, P (gtth_hol n).
  Hypothesis P_send : forall p q xs, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ P g)) xs -> P (gtth_send p q xs).
  
  Fixpoint gtth_ind_ref p : P p.
  Proof.
    destruct p.
    - apply P_hol.
    - apply P_send.
      induction l; intros; try easy.
      constructor; try easy.
      destruct a. 
      - destruct p. right. exists s1. exists g. split. easy. apply gtth_ind_ref.
      - left. easy.
  Qed.

End gtth_ind_ref.

Inductive typ_gtth : list (option gtt) -> gtth -> gtt -> Prop := 
  | gt_hol : forall n ctx gc, onth n ctx = Some gc -> typ_gtth ctx (gtth_hol n) gc
  | gt_send : forall ctx p q xs ys, SList xs -> List.Forall2 (fun u v => (u = None /\ v = None) \/ 
                                                (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ typ_gtth ctx g g')) xs ys -> 
                                                typ_gtth ctx (gtth_send p q xs) (gtt_send p q ys).

Section typ_gtth_ind_ref.
  Variable P : list (option gtt) -> gtth -> gtt -> Prop.
  Hypothesis P_hol : forall n ctx gc, onth n ctx = Some gc -> P ctx (gtth_hol n ) gc.
  Hypothesis P_send : forall ctx p q xs ys, SList xs -> List.Forall2 (fun u v => (u = None /\ v = None) \/ 
                                                 (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ P ctx g g')) xs ys -> 
                                                 P ctx (gtth_send p q xs) (gtt_send p q ys).
  
  Fixpoint typ_gtth_ind_ref ctx G G' (a : typ_gtth ctx G G') {struct a} : P ctx G G'.
  Proof.
    refine (match a with 
      | gt_hol n ctx gc Ha => P_hol n ctx gc Ha
      | gt_send ctx p q xs ys Ha Hl => P_send ctx p q xs ys Ha _
    end); try easy.
    revert Hl. apply Forall2_mono.
    intros. 
    destruct H.
    - left. easy.
    - destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
      right. exists x0. exists x1. exists x2. split. easy. split. easy. 
      apply typ_gtth_ind_ref; try easy.
  Qed.

End typ_gtth_ind_ref.