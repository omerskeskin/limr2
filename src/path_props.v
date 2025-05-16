(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local src.lcontext CpdtTactics.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations.
Require Import Coq.Program.Equality.
Import ListNotations.


CoInductive coseq (A: Type): Type :=
  | conil : coseq A
  | cocons: A -> coseq A -> coseq A.

Arguments conil {_}.
Arguments cocons {_} _ _.

Definition coseq_id {A: Type} (c: coseq A): coseq A :=
  match c with
    | conil       => conil
    | cocons x xs => cocons x xs
  end.

Lemma coseq_eq: forall {A: Type} (c: coseq A), c = coseq_id c.
Proof. destruct c; easy. Defined.

Notation Path := (coseq (tctx*label)) (only parsing).

Inductive eventually {A: Type} (F: coseq A -> Prop): coseq A -> Prop :=
  | evh: forall xs, F xs -> eventually F xs
  | evc: forall x xs, eventually F xs -> eventually F (cocons x xs).

Definition eventualyP := @eventually (tctx*label).

Inductive alwaysG {A: Type} (F: coseq A -> Prop) (R: coseq A -> Prop): coseq A -> Prop :=
  | alwn: F conil -> alwaysG F R conil
  | alwc: forall x xs, F (cocons x xs) -> R xs -> alwaysG F R (cocons x xs).

Definition alwaysP := @alwaysG (tctx*label).

Definition alwaysC F p := paco1 (alwaysP F) bot1 p.

Definition enabled (F: tctx -> Prop) (pt: Path): Prop :=
  match pt with
    | cocons (g, l) xs => F g
    | _                => False 
  end.

Definition headRecv (p q: part) (pt: Path): Prop :=
  match pt with
    | cocons (g, (lrecv a b (Some s) n)) xs => if Nat.eq_dec p a then if Nat.eq_dec q b then True else False else False
    | _                                   => False 
  end.

Definition headSend (p q: part) (pt: Path): Prop :=
  match pt with
    | cocons (g, (lsend a b (Some s) n)) xs => if Nat.eq_dec p a then if Nat.eq_dec q b then True else False else False
    | _                                   => False 
  end.

Definition headComm (p q: part) (pt: Path): Prop :=
  match pt with
    | cocons (g, (lcomm a b n)) xs => if Nat.eq_dec p a then if Nat.eq_dec q b then True else False else False
    | _                          => False 
  end.

Definition fairPath (pt: Path): Prop :=
  forall p q n, enabled (tctxRE (lcomm p q n)) pt ->  eventually (headComm p q) pt.

Definition fairness := alwaysC fairPath.

Definition livePath (pt: Path) : Prop := forall p q s n, 
enabled (tctxRE (lsend p q (Some s) n)) pt -> eventually (headComm p q) pt /\
enabled (tctxRE (lrecv p q (Some s) n)) pt -> eventually (headComm p q) pt.
Definition liveness := alwaysC livePath.

Definition weak_safety (c: tctx ) :=
forall p q s s'  k k', tctxRE (lsend p q (Some s) k) c -> tctxRE (lrecv q p (Some s') k') c ->
                               tctxRE (lcomm p q k) c.

Inductive safe (R: tctx -> Prop): tctx -> Prop :=
  | safety_red :  forall c, weak_safety c -> (forall p q c' k, 
    tctxR c (lcomm p q k) c' -> (weak_safety c' /\ (exists c'', M.Equal c' c'' /\ R c''))) 
    ->  safe R c.
                               (*
Definition weak_safe_tctx := {c | weak_safety c}.
Inductive safe (R: weak_safe_tctx -> Prop): weak_safe_tctx -> Prop :=
  | safety_red :  forall c, (forall p q c' k, 
    tctxR (proj1_sig c) (lcomm p q k) c' -> (exists P, R (exist weak_safety c' P))) 
    -> safe R c.
*)
Definition safeC c := paco1 safe bot1 c.

Lemma safe_monotone : monotone1 safe.
Proof.
  unfold monotone1.
  intros.
  induction IN. 
  eapply safety_red with (c:=c) ;try easy.
  intros.
  eapply H0 in H1. destr_hyps. split; try easy.
  intros. exists x. split;try easy. eapply LE;easy.  
Qed.

#[global] Instance RWMTCTXR: Proper ((@M.Equal ltt) ==> (eq) ==> (@M.Equal ltt) ==> (iff)) tctxR.
Proof. unfold "==>". constructor; intros; subst. 
apply Rstruct with (g1:=y) (g2:=y1) (g1':=x) (g2':=x1);crush. 
apply Rstruct with (g1:=x) (g2:=x1) (g1':=y) (g2':=y1);crush.
Qed.
Lemma weak_safe_meq_invariant: forall c c', weak_safety c -> M.Equal c c' -> 
  weak_safety c'.
Proof.
  intros.
  unfold weak_safety.
  intros.
  unfold weak_safety in H.
  unfold tctxRE in *. destr_hyps. rename x0 into g1, x into g2. 
  specialize (H p q s s' k k'). setoid_rewrite <- H0 in H1.
  setoid_rewrite <- H0 in H2.
  setoid_rewrite <- H0.
  apply H;[exists g1 | exists g2];easy. 
Qed.

Lemma safe_meq_invariant: forall c c', safeC c -> M.Equal c c' -> safeC c'.
Proof.
  
  intros.
  pcofix CIH.
  pfold. constructor.
  { 
    pinversion H;try apply safe_monotone. 
    eapply weak_safe_meq_invariant with (c':=c') in H1; try easy. 
  }
  {
    intros.
    pinversion H;try apply safe_monotone;subst. setoid_rewrite <- H0 in H1.
    pose proof H1 as Htx.
    eapply H3 in H1.
    split;try easy.
    
    destr_hyps.
    exists x;crush.
    left.
    eapply paco1_mon_bot with (gf:=safe);pclearbot;try easy.
  }
Qed.
(*
Inductive livePath (pt: Path): Prop :=
  | L1: forall p q s, enabled (tctxRE (lsend p q (Some s) n)) pt -> eventually (headComm p q) pt -> livePath pt
  | L2: forall p q s, enabled (tctxRE (lrecv q p (Some s)) n) pt -> eventually (headComm p q) pt -> livePath pt.

Definition liveness := alwaysC livePath.

Inductive safe (R: tctx -> Prop): tctx -> Prop :=
  | sasr  : forall p q s s' c, tctxRE (lsend p q (Some s)) c -> tctxRE (lrecv q p (Some s')) c ->
                               tctxRE (lcomm p q) c -> safe R c
  | saimpl:  forall p q c c', R c -> tctxRF (lcomm p q) c c' -> safe R c'.

Definition safeC c := paco1 safe bot1 c.
*)