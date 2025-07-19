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

(*
CoInductive valid_path : Path -> Prop :=
  | nil_valid: valid_path conil
  | cons_nil_valid: forall x, valid_path (cocons x conil)
  | cons_cons_valid: forall g p q ell g' l' xs, valid_path (cocons (g',(lcomm p q ell)) xs) ->
    tctxR g (lcomm p q ell) g' -> valid_path (cocons (g, (lcomm p q ell)) (cocons (g', l') xs)). 
*)


Variant valid_pathGI {A:Type} (V: A -> A -> Prop)  
(R: coseq A ->  Prop) 
: 
coseq A -> Prop :=
  | nil_validGI: valid_pathGI V R conil
  | cons_nill_validGI: forall x, valid_pathGI V R (cocons x conil)  
  | cons_cons_validGI: forall x y xs, 
  R (cocons x xs) ->
    V y x -> 
    valid_pathGI V R (cocons y (cocons x xs)).
  

Definition valid_path_GC {A:Type} (V: A-> A-> Prop) := paco1 (valid_pathGI V) bot1.



Variant valid_pathI (R: Path -> Prop) : Path -> Prop :=
  | nil_validI: valid_pathI R conil
  | cons_nill_validI: forall x, valid_pathI R (cocons x conil)
  | cons_cons_validI: forall g p q ell g' l' xs, R (cocons (g',(lcomm p q ell)) xs) ->
    tctxR g (lcomm p q ell) g' -> valid_pathI R (cocons (g, (lcomm p q ell)) (cocons (g', l') xs)). 


Definition local_path_vcriteria := (fun (x1 x2 : tctx* label) =>
  match (x1,x2) with 
    | ((g1,lcomm p q ell),(g2,_)) => tctxR g1 (lcomm p q ell) g2
    | _ => False 
  end
).

Definition valid_local_path := valid_path_GC local_path_vcriteria.


Lemma valid_path_mon {A:Type}: forall (V : A -> A-> Prop), monotone1 (valid_pathGI V).
Proof.
  
  red;intros.
  induction IN;try constructor;try easy.
  eapply LE;easy.
Qed.


Inductive eventually {A: Type} (F: coseq A -> Prop): coseq A -> Prop :=
  | evh: forall xs, F xs -> eventually F xs
  | evc: forall x xs, eventually F xs -> eventually F (cocons x xs).

Definition eventualyP := @eventually (tctx*label).

Inductive alwaysG {A: Type} (F: coseq A -> Prop) (R: coseq A -> Prop): coseq A -> Prop :=
  | alwn: F conil -> alwaysG F R conil
  | alwc: forall x xs, F (cocons x xs) -> R xs -> alwaysG F R (cocons x xs).


Definition alwaysCG {A:Type} (F: coseq A -> Prop) := paco1 (alwaysG F) bot1.

Lemma always_mon {A:Type}: forall (F: coseq A -> Prop), monotone1 (alwaysG F).
Proof.
  red;intros. induction IN;try constructor;try easy. eapply LE. easy.
Qed.

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

Definition fair_path_local (pt: Path): Prop :=
  forall p q n, enabled (tctxRE (lcomm p q n)) pt ->  eventually (headComm p q) pt.

Definition fair_path := alwaysCG fair_path_local.

Definition live_path_inner (pt: Path) : Prop := forall p q s n, 
(enabled (tctxRE (lsend p q (Some s) n)) pt -> eventually (headComm p q) pt) /\
(enabled (tctxRE (lrecv p q (Some s) n)) pt -> eventually (headComm p q) pt).
Definition live_path := alwaysCG live_path_inner.

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

#[global] Instance RWMTCTXR: Proper (( @M.Equal ltt) ==> (eq) ==> ( @M.Equal ltt) ==> (iff)) tctxR.
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

Definition tctxRcomm (g: tctx) (g':tctx) := exists p q ell, tctxR g (lcomm p q ell) g'.

Definition tctxRtc := clos_refl_trans tctx tctxRcomm.


Definition all_fair_live (g:tctx) := forall l xs,  
  valid_local_path (cocons (g, l) xs) -> fair_path (cocons (g, l) xs) -> 
  live_path (cocons (g, l) xs).

Definition liveCtx (g: tctx) := forall g',
  tctxRtc g g' -> all_fair_live g'.



(*

Inductive liveCtxI (R: tctx -> Prop): tctx -> Prop :=
  | live_red :  forall c, all_fair_live c -> (forall p q c' k, 
    tctxR c (lcomm p q k) c' -> (all_fair_live c' /\ (exists c'', M.Equal c' c'' /\ R c''))) 
    ->  liveCtxI R c.
                               (*
Definition weak_safe_tctx := {c | weak_safety c}.
Inductive safe (R: weak_safe_tctx -> Prop): weak_safe_tctx -> Prop :=
  | safety_red :  forall c, (forall p q c' k, 
    tctxR (proj1_sig c) (lcomm p q k) c' -> (exists P, R (exist weak_safety c' P))) 
    -> safe R c.
*)
Definition liveCtxC c := paco1 liveCtxI bot1 c.

Lemma liveCtx_mon : monotone1 liveCtxI.
Proof.
  red;intros.
  induction IN. constructor;try easy. intros.
  eapply H0 in H1 as H2.
  destr_hyps. split;try easy. apply LE in H4. exists x. split;easy.
Qed.*)

