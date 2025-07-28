(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local src.projection 
src.lcontext src.step CpdtTactics src.assoc src.global.
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

Notation local_path := (coseq (tctx*(option label))) (only parsing).

(*
CoInductive valid_path : Path -> Prop :=
  | nil_valid: valid_path conil
  | cons_nil_valid: forall x, valid_path (cocons x conil)
  | cons_cons_valid: forall g p q ell g' l' xs, valid_path (cocons (g',(lcomm p q ell)) xs) ->
    tctxR g (lcomm p q ell) g' -> valid_path (cocons (g, (lcomm p q ell)) (cocons (g', l') xs)). 
*)


Variant valid_pathGI {A:Type} (V: A  ->  label -> A -> Prop)  
(R: coseq (A * option label) ->  Prop) 
: 
coseq (A * option label) -> Prop :=
  | nil_validGI: valid_pathGI V R conil
  | cons_nill_validGI: forall x, valid_pathGI V R (cocons (x, None) conil)  
  | cons_cons_validGI: forall x y l l' xs, 
  R (cocons (x,l') xs) ->
    V y l x -> 
    valid_pathGI V R (cocons (y,Some l) (cocons (x,l') xs)).
  

Definition valid_path_GC {A:Type} (V: A-> label -> A-> Prop) := paco1 (valid_pathGI V) bot1.


Definition local_path_vcriteria := (fun x1 l  x2  =>
  match (x1,l,x2) with 
    | ((g1,lcomm p q ell),g2) => tctxR g1 (lcomm p q ell) g2
    | _ => False 
  end
).

Definition valid_local_path := valid_path_GC local_path_vcriteria.


Lemma valid_path_mon {A:Type}: forall (V : A -> label ->  A-> Prop), monotone1 (valid_pathGI V).
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

Definition enabled (F: tctx -> Prop) (pt: local_path): Prop :=
  match pt with
    | cocons (g, l) xs => F g
    | _                => False 
  end.

Definition headRecv (p q: part) (pt: local_path): Prop :=
  match pt with
    | cocons (g, Some (lrecv a b (Some s) n)) xs => if Nat.eq_dec p a then if Nat.eq_dec q b then True else False else False
    | _                                   => False 
  end.

Definition headSend (p q: part) (pt: local_path): Prop :=
  match pt with
    | cocons (g, Some (lsend a b (Some s) n)) xs => if Nat.eq_dec p a then if Nat.eq_dec q b then True else False else False
    | _                                   => False 
  end.

Definition headComm (p q: part) (pt: local_path): Prop :=
  match pt with
    | cocons (g, Some (lcomm a b n)) xs => if Nat.eq_dec p a then if Nat.eq_dec q b then True else False else False
    | _                          => False 
  end.

Definition fair_path_local (pt: local_path): Prop :=
  forall p q n, enabled (tctxRE (lcomm p q n)) pt ->  eventually (headComm p q) pt.

Definition fair_path := alwaysCG fair_path_local.

Definition live_path_inner (pt: local_path) : Prop := forall p q s n, 
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


Notation global_path := (coseq (gtt*option label)) (only parsing).

Section global_path.


Definition global_path_vcriteria :  gtt -> label -> gtt -> Prop := fun x1 l x2 =>
    match (x1,l,x2) with 
        | (g1,lcomm p q ell,g2) => gttstepC g1 g2 p q ell
        | _ =>False
    end.

Definition global_valid_pathC := valid_path_GC global_path_vcriteria.



Definition global_comm_enabled p q n g := exists xs ys, 
projectionC g p (ltt_send q xs)  /\ projectionC g q (ltt_recv p ys) /\
onth n xs <>None.

Definition enabled_global (P: gtt -> Prop) (xs: global_path) :=  
 match xs with
    | cocons (g, l) xs => P g
    | _                => False 
  end.

Definition headComm_global (p q: part) (pt: global_path): Prop :=
  match pt with
    | cocons (g, Some (lcomm a b n)) xs => if Nat.eq_dec p a then if Nat.eq_dec q b then True else False else False
    | _                          => False 
  end.

Definition fair_path_inner_global (pt: global_path): Prop :=
  forall p q n, 
  enabled_global (global_comm_enabled p q n) pt ->  
  eventually (headComm_global p q) pt.



Definition fair_path_global := alwaysCG fair_path_inner_global.

Definition global_label_enabled l g:= match l with 
    | lsend p q (Some s) n => exists xs g',
        projectionC g p  (ltt_send q xs) /\ onth n xs=Some (s,g')
    | lrecv p q (Some s) n => exists xs g',
        projectionC g p  (ltt_recv q xs) /\ onth n xs=Some (s,g')
    | lcomm p q n => exists xs ys, projectionC g p (ltt_send q xs)  /\ projectionC g q (ltt_recv p ys) /\
    onth n xs <>None
    | _ => False end.
    
Definition live_path_inner_global (pt: global_path) : Prop := forall p q s n, 
(enabled_global (global_label_enabled (lsend p q (Some s) n)) pt -> 
eventually (headComm_global p q) pt) /\
(enabled_global (global_label_enabled (lrecv p q (Some s) n)) pt -> 
eventually (headComm_global p q) pt).

Definition live_path_global := alwaysCG live_path_inner_global.

Definition all_fair_live_global (g:gtt) := forall l xs,  
  global_valid_pathC (cocons (g, l) xs) -> fair_path_global (cocons (g, l) xs) -> 
  live_path_global (cocons (g, l) xs).


Definition live_type_global (g: gtt) := forall g',
  gttstepRtc g g' -> all_fair_live_global g'.

End global_path.



Notation paired_path := (coseq (tctx*gtt*option label)) (only parsing).

Definition paired_path_vcriteria x1 l (x2: (tctx*gtt))  :=
    match (x1,l,x2) with 
        | ((t1, g1), lcomm p q ell,(t2,g2)) => (gttstepC g1 g2 p q ell) 
        /\ tctxR t1  (lcomm p q ell) t2
        | _ =>False
    end.

Definition assoc_cond := fun u:paired_path => match u with 
    | (cocons (a,b,_) xs) => assoc a b
    | (conil) => True end.

Definition paired_path_assoc_cond := alwaysCG assoc_cond.

CoFixpoint proj1_paired_path (xs: paired_path) := match xs with 
    | conil => conil
    | cocons (t,g, c) xss => cocons (t,c) (proj1_paired_path xss) end.

CoFixpoint proj2_paired_path (xs: paired_path) := match xs with 
    | conil => conil
    | cocons (t,g,c) xss => cocons (g,c) (proj2_paired_path xss) end.

Definition paired_valid_pathC := valid_path_GC paired_path_vcriteria.

Lemma valid_path_some_l_next_cons {A:Type}: forall (V: A -> label -> A -> Prop) a l xs,
(valid_path_GC V) (cocons (a, Some l) xs) ->
  exists y ys, xs=cocons y ys.
Proof.
  intros. pinversion H;try apply valid_path_mon;subst. inversion H;subst.
  exists (x,l'), xs0. reflexivity.
Qed.

Lemma valid_path_none_next_nil {A:Type}: forall (V: A -> label -> A -> Prop) a xs,
(valid_path_GC V) (cocons (a, None) xs) ->
  xs=conil.
Proof.
  intros. pinversion H;try apply valid_path_mon;subst;easy.
Qed.

Lemma pair_valid_proj1_valid: forall xs, paired_valid_pathC xs -> (valid_local_path (proj1_paired_path xs)).
Proof.
    pcofix CIH.
    intros.
    destruct xs;
    [
    pfold;
    rewrite coseq_eq; simpl; constructor|].

    rewrite coseq_eq. destruct p as [[t g]  l].  simpl.
    destruct l. 
    {
      eapply valid_path_some_l_next_cons in H0 as Hnc;destr_hyps;subst.
      pfold.
      pinversion H0;try apply valid_path_mon;subst.
      
      destruct x1 as [t' g'].
      
      rewrite (coseq_eq (proj1_paired_path _));simpl.
      constructor.
      right.     specialize (CIH (cocons (t',g',l') x0)) as CIH'.
      rewrite (coseq_eq (proj1_paired_path _)) in CIH';simpl in CIH';eapply CIH';easy.

      red in H5;destruct l;easy.
      
    }
    {
      pfold.
      pinversion H0;try apply valid_path_mon;subst.
      rewrite (coseq_eq (proj1_paired_path _)). simpl.
      constructor.
    }
Qed.
