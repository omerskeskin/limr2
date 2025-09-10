From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.assoc src.sim src.expr src.process src.local src.global src.balanced src.typecheck 
src.part src.gttreeh src.step src.merge src.projection src.lcontext src.wfltt. 

Inductive session: Type :=
  | s_ind : part   -> process -> session
  | s_par : session -> session -> session
  | s_zero : session.
  
Notation "p '<--' P"   :=  (s_ind p P) (at level 50, no associativity).
Notation "s1 '|||' s2" :=  (s_par s1 s2) (at level 50, no associativity).

Inductive ForallT (P : part -> process -> Prop) : session -> Prop := 
  | ForallT_mono : forall pt op, P pt op -> ForallT P (pt <-- op)
  | ForallT_par : forall (M1 M2 : session), ForallT P M1 -> ForallT P M2 -> ForallT P (M1 ||| M2)
  | ForallT_zero: ForallT P s_zero.

Fixpoint flattenT (M : session) : (list part) := 
  match M with 
    | p <-- _   => p :: nil
    | M1 ||| M2 => flattenT M1 ++ flattenT M2
    | s_zero => nil
  end.

Definition InT (pt : part) (M : session) : Prop :=
  In pt (flattenT M).

Definition in_not_end (pt:part) (gamma: tctx) := exists x, M.find pt gamma=Some x /\ x <> ltt_end.  

Inductive unfoldP : relation session := 
  | pc_tau   : forall p P Q M, tauP P Q -> unfoldP ((p <-- P) ||| M) ((p <-- Q) ||| M)
  | pc_refl  : forall M, unfoldP M M
  | pc_trans : forall M M' M'', unfoldP M M' -> unfoldP M' M'' -> unfoldP M M''
  | pc_par1  : forall M M', unfoldP (M ||| M') (M' ||| M)
  | pc_par2  : forall M M' M'', unfoldP ((M ||| M') ||| M'') (M ||| (M' ||| M''))
  | pc_par1m : forall M M' M'', unfoldP ((M ||| M') ||| M'') ((M' ||| M) ||| M'')
  | pc_par2m : forall M M' M'' M''', unfoldP (((M ||| M') ||| M'') ||| M''') ((M ||| (M' ||| M'')) ||| M''')
  | pc_zero_elim : forall M, unfoldP (M ||| s_zero) M
  | pc_zero_intro : forall M, unfoldP  M (M ||| s_zero).

Inductive typ_sess : session -> tctx -> Prop := 
  | t_sess : forall M gamma (Hassocable: exists g, wfgC g /\ assoc gamma g), tctx_wf gamma ->
                         (forall pt, in_not_end pt gamma -> InT pt M) ->
                         NoDup (flattenT M) ->
                         ForallT (fun u P => exists T, M.find u gamma = Some T /\
                        typ_proc nil nil P T /\ (forall n, exists m, guardP n m P)) M ->
                         typ_sess M gamma.

Inductive betaP: relation session :=
  | r_comm  : forall p q xs y l e v Q M, 
              onth l xs = Some y -> stepE e (e_val v) -> 
              betaP ((p <-- (p_recv q xs)) ||| (q <-- (p_send p l e Q)) ||| M)
                    ((p <-- subst_expr_proc y (e_val v) 0 0) ||| (q <-- Q) ||| M) 
  | r_struct: forall M1 M1' M2 M2', unfoldP M1 M1' -> unfoldP M2' M2 -> betaP M1' M2' -> betaP M1 M2.


Definition stuck (M : session) := ((exists M', unfoldP M M' /\ ForallT (fun _ P => P = p_inact) M') -> False) /\ ((exists M', betaP M M') -> False).

Definition stuckM (M : session) := exists M', multi betaP M M' /\ stuck M'.