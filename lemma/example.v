From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms 
Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
Require Import Lia.
From SST Require Import src.header src.sim src.assoc src.expr src.lcontext src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh src.step src.merge src.projection src.session.  
From SST Require Import lemma.inversion lemma.inversion_expr lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step
lemma.projection_helper lemma.projection lemma.fairness_feasible lemma.subj_red_helpers lemma.subj_red_prog_fid lemma.live_proc.



Definition G := gtt_send 0 1 [
  Some (snat, gtt_send 1 2 [Some(snat, gtt_send 2 0 [Some (snat, gtt_end)])] );
  Some (snat, gtt_send 1 2 [Some(snat, gtt_send 2 0 [Some (snat, gtt_end)])] )
  ].

Definition TAlice := ltt_send 1 [Some (snat, ltt_recv 2 [Some (snat, ltt_end)])].

Definition T'Alice := ltt_send 1 [
  Some (snat, ltt_recv 2 [Some (snat, ltt_end)]);
  Some (snat, ltt_recv 2 [Some (snat, ltt_end)])
  ].

Definition TCarol := ltt_recv 1 [Some (snat, ltt_send 0 [Some (snat, ltt_end)])].

Definition TBob := ltt_recv 0 [
  Some(snat, ltt_send 2 [Some(snat, ltt_end)]);
  Some(snat, ltt_send 2 [Some(snat, ltt_end)])
  ].

Search isgPartsC gtt_end.

Lemma no_part_end: forall p,
  isgPartsC p (gtt_end) -> False.
Proof. intros.
       specialize(part_break_s gtt_end p H); intro HH.
       destruct HH as (g, (Ha,(Hb,[Hc | (r,(s,(xs,Hxs)))]))).
       subst. inversion Hb.
       subst.
       pinversion Ha.
       apply gttT_mon.
Qed. 

Lemma no_part_send: forall p q r,
  p <> r ->
  q <> r ->
  isgPartsC r (gtt_send p q [Some (snat, gtt_end)]) -> False.
Proof. intros.
       apply part_cont in H1; try easy.
       destruct H1 as (n,(s,(g,(Hg1,Hg2)))).
       destruct n. simpl in Hg1.
       inversion Hg1. subst.
       apply no_part_end in Hg2. easy.
       simpl in Hg1.
       destruct n. simpl in Hg1. easy. simpl in Hg1. easy.
Qed.

Lemma no_part_send_send: forall pt p q r s,
  pt <> p ->
  pt <> q ->
  pt <> r ->
  pt <> s ->
  isgPartsC pt (gtt_send p q [Some (snat, gtt_send r s [Some (snat, gtt_end)])]) -> False.
Proof. intros.
       apply part_cont in H3; try easy.
       destruct H3 as (n1,(s1,(g1,(Hg1,Hg2)))).
       destruct n1. simpl in Hg1.
       inversion Hg1. subst.
       apply no_part_send in Hg2; try easy.
       simpl in Hg1.
       destruct n1. simpl in Hg1. easy. simpl in Hg1. easy.
Qed.

Lemma GPAlice: projectionC G 0 T'Alice.
Proof. unfold G, T'Alice.
       pfold.
       constructor. easy.

       unfold isgPartsC.
       exists(
       (g_send 0 1
       [Some (snat, g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]);
        Some (snat, g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])])])
       ).
       split.
       pfold.
       constructor.
       constructor. right.
       exists snat. exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left.
       pfold. constructor.
       constructor.
       right. exists snat. exists(g_send 2 0 [Some (snat, g_end)]).
       exists(gtt_send 2 0 [Some (snat, gtt_end)]). split. easy.
       split. easy.
       left.
       pfold. constructor.
       constructor. right.
       exists snat. exists g_end. exists gtt_end. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
       right. 
       exists snat. exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left.
       pfold. constructor.
       constructor.
       right. exists snat. exists (g_send 2 0 [Some (snat, g_end)]).
       exists (gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end. split. easy. split. easy.
       left.
       pfold. constructor.
       constructor.
       constructor.
       constructor.
       split.
       intro n.
       induction n; intros.
       exists 0.
       constructor.
       destruct IHn as (m, IHn).
       exists m.
       constructor.
       constructor.
       right.
       exists snat. exists (g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       case_eq n; intros.
       constructor.
       constructor. constructor.
       right.
       exists snat. exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       case_eq n0; intros.
       constructor.
       constructor. constructor.
       right. exists snat. exists g_end.
       split. easy. constructor. constructor. constructor.
       constructor.
       right.
       exists snat. exists (g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       case_eq n; intros.
       constructor.
       constructor. constructor.
       right.
       exists snat. exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       case_eq n0; intros.
       constructor.
       constructor. constructor.
       right. exists snat. exists g_end.
       split. easy. constructor. constructor. constructor.
       constructor.
       constructor.
       
       constructor.
       right.
       
       exists snat. 
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       exists( ltt_recv 2 [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold.
       apply proj_cont with (ys := [Some (ltt_recv 2 [Some (snat, ltt_end)])]).
       easy. easy. easy.
       unfold isgPartsC. 
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. pfold. constructor. constructor.
       right. exists snat. exists( g_send 2 0 [Some (snat, g_end)]).
       exists(gtt_send 2 0 [Some (snat, gtt_end)]). split. easy. split. easy.
       left. pfold. constructor. constructor. right.
       exists snat. exists g_end. exists gtt_end. split. easy. split. easy.
       left. pfold. constructor.
       constructor. constructor.
       split.
       intro n.
       case_eq n; intros.
       exists 0. constructor.
       exists 0. constructor. 
       constructor.
       right. exists snat. exists( g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       case_eq n0; intros.
       constructor.
       constructor.
       constructor.
       right. exists snat. exists g_end. split. easy. constructor.
       constructor. constructor.
       apply pa_sendr with (n := 0) (s := snat) (g := g_send 2 0 [Some (snat, g_end)]). easy. easy.
       simpl. easy.
       constructor.
       
       constructor.
       right. exists snat. exists (gtt_send 2 0 [Some (snat, gtt_end)]).
       exists((ltt_recv 2 [Some (snat, ltt_end)])). split. easy.
       split. easy.
       left. pfold. constructor. easy.
       
       unfold isgPartsC.
       exists((g_send 2 0 [Some (snat, g_end)])).
       split. pfold. constructor.
       constructor.
       right. exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy. left. pfold. constructor. constructor.
       split.
       intro n.
       exists 0.
       destruct n; constructor.
       constructor. right. exists snat. exists g_end. split. easy. constructor.
       constructor.
       constructor.

       constructor.
       right.
       exists snat. exists gtt_end. exists ltt_end. split. easy. split. easy.
       left. pfold. constructor.
       apply no_part_end.
       constructor.
       constructor. constructor.
      
       constructor.
       right.
       exists snat. exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       exists(ltt_recv 2 [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold.
       apply proj_cont with (ys := [Some (ltt_recv 2 [Some (snat, ltt_end)])]).
       easy. easy. easy.
       unfold isgPartsC.
       
       exists((g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])])).
       split. pfold. constructor.
       constructor. right.
       exists snat. exists(g_send 2 0 [Some (snat, g_end)]).
       exists(gtt_send 2 0 [Some (snat, gtt_end)]). split. easy. split. easy.
       left.  pfold. constructor. constructor.
       right. exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy. left. pfold. constructor. constructor. constructor.
       split.
       intro n.
       exists 0.
       case_eq n; constructor.
       constructor. right.
       exists snat. exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy. 
       case_eq n0; constructor. constructor.
       right. exists snat. exists g_end. split. easy. constructor. constructor. constructor.
       apply pa_sendr with (n := 0) (s := snat) (g := g_send 2 0 [Some (snat, g_end)]). easy. easy.
       simpl. easy. constructor.

       constructor.
       right. exists snat.
       exists(gtt_send 2 0 [Some (snat, gtt_end)]).
       exists (ltt_recv 2 [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       easy.
       
       unfold isgPartsC.
       exists( (g_send 2 0 [Some (snat, g_end)])).
       split. pfold. constructor.
       constructor. right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       split.
       intro n.
       exists 0.
       case_eq n; constructor.
       constructor. right.
       exists snat. exists g_end. split. constructor.
       constructor. constructor.
       constructor.

       constructor. right.
       exists snat. exists gtt_end. exists ltt_end.
       split. easy. split. easy. left. pfold. constructor.
       apply no_part_end.
       constructor.
       constructor.
       constructor.
       constructor.
Qed.

Lemma GPBob: projectionC G 1 TBob.
Proof. unfold G, TBob.
       pfold. constructor.
       easy.
       (**)
       unfold isgPartsC.
       exists((g_send 0 1
         [Some (snat, g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]);
          Some (snat, g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])])])).
       split.
       pfold. constructor.
       constructor. right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists( gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists( g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold. 
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists( gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
       
       split.
       intro n.
       exists 0.
       destruct n; constructor.
       constructor.
       right.
       exists snat.
       exists( g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat.
       exists(g_end). split. easy. constructor.
       constructor. constructor. 
       constructor.
       right.
       exists snat.
       exists( g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat.
       exists(g_end). split. easy. constructor.
       constructor. constructor. 
       constructor.
       constructor.
       (**)
       constructor.
       right.
       exists snat.
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       exists(ltt_send 2 [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       easy.
       
       unfold isgPartsC.
       exists((g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]) ).
       split.
       pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists(gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat.
       exists g_end.
       exists gtt_end.
       split. easy. split. easy. left. pfold. constructor.
       constructor. constructor.
       split.
       intro n.
       exists 0.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists(g_end).
       split. easy. constructor.
       constructor. constructor.
       constructor.
       (**)

       constructor.
       right.
       exists snat.
       exists (gtt_send 2 0 [Some (snat, gtt_end)]).
       exists ltt_end.
       split. easy. split. easy.
       left. pfold.
       constructor.
       apply no_part_send; easy.
       constructor.
       
       constructor.
       right.
       exists snat.
       exists( gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       exists(ltt_send 2 [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       easy.
       
       (**)
       unfold isgPartsC.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split.
       pfold. constructor.
       constructor. right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists(gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat.
       exists g_end.
       exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       split.
       intro n.
       exists 0.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists(g_end).
       split. easy. constructor.
       constructor. constructor.
       constructor.

       constructor.
       right.
       exists snat.
       exists( gtt_send 2 0 [Some (snat, gtt_end)]).
       exists(ltt_end). split. easy. split. easy.
       left. pfold.
       constructor.
       apply no_part_send; easy.
       constructor.
       constructor.
Qed.

Lemma GPCarol: projectionC G 2 TCarol.
Proof. unfold G, TCarol.
       pfold.
       apply proj_cont with (ys := [Some (ltt_recv 1 [Some (snat, ltt_send 0 [Some (snat, ltt_end)])]); Some (ltt_recv 1 [Some (snat, ltt_send 0 [Some (snat, ltt_end)])])]).
       easy. easy. easy.
       unfold isgPartsC.
       exists((g_send 0 1
         [Some (snat, g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]);
          Some (snat, g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])])])). 
       split.
       pfold. constructor.
       constructor. right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists(gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor. right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy. left. pfold. constructor.
       constructor. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists( gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor. constructor. constructor.
       split.
       intro n.
       exists 0.
       case_eq n; constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       case_eq n0; constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]). split. easy.
       case_eq n1; constructor.
       constructor.
       right. exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       case_eq n0; constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]). split. easy.
       case_eq n1; constructor.
       constructor.
       right. exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       apply pa_sendr with (n := 0) (s := snat) (g := g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]). easy. easy.
       simpl. easy.
       constructor.
       (**)
       constructor.
       right.
       exists snat.
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       exists(ltt_recv 1 [Some (snat, ltt_send 0 [Some (snat, ltt_end)])]).
       split. easy. split. easy.
       left. pfold. constructor.
       easy.
       
       unfold isgPartsC.
       exists((g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])])).
       split.
       pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists( gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       split.
       intro n. exists 0.
       destruct n; constructor.
       constructor. right.
       exists snat. exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       (**)
       constructor.
       right.
       exists snat.
       exists( gtt_send 2 0 [Some (snat, gtt_end)]).
       exists(ltt_send 0 [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold. constructor. easy.
       
       unfold isgPartsC.
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. pfold. constructor.
       constructor.
       right. exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       split.
       intro n. exists 0.
       destruct n; constructor.
       constructor.
       right. exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.

       constructor.
       right.
       exists snat. exists gtt_end. exists ltt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       apply no_part_end.
       constructor. constructor.
       constructor.
       right.
       exists snat.
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       exists(ltt_recv 1 [Some (snat, ltt_send 0 [Some (snat, ltt_end)])]).
       split. easy. split. easy.
       left. pfold. constructor.
       easy.

       unfold isgPartsC.
       exists((g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])])).
       split.
       pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists( gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       split.
       intro n. exists 0.
       destruct n; constructor.
       constructor. right.
       exists snat. exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.

       constructor.
       right.
       exists snat.
       exists( gtt_send 2 0 [Some (snat, gtt_end)]).
       exists(ltt_send 0 [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold. constructor. easy.

       unfold isgPartsC.
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. pfold. constructor.
       constructor.
       right. exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       split.
       intro n. exists 0.
       destruct n; constructor.
       constructor.
       right. exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.

       constructor.
       right.
       exists snat. exists gtt_end. exists ltt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       apply no_part_end.
       constructor. constructor.
       constructor.
       constructor.
       constructor.
Qed.

(*subtype*)

Lemma stAlice: subtypeC TAlice T'Alice.
Proof. unfold TAlice, T'Alice.
       pfold.
       constructor.
       simpl. split. constructor.
       split. left.
       pfold. constructor.
       simpl. split. constructor.
       split. left.
       pfold. constructor.
       easy.
       easy.
Qed.

(*typing*)

Definition PAlice := p_send 1 0 (e_val (vnat 50)) (p_recv 2 [Some (p_inact)] ).

Lemma TypAlice: typ_proc nil nil PAlice TAlice.
Proof. unfold PAlice, TAlice.
       specialize(tc_send nil nil 1 0 (e_val (vnat 50)) (p_recv 2 [Some p_inact])
       snat
       ( ltt_recv 2 [Some (snat, ltt_end)])
       ); intro HP.
       simpl in HP.
       apply HP.
       constructor.
       constructor. simpl. easy.
       simpl. easy.
       constructor.
       right.
       exists p_inact. exists snat. exists ltt_end.
       split. easy. split. easy.
       constructor.
       constructor.
Qed.

Definition PBob := p_recv 0 [
  Some(p_send 2 0 (e_val (vnat 100)) (p_inact));
  Some(p_send 2 0 (e_val (vnat 2)) (p_inact))
  ].

Lemma TypBob: typ_proc nil nil PBob TBob.
Proof. unfold PBob, TBob.
       constructor.
       simpl. easy.
       simpl. easy.
       constructor.
       right.
       exists(p_send 2 0 (e_val (vnat 100)) p_inact).
       exists snat.
       exists(ltt_send 2 [Some (snat, ltt_end)]).
       split. easy. split. easy.
       specialize(tc_send [Some snat] nil 2 0 (e_val (vnat 100)) p_inact
       snat ltt_end
       ); intro HP.
       simpl in HP.
       apply HP.
       constructor.
       constructor.
       
       constructor.
       right.
       exists(p_send 2 0 (e_val (vnat 2)) p_inact).
       exists snat.
       exists(ltt_send 2 [Some (snat, ltt_end)]).
       split. easy. split. easy.
       specialize(tc_send [Some snat] nil 2 0 (e_val (vnat 2)) p_inact
       snat ltt_end
       ); intro HP.
       simpl in HP.
       apply HP.
       constructor.
       constructor.
       constructor.
Qed.

Definition PCarol := p_recv 1 [Some (p_send 0 0 (e_succ (e_var 0)) p_inact)].

Lemma TypCarol: typ_proc nil nil PCarol TCarol.
Proof. unfold PCarol, TCarol.
       constructor.
       simpl. easy. easy.
       constructor.
       right.
       exists((p_send 0 0 (e_succ (e_var 0)) p_inact) ).
       exists snat.
       exists(ltt_send 0 [Some (snat, ltt_end)]).
       split. easy. split. easy.
       specialize(tc_send [Some snat] nil 0 0 (e_succ (e_var 0)) p_inact
       snat ltt_end
       ); intro HP.
       simpl in HP.
       apply HP. 
       constructor.
       constructor. simpl. easy.
       constructor.
       constructor.
Qed.

Definition M := s_par (s_par (s_ind 0 PAlice) (s_ind 1 PBob)) (s_ind 2 PCarol).

Lemma pwf: forall pt, isgPartsC pt G -> InT pt M.
Proof. intros.
       case_eq (Nat.eqb pt 0); intros.
       rewrite Nat.eqb_eq in H0. subst.
       unfold M.
       unfold InT. simpl. left. easy.
       rewrite Nat.eqb_neq in H0.
       case_eq (Nat.eqb pt 1); intros.
       rewrite Nat.eqb_eq in H1. subst.
       unfold InT. simpl. right. left. easy.
       rewrite Nat.eqb_neq in H1.
       case_eq (Nat.eqb pt 2); intros.
       rewrite Nat.eqb_eq in H2. subst.
       unfold InT. simpl. right. right. left. easy.
       rewrite Nat.eqb_neq in H2.
       apply part_cont in H; try easy.
       destruct H as (n,(s,(g,(Ha,Hb)))).
       revert pt H0 H1 H2 Hb. revert s g Ha.
       induction n; intros.
       - simpl in Ha.
         inversion Ha. subst. apply no_part_send_send in Hb; try easy.
         simpl in Ha.
       - destruct n. simpl in Ha. inversion Ha.
         subst. apply no_part_send_send in Hb; try easy.
         simpl in Ha.
         destruct n. simpl in Ha. easy. simpl in Ha. easy.
Qed.


Lemma endP: forall w, gttmap G w None gnode_end ->
  w = [0;0;0] \/ w = [1;0;0].
Proof. intros.
       inversion H. subst.
       case_eq n; intros.
       - subst. simpl in H6.
         inversion H6. subst.
         inversion H7. subst.
         case_eq n; intros.
         + subst. simpl in H8.
           inversion H8. subst.
           inversion H9. subst.
           case_eq n; intros.
           ++ subst. simpl in H10. inversion H10. subst.
              inversion H11. subst. left. easy.
           ++ subst. simpl in H10. 
              destruct n0; simpl in H10; easy.
         + subst. simpl in H8.
           destruct n0; simpl in H8; easy.
      - subst. simpl in H6.
        case_eq n0; intros.
        + subst. simpl in H6. 
          inversion H6. subst.
          inversion H7. subst.
          case_eq n; intros.
          ++ subst. simpl in H8.
             inversion H8. subst.
             inversion H9. subst.
             case_eq n; intros.
             * subst. simpl in H10.
               inversion H10. subst. 
               inversion H11. subst. right. easy.
             * subst. simpl in H10.
               destruct n0; simpl in H10; easy.
          ++ subst. simpl in H8.
             destruct n0; simpl in H8; easy.
        + subst. simpl in H6.
          destruct n; simpl in H6; easy.
Qed.

Lemma spq: forall w p q, gttmap G w None (gnode_pq p q) ->
  (w = [] /\ p = 0 /\ q = 1) \/ 
  (w = [0] /\ p = 1 /\ q = 2) \/ 
  (w = [1] /\ p = 1 /\ q = 2) \/
  (w = [0;0] /\ p = 2 /\ q = 0) \/ 
  (w = [1;0] /\ p = 2 /\ q = 0).
Proof. intros.
       inversion H.
       - subst. left. easy.
       - subst. 
         case_eq n; intros.
         + subst. simpl in H6.
           inversion H6. subst.
           inversion H7. subst.
           right. left. easy.
           subst.
           case_eq n; intros.
           ++ subst. simpl in H8.
              inversion H8. subst. 
              inversion H9. subst. 
              right. right. right. left. easy.
              subst.
              case_eq n; intros.
              * subst. simpl in H10. inversion H10. subst.
                inversion H11.
              * subst. simpl in H10.
                destruct n0; simpl in H10; easy.
           ++ subst. simpl in H8.
              destruct n0; simpl in H8; easy.
         + subst.
           simpl in H6.
           case_eq n0; intros.
           ++ subst. simpl in H6.
              inversion H6. subst.
              inversion H7. subst.
              right. right. left. easy.
              subst.
              case_eq n; intros.
              * subst. simpl in H8.
                inversion H8. subst. 
                inversion H9. subst.
                right. right. right. right. easy.
              * subst.
                case_eq n; intros.
                ** subst. simpl in H10. inversion H10. subst.
                   inversion H11.
                ** subst. simpl in H10.
                   destruct n0; simpl in H10; easy.
           ++ subst. simpl in H8.
              destruct n0; simpl in H8; easy.
         + subst. simpl in H6.
           destruct n; simpl in H7; easy.
Qed.

Lemma spqn: forall n l p q, gttmap G (n :: l) None (gnode_pq p q) -> 
  (n = 0 /\ ((l = [] /\ p = 1 /\ q = 2) \/ (l = [0] /\ p = 2 /\ q = 0))) \/
  (n = 1 /\ ((l = [] /\ p = 1 /\ q = 2) \/ (l = [0] /\ p = 2 /\ q = 0))).
Proof. intros.
       case_eq n; intros.
       - subst. left.
         inversion H. subst.
         simpl in H7. inversion H7.
         subst. split. easy.
         inversion H8. subst. left. easy.
         subst. 
         case_eq n; intros.
         + subst. simpl in H6. inversion H6. subst.
           inversion H9. subst.
           right. easy.
           subst.
           case_eq n; intros.
           ++ subst. simpl in H10. inversion H10. subst.
              inversion H11.
           ++ subst. simpl in H10.
              destruct n0; simpl in H10; easy.
        + subst. simpl in H6.
          destruct n0; simpl in H6; easy.
       - subst. simpl. right.
         case_eq n0; intros.
         + subst. split. easy.
           inversion H. subst.
           simpl in H7. inversion H7. subst.
           inversion H8. subst. left. easy.
           subst. 
           case_eq n; intros.
           ++ right. subst. simpl in H6.
              inversion H6. subst.
              inversion H9. subst. easy.
              subst. 
              case_eq n; intros.
              * subst. simpl in H10. inversion H10. subst.
                inversion H11.
              * subst. simpl in H10.
                destruct n0; simpl in H10; easy.
            ++ subst. simpl in H6. 
               destruct n0; simpl in H6; easy.
        - subst. inversion H.
          subst.
          case_eq n; subst; simpl in H7.
          destruct n; easy.
          destruct n; easy.
Qed.

Lemma blen1: forall w t, length w = 1 -> gttmap G w None t ->
  (w = [0] /\ t = gnode_pq 1 2) \/
  (w = [1] /\ t = gnode_pq 1 2).
Proof. intros.
       inversion H0.
       subst. easy.
       subst.
       case_eq n; intros.
       + subst. simpl in H7. inversion H7. subst.
         inversion H8. subst. left. easy.
       + subst.
         case_eq n; intros.
         ++ subst. simpl in H9. inversion H9. subst.
            easy.
         ++ easy.
       subst. simpl in H7.
       case_eq n0; intros.
       + subst. simpl in H7.
         inversion H7. subst.
         inversion H8. subst.
         right. easy.
       + subst. easy.
       subst.
       simpl in H7.
       destruct n; simpl in H7; easy.
Qed.

Lemma blen2: forall w t, length w = 2 -> gttmap G w None t ->
  (w = [0;0] /\ t = gnode_pq 2 0) \/
  (w = [1;0] /\ t = gnode_pq 2 0).
Proof. intros.
       inversion H0.
       subst. easy.
       subst.
       case_eq n; intros.
       + subst. simpl in H7. inversion H7. subst.
         inversion H8. subst. left. easy.
       + subst.
         case_eq n; intros.
         ++ subst. simpl in H9. inversion H9. subst.
            inversion H10. subst.
            left. easy.
            subst. easy.
         ++ subst. simpl in H9.
            destruct n0; simpl in H9; easy.
         subst. simpl in H7.
         right.
       case_eq n0; intros.
       + subst. simpl in H7.
         inversion H7. subst.
         inversion H8. subst. easy.
         subst. 
         case_eq n; intros.
         ++ subst. simpl in H9. inversion H9. subst.
            inversion H10. subst. easy.
            subst. 
            case_eq n; intros.
            +++ subst. simpl in H11. inversion H11. subst.
                easy.
            +++ subst. easy.
          ++ subst. simpl in H9. 
             destruct n0 in H9; easy.
             subst.
             simpl in H7.
             destruct n; easy.
Qed.

Lemma bnil: forall {A: Type} (w1 w2: list A), w1 ++ w2 = [] -> w1 = [] /\ w2 = [].
Proof. intros A w1.
       induction w1; intros.
       - simpl in H. subst. easy.
       - simpl in H. easy.
Qed.

Lemma onenil: forall {A: Type} w1 w2 (a: A), w1 ++ w2 = [a] -> (w1 = [a] /\ w2 = []) \/ (w1 = [] /\ w2 = [a]).
Proof. intros a w1.
       induction w1; intros.
       - simpl in H. simpl. right. easy.
       - simpl in H.
         inversion H. subst.
         apply bnil in H2.
         destruct H2 as (H2a,H2b). subst.
         simpl. left. easy.
Qed.

Lemma balG: balancedG G.
Proof. unfold balancedG.
       intros.
       inversion H.
       - subst. simpl in H0. simpl.
         destruct H0 as [H0 | H0].
         + apply spq in H0.
           destruct H0 as [(Ha1,(Ha2,Ha3)) | [(Ha1,(Ha2,Ha3)) | [(Ha1,(Ha2,Ha3))| [(Ha1,(Ha2,Ha3)) | (Ha1,(Ha2,Ha3))]]]].
           ++ subst.
              exists 0.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** subst. exists []. exists [0;0;0].
                   simpl. split. easy.
                   exists 1.
                   left. easy.
                ** subst. exists []. exists [1;0;0].
                   simpl. split. easy.
                   exists 1.
                   left. easy.
                destruct H0 as (Ha,(t,Hb)).
                assert (w' = []).
                { apply length_zero_iff_nil. easy. } 
                subst.
                exists []. exists []. 
                split. easy. 
                exists 1.
                left. easy.
           ++ exists 1.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** rewrite H0. exists [0]. exists [0;0].
                   simpl. split. easy.
                   exists 2.
                   left. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                   simpl. easy.
                   rewrite Ha2.
                   constructor.
                ** exists [1]. exists [0;0].
                   simpl. split. easy.
                   exists 2.
                   left. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                   simpl. easy.
                   rewrite Ha2.
                   constructor.
                   destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w'0 t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists [0]. exists [].
                       split. easy. exists 2. 
                       left. easy.
                   *** subst.  exists [1]. exists [].
                       split. easy. exists 2. 
                       left. easy.
           ++ subst.
              exists 1.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** rewrite H0. exists [0]. exists [0;0].
                   simpl. split. easy.
                   exists 2.
                   left. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                   simpl. easy.
                   constructor.
                ** exists [1]. exists [0;0].
                   simpl. split. easy.
                   exists 2.
                   left. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                   simpl. easy.
                   constructor.
                   destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists [0]. exists [].
                       split. easy. exists 2. 
                       left. easy.
                   *** subst.  exists [1]. exists [].
                       split. easy. exists 2. 
                       left. easy.
             ++ subst.
                exists 1.
                intros.
                destruct H0 as [H0 | H0].
                * apply endP in H0.
                  destruct H0 as [H0 | H0].
                  ** exists [0;0]. exists [0].
                     simpl. split. easy.
                     exists 0.
                     left. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                  ** exists [1;0]. exists [0].
                     simpl. split. easy.
                     exists 0.
                     left. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                * destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists [0]. exists [].
                       split. easy. exists 1. 
                       right. easy.
                   *** subst.  exists [1]. exists [].
                       split. easy. exists 1. 
                       right. easy.
             ++ exists 2. subst.
                intros.
                destruct H0 as [H0 | H0].
                * apply endP in H0.
                  destruct H0 as [H0 | H0].
                  ** exists [0;0]. exists [0].
                     simpl. split. easy.
                     exists 0.
                     left.
                     apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                  ** exists [1;0]. exists [0].
                     simpl. split. easy.
                     exists 0.
                     left. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                 * destruct H0 as (Ha,(t,Hb)).
                   specialize(blen2 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   ** subst. exists [0;0]. exists [].
                      simpl. split. easy.
                      exists 0. left. easy.
                   ** subst. exists [1;0]. exists [].
                      simpl. split. easy.
                      exists 0. left. easy.
         + apply spq in H0.
           destruct H0 as [(Ha1,(Ha2,Ha3)) | [(Ha1,(Ha2,Ha3)) | [(Ha1,(Ha2,Ha3))| [(Ha1,(Ha2,Ha3)) | (Ha1,(Ha2,Ha3))]]]].
           ++ subst.
              exists 0.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** subst. exists []. exists [0;0;0].
                   simpl. split. easy.
                   exists 0.
                   right. easy.
                ** subst. exists []. exists [1;0;0].
                   simpl. split. easy.
                   exists 0.
                   right. easy.
                destruct H0 as (Ha,(t,Hb)).
                assert (w' = []).
                { apply length_zero_iff_nil. easy. } 
                subst.
                exists []. exists []. 
                split. easy. 
                exists 0.
                right. easy.
           ++ exists 1.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** rewrite H0. exists [0]. exists [0;0].
                   simpl. split. easy.
                   exists 1.
                   right. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                   simpl. easy.
                   subst.
                   constructor.
                ** exists [1]. exists [0;0].
                   simpl. split. easy.
                   exists 1.
                   right. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                   simpl. easy.
                   subst.
                   constructor.
                   destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w'0 t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists [0]. exists [].
                       split. easy. exists 1. 
                       right. easy.
                   *** subst.  exists [1]. exists [].
                       split. easy. exists 1. 
                       right. easy.
           ++ subst.
              exists 1.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** rewrite H0. exists [0]. exists [0;0].
                   simpl. split. easy.
                   exists 1.
                   right. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                   simpl. easy.
                   constructor.
                ** exists [1]. exists [0;0].
                   simpl. split. easy.
                   exists 1.
                   right. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                   simpl. easy.
                   constructor.
                   destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists [0]. exists [].
                       split. easy. exists 1. 
                       right. easy.
                   *** subst.  exists [1]. exists [].
                       split. easy. exists 1. 
                       right. easy.
             ++ subst.
                exists 1.
                intros.
                destruct H0 as [H0 | H0].
                * apply endP in H0.
                  destruct H0 as [H0 | H0].
                  ** exists [0;0]. exists [0].
                     simpl. split. easy.
                     exists 2.
                     right. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                  ** exists [1;0]. exists [0].
                     simpl. split. easy.
                     exists 2.
                     right. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                * destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists []. exists [0].
                       split. easy. exists 1. 
                       left. easy.
                   *** subst.  exists []. exists [1].
                       split. easy. exists 1. 
                       left. easy.
             ++ exists 2. subst.
                intros.
                destruct H0 as [H0 | H0].
                * apply endP in H0.
                  destruct H0 as [H0 | H0].
                  ** exists [0;0]. exists [0].
                     simpl. split. easy.
                     exists 2.
                     right.
                     apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                  ** exists [1;0]. exists [0].
                     simpl. split. easy.
                     exists 2.
                     right. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                 * destruct H0 as (Ha,(t,Hb)).
                   specialize(blen2 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   ** subst. exists [0;0]. exists [].
                      simpl. split. easy.
                      exists 2. right. easy.
                   ** subst. exists [1;0]. exists [].
                      simpl. split. easy.
                      exists 2. right. easy. 
             ++ subst.
                destruct H0 as [H0 | H0].
                * assert(((n :: lis) ++ w') = n :: (lis++w')).
                  { simpl. easy. }
                  rewrite H1 in H0.
                  apply spqn in H0.
                  destruct H0 as [H0 | H0].
                  ** destruct H0 as (Ha, Hb).
                     subst. simpl in H7.
                     destruct Hb as [Hb | Hb].
                     *** destruct Hb as (Hb1,(Hb2,Hb3)).
                         subst.
                         assert(lis = [] /\ w' = []).
                         { apply bnil. easy. }
                         destruct H0 as (H0a,H0b).
                         subst. simpl.
                         inversion H7. subst.
                         exists 0.
                         intros.
                         destruct H0 as [H0 | H0].
                         **** apply endP in H0. 
                              destruct H0 as [H0 | H0].
                              +++ inversion H0. subst.
                                  exists []. exists [0;0].
                                  simpl. split. easy.
                                  exists 2.
                                  left. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                                  easy.
                              +++ destruct H0 as (H0a,H0b).
                                  assert(w' = []).
                                  { apply length_zero_iff_nil. easy. } 
                                  subst.
                                  exists []. exists []. split. easy.
                                  exists 2.
                                  left. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                         **** destruct Hb as (Hb1,(Hb2,Hb3)).
                              subst.
                              apply onenil in Hb1.
                              destruct Hb1 as [(Hb1,Hb2) | (Hb1,Hb2)].
                              +++ subst.
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       **** inversion H0. subst.
                                            exists []. exists [0]. split. easy.
                                            exists 0.
                                            simpl. left.
                                            apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                            easy.
                                       **** destruct H0 as (H0a,H0b).
                                            assert(w' = []).
                                            { apply length_zero_iff_nil. easy. } 
                                            subst.
                                            exists []. exists []. split. easy.
                                            exists 0.
                                            left.
                                            apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                              +++ subst. 
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       inversion H0. subst.
                                       exists [0]. exists [0].
                                       simpl. split. easy.
                                       exists 0.
                                       simpl. left.
                                       apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                       simpl. easy.
                                       constructor.
                                       easy.
                                       destruct H0 as (Ha,(t,Hb)).
                                       assert(w' = []).
                                       { apply length_zero_iff_nil. easy. } 
                                       subst. simpl in Hb.
                                       exists []. exists []. split. easy. simpl.
                                       exists 1.
                                       right.
                                       apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       constructor.
                  ++ destruct H0 as (Ha, Hb).
                     subst.
                     simpl in H7.
                     destruct Hb as [Hb | Hb].
                     *** destruct Hb as (Hb1,(Hb2,Hb3)).
                         subst.
                         assert(lis = [] /\ w' = []).
                         { apply bnil. easy. }
                         destruct H0 as (H0a,H0b).
                         subst. simpl.
                         inversion H7. subst.
                         exists 0.
                         intros.
                         destruct H0 as [H0 | H0].
                         **** apply endP in H0. 
                              destruct H0 as [H0 | H0].
                              +++ easy.
                                  inversion H0. subst.
                                  exists []. exists [0;0].
                                  simpl. split. easy.
                                  exists 2.
                                  left. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                              +++ destruct H0 as (H0a,H0b).
                                  assert(w' = []).
                                  { apply length_zero_iff_nil. easy. } 
                                  subst.
                                  exists []. exists []. split. easy.
                                  exists 2.
                                  left. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                         **** destruct Hb as (Hb1,(Hb2,Hb3)).
                              subst.
                              apply onenil in Hb1.
                              destruct Hb1 as [(Hb1,Hb2) | (Hb1,Hb2)].
                              +++ subst.
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       **** easy.
                                            inversion H0. subst.
                                            exists []. exists [0]. split. easy.
                                            exists 0.
                                            simpl. left.
                                            apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                       **** destruct H0 as (H0a,H0b).
                                            assert(w' = []).
                                            { apply length_zero_iff_nil. easy. } 
                                            subst.
                                            exists []. exists []. split. easy.
                                            exists 0.
                                            left.
                                            apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                              +++ subst. 
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       easy.
                                       inversion H0. subst.
                                       exists [0]. exists [0].
                                       simpl. split. easy.
                                       exists 0.
                                       simpl. left.
                                       apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                       simpl. easy.
                                       constructor.
                                       destruct H0 as (Ha,(t,Hb)).
                                       assert(w' = []).
                                       { apply length_zero_iff_nil. easy. } 
                                       subst. simpl in Hb.
                                       exists []. exists []. split. easy. simpl.
                                       exists 1.
                                       right.
                                       apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       constructor.
               ++ assert(((n :: lis) ++ w') = n :: (lis++w')).
                  { simpl. easy. }
                  rewrite H1 in H0.
                  apply spqn in H0.
                  destruct H0 as [H0 | H0].
                  ** destruct H0 as (Ha, Hb).
                     subst. simpl in H7.
                     destruct Hb as [Hb | Hb].
                     *** destruct Hb as (Hb1,(Hb2,Hb3)).
                         subst.
                         assert(lis = [] /\ w' = []).
                         { apply bnil. easy. }
                         destruct H0 as (H0a,H0b).
                         subst. simpl.
                         inversion H7. subst.
                         exists 0.
                         intros.
                         destruct H0 as [H0 | H0].
                         **** apply endP in H0. 
                              destruct H0 as [H0 | H0].
                              +++ inversion H0. subst.
                                  exists []. exists [0;0].
                                  simpl. split. easy.
                                  exists 1.
                                  right. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                                  easy.
                              +++ destruct H0 as (H0a,H0b).
                                  assert(w' = []).
                                  { apply length_zero_iff_nil. easy. } 
                                  subst.
                                  exists []. exists []. split. easy.
                                  exists 1.
                                  right. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                         **** destruct Hb as (Hb1,(Hb2,Hb3)).
                              subst.
                              apply onenil in Hb1.
                              destruct Hb1 as [(Hb1,Hb2) | (Hb1,Hb2)].
                              +++ subst.
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       **** inversion H0. subst.
                                            exists []. exists [0]. split. easy.
                                            exists 2.
                                            simpl. right.
                                            apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                            easy.
                                       **** destruct H0 as (H0a,H0b).
                                            assert(w' = []).
                                            { apply length_zero_iff_nil. easy. } 
                                            subst.
                                            exists []. exists []. split. easy.
                                            exists 2.
                                            right.
                                            apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                              +++ subst.
                                  exists 1.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       inversion H0. subst.
                                       exists [0]. exists [0].
                                       simpl. split. easy.
                                       exists 2.
                                       simpl. right.
                                       apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                       simpl. easy.
                                       constructor.
                                       easy.
                                       destruct H0 as (Ha,(t,Hb)).
                                       simpl in Hb.
                                       inversion Hb.
                                       subst. simpl in H10. inversion H10. subst.
                                       inversion H11. subst.
                                       easy.
                                       subst.
                                       case_eq n; intros.
                                       **** subst. simpl in H9. inversion H9. subst.
                                            inversion H12. subst. 
                                            exists [0]. exists []. 
                                            split. easy.
                                            exists 2.
                                            simpl. right.
                                            apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                            subst.
                                            easy.
                                      **** subst. simpl in H9. 
                                           destruct n0; easy.
                  ++ destruct H0 as (Ha, Hb).
                     subst.
                     simpl in H7.
                     destruct Hb as [Hb | Hb].
                     *** destruct Hb as (Hb1,(Hb2,Hb3)).
                         subst.
                         assert(lis = [] /\ w' = []).
                         { apply bnil. easy. }
                         destruct H0 as (H0a,H0b).
                         subst. simpl.
                         inversion H7. subst.
                         exists 0.
                         intros.
                         destruct H0 as [H0 | H0].
                         **** apply endP in H0. 
                              destruct H0 as [H0 | H0].
                              +++ easy.
                                  inversion H0. subst.
                                  exists []. exists [0;0].
                                  simpl. split. easy.
                                  exists 1.
                                  right. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                              +++ destruct H0 as (H0a,H0b).
                                  assert(w' = []).
                                  { apply length_zero_iff_nil. easy. } 
                                  subst.
                                  exists []. exists []. split. easy.
                                  exists 1.
                                  right. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                         **** destruct Hb as (Hb1,(Hb2,Hb3)).
                              subst.
                              apply onenil in Hb1.
                              destruct Hb1 as [(Hb1,Hb2) | (Hb1,Hb2)].
                              +++ subst.
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       **** easy.
                                            inversion H0. subst.
                                            exists []. exists [0]. split. easy.
                                            exists 2.
                                            simpl. right.
                                            apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                       **** destruct H0 as (H0a,H0b).
                                            assert(w' = []).
                                            { apply length_zero_iff_nil. easy. } 
                                            subst.
                                            exists []. exists []. split. easy.
                                            exists 2.
                                            right.
                                            apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                              +++ subst. 
                                  exists 1.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       easy.
                                       inversion H0. subst.
                                       exists [0]. exists [0].
                                       simpl. split. easy.
                                       exists 2.
                                       simpl. right.
                                       apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                       simpl. easy.
                                       constructor.
                                       destruct H0 as (Ha,(t,Hb)).
                                       inversion Hb. subst.
                                       simpl in H10. inversion H10. subst.
                                       inversion H11. subst. easy.
                                       subst. 
                                       case_eq n; intros.
                                       **** subst. simpl in H9.
                                            inversion H9. subst.
                                            inversion H12. subst.
                                            exists [0]. exists [].
                                            simpl. split. easy.
                                            exists 2.
                                            right.
                                            apply gmap_con with (st := snat) (gk := gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send 2 0 [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                            subst.
                                            case_eq n; intros.
                                            ++++ subst. simpl in H13. inversion H13. subst. easy.
                                            ++++ subst. easy.
                                            subst. simpl in H9.
                                            destruct n0; easy.
Qed.

Lemma wfgCG: wfgC G.
Proof. unfold wfgC.
       unfold G.
       exists((g_send 0 1
         [Some (snat, g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]);
          Some (snat, g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])])])).
       split.
       pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists(gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. 
       constructor.
       constructor.
       right. exists snat.
       exists g_end.
       exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists(gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. 
       constructor.
       constructor.
       right. exists snat.
       exists g_end.
       exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
       split.
       constructor. simpl. easy. easy.
       constructor. right.
       exists snat.
       exists( g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       constructor.
       simpl. easy. easy.
       constructor. right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       constructor. easy. easy.
       constructor. right.
       exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       right. 
       exists snat.
       exists( g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       constructor.
       simpl. easy. easy.
       constructor. right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       constructor. easy. easy.
       constructor. right.
       exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       split.
       intro n. exists 0.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       destruct n; constructor.
       constructor.
       right. exists snat. 
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       destruct n; constructor.
       constructor.
       right. exists snat. 
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       
       apply balG.
Qed.

Definition Gtype:=(g_send 0 1
         [Some (snat, g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]);
          Some (snat, g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])])]).

Lemma gttTC_G : gttTC Gtype G.
Proof.
  unfold G.
  
       pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists(gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. 
       constructor.
       constructor.
       right. exists snat.
       exists g_end.
       exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       exists(gtt_send 1 2 [Some (snat, gtt_send 2 0 [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 2 0 [Some (snat, g_end)]).
       exists(gtt_send 2 0 [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. 
       constructor.
       constructor.
       right. exists snat.
       exists g_end.
       exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
Qed.

Definition gamma := M.add 0 TAlice (M.add 1 TBob (M.add 2 TCarol M.empty)).

Lemma G_allGuarded: forall n, exists m, guardG n m Gtype.
Proof.
  intro n. exists 0.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       destruct n; constructor.
       constructor.
       right. exists snat. 
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send 1 2 [Some (snat, g_send 2 0 [Some (snat, g_end)])]).
       split. easy.
       destruct n; constructor.
       constructor.
       right. exists snat. 
       exists(g_send 2 0 [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
Qed.

Lemma assoc_gamma : assoc gamma G.
Proof.
  red;intros;split;intros Hisparts.
  {
    eapply pwf in Hisparts;cbv in Hisparts;
    destruct Hisparts as [?Hisparts | [?Hisparts | [?Hisparts | ?Hisparts]] ];try easy;subst;
    evar (T':ltt);unfold gamma; autorewrite with mmaps; exists T';split; unfold T';
    try solve  [reflexivity];red;intros.
    exists T'Alice. split. eapply GPAlice. eapply stAlice.
    exists TBob. split. eapply GPBob. eapply stRefl.
    exists TCarol. split. eapply GPCarol. eapply stRefl.  
  }
  {
    intros.
    destruct (Nat.eq_dec p 0);
    destruct (Nat.eq_dec p 1);
    destruct (Nat.eq_dec p 2);unfold gamma in *;subst;try easy;autorewrite with mmaps in H;
    inversion H;subst;try easy;
    exfalso;eapply Hisparts;red;
    exists Gtype;split;try solve [eapply gttTC_G];split;try solve [eapply G_allGuarded].
    constructor. constructor.
    econstructor 4 with (n:=0);try easy. constructor. 
  }
Qed.

Lemma TypM: typ_sess M gamma.
Proof.
  constructor.
  {
    exists G. split. eapply wfgCG. eapply assoc_gamma. 
  }
  {
    red;intros;
    destruct (Nat.eq_dec p 0); 
    destruct (Nat.eq_dec p 1);
    destruct (Nat.eq_dec p 2);subst;try easy;unfold gamma in H;autorewrite with mmaps in H;
    inversion H;subst;
    pfold;constructor;simpl;try easy;constructor;try right;try solve [constructor];
    evar (s:sort);evar (g:ltt);try right;exists s,g;split;unfold s, g;try solve [reflexivity];
    left;pfold;constructor;simpl;try easy;constructor;try solve [constructor];right;
    evar (s':sort);evar (g':ltt);exists s',g';unfold s',g';split;try solve [reflexivity];
    left;pfold;constructor.
  }
  {
    intros. red in H. destr_hyps.
    destruct (Nat.eq_dec pt 0);
    destruct (Nat.eq_dec pt 1);
    destruct (Nat.eq_dec pt 2);subst;try easy;cbv;simpl;try tauto.
    unfold gamma in H. autorewrite with mmaps in H. easy. 
  }
  {
    simpl. repeat (constructor;simpl;try solve [lia]). 
  }
  {
    repeat constructor;
    [exists TAlice|exists TBob|exists TCarol];split;try split;
    try solve [eapply TypAlice | eapply TypBob | eapply TypCarol];
    intros;cbv;exists 0.
    destruct n;subst;try solve [constructor].
    constructor.
    destruct n;subst;try solve [constructor]. constructor. constructor. right.
    exists p_inact. split;try easy. constructor. constructor.
    destruct n;subst;try solve [constructor]. constructor. constructor.
    right. exists (p_send 2 0 (e_val (vnat 100)) p_inact). split;try easy. destruct n.
    constructor. constructor. constructor. constructor. right.
    exists (p_send 2 0 (e_val (vnat 2)) p_inact).
    split;try easy. destruct n. constructor. constructor. constructor.
    constructor. destruct n;constructor. constructor.
    right. exists (p_send 0 0 (e_succ (e_var 0)) p_inact). split;try easy.
    destruct n;constructor. constructor. constructor.
  }
Qed.

Definition P'Alice := p_recv 2 [Some (p_inact)].

Definition P'Bob := p_send 2 0 (e_val (vnat 100)) (p_inact).

Definition M' := s_par (s_par (s_ind 0 P'Alice) (s_ind 1 P'Bob)) (s_ind 2 PCarol).

Lemma redM: betaP M M'.
Proof. unfold M, M', PAlice, P'Alice, PBob, P'Bob.
    exists (lcomm 0 1 0).
       specialize(r_struct
       M
       (s_par (s_par (s_ind 1 PBob) (s_ind 0 PAlice)) (s_ind 2 PCarol))
       M'
       (s_par (s_par (s_ind 1 P'Bob) (s_ind 0 P'Alice)) (s_ind 2 PCarol))
       ); intro HR.
       apply HR.
       unfold M.
       apply pc_par1m.
       unfold M.
       apply pc_par1m.

       unfold M, M', PAlice, P'Alice, PBob, P'Bob.
       specialize(r_comm 1 0
         ([Some (p_send 2 0 (e_val (vnat 100)) p_inact); Some (p_send 2 0 (e_val (vnat 2)) p_inact)])
         (p_send 2 0 (e_val (vnat 100)) p_inact)
         0 (e_val (vnat 50)) (vnat 50)
         (p_recv 2 [Some p_inact])
          (2 <-- PCarol)
       ); intro HC.
       simpl in HC.
       apply HC.
       easy.
       constructor.
Qed.

Lemma SRExa: exists gamma', typ_sess M' gamma' /\ path_props.tctxRtc gamma gamma'.
Proof.
  apply sub_red with (M := M).
       apply TypM.
       Check redM.
       apply redM.
Qed.

Locate betaRtc.
Lemma live_exa: exists M'', betaRtc M M'' /\ 
  exists Mr vl, scong M'' (2 <--p_send 0 0 vl p_inact ||| Mr).
Proof.
  assert(Hlive : live_sess M).
  {
    eapply typable_sess_live. red. exists gamma. eapply TypM. 
  }
  red in Hlive.
  assert(Hbr: betaRtc M M) by constructor.
  eapply Hlive in Hbr.
  destruct Hbr as [Hbr1 Hbr2].
  Compute M.
  specialize (Hbr2 2 1  [Some (p_send 0 0 (e_succ (e_var 0)) p_inact)]).
  specialize (Hbr2 ((0 <-- p_send 1 0 (e_val (vnat 50)) (p_recv 2 [Some p_inact]))
||| (1 <--
p_recv 0
[Some (p_send 2 0 (e_val (vnat 100)) p_inact);
Some (p_send 2 0 (e_val (vnat 2)) p_inact)]))).
  clear Hlive Hbr1.
  assert(H20: 2 <> 1) by lia.
  assert(Hunf: unfoldP M
    ((2 <-- p_recv 1 [Some (p_send 0 0 (e_succ (e_var 0)) p_inact)])
    ||| ((0 <-- p_send 1 0 (e_val (vnat 50)) (p_recv 2
    [Some p_inact]))
    ||| (1 <--
    p_recv 0
    [Some (p_send 2 0 (e_val (vnat 100)) p_inact);
    Some (p_send 2 0 (e_val (vnat 2)) p_inact)])))).
  {
    cbv.
    eauto with procs.
  }
  specialize (Hbr2 H20 Hunf).
  destr_hyps.
  destruct x2.
  {
    simpl in H. inversion H;subst. 
    exists ((2 <-- subst_expr_proc (p_send 0 0 (e_succ (e_var 0)) p_inact) x1 0 0) ||| x).
    split;try easy.
    exists x, (e_succ (incr_freeE 0 0 x1)).
    simpl.
    constructor. 
  }
  {
    simpl in H. rewrite onth_nil in H. easy. 
  }
Qed.