(* From mathcomp Require Import ssreflect.seq all_ssreflect. *)
From Paco Require Import paco pacotac.
From SST Require Import src.expr src.header src.local CpdtTactics src.lcontext.
From SST Require Import src.global src.projection src.part  src.balanced src.merge src.wfltt src.gttreeh.
From SST Require Import lemma.projection lemma.projection_helper lemma.decidable.
From SST Require Import src.step lemma.step src.assoc.
Require Import List String Ring Coq.Arith.PeanoNat Morphisms Relations Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic.
Require Import Lia Arith.

Inductive ltth :=
    | ltth_send : part -> list (option (sort*ltth)) -> ltth
    | ltth_recv : part -> list (option (sort*ltth)) -> ltth
    | ltth_hol :  nat -> ltth.

Print list_max.
Definition max_option_list (xs: list (option nat)) : nat :=
    list_max (map (fun u=> match u with 
        | None => 0
        | Some x => x end
    ) xs).


Inductive wfgtth : gtth -> Prop :=
    | wfg_hol : forall n, wfgtth (gtth_hol n)
    | wfg_hsend : forall p q xs, SList xs -> 
    Forall (fun u=> u=None \/ exists s g, u= Some (s,g) /\ wfgtth g) xs->
        wfgtth (gtth_send p q xs).

Inductive wfltth : ltth -> Prop :=
    | wfgl_hol : forall n, wfltth (ltth_hol n)
    | wfgl_hsend : forall p xs, SList xs -> 
    Forall (fun u=> u=None \/ exists s g, u= Some (s,g) /\ wfltth g) xs->
        wfltth (ltth_send p xs)
    | wfgl_hrecv : forall p xs, SList xs -> 
    Forall (fun u=> u=None \/ exists s g, u= Some (s,g) /\ wfltth g) xs->
        wfltth (ltth_recv p xs)    
    .

Inductive used_in_ltth : nat -> ltth -> Prop := 
    | used_hol : forall n, used_in_ltth n (ltth_hol n)
    | used_send : forall n xs p k s ll, onth k xs = Some (s, ll) -> used_in_ltth n ll -> 
    used_in_ltth n (ltth_send p xs)
    | used_recv : forall n xs p k s ll, onth k xs = Some (s, ll) -> used_in_ltth n ll -> 
    used_in_ltth n (ltth_recv p xs).

Definition fills_holes (ls :list (option ltth)) (l : ltth) :=
    forall n, used_in_ltth n l -> exists s, onth n ls = Some s.

Inductive typ_ltth : ltth -> list (option ltt) -> ltt -> Prop :=
    | typ_ltth_hol : forall n ll xs, 
    onth n xs = Some ll -> typ_ltth (ltth_hol n) xs ll
    | typ_ltth_send : 
    forall xs ys p ls,
    Forall2 
    (fun u v=> (u=None /\ v= None) 
    \/ exists s lt ltr, u=Some (s,lt) /\ v= Some (s, ltr) /\ typ_ltth lt ls ltr) xs ys ->
    typ_ltth (ltth_send p xs) ls (ltt_send p ys)
    | typ_ltth_recv : 
    forall xs ys p ls,
    Forall2 
    (fun u v=> (u=None /\ v= None) 
    \/ exists s lt ltr, u=Some (s,lt) /\ v= Some (s, ltr) /\ typ_ltth lt ls ltr) xs ys ->
    typ_ltth (ltth_recv p xs) ls (ltt_recv p ys).  
    
Print ishParts.
Inductive ishlParts : part -> ltth -> Prop :=
    | hal_send: forall p xs, ishlParts p (ltth_send p xs)
    | hal_rec: forall p xs, ishlParts p (ltth_recv p xs)
    | hal_sendr : forall p r n lis s g,  p <> r -> onth n lis= Some (s,g) ->
    ishlParts r g -> ishlParts r (ltth_send p lis)
    | hal_recvr : forall p r n lis s g,  p <> r -> onth n lis= Some (s,g) ->
    ishlParts r g -> ishlParts r (ltth_recv p lis).

Print typ_p_gtth.
Definition typ_p_send_ltth (ls:list (option ltt)) (ctx: ltth) (p:part) (t:ltt) := 
    typ_ltth ctx ls t /\  (ishlParts p ctx -> False) /\
     
    (forall n, used_in_ltth n ctx -> exists xs, onth n ls=Some (ltt_send p xs)).
     

Definition typ_p_recv_ltth (ls:list (option ltt)) (ctx: ltth) (p:part) (t:ltt) := 
    typ_ltth ctx ls t /\  (ishlParts p ctx -> False) /\
    (forall n, used_in_ltth n ctx -> exists xs, onth n ls=Some (ltt_recv p xs)).
Fixpoint gtth_height (gh : gtth) : nat :=
    match gh with
    | gtth_hol n => 0 
    | gtth_send p q xs =>
    list_max (map (fun u=> match u with 
        | None => 0
        | Some (s,x) => gtth_height x end
        ) xs)+1 end
.

Lemma onth_cons {A:Type} : forall (a:A) x xs n,
onth n (x::xs) = Some a -> n=0 \/ exists n', n=S n' /\ onth n' xs= Some a.
Proof.
    intros; destruct n;[ | right; exists n]; crush.
Qed.

Lemma list_max_in : forall a xs, In a xs -> a<= list_max xs.
Proof.
    intros.
    induction xs.
    {
        crush.   
    }
    {
        simpl in H. destruct H. unfold list_max. crush.
        eapply IHxs in H. simpl.
        apply Nat.max_le_iff.
        right;easy.   
    }
Qed.  

Lemma list_max_le_in : forall a b xs, b <= a -> In a xs -> b <= (list_max xs).
Proof.
    intros.
    induction xs.
    {
        crush.   
    }
    {
        simpl in H0. destruct H0;subst. crush.
        eapply IHxs in H0. simpl. apply Nat.max_le_iff. right.
        easy.   
    } 
Qed.

Lemma gtth_height_ge_children : forall  ghs n gh k p q s, onth n ghs = Some (s,gh) -> gtth_height gh >= k ->
    gtth_height (gtth_send p q ghs) >= k+1.
Proof.
    induction ghs.
    {
        intros.
        rewrite onth_nil in H. easy.   
    }
    {
        intros. red. simpl.
        destruct a.
        {
            rewrite <- Nat.add_le_mono_r.
            apply Nat.max_le_iff.
            
            eapply onth_cons in H as Honthcons.
            destruct Honthcons;
            [|
                destr_hyps; eapply IHghs with (k:=k) (p:=p) (q:=q) in H2];crush.
        }
        {
            eapply onth_cons in H as Honthcons.
            destruct Honthcons;[crush|].
            destr_hyps;subst. rename x into n'. simpl in H.
             rewrite <- Nat.add_le_mono_r.
            apply Nat.max_le_iff.
            right.
            
            set (ghs_map:=(map
        (fun u : option (sort * gtth) =>
        match u with
        | Some (_, x) => gtth_height x
        | None => 0
        end) ghs)).
            eapply list_max_le_in with (a:=(gtth_height gh)).
            crush.
            apply some_onth_implies_In in H.
            
            eapply in_map with (f:=(fun u : option (sort * gtth) => match u with
        | Some (_, x) => gtth_height x
        | None => 0
        end)) in H.
        fold ghs_map in H. easy.
        }
    }
Qed.


Lemma gtth_height_ge_0 : forall gh, wfgtth gh -> 0 <= gtth_height gh.
Proof.
    intros.
    induction gh using gtth_ind_ref. crush.
    inversion H;subst. apply slist_implies_some in H3. destr_hyps.
    eapply Forall_prop with (l:=x) (p:=x0) in H0;try easy. destruct H0;try easy.
    destr_hyps. crush.
Qed.
    
Lemma wfgtth_onth: forall p q xs n s g, wfgtth (gtth_send p q xs) -> onth n xs = Some (s,g) ->
    wfgtth g.
Proof.
    intros.
    inversion H;subst.
    eapply Forall_prop in H5;crush. inversion H1;crush.
Qed.
 
Lemma gtth_height_0_means_hol : forall gh, 
wfgtth gh -> gtth_height gh = 0 -> exists n, gh=gtth_hol n.
Proof.
    intros.
    destruct gh.
    { 
        exists n. easy.
    }
    {
        (*simpl in H0.*)
        inversion H;subst.
        apply slist_implies_some in H3. destr_hyps.
        destruct x0.
        eapply wfgtth_onth in H1 as Hwfgo;[ | exact H].
        eapply gtth_height_ge_children with (p:=n) (q:=n0) (k:=0) in H1 as Hchildren.
        eapply Forall_prop  with (l:=x) (p:=(s,g)) in H5; try easy.
        2: apply gtth_height_ge_0;crush.
        
        destruct H5;try easy.
        destr_hyps.
        crush.   
    }
Qed.

Section gtth_ind_by_height.

Variable P : gtth -> Prop.

Variable gh:gtth.
Hypothesis wfgh: wfgtth gh.
Hypothesis P0 : forall gh', wfgtth gh' -> gtth_height gh' = 0 -> 
        P gh'.

Hypothesis IH :
forall gh'',
wfgtth gh'' ->
(forall gh', wfgtth gh' -> gtth_height gh' < (gtth_height gh'') -> P gh') -> P gh''.

Lemma gtth_ind_by_height_aux : forall n g, wfgtth g -> gtth_height g = n -> P g.
Proof.
    induction n as [n IHn] using lt_wf_ind.
    {
        intros.
        eapply IH;try easy.
        intros. eapply IHn;try easy.
        subst;easy. 
    }
Qed.

Lemma gtth_ind_by_height: P gh.
Proof.
    eapply (gtth_ind_by_height_aux);easy.
Qed.

End gtth_ind_by_height.

(*
Inductive typ_ltth : ltth -> list (option ltt) -> ltt -> Prop :=
    | typ_ltth_hol : forall n lcs T, onth n lcs = Some T -> typ_ltth (ltth_hol n) lcs T
    | typ_ltth_send : ltth_hole_fill (ltth_send p lhs) lcs -> Forall2 (
        fun u v => u=None \/ v=None \/ exists s t1 t2,
        u=Some (s, t1) /\ v=Some (s,t2) /\ typ_ltth t1 lcs t2
    ) lhs ts ->
        typ_ltth (ltth_send p lhs) lcs (ltt_send p ts).   *)

