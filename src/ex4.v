(* Exercice 4 : Proof terms *)

From Project Require Import ex1 ex2.
From Stdlib Require Import Lia ZArith List Program.Equality.
Import ListNotations.

(* Part 4.1 : Hilbert systems *)

(* Question 4.1.a *)

Reserved Notation "A |-H s" (at level 70).

Inductive hil (A : list form) : form -> Prop :=
  | hil_assm s : In s A -> hil A s
  | hil_elim s t : hil A (s ~> t) -> hil A s -> hil A t
  | hil_axmK s t : hil A (s ~> t ~> s)
  | hil_axmS s t u : hil A ((s ~> t ~> u) ~> (s ~> t) ~> s ~> u).

Notation "A |-H s" := (hil A s) (at level 70).

(* Question 4.1.b *)

Lemma hil_ndm A s :
  A |-H s -> A |-m s.
Proof.
  intros hs.
  induction hs as [ s hs | s t hst IHst hs IHs | s t | s t u ].
  - apply ndm_assm. apply hs.
  - apply ndm_elim with (s := s). all: assumption.
  - repeat apply ndm_intr. apply ndm_assm. firstorder.
  - repeat apply ndm_intr. apply ndm_elim with (s := t).
    all: apply ndm_elim with (s := s).
    all: apply ndm_assm.
    all: firstorder.
Qed.

(* Question 4.1.c *)

Fact hil_weak A s t :
  A |-H s -> A |-H t ~> s.
Proof.
  intros hs.
  apply hil_elim with (s := s).
  + apply hil_axmK.
  + apply hs.
Qed.

Fact hil_trans A s t u :
  A |-H s ~> t ~> u -> A |-H s ~> t -> A |-H s ~> u.
Proof.
  intros hstu hst.
  apply hil_elim with (s := s ~> t).
  - apply hil_elim with (s := s ~> t ~> u).
    * apply hil_axmS.
    * apply hstu.
  - apply hst.
Qed.

Fact hil_refl A s :
  A |-H s ~> s.
Proof.
  apply hil_elim with (s := s ~> (s ~> s)).
  - apply hil_elim with (s := s ~> (s ~> s) ~> s).
    + apply hil_axmS.
    + apply hil_axmK.
  - apply hil_axmK.
Qed.

(* Question 4.1.d *)

Lemma hil_intr A s t :
  s :: A |-H t -> A |-H s ~> t.
Proof.
  intros hs.
  induction hs as [ t hs | t u hst IHst hs IHs | t u | t u v ]; simpl in *.
  - destruct hs as [ e | hin ]; subst.
    + apply hil_refl.
    + apply hil_weak. apply hil_assm. apply hin.
  - apply hil_trans with (t := t). all: assumption.
  - apply hil_weak. apply hil_axmK.
  - apply hil_weak. apply hil_axmS.
Qed.

(* Question 4.1.e *)

Fact ndm_hil A s :
  A |-m s -> A |-H s.
Proof.
  intros hs.
  induction hs as [ A s hs | A s t hs IH | A s t hst IHst hs IHs ].
  - apply hil_assm. apply hs.
  - apply hil_intr. apply IH.
  - apply hil_elim with (s := s). all: assumption.
Qed.

(*
  Why it is crucial that A is parameter of the hil predicate ?

  Since A is a parameter, A is fixed in the induction and therefore constant.
  Whereas if it were an inductive argument, each rule in the induction could change or modify this A,
  and then we would not have the same context in each branch of the induction, which would go against
  the logic of Hilbert systems, which require a fixed global context in order to avoid dealing with
  the management of variables and substitutions.
*)

(* Part 4.2 : Abstract reduction systems *)

Section ARS.

  Context {A : Type} (R : A -> A -> Prop).

  (* Question 4.2.a *)

  Inductive SN_on : A -> Prop :=
    | SN_cnstr x : (forall y, R x y -> SN_on y) -> SN_on x.

  (* Question 4.2.b *)

  Inductive rtc : A -> A -> Prop :=
    | rtc_refl x : rtc x x
    | rtc_fromR x y : R x y -> rtc x y
    | rtc_trans x y z : rtc x y -> rtc y z -> rtc x z.

  (* Question 4.2.c *)

  Lemma SN_on_rtc x y :
    SN_on x -> rtc x y -> SN_on y.
  Proof.
    intros hsn hrtc.
    induction hrtc as [ x | x y hrxy | x y z hrtcxy IH1 hrtcyz IH2 ].
    - apply hsn.
    - inversion hsn as [ ? h ]; subst. apply h. apply hrxy.
    - apply IH2. apply IH1. apply hsn.
  Qed.

  (* Question 4.2.d *)

  Variables T V : A -> Prop.

  Variable Hpres : forall x y, T x -> R x y -> T y.
  Variable Hprog : forall x, T x -> (exists y, R x y) \/ V x.

  Lemma SN_to_WN x :
    T x -> SN_on x -> exists v, rtc x v /\ T v /\ V v.
  Proof.
    intros ht hsn.
    induction hsn as [ x hsn IH ].
    destruct (Hprog x ht) as [ [ y h ] | h ].
    - destruct (IH y h (Hpres x y ht h)) as [ z [ hrtc [ htz hvz ] ] ]. 
      exists z. split.
      + apply rtc_trans with (y := y).
        * apply rtc_fromR. apply h.
        * apply hrtc.
      + split; assumption.
    - exists x. split.
      + apply rtc_refl.
      + split; assumption.
  Qed.

End ARS.

(* Question 4.2.e *)

Lemma SN_on_double_induction [A B : Type] [R1 : A -> A -> Prop] [R2 : B -> B -> Prop] (P : A -> B -> Prop) :
  (forall (a : A) (b : B),
    (forall (a' : A), R1 a a' -> SN_on R1 a') ->
    (forall (a' : A), R1 a a' -> P a' b) ->
    (forall (b' : B), R2 b b' -> SN_on R2 b') ->
    (forall (b' : B), R2 b b' -> P a b') ->
    P a b) ->
  forall (x : A) (y : B),
    SN_on R1 x -> SN_on R2 y -> P x y.
Proof.
  intros h x y hsnx hsny.
  generalize dependent y.
  induction hsnx as [ x hsnx IHx ].
  intros y hsny.
  induction hsny as [ y hsny IHy ].
  apply h.
  - apply hsnx.
  - intros a hra. apply (IHx a hra).
    constructor. apply hsny.
  - apply hsny.
  - apply IHy.
Qed.

(* Part 4.3 : Combinatory Logic *)

Inductive term :=
  | S
  | K
  | V (n : nat)
  | app (e1 e2 : term).

Coercion app : term >-> Funclass.

Section typing.

  Variable A : list form.

  Reserved Notation "|- e : s" (at level 60, e at next level).

  (* Question 4.3.a *)

  Inductive typing : term -> form -> Prop :=
    | typ_var n s : nth_error A n = Some s -> typing (V n) s
    | typ_app e1 e2 s t : typing e1 (s ~> t) -> typing e2 s -> typing (e1 e2) t
    | typ_axK s t : typing K (s ~> t ~> s)
    | typ_axS s t u : typing S ((s ~> t ~> u) ~> (s ~> t) ~> s ~> u).

  Notation "|- e : s" := (typing e s) (at level 60, e at next level).

  (* Question 4.3.b *)

  Search nth_error.
  About In_nth_error.
  About nth_error_In.

  Lemma hil_equiv s :
    A |-H s <-> exists e, |- e : s.
  Proof.
    split.
    - intros hs.
      induction hs as [ s hs | s t hst IHst hs IHs | s t | s t u ].
      + apply In_nth_error in hs as [ n eq ].
        exists (V n). apply typ_var. apply eq.
      + destruct IHst as [ e1 he1 ]. destruct IHs as [ e2 he2 ].
        exists (e1 e2). apply (typ_app e1 e2 s t he1 he2).
      + exists K. apply typ_axK.
      + exists S. apply typ_axS.
    - intros h.
      destruct h as [ e he ].
      induction he as [ n s eq | e1 e2 s t he1 IH1 he2 IH2 | s t | s t u ].
      + apply hil_assm. apply nth_error_In with (n := n). apply eq.
      + apply hil_elim with (s := s). all: assumption.
      + apply hil_axmK.
      + apply hil_axmS.
  Qed.

  (* Question 4.3.c *)

  Inductive red : term -> term -> Prop :=
    | red_axmK (e1 e2 : term) : red (K e1 e2) e1
    | red_axmS (e1 e2 e3 : term) : red (S e1 e2 e3) (e1 e3 (e2 e3))
    | red_appl (e1 e1' e2 : term) : red e1 e1' -> red (e1 e2) (e1' e2)
    | red_appr (e1 e2 e2' : term) : red e2 e2' -> red (e1 e2) (e1 e2').

  Notation "e1 >- e2" := (red e1 e2) (at level 60).

  (* Question 4.3.d *)

  Lemma preservation e1 e2 s :
    |- e1 : s -> e1 >- e2 -> |- e2 : s.
  Proof.
    intros hs hr.
    generalize dependent s.
    induction hr as [ e1 e2 | e1 e2 e3 | e1 e1' e2 hr IH | e1 e2 e2' hr IH ].
    all: intros s hs.
    - inversion hs as [ | ?? t ? hts ht | | ]; subst.
      inversion hts as [ | ?? u ? huts hu | | ]; subst.
      inversion huts; subst.
      assumption.
    - inversion hs as [ | ?? t ? hts ht | | ]; subst.
      inversion hts as [ | ?? u ? huts hu | | ]; subst.
      inversion huts as [ | ?? v ? hvuts hv | | ]; subst.
      inversion hvuts; subst.
      eapply typ_app.
      all: eapply typ_app.
      all: eassumption.
    - inversion hs as [ | ?? t ? hts ht | | ]; subst.
      apply typ_app with (s := t). apply IH.
      all: assumption.
    - inversion hs as [ | ?? t ? hts ht | | ]; subst.
      apply typ_app with (s := t). 2: apply IH.
      all: assumption.
  Qed.

  (* Question 4.3.e *)

  Definition reds := rtc red.

  Notation "e1 >-* e2" := (reds e1 e2) (at level 60).

  Lemma app_red e1 e1' e2 :
    e1 >-* e1' -> e1 e2 >-* e1' e2.
  Proof.
    intros hreds.
    induction hreds as [ x | x y hrxy | x y z hrtcxy IH1 hrtcyz IH2 ].
    - apply rtc_refl.
    - apply rtc_fromR. apply red_appl. apply hrxy.
    - apply rtc_trans with (y := y e2).
      + apply IH1.
      + apply IH2.
  Qed.

  (* Question 4.3.f *)

  Lemma subject_reduction e1 e2 s :
    |- e1 : s -> e1 >-* e2 -> |- e2 : s.
  Proof.
    intros hs hreds.
    induction hreds as [ x | x y hrxy | x y z hrtcxy IH1 hrtcyz IH2 ].
    - apply hs.
    - apply preservation with (e1 := x). all: assumption.
    - apply IH2. apply IH1. apply hs.
  Qed.

End typing.

(* Question 4.3.g *)

Notation "A |- e : s" := (typing A e s) (at level 60, e at next level).

Notation "t1 >- t2" := (red t1 t2) (at level 60).
Notation "t1 >-* t2" := (reds t1 t2) (at level 60).

Definition SN (e : term) := SN_on red e.

Lemma SN_app (e1 e2 : term) :
  SN (e1 e2) -> SN e1.
Proof.
  intros hsn.
  remember (e1 e2) as e.
  generalize dependent e1.
  induction hsn as [ e3 hsn IH ].
  all: intros e1 eq. all: subst.
  constructor. intros e3 hr.
  apply IH with (y := e3 e2) (e1 := e3).
  - apply red_appl. apply hr.
  - reflexivity.
Qed.

(* Question 4.3.h *)

Definition neutral (e : term) :=
  match e with
  | app K _
  | K
  | app (app S _) _
  | S
  | app S _ => False
  | _ => True
  end.

Lemma neutral_app e1 e2 :
  neutral e1 -> neutral (e1 e2).
Proof.
  intros hne1.
  destruct e1 as [ | | | e1 e1' ]; simpl in *.
  all: trivial.
  destruct e1.
  all: trivial.
Qed.

(* Question 4.3.i *)

Lemma progress e s :
  ([] |- e : s) -> (exists e', red e e') \/ ~ neutral e.
Proof.
  intros hs.
  induction hs as [ n s eq | e1 e2 s t he1 IH1 he2 IH2 | s t | s t u ]; simpl in *.
  3-4: right; intros bot; apply bot.
  1: destruct n; simpl in *. 1-2: discriminate.
  destruct IH1 as [ [ e1' hr ] | hne1 ].
  - left. exists (e1' e2). apply red_appl. apply hr.
  - destruct IH2 as [ [ e2' hr ] | hne2 ].
    + left. exists (e1 e2'). apply red_appr. apply hr.
    + destruct e1 as [ | | | e1 e1' ]; simpl in *.
      all: firstorder.
      destruct e1 as [ | | | e1 e1'' ]; simpl in *.
      all: firstorder.
      * left. exists e1'. apply red_axmK.
      * destruct e1 as [ | | | e1 e1''' ]; simpl in *.
        all: firstorder.
        left. exists (e1'' e2 (e1' e2)). apply red_axmS.
Qed.

(* Part 4.4 : Normalisation *)

(* Definition 1 *)

Fixpoint semantic (e : term) (s : form) : Prop :=
  match s with
  | var _ => SN e
  | bot => SN e
  | imp s1 s2 => forall e1, semantic e1 s1 -> semantic (e e1) s2
  end.

(* Theorem 8 *)

Theorem logical_relation (s : form) (e : term) :
     (semantic e s -> SN e)
  /\ (semantic e s -> forall e', e >-* e' -> semantic e' s)
  /\ (neutral e -> (forall e', e >- e' -> semantic e' s) -> semantic e s).
Proof.
  induction s as [ x | | s1 IHs1 s2 IHs2 ] in e |- *; simpl in *.
  (* proof of (1) for var x and bot *)
  1-2: split. 1,3: trivial.
  (* proof of (2) for var x and bot *)
  1-2: split. 1,3: intros. 1,2: apply SN_on_rtc with (x := e). 1-4: assumption.
  (* proof of (3) for var x and bot *)
  1-2: intros ? h. 1-2: constructor. 1-2: intros e' hr. 1-2: apply h. 1-2: apply hr.
  (* proof for s1 s2 : *)
  split. 2: split.
  - intros h. apply SN_app with (e2 := V 0). apply IHs2. apply h. apply IHs1; simpl.
    + split.
    + intros e' hr. inversion hr.
  - intros h e' hr e1 hsem. destruct (IHs2 (e e1)) as [ IH1s2 [ IH2s2 IH3s2 ] ]. apply IH2s2.
    + apply h. apply hsem.
    + apply app_red. apply hr.
  - intros hne H e1 hsem.
    assert (hsne1 : SN e1).
    { apply IHs1. apply hsem. }
    induction hsne1 as [ e1 IH1 IH2 ]. apply IHs2.
    + apply neutral_app. apply hne.
    + intros e' hr. inversion hr as [ | | ? e3 ? hre3 | ?? e1' hre1 ]; subst; simpl in *.
      * contradiction.
      * contradiction.
      * apply H. all: assumption.
      * apply IH2. apply hre1.
        destruct (IHs1 e1) as [ IH1s1 [ IH2s1 IH3s1 ] ]. apply IH2s1.
        apply hsem. constructor. apply hre1.
Qed.

(* Lemma 9 *)

Lemma semantic_for_K s t :
  semantic K (s ~> t ~> s).
Proof.
  intros e1 hseme1 e2 hseme2.

  assert (hsne1 : SN e1).
  { eapply logical_relation. apply hseme1. }

  assert (hsne2 : SN e2).
  { eapply logical_relation. apply hseme2. }

  eapply SN_on_double_induction with (R1 := red) (R2 := red); subst.
  2-3: eassumption.

  intros a b h1 h2 h3 h4.
  apply logical_relation; simpl in *.
  - split.
  - intros e' hr. inversion hr as [ | | ? e3 ? hre3 | ?? e2' hre1 ]; subst; simpl in *.
    + assumption.
    + inversion hre3 as [ | | ??? h | ?? e2' hre1 ]; subst; simpl in *.
      * inversion h.
      * destruct (logical_relation s (K e1 e2)) as [ lr1 [ lr2 lr3 ] ].
        apply lr2.
        -- eapply h2. admit.
        -- constructor. apply hr.
    + destruct (logical_relation s (K e1 e2)) as [ lr1 [ lr2 lr3 ] ].
      apply lr2.
      * eapply h2. admit.
      * constructor. apply hr.
Admitted.

(* Lemma 10 *)

Lemma semantic_for_S s t u :
  semantic S ((s ~> t ~> u) ~> (s ~> t) ~> s ~> u).
Proof.
Admitted.

(* Theorem 11 *)

Theorem semantic_by_typing A e s :
  (forall n s, nth_error A n = Some s -> semantic (V n) s) -> A |- e : s -> semantic e s.
Proof.
  intros h hs.
  induction hs as [ n s eq | e1 e2 s t he1 IH1 he2 IH2 | s t | s t u ]; simpl in *.
  - apply (h n s eq).
  - apply IH1. apply IH2.
  - intros. eapply semantic_for_K. all: eassumption.
  - intros. eapply semantic_for_S. all: eassumption.
Qed.

(* Lemma 12 *)

Lemma well_typed_terms_SN e s :
  ([] |- e : s) -> SN e.
Proof.
  intros hs.

  assert (h1 : forall n t, nth_error [] n = Some t -> semantic (V n) t).
  { intros n t h. destruct n; simpl in *. all: discriminate. }

  assert (h2 : semantic e s).
  { apply (semantic_by_typing []). all: assumption. }

  eapply logical_relation. apply h2.
Qed.

(* Lemma 13 *)

Lemma progress_with_typing e s :
  [] |- e : s -> exists e', e >-* e' /\ [] |- e' : s /\ ~ neutral e'.
Proof.
  intros hs.

  assert (h1 : SN e).
  { apply (well_typed_terms_SN e s hs). }

  apply (SN_to_WN red (fun x => [] |- x : s) (fun x => ~ neutral x)).
  - intros. eapply preservation. all: eassumption.
  - intros. eapply progress. eassumption. 
  - apply hs.
  - apply h1.
Qed.

(* Part 4.5 : Consistency *)

(* Question 4.5.a *)

Lemma noterm e :
  ~ [] |- e : bot.
Proof.
  intros hbot.
  destruct (progress_with_typing e bot hbot) as [ e' [ hr [ hbot' hne' ] ] ].
  destruct e' as [ | | n | e1 e2 ]; simpl in *.
  - inversion hbot'.
  - inversion hbot'.
  - contradiction.
  - destruct e1 as [ | | n | e4 e3 ]; simpl in *.
    + inversion hbot' as [ | ???? H | | ]; subst. inversion H.
    + inversion hbot' as [ | ???? H | | ]; subst. inversion H.
    + contradiction.
    + destruct e4.
      * inversion hbot' as [ | ???? H | | ]; subst. inversion H as [ | ???? H' | | ]; subst. inversion H'.
      * contradiction.
      * contradiction.
      * contradiction.
Qed.

(* Question 4.5.b *)

Corollary nd_consistent :
  ~ [] |-m bot.
Proof.
  intros hbot.
  apply ndm_hil in hbot.
  apply hil_equiv in hbot as [ e hbot ].
  apply (noterm e).
  apply hbot.
Qed.

(* Question 4.5.c *)

Corollary ndc_consistent :
  ~ [] |-c bot.
Proof.
  intros hbot.
  apply nd_consistent.
  apply consistency_iff.
  apply hbot.
Qed.