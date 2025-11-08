(* Exercice 4 : Proof terms *)

From Project Require Import ex1 ex2.
From Stdlib Require Import Lia ZArith List Program.Equality.
Import ListNotations.

Set Default Goal Selector "!".

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
  induction hs as [ | s | | s t ].
  - apply ndm_assm. assumption.
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
  + assumption.
Qed.

Fact hil_trans A s t u :
  A |-H s ~> t ~> u -> A |-H s ~> t -> A |-H s ~> u.
Proof.
  intros hstu hst.
  apply hil_elim with (s := s ~> t).
  - apply hil_elim with (s := s ~> t ~> u).
    * apply hil_axmS.
    * assumption.
  - assumption.
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
  induction hs as [ ? hs | t | | ]; simpl in *.
  - destruct hs as [ e | hin ]; subst.
    + apply hil_refl.
    + apply hil_weak. apply hil_assm. assumption.
  - apply hil_trans with (t := t). all: assumption.
  - apply hil_weak. apply hil_axmK.
  - apply hil_weak. apply hil_axmS.
Qed.

(* Question 4.1.e *)

Fact ndm_hil A s :
  A |-m s -> A |-H s.
Proof.
  intros hs.
  induction hs as [ | | ? s ].
  - apply hil_assm. assumption.
  - apply hil_intr. assumption.
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
    induction hrtc as [ | | ???? IH1 ? IH2 ].
    - assumption.
    - inversion hsn as [ ? h ]; subst. apply h. assumption.
    - apply IH2. apply IH1. assumption.
  Qed.

  (* Question 4.2.d *)

  Variables T V : A -> Prop.

  Variable Hpres : forall x y, T x -> R x y -> T y.
  Variable Hprog : forall x, T x -> (exists y, R x y) \/ V x.

  Lemma SN_to_WN x :
    T x -> SN_on x -> exists v, rtc x v /\ T v /\ V v.
  Proof.
    intros ht hsn.
    induction hsn as [ x ? IH ].
    destruct (Hprog x ht) as [ [ y h ] | ].
    - destruct (IH y h (Hpres x y ht h)) as [ z [ ? [ ?? ] ] ]. 
      exists z. split.
      + apply rtc_trans with (y := y).
        * apply rtc_fromR. assumption.
        * assumption.
      + split. all: assumption.
    - exists x. split.
      + apply rtc_refl.
      + split. all: assumption.
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
  induction hsnx as [ ?? IHx ].
  intros y hsny.
  induction hsny.
  apply h.
  - assumption.
  - intros a hra. apply IHx.
    + assumption.
    + constructor. assumption.
  - assumption.
  - assumption.
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
    | typ_var (n : nat) (s : form) : nth_error A n = Some s -> typing (V n) s
    | typ_app (e1 e2 : term) (s t : form) : typing e1 (s ~> t) -> typing e2 s -> typing (e1 e2) t
    | typ_axK (s t : form) : typing K (s ~> t ~> s)
    | typ_axS (s t u : form) : typing S ((s ~> t ~> u) ~> (s ~> t) ~> s ~> u).

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
      induction hs as [ ? hs | s ?? IHst ? IHs | | ].
      + apply In_nth_error in hs as [ n eq ].
        exists (V n). apply typ_var. assumption.
      + destruct IHst as [ e1 he1 ]. destruct IHs as [ e2 he2 ].
        exists (e1 e2). apply typ_app with (s := s). all: assumption.
      + exists K. apply typ_axK.
      + exists S. apply typ_axS.
    - intros h.
      destruct h as [ ? he ].
      induction he as [ n | ?? s | | ].
      + apply hil_assm. apply nth_error_In with (n := n). assumption.
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
    induction hr as [ | | ???? IH | ???? IH ].
    all: intros s hs.
    - inversion hs as [ | ?? t ? hts | | ]; subst.
      inversion hts as [ | ?? u ? huts | | ]; subst.
      inversion huts; subst.
      assumption.
    - inversion hs as [ | ?? t ? hts | | ]; subst.
      inversion hts as [ | ?? u ? huts | | ]; subst.
      inversion huts as [ | ?? v ? hvuts | | ]; subst.
      inversion hvuts; subst.
      eapply typ_app.
      all: eapply typ_app.
      all: eassumption.
    - inversion hs as [ | ?? t | | ]; subst.
      apply typ_app with (s := t).
      + apply IH. assumption.
      + assumption.
    - inversion hs as [ | ?? t | | ]; subst.
      apply typ_app with (s := t).
      + assumption.
      + apply IH. assumption.
  Qed.

  (* Question 4.3.e *)

  Definition reds := rtc red.

  Notation "e1 >-* e2" := (reds e1 e2) (at level 60).

  Lemma app_red e1 e1' e2 :
    e1 >-* e1' -> e1 e2 >-* e1' e2.
  Proof.
    intros hreds.
    induction hreds as [ | | ? y ].
    - apply rtc_refl.
    - apply rtc_fromR. apply red_appl. assumption.
    - apply rtc_trans with (y := y e2). all: assumption.
  Qed.

  (* Question 4.3.f *)

  Lemma subject_reduction e1 e2 s :
    |- e1 : s -> e1 >-* e2 -> |- e2 : s.
  Proof.
    intros hs hreds.
    induction hreds as [ | x | ???? IH1 ? IH2 ].
    - assumption.
    - apply preservation with (e1 := x). all: assumption.
    - apply IH2. apply IH1. assumption.
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
  induction hsn as [ ?? IH ].
  all: intros e1 eq. all: subst.
  constructor. intros e3 hr.
  apply IH with (y := e3 e2) (e1 := e3).
  - apply red_appl. assumption.
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
  destruct e1 as [ | | | e1 ]; simpl in *.
  1-3: trivial.
  destruct e1.
  all: trivial.
Qed.

(* Question 4.3.i *)

Lemma progress e s :
  ([] |- e : s) -> (exists e', red e e') \/ ~ neutral e.
Proof.
  intros hs.
  induction hs as [ n | e1 e2 ??? IH1 ? IH2 | | ]; simpl in *.
  3-4: right; intros bot; apply bot.
  1: destruct n; simpl in *. 1-2: discriminate.
  destruct IH1 as [ [ e1' hr ] | hne1 ].
  - left. exists (e1' e2). apply red_appl. assumption.
  - destruct IH2 as [ [ e2' hr ] | hne2 ].
    + left. exists (e1 e2'). apply red_appr. assumption.
    + destruct e1 as [ | | | e1 e1' ]; simpl in *.
      1-3: firstorder.
      destruct e1 as [ | | | e1 e1'' ]; simpl in *.
      1,3: firstorder.
      * left. exists e1'. apply red_axmK.
      * destruct e1 as [ | | | e1 e1''' ]; simpl in *.
        2-4: firstorder.
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
  induction s as [ | | ? IHs1 ? IHs2 ] in e |- *; simpl in *.
  (* proof of (1) for var x and bot *)
  1-2: split. 1,3: trivial.
  (* proof of (2) for var x and bot *)
  1-2: split. 1,3: intros. 1,2: apply SN_on_rtc with (x := e). 1-4: assumption.
  (* proof of (3) for var x and bot *)
  1-2: intros ? h. 1-2: constructor. 1-2: intros e' hr. 1-2: apply h. 1-2: assumption.
  (* proof for s1 s2 : *)
  split. 2: split.
  - intros h. apply SN_app with (e2 := V 0). apply IHs2. apply h. apply IHs1; simpl.
    + split.
    + intros e' hr. inversion hr.
  - intros h e' hr e1 hsem. destruct (IHs2 (e e1)) as [ IH1s2 [ IH2s2 IH3s2 ] ]. apply IH2s2.
    + apply h. assumption.
    + apply app_red. assumption.
  - intros hne H e1 hsem.
    assert (hsne1 : SN e1).
    { apply IHs1. apply hsem. }
    induction hsne1 as [ e1 IH1 IH2 ]. apply IHs2.
    + apply neutral_app. assumption.
    + intros e' hr. inversion hr as [ | | ? e3 ? hre3 | ?? e1' hre1 ]; subst; simpl in *.
      * contradiction.
      * contradiction.
      * apply H. all: assumption.
      * apply IH2. 1: assumption.
        destruct (IHs1 e1) as [ IH1s1 [ IH2s1 IH3s1 ] ]. apply IH2s1. 1: assumption.
        constructor. assumption.
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

  revert e1 e2 hsne1 hsne2 hseme1 hseme2.
  apply (
    SN_on_double_induction
      (A := term) (B := term)
      (R1 := red) (R2 := red)
      (fun a b => semantic a s -> semantic b t -> semantic (K a b) s) ).
  intros e1 e2 hsne1 IHe1 hsne2 IHe2 hseme1 hseme2.

  apply logical_relation; simpl in *. 1: split.
  intros e' hr.
  inversion hr as [ | | ??? hre3 | ]; subst; simpl in *.
  - assumption.
  - inversion hre3 as [ | | ??? h | ]; subst; simpl in *.
    + inversion h.
    + apply IHe1.
      1,3 : assumption.
      destruct (logical_relation s e1) as [ lr1 [ lr2 lr3 ] ].
      apply lr2. 2: constructor. all: assumption.
  - apply IHe2.
    1-2: assumption.
    destruct (logical_relation t e2) as [ lr1 [ lr2 lr3 ] ].
    apply lr2. 2: constructor. all: assumption.
Qed.

(* Lemma 10 *)

Lemma SN_on_triple_induction
  [A B C : Type]
  [R1 : A -> A -> Prop]
  [R2 : B -> B -> Prop]
  [R3 : C -> C -> Prop]
  (P : A -> B -> C -> Prop) :
    (forall (a : A) (b : B) (c : C),
      (forall (a' : A), R1 a a' -> SN_on R1 a') ->
      (forall (a' : A), R1 a a' -> P a' b c) ->
      (forall (b' : B), R2 b b' -> SN_on R2 b') ->
      (forall (b' : B), R2 b b' -> P a b' c) ->
      (forall (c' : C), R3 c c' -> SN_on R3 c') ->
      (forall (c' : C), R3 c c' -> P a b c') ->
      P a b c) ->
    forall (x : A) (y : B) (z : C),
      SN_on R1 x -> SN_on R2 y -> SN_on R3 z -> P x y z.
Proof.
  intros h x y z hsnx hsny hsnz.
  generalize dependent z.
  generalize dependent y.
  induction hsnx as [ ?? IHx ].
  intros y hsny.
  induction hsny as [ ?? IHy ].
  intros z hsnz.
  induction hsnz.
  apply h.
  - assumption.
  - intros a hra. apply IHx.
    + assumption.
    + constructor. assumption.
    + constructor. assumption.
  - assumption.
  - intros b hrb. apply IHy.
    + assumption.
    + constructor. assumption.
  - assumption.
  - assumption.
Qed.

Lemma semantic_for_S s t u :
  semantic S ((s ~> t ~> u) ~> (s ~> t) ~> s ~> u).
Proof.
  intros e1 hseme1 e2 hseme2 e3 hseme3.

  assert (hsne1 : SN e1).
  { eapply logical_relation. apply hseme1. }

  assert (hsne2 : SN e2).
  { eapply logical_relation. apply hseme2. }

  assert (hsne3 : SN e3).
  { eapply logical_relation. apply hseme3. }

  revert e1 e2 e3 hsne1 hsne2 hsne3 hseme1 hseme2 hseme3.
  apply (
    SN_on_triple_induction
      (A := term) (B := term) (C := term)
      (R1 := red) (R2 := red) (R3 := red)
      (fun a b c => semantic a (s ~> t ~> u) -> semantic b (s ~> t) -> semantic c s -> semantic (S a b c) u) ).
  intros e1 e2 e3 hsne1 IHe1 hsne2 IHe2 hsne3 IHe3 hseme1 hseme2 hseme3.

  apply logical_relation; simpl in *. 1: split.
  intros e' hr.
  inversion hr as [ | | ??? hre4 | ]; subst; simpl in *.
  - apply hseme1.
    + assumption.
    + apply hseme2. assumption.
  - inversion hre4 as [ | | ??? hr1 | ]; subst; simpl in *.
    + inversion hr1 as [ | | ??? hr2 | ]; subst; simpl in *.
      * inversion hr2.
      * apply IHe1. 1,3,4: assumption.
        intros e5 hseme5 e6 hseme6.
        destruct (logical_relation u (e1 e5 e6)) as [ lr1 [ lr2 lr3 ] ].
        apply lr2.
        -- apply hseme1. all: assumption.
        -- apply app_red. apply app_red. constructor. assumption.
    + apply IHe2. 1,2,4: assumption.
      intros e5 hseme5.
      destruct (logical_relation t (e2 e5)) as [ lr1 [ lr2 lr3 ] ].
      apply lr2.
      * apply hseme2. assumption.
      * apply app_red. constructor. assumption.
  - apply IHe3.
    + assumption.
    + assumption.
    + assumption.
    + destruct (logical_relation s e3) as [ lr1 [ lr2 lr3 ] ].
      apply lr2. 2: constructor. all: assumption.
Qed.

(* Theorem 11 *)

Theorem semantic_by_typing A e s :
  (forall n s, nth_error A n = Some s -> semantic (V n) s) -> A |- e : s -> semantic e s.
Proof.
  intros h hs.
  induction hs as [ | ????? IH1 ? IH2 | | ]; simpl in *.
  - apply h. assumption.
  - apply IH1. assumption.
  - intros. eapply semantic_for_K. all: eassumption.
  - intros. eapply semantic_for_S. all: eassumption.
Qed.

(* Lemma 12 *)

Lemma well_typed_terms_SN e s :
  ([] |- e : s) -> SN e.
Proof.
  intros hs.
  apply logical_relation with (s := s).
  apply semantic_by_typing with (A := []).
  - intros n t h. destruct n; simpl in *. all: discriminate.
  - assumption.
Qed.

(* Lemma 13 *)

Lemma progress_with_typing e s :
  [] |- e : s -> exists e', e >-* e' /\ [] |- e' : s /\ ~ neutral e'.
Proof.
  intros hs.
  apply SN_to_WN.
  - intros. apply preservation with (e1 := x). all: assumption.
  - intros. apply progress with (s := s). assumption.
  - assumption.
  - apply well_typed_terms_SN with (s := s). assumption.
Qed.

(* Part 4.5 : Consistency *)

(* Question 4.5.a *)

Lemma noterm e :
  ~ [] |- e : bot.
Proof.
  intros hbot.
  destruct (progress_with_typing e bot hbot) as [ e' [ ? [ hbot' ? ] ] ].
  destruct e' as [ | | | e1 ]; simpl in *.
  - inversion hbot'.
  - inversion hbot'.
  - contradiction.
  - destruct e1 as [ | | | e2 ]; simpl in *.
    + inversion hbot' as [ | ???? h | | ]; subst. inversion h.
    + inversion hbot' as [ | ???? h | | ]; subst. inversion h.
    + contradiction.
    + destruct e2.
      * inversion hbot' as [ | ???? h | | ]; subst. inversion h as [ | ???? h' | | ]; subst. inversion h'.
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
  assumption.
Qed.

(* Question 4.5.c *)

Corollary ndc_consistent :
  ~ [] |-c bot.
Proof.
  intros hbot.
  apply nd_consistent.
  apply consistency_iff.
  assumption.
Qed.