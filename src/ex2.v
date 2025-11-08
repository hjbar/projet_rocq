(* Exercice 2 : Minimal propositional logic *)

From Project Require Import ex1.
From Stdlib Require Import List.
Import ListNotations.

Set Default Goal Selector "!".

(* Part 2.1 : Minimal natural deduction *)

(* Question 2.1.a *)

Reserved Notation "A |-m s" (at level 70).

Inductive ndm : list form -> form -> Prop :=
  | ndm_assm A s : In s A -> ndm A s
  | ndm_intr A s t : ndm (s :: A) t -> ndm A (s ~> t)
  | ndm_elim A s t : ndm A (s ~> t) -> ndm A s -> ndm A t.

Notation "A |-m s" := (ndm A s) (at level 70).

(* Question 2.1.b *)

Lemma Weakm A B s :
  A |-m s -> incl A B -> B |-m s.
Proof.
  intros hs.
  induction hs as [ | ???? IH | ???? IHst ? IHs ] in B |- *.
  all: intros hincl.
  - apply ndm_assm. apply hincl. assumption.
  - apply ndm_intr. apply IH. firstorder.
  - apply ndm_elim with (s := s).
    + apply IHst. assumption.
    + apply IHs. assumption.
Qed.

(* Question 2.1.c *)

Lemma Implication A s :
  A |-m s -> A |-c s.
Proof.
  intros hs.
  induction hs.
  - apply ndc_assm. assumption.
  - apply ndc_intr. assumption.
  - apply ndc_elim with (s := s). all: assumption.
Qed.

(* Question 2.1.d *)

Fixpoint trans (t s : form) : form :=
  match s with
  | var x => (var x ~> t) ~> t
  | bot => t
  | imp s1 s2 => imp (trans t s1) (trans t s2)
  end.

(* Question 2.1.e *)

Lemma DNE_Friedman A s t :
  A |-m ((trans t s ~> t) ~> t) ~> (trans t s).
Proof.
  induction s as [ x | | s1 IHs1 s2 IHs2 ] in A |- *; simpl.
  - repeat apply ndm_intr.
    apply ndm_elim with (s := ((var x ~> t) ~> t) ~> t).
    + apply ndm_assm. firstorder.
    + apply ndm_intr. apply ndm_elim with (s := var x ~> t).
      all: apply ndm_assm.
      all: firstorder.
  - apply ndm_intr.
    apply ndm_elim with (s := t ~> t).
    + apply ndm_assm. firstorder.
    + apply ndm_intr. apply ndm_assm. firstorder.
  - repeat apply ndm_intr.
    apply ndm_elim with (s := (trans t s2 ~> t) ~> t).
    1: apply IHs2.
    apply ndm_intr. apply ndm_elim with (s := (trans t s1 ~> trans t s2) ~> t).
    1: apply ndm_assm. 1: firstorder.
    apply ndm_intr. apply ndm_elim with (s := trans t s2).
    1: apply ndm_assm. 1: firstorder.
    apply ndm_elim with (s := trans t s1).
    1: apply ndm_assm. 1: firstorder.
    apply ndm_elim with (s := (trans t s1 ~> t) ~> t).
    1: apply IHs1.
    apply ndm_intr. apply ndm_elim with (s := trans t s1).
    all: apply ndm_assm.
    all: firstorder.
Qed.

(* Question 2.1.f *)

Lemma Friedman A s t :
  A |-c s -> map (trans t) A |-m trans t s.
Proof.
  intros hs.
  induction hs as [ | | ? s1 | ? s ]; simpl in *.
  - apply ndm_assm. apply in_map. assumption.
  - apply ndm_intr. assumption.
  - apply ndm_elim with (s := trans t s1). all: assumption.
  - apply ndm_elim with (s := (trans t s ~> t) ~> t).
    + apply DNE_Friedman.
    + apply ndm_intr. assumption.
Qed.

(* Question 2.1.g *)

Lemma ground_trans_bot_id s :
  ground s -> trans bot s = s.
Proof.
  intros hg.
  induction s as [ | | ? IHs1 ? IHs2 ]; simpl in *.
  - contradiction.
  - reflexivity.
  - destruct hg as [hgs1 hgs2].
    rewrite (IHs1 hgs1). rewrite (IHs2 hgs2). reflexivity.
Qed.

Lemma ground_truths s :
  ground s -> ([] |-m s <-> [] |-c s).
Proof.
  intros hg.
  split. all: intros hs.
  - apply Implication. assumption.
  - rewrite <- ground_trans_bot_id.
    + change (map (trans bot) [] |-m trans bot s). apply Friedman. assumption.
    + assumption.
Qed.

(* Question 2.1.h *)

Lemma consistency_iff :
  [] |-m bot <-> [] |-c bot.
Proof.
  apply ground_truths; simpl.
  split.
Qed.

(* Question 2.1.i *)

Definition dne s := ((s ~> bot) ~> bot) ~> s.

Lemma consistency_of_dne s :
  ~ ([] |-m neg (dne s)).
Proof.
  intros hmns.
  apply constructive_consistency.
  apply ndc_elim with (s := dne s).
  - apply Implication. assumption.
  - apply dne_classical.
Qed.

(* Part 2.2 : World-based semantics *)

(* Question 2.2.a *)

Record WModel : Type := {
  world : Type ;

  rel : world -> world -> Prop ;
  bot_w : world -> Prop ;
  mu_w : world -> nat -> Prop ;

  rel_refl w : rel w w ;
  rel_trans w1 w2 w3 : rel w1 w2 -> rel w2 w3 -> rel w1 w3 ;

  bot_mon w1 w2 : rel w1 w2 -> bot_w w1 -> bot_w w2 ;

  mu_mon w1 w2 x : rel w1 w2 -> mu_w w1 x -> mu_w w2 x ;
}.

Notation "w '<=(' M ) w'" := (M.(rel) w w') (at level 40, w' at next level).

(* Question 2.2.b *)

Fixpoint winterp (M : WModel) (w : M.(world)) (s : form) : Prop :=
  match s with
  | var x => M.(mu_w) w x
  | bot => M.(bot_w) w
  | imp s t =>
      forall w',
        w <=(M) w' -> winterp M w' s -> winterp M w' t
  end.

(* Question 2.2.c *)

Fixpoint ctx_winterp (M : WModel) (w : M.(world)) (A : list form) : Prop :=
  match A with
  | [] => True
  | s :: A => winterp M w s /\ ctx_winterp M w A
  end.

(* Question 2.2.d *)

Lemma monotonicity M s w w' :
  w <=(M) w' -> winterp M w s -> winterp M w' s.
Proof.
  intros hr hi.
  induction s; simpl in *.
  - apply mu_mon with (w1 := w). all: assumption.
  - apply bot_mon with (w1 := w). all: assumption.
  - intros w'' hr' hi'. apply hi.
    + apply rel_trans with (w2 := w'). all: assumption.
    + assumption.
Qed.

(* Question 2.2.e *)

Lemma ctx_monotonicity M A w w' :
  w <=(M) w' -> ctx_winterp M w A -> ctx_winterp M w' A.
Proof.
  intros hr hci.
  induction A; simpl in *.
  - split.
  - destruct hci as [ hi hci ]. split.
    + apply monotonicity with (w := w). all: assumption.
    + apply IHA. assumption.
Qed.

(* Question 2.2.f *)

Lemma wsoundness M A s :
  A |-m s -> forall w, ctx_winterp M w A -> winterp M w s.
Proof.
  intros hs.
  induction hs as [ A ? hs | ???? IH | ???? IHst ? IHs ]; simpl in *.
  all: intros w hci.
  - induction A as [ | ?? IHA ]; simpl in *.
    + contradiction.
    + destruct hci as [ hi hci ]. destruct hs as [ e | hin ]; subst.
      * assumption.
      * apply IHA. all: assumption.
  - intros w' hr hi. apply IH. split.
    + assumption.
    + apply ctx_monotonicity with (w := w). all: assumption.
  - apply IHst with (w := w).
    + assumption.
    + apply rel_refl.
    + apply IHs. assumption.
Qed.

(* Question 2.2.g *)

Definition consistency_model : WModel.
Proof.
  refine {|
    world := unit ;
    rel _ _ := True ;
    bot_w _ := False ;
    mu_w _ _ := True ;
  |}.
  all: trivial.
Defined.

(* Question 2.2.h *)

Lemma consistency :
  ~ ([] |-m bot).
Proof.
  intros hbot.
  apply (wsoundness consistency_model [] bot) with (w := tt); simpl.
  - assumption.
  - split.
Qed.

(* Question 2.2.i *)

Definition notdne_model : WModel.
Proof.
  refine {|
    world := bool ;

    rel w1 w2 :=
      match w1, w2 with
      | false, false => True
      | false, true => True
      | true, false => False
      | true, true => True
      end;

    bot_w _ := False ;

    mu_w b _ :=
      match b with
      | false => False
      | true => True
      end;
  |}.
  all: repeat intros [ | ].
  all: trivial.
Defined.

(* Question 2.2.j *)

Lemma dne_independant :
  ~ (forall s, [] |-m dne s).
Proof.
  intros hs.

  assert (hi : winterp notdne_model false (dne (var 0))).
  {
    apply wsoundness with (A := []); simpl.
    - apply hs.
    - split.
  }

  simpl in *.
  apply (hi false). 1: split.
  intros ?? h.
  apply (h true). all: auto.
Qed.

(* Part 2.3 : Completeness *)

(* Question 2.3.a *)

Definition syntactic_model : WModel.
Proof.
  refine {|
    world := list form ;

    rel A B := incl A B ;
    bot_w A := A |-m bot ;
    mu_w A x := A |-m var x ;
  |}.
  - apply incl_refl.
  - apply incl_tran.
  - intros A B hincl hbot.
    apply Weakm with (A := A).
    all: assumption.
  - intros A B x hincl hs.
    apply Weakm with (A := A).
    all: assumption.
Defined.

(* Question 2.3.b *)

Lemma correctness A s :
  winterp syntactic_model A s <-> A |-m s.
Proof.
  induction s as [ | | s1 IHs1 ? IHs2 ] in A |- *; simpl in *.
  1-2: reflexivity.
  split.
  - intros h. apply ndm_intr. apply IHs2. apply h.
    + firstorder.
    + apply IHs1. apply ndm_assm. firstorder.
  - intros hs B hincl hi. apply IHs2. apply ndm_elim with (s := s1).
    + apply Weakm with (A := A). all: assumption.
    + apply IHs1. assumption.
Qed.

(* Question 2.3.c *)

Lemma completeness A s :
  (forall M w, ctx_winterp M w A -> winterp M w s) -> A |-m s.
Proof.
  assert (hc : ctx_winterp syntactic_model A A).
  {
    induction A as [ | ? A ]; simpl.
    all: split.
    - apply correctness. apply ndm_assm. firstorder.
    - apply ctx_monotonicity with (w := A); simpl.
      + firstorder.
      + assumption.
  }

  intros h. apply correctness. apply h. assumption.
Qed.