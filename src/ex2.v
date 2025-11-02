(* Exercice 2 : Minimal propositional logic *)

From Project Require Import ex1.
From Stdlib Require Import List.
Import ListNotations.

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
  induction hs as [ A s hs | A s t hs IH | A s t hst IHst hs IHs ] in B |- *.
  all: intros hincl.
  - apply ndm_assm. now apply hincl.
  - apply ndm_intr. apply IH. firstorder.
  - apply ndm_elim with (s := s).
    + now apply IHst.
    + now apply IHs.
Qed.

(* Question 2.1.c *)

Lemma Implication A s :
  A |-m s -> A |-c s.
Proof.
  intros hs.
  induction hs.
  - now apply ndc_assm.
  - now apply ndc_intr.
  - now apply ndc_elim with (s := s).
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
  induction hs as [ A s hs | A s1 s2 hs IH | A s1 s2 hst IHst hs IHs | A s hs IH ]; simpl in *.
  - apply ndm_assm. now apply in_map.
  - now apply ndm_intr.
  - apply ndm_elim with (s := trans t s1).
    all: assumption.
  - apply ndm_elim with (s := (trans t s ~> t) ~> t).
    + apply (DNE_Friedman (map (trans t) A) s t).
    + now apply ndm_intr.
Qed.

(* Question 2.1.g *)

Lemma ground_trans_bot_id s :
  ground s -> trans bot s = s.
Proof.
  intros hg.
  induction s as [ x | | s1 IHs1 s2 IHs2 ]; simpl in *.
  - contradiction.
  - reflexivity.
  - destruct hg as [hgs1 hgs2].
    now rewrite (IHs1 hgs1), (IHs2 hgs2).
Qed.

Lemma ground_truths s :
  ground s -> ([] |-m s <-> [] |-c s).
Proof.
  intros hg.
  split; intros hs.
  - now apply Implication.
  - specialize (Friedman [] s bot hs).
    simpl. intros hf.
    now rewrite <- ground_trans_bot_id.
Qed.

(* Question 2.1.h *)

Lemma consistency_iff :
  [] |-m bot <-> [] |-c bot.
Proof.
  now apply (ground_truths bot).
Qed.

(* Question 2.1.i *)

Definition dne s := ((s ~> bot) ~> bot) ~> s.

Lemma dne_classical s :
  [] |-c dne s.
Proof.
  apply ndc_intr.
  apply ndc_cntr.
  apply ndc_elim with (s := neg s).
  all: apply ndc_assm.
  all: firstorder.
Qed.

Lemma consistency_of_dne s :
  ~ ([] |-m neg (dne s)).
Proof.
  intros hmns.

  assert (hcns : [] |-c neg (dne s)).
  { apply (Implication [] (neg (dne s)) hmns). }

  assert (hcs : [] |-c dne s).
  { apply dne_classical. }

  assert (hcbot : [] |-c bot).
  { apply ndc_elim with (s := dne s). all: assumption. }

  apply (constructive_consistency hcbot).
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
  induction s as [ x | | s1 IHs1 s2 IHs2 ]; simpl in *.
  - apply (mu_mon M w w' x). all: assumption.
  - apply (bot_mon M w w'). all: assumption.
  - intros w'' hr' hi'. apply hi.
    + apply (rel_trans M w w' w''); assumption.
    + assumption.
Qed.

(* Question 2.2.e *)

Lemma ctx_monotonicity M A w w' :
  w <=(M) w' -> ctx_winterp M w A -> ctx_winterp M w' A.
Proof.
  intros hr hci.
  induction A as [ | s A IHA ]; simpl in *.
  - split.
  - destruct hci as [ hi hci ]. split.
    + apply (monotonicity M s w w' hr hi).
    + apply (IHA hci).
Qed.

(* Question 2.2.f *)

Lemma wsoundness M A s :
  A |-m s ->
    forall w,
      ctx_winterp M w A -> winterp M w s.
Proof.
  intros hs.
  induction hs as [ A s hs | A s t hs IH | A s t hst IHst hs IHs ]; simpl in *.
  all: intros w hci.
  - induction A as [ | t A IHA ]; simpl in *.
    + contradiction.
    + destruct hci as [ hi hci ]. destruct hs as [ e | hin ]; subst.
      * exact hi.
      * apply (IHA hin hci).
  - intros w' hr hi. apply IH. split.
    + assumption.
    + apply (ctx_monotonicity M A w w' hr hci).
  - apply (IHst w hci).
    + apply rel_refl.
    + apply (IHs w hci).
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

  assert (hc : ctx_winterp consistency_model tt []).
  { simpl. split. }

  apply (wsoundness consistency_model [] bot hbot tt hc).
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

  assert (hc : ctx_winterp notdne_model false []).
  { simpl. split. }

  assert (hi : winterp notdne_model false (dne (var 0))).
  { apply (wsoundness notdne_model [] (dne (var 0)) (hs (var 0)) false hc). }

  clear hc hs.

  simpl in *.
  apply (hi false); auto.
  intros w ? h.
  apply (h true); auto.
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
  induction s as [ x | | s1 IHs1 s2 IHs2 ] in A |- *; simpl in *.
  all: try reflexivity.
  split.
  - intros h. apply ndm_intr. apply IHs2. apply h.
    + apply incl_tl. apply incl_refl.
    + apply IHs1. apply ndm_assm. firstorder.
  - intros hs B hincl hi. apply IHs2. apply ndm_elim with (s := s1).
    + apply Weakm with (A := A). all: assumption.
    + apply IHs1. apply hi.
Qed.

(* Question 2.3.c *)

Lemma completeness A s :
  (forall M w, ctx_winterp M w A -> winterp M w s) -> A |-m s.
Proof.
  assert (hc : ctx_winterp syntactic_model A A).
  {
    induction A as [ | t A IHA ]; simpl.
    all: split.
    - apply correctness. apply ndm_assm. firstorder.
    - apply ctx_monotonicity with (w := A); simpl.
      + apply incl_tl. apply incl_refl.
      + apply IHA.
  }
  intros h.
  apply correctness.
  apply h.
  apply hc.
Qed.