(* Exercice 1 : Classical propositional logic *)

(* Part 1.1 : Classical natural deduction *)

From Stdlib Require Import List.
Import ListNotations.

Inductive form : Type :=
  | var (x : nat)
  | bot
  | imp (s t : form).

Print In.
Print incl.

Notation "s ~> t" := (imp s t) (at level 51, right associativity).
Notation neg s := (imp s bot).
Reserved Notation "A |-c s" (at level 70).

(* Question 1.1.a. *)

Inductive ndc : list form -> form -> Prop :=
  | ndc_assm (A : list form) (s : form) : In s A -> ndc A s
  | ndc_intr (A : list form) (s : form) (t : form) : ndc (s :: A) t -> ndc A (s ~> t)
  | ndc_elim (A : list form) (s : form) (t : form) : ndc A (s ~> t) -> ndc A s -> ndc A t
  | ndc_cntr (A : list form) (s : form) : ndc (neg s :: A) bot -> ndc A s.

Notation "A |-c s" := (ndc A s) (at level 70).

(* Question 1.1.b.1 *)

Goal forall A s, A |-c s ~> s.
Proof.
  intros A s.
  apply ndc_intr.
  apply ndc_assm.
  now constructor.
Qed.

(* Question 1.1.b.2 *)

Goal forall A s, s :: A |-c neg (neg s).
Proof.
  intros A s.
  apply ndc_intr.
  apply ndc_elim with (s := s).
  all: apply ndc_assm.
  all: firstorder.
Qed.

(* Question 1.1.b.3 *)

(* We can prove it without using contradiction *)

Goal [ neg (neg bot) ] |-c bot.
Proof.
  apply ndc_elim with (s := neg bot).
  - apply ndc_assm. firstorder.
  - apply ndc_intr. apply ndc_assm. firstorder.
Qed.

(* Question 1.1.b.4 *)

Goal forall A s, A |-c (neg (neg s)) ~> s.
Proof.
  intros A s.
  apply ndc_intr.
  apply ndc_cntr.
  apply ndc_elim with (s := neg s).
  all: apply ndc_assm.
  all: firstorder.
Qed.

(* Question 1.1.c *)

Fact Weakc A B s :
  A |-c s -> incl A B -> B |-c s.
Proof.
  intros hs.
  induction hs as [ A s hs | A s t hs IH | A s t hst IHst hs IHs | A s hs IH ] in B |- *.
  all: intros hincl.
  - apply ndc_assm. now apply hincl.
  - apply ndc_intr. apply IH. firstorder.
  - apply ndc_elim with (s := s).
    + now apply IHst.
    + now apply IHs.
  - apply ndc_cntr. apply IH. firstorder.
Qed.

(* Question 1.1.d *)

Fixpoint ground (s : form) : Prop :=
  match s with
  | var _ => False
  | bot => True
  | imp s t => ground s /\ ground t
  end.

(* Part 1.2 : Model-based semantics *)

Definition Model := nat -> Prop.

(* Question 1.2.a *)

Fixpoint interp (M : Model) (s : form) : Prop :=
  match s with
  | var x => M x
  | bot => False
  | imp s t => interp M s -> interp M t
  end.

(* Question 1.2.b *)

Fixpoint ctx_interp (M : Model) (A : list form) : Prop :=
  match A with
  | [] => True
  | s :: A => interp M s /\ ctx_interp M A
  end.

(* Question 1.2.c *)

Lemma soundness M A (s : form) :
  (forall P, ~~P -> P) ->
  A |-c s ->
  ctx_interp M A ->
  interp M s.
Proof.
  intros DNE hs hc.
  induction hs as [ A s hs | A s t hs IH | A s t hst IHst hs IHs | A s hs IH ]; simpl in *.
  - induction A as [ | t A IHA ].
    + contradiction.
    + destruct hc. inversion hs; subst.
      * assumption.
      * apply IHA; assumption.
 - intros hi. apply IH. split; assumption.
 - apply (IHst hc (IHs hc)).
 - apply DNE. intros nhi. apply IH. split; assumption.
Qed.

(* Question 1.2.d *)

Lemma classical_consistency :
  (forall P, ~~P -> P) -> ~ ([] |-c bot).
Proof.
  intros DNE hbot.
  set (M := fun (_ : nat) => True).

  assert (hc : ctx_interp M []) by firstorder.

  apply (soundness M [] bot DNE hbot hc).
Qed.

(* Question 1.2.e *)

Lemma constructive_soundness M A (s : form) :
  A |-c s -> ctx_interp M A -> ~~ interp M s.
Proof.
  intros hs hc nhi.
  induction hs as [ A s hs | A s t hs IH | A s t hst IHst hs IHs | A s hs IH ]; simpl in *.
  - induction A as [ | t A IHA ].
    + contradiction.
    + destruct hc. inversion hs; subst.
      * now apply nhi.
      * apply IHA; assumption.
  - apply nhi. intros his. exfalso. apply IH.
    + split; assumption.
    + intros hit. now apply nhi.
  - apply (IHs hc). intros his.
    apply (IHst hc). intros hist.
    apply (nhi (hist his)).
  - apply IH.
    + split; assumption.
    + now intros bot.
Qed.

(* Question 1.2.f *)

Lemma constructive_consistency :
  ~ ([] |-c bot).
Proof.
  intros hbot.
  set (M := fun (_ : nat) => True).

  assert (hc : ctx_interp M []) by firstorder.

  now apply (constructive_soundness M [] bot hbot hc).
Qed.