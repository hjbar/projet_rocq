(* Exercice 1 : Classical propositional logic *)

(* Part 1.1 : Classical natural deduction *)

From Stdlib Require Import List.
Import ListNotations.

Set Default Goal Selector "!".

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
  | ndc_assm A s : In s A -> ndc A s
  | ndc_intr A s t : ndc (s :: A) t -> ndc A (s ~> t)
  | ndc_elim A s t : ndc A (s ~> t) -> ndc A s -> ndc A t
  | ndc_cntr A s : ndc (neg s :: A) bot -> ndc A s.

Notation "A |-c s" := (ndc A s) (at level 70).

(* Question 1.1.b.1 *)

Goal forall A s, A |-c s ~> s.
Proof.
  intros A s.
  apply ndc_intr.
  apply ndc_assm.
  constructor.
  reflexivity.
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

Lemma dne_classical A s :
  A |-c (neg (neg s)) ~> s.
Proof.
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
  induction hs as [ | ???? IH | ???? IHst ? IHs | ??? IH ] in B |- *.
  all: intros hincl.
  - apply ndc_assm. apply hincl. assumption.
  - apply ndc_intr. apply IH. apply incl_cons.
    + firstorder.
    + apply incl_tl. assumption.
  - apply ndc_elim with (s := s).
    + apply IHst. assumption.
    + apply IHs. assumption.
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
  (forall P, ~~P -> P) -> A |-c s -> ctx_interp M A -> interp M s.
Proof.
  intros DNE hs hc.
  induction hs as [ ?? hs | ???? IH | ???? IHst ? IHs | ??? IH ]; simpl in *.
  - induction A as [ | t A IHA ]; simpl in *.
    + contradiction.
    + destruct hc. inversion hs; subst.
      * assumption.
      * apply IHA. all: assumption.
 - intros hi. apply IH. split. all: assumption.
 - apply IHst.
   + assumption.
   + apply IHs. assumption.
 - apply DNE. intros nhi. apply IH. split. all: assumption.
Qed.

(* Question 1.2.d *)

Lemma classical_consistency :
  (forall P, ~~P -> P) -> ~ ([] |-c bot).
Proof.
  intros DNE hbot.
  set (M := fun (_ : nat) => True).
  change (interp M bot).
  apply soundness with (A := []); simpl.
  - assumption.
  - assumption.
  - split.
Qed.

(* Question 1.2.e *)

Lemma constructive_soundness M A (s : form) :
  A |-c s -> ctx_interp M A -> ~~ interp M s.
Proof.
  intros hs hc nhi.
  induction hs as [ ?? hs | ???? IH | ???? IHst ? IHs | ??? IH ]; simpl in *.
  - induction A as [ | t A IHA ]; simpl in *.
    + contradiction.
    + destruct hc. inversion hs; subst.
      * congruence.
      * apply IHA. all: assumption.
  - apply nhi. intros his. exfalso. apply IH.
    + split. all: assumption.
    + intros hit. apply nhi. intros. assumption.
  - apply (IHs hc). intros his.
    apply (IHst hc). intros hist.
    apply nhi. apply hist. apply his.
  - apply IH.
    + split. all: assumption.
    + intros bot. apply bot.
Qed.

(* Question 1.2.f *)

Lemma constructive_consistency :
  ~ ([] |-c bot).
Proof.
  intros hbot.
  set (M := fun (_ : nat) => True).
  apply (constructive_soundness M [] bot); simpl.
  - assumption.
  - split.
  - intros bot. apply bot.
Qed.