(* Exercice 3 : Cut Elimination *)

From Project Require Import ex1 ex2.
From Stdlib Require Import List Program.Equality.
Import ListNotations.

(* Definition of |-cf and |-ae *)

Reserved Notation "A |-cf s" (at level 70).
Reserved Notation "A |-ae s" (at level 70).

Inductive cf : list form -> form -> Prop :=
  | cf_intr A s t : cf (s :: A) t -> cf A (s ~> t)
  | cf_frae A s : ae A s -> cf A s

with ae : list form -> form -> Prop :=
  | ae_elim A s t : ae A (s ~> t) -> cf A s -> ae A t
  | ae_assm A s : In s A -> ae A s.

Notation "A |-cf s" := (cf A s) (at level 70).
Notation "A |-ae s" := (ae A s) (at level 70).

Scheme cf_ind_mut := Induction for cf Sort Prop
  with ae_ind_mut := Induction for ae Sort Prop.
Combined Scheme cf_ae_ind from cf_ind_mut, ae_ind_mut.
Check cf_ae_ind.

(* Lemma 1 : Weakening *)

Lemma Weak_mut :
     (forall A s, A |-cf s -> forall B, incl A B -> B |-cf s)
  /\ (forall A s, A |-ae s -> forall B, incl A B -> B |-ae s).
Proof.
  apply cf_ae_ind.
  - intros A s t hcft h B hincl.
    apply cf_intr. apply h. firstorder.
  - intros A s haes h B hincl.
    apply cf_frae. now apply h.
  - intros A s t haest h1 hcfs h2 B hincl.
    apply ae_elim with (s := s).
    + now apply h1.
    + now apply h2.
  - intros A s hin B hincl.
    apply ae_assm. now apply hincl.
Qed.

Lemma Weakcf A B s :
  A |-cf s -> incl A B -> B |-cf s.
Proof.
  intros hcfs hincl.
  destruct Weak_mut as [ hcf hae ].
  apply (hcf A s hcfs B hincl).
Qed.

Lemma Weakae A B s :
  A |-ae s -> incl A B -> B |-ae s.
Proof.
  intros haes hincl.
  destruct Weak_mut as [ hcf hae ].
  apply (hae A s haes B hincl).
Qed.

(* Definition of the cut-free syntactic model *)

Definition cutfree_syntactic_model : WModel.
Proof.
  refine {|
    world := list form ;

    rel A B := incl A B ;
    bot_w A := A |-cf bot ;
    mu_w A x := A |-cf var x ;
  |}.
  - apply incl_refl.
  - apply incl_tran.
  - intros A B hincl hbot.
    apply Weakcf with (A := A).
    all: assumption.
  - intros A B x hincl hs.
    apply Weakcf with (A := A).
    all: assumption.
Defined.

(* Lemma 2 : Correctness *)

Lemma cutfree_correctness_mut A s :
     (winterp cutfree_syntactic_model A s -> A |-cf s)
  /\ (A |-ae s -> winterp cutfree_syntactic_model A s).
Proof.
  induction s as [ x | | s1 IHs1 s2 IHs2 ] in A |- *; simpl; split.
  1,3: trivial.
  1,2: intros haes. 1,2: now apply cf_frae.
  - intros h. apply cf_intr. apply IHs2. apply h.
    + apply incl_tl. apply incl_refl.
    + apply IHs1. apply ae_assm. firstorder.
  - intros haes A' hincl hi. apply IHs2. apply ae_elim with (s := s1).
    + apply Weakae with (A := A). all: assumption.
    + apply IHs1. apply hi.
Qed.

Lemma cutfree_correctness_cf A s :
  winterp cutfree_syntactic_model A s -> A |-cf s.
Proof.
  intros hi.
  destruct (cutfree_correctness_mut A s) as [ hcf hae ].
  apply (hcf hi).
Qed.

Lemma cutfree_correctness_ae A s :
  A |-ae s -> winterp cutfree_syntactic_model A s.
Proof.
  intros haes.
  destruct (cutfree_correctness_mut A s) as [ hcf hae ].
  apply (hae haes).
Qed.

(* Lemma 3 *)

Lemma cutfree_completeness_id A :
  ctx_winterp cutfree_syntactic_model A A.
Proof.
  induction A as [ | s A IHA ]; simpl.
  all: split.
  - apply cutfree_correctness_ae. apply ae_assm. firstorder.
  - apply ctx_monotonicity with (w := A); simpl.
    + apply incl_tl. apply incl_refl.
    + apply IHA.
Qed.

(* Theorem 4 : Cut elimination *)

Theorem cut_elimination A s :
  (forall M w, ctx_winterp M w A -> winterp M w s) -> A |-cf s.
Proof.
  intros h.
  apply cutfree_correctness_cf.
  apply h.
  apply cutfree_completeness_id.
Qed.

(* Lemma 5 *)

Lemma cutfree_consistency s :
  ~ ([] |-ae s).
Proof.
  intros hs.
  remember [] as A.
  induction hs as [ A s t hst IHst hs | A s hs ]; subst.
  - apply IHst. reflexivity.
  - contradiction.
Qed.

(* Lemma 6 *)

Fixpoint apply (A : list form) (s : form) : form :=
  match A with
  | [] => s
  | t :: A' => t ~> apply A' s
  end.

Lemma no_dne_apply A :
  let s := var 0 in
  ~ ([ neg (neg s) ] |-ae apply A s).
Proof.
  intros s hs.
  remember [ neg (neg s) ] as B.
  remember (apply A s) as f eqn:e.
  generalize dependent A.
  induction hs as [ B s1 s2 hst IHst hs | B s1 hs ]; subst.
  all: intros A e.
  all: subst; simpl in *.
  - apply IHst with (A := s1 :: A); simpl.
    all: reflexivity.
  - destruct hs as [ h | bot ].
    2: contradiction.
    destruct A as [ | t A ]; simpl in *.
    1: discriminate.
    destruct A as [ | u A ]; simpl in *.
    + discriminate.
    + discriminate.
Qed.

(* Theorem 7 *)

Theorem no_dne :
  ~ (forall s, [] |-m neg (neg s) ~> s).
Proof.
  intros hs.
  specialize (hs (var 0)).

  assert (hi : winterp cutfree_syntactic_model [] (neg (neg (var 0)) ~> var 0)).
  {
    eapply wsoundness.
    - apply hs.
    - apply cutfree_completeness_id.
  }

  assert (hcfs : [] |-cf neg (neg (var 0)) ~> var 0).
  { apply cutfree_correctness_cf. apply hi. }

  clear hs hi.

  remember [] as A.
  remember (neg (neg (var 0)) ~> var 0) as f eqn:e.

  destruct hcfs as [ A s t hst | A s hs ]; subst.
  + inversion e. subst.
    inversion hst. subst.
    apply no_dne_apply with (A := []).
    simpl. assumption.
  + eapply cutfree_consistency. apply hs.
Qed.