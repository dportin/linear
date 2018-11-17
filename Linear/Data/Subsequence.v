Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.

Set Implicit Arguments.

Inductive subsequence {A : Type} : list A -> list A -> Prop :=
  | subseq_base : forall ys,
      subsequence nil ys
  | subseq_cons : forall y xs ys,
      subsequence xs ys ->
      subsequence xs (y :: ys)
  | subseq_both : forall x xs ys,
      subsequence xs ys ->
      subsequence (x :: xs) (x :: ys).

Hint Constructors subsequence.

Lemma subseq_refl : forall A (xs : list A),
    subsequence xs xs.
Proof.
  induction xs; auto.
Qed.

Lemma subseq_weaken_left : forall A (us xs zs : list A),
    subsequence xs zs ->
    subsequence xs (us ++ zs).
Proof.
  induction us; simpl; auto.
Qed.

Lemma subseq_weaken_right : forall A (us xs ys : list A),
    subsequence xs ys ->
    subsequence xs (ys ++ us).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma subseq_reduce_left_cons : forall A (x : A) (xs ys : list A),
    subsequence (x :: xs) ys ->
    subsequence xs ys.
Proof.
  intros A x xs ys H1. dependent induction H1; eauto.
Qed.

Lemma subseq_reduce_left : forall A (us xs ys : list A),
    subsequence (us ++ xs) ys ->
    subsequence xs ys.
Proof.
  induction us; eauto using subseq_reduce_left_cons.
Qed.

Lemma subseq_reduce_both : forall A (x y : A) (xs ys : list A),
    subsequence (x :: xs) (y :: ys) ->
    subsequence xs ys.
Proof.
  inversion 1; eauto using subseq_reduce_left_cons.
Qed.

Lemma subseq_dom : forall A (x1 : atom) (E1 E2 : list (atom * A)),
    x1 `notin` dom E2 ->
    subsequence E1 E2 ->
    x1 `notin` dom E1.
Proof.
  intros A x1 E1 E2 H1 H2; induction H2;
    try destruct x as [x2 T2];
    try destruct y as [x3 T3];
    try solve [solve_uniq].
Qed.

Lemma subseq_uniq : forall A (E1 E2 : list (atom * A)),
    uniq E2 ->
    subsequence E1 E2 ->
    uniq E1.
Proof.
  intros A E1 E2 H1 H2; induction H2;
    try destruct x as [x2 T2];
    try destruct y as [x3 T3];
    try solve [solve_uniq].
  - inversion H1; eauto using subseq_dom.
Qed.

Lemma subseq_binds : forall A (E1 E2 : list (atom * A)),
    (* uniq E2 -> *)
    subsequence E1 E2 ->
    (forall x1 T1, binds x1 T1 E1 -> binds x1 T1 E2).
Proof.
  intros A E1 E2 H1 x1 T1 H2.
  induction H1 as [| [x2 T2] | [x2 T2]]; auto.
  - analyze_binds H2.
  - analyze_binds H2.
Qed.

Lemma subseq_reduce_notin : forall A (x1 : atom) (T1 : A) (E1 E2 : list (atom * A)),
    x1 `notin` dom E1 ->
    subsequence E1 ((x1 ~ T1) ++ E2) ->
    subsequence E1 E2.
Proof.
  induction E1; intros E2 H1 H2; eauto;
    try destruct a as [x2 T2].
  - assert (D1 : x1 <> x2) by solve_uniq.
    inversion H2; subst; intuition.
Qed.

Lemma subseq_remove_left_notin : forall A (x1 : atom) (T1 : A) (E1 F2 : list (atom * A)),
    x1 `notin` dom E1 ->
    subsequence E1 ((x1 ~ T1) ++ F2) ->
    subsequence E1 F2.
Proof.
  intros A x1 T1 E1 F2 H1 H2.
  dependent induction H2; simpl; eauto.
  - simpl in H1. solve_uniq.
Qed.

Lemma subseq_remove_mid_notin : forall A (x1 : atom) (T1 : A) (E1 F1 F2 : list (atom * A)),
    x1 `notin` dom E1 ->
    subsequence E1 (F1 ++ (x1 ~ T1) ++ F2) ->
    subsequence E1 (F1 ++ F2).
Proof.
  intros A x1 T1 E1 F1.
  generalize dependent E1.
  dependent induction F1;
    intros E1 E2 H1 H2;
    try destruct a as [x2 T2].
  - eapply subseq_remove_left_notin; eauto.
  - inversion H2; subst; simpl; eauto.
Qed.

Lemma subseq_notin_reverse : forall A (x1 : atom) (E1 E2 : list (atom * A)),
    x1 `notin` dom E2 ->
    subsequence E1 E2 ->
    x1 `notin` dom E1.
Proof.
  intros A x1 E1 E2 H1 H2; induction H2;
  try destruct x as [x2 T2];
  try destruct y as [x3 T3]; eauto.
Qed.

Lemma subseq_invert_cons : forall A (x1 x2 : atom) (T1 T2 : A) (E1 E2 : list (atom * A)),
    x1 `notin` dom E2 ->
    subsequence ((x1 ~ T1) ++ E1) ((x2 ~ T2) ++ E2) ->
    x1 = x2 /\ T1 = T2.
Proof.
  intros A x1 x2 T1 T2 E1 E2 H1 H2.
  dependent induction H2; eauto.
  - pose proof (subseq_notin_reverse H1 H2).
    simpl in H. solve_uniq.
Qed.

Lemma subseq_cons_mid : forall A (u : A) (xs ys vs us : list A),
    subsequence (xs ++ ys) (vs ++ us) ->
    subsequence (xs ++ ys) (vs ++ u :: us).
Proof.
  intros A u xs ys vs us H1. dependent induction H1.
  - apply nil_eq_app in x as [? ?]. subst. constructor.
  - apply cons_eq_app in x as [[zs [? ?]] | [? ?]]; subst; simpl; eauto.
  - apply cons_eq_app in x1 as [[ws [? ?]] | [? ?]]; subst; simpl;
    apply cons_eq_app in x as [[zs [? ?]] | [? ?]]; subst; simpl; eauto.
    + apply subseq_both. rewrite_env (nil ++ xs0). eauto.
Qed.



Lemma subseq_trans : forall A (xs ys zs : list A),
    subsequence xs ys ->
    subsequence ys zs ->
    subsequence xs zs.
Proof.
  intros A xs ys zs H1 H2.
  generalize dependent ys.
  generalize dependent xs.
  induction zs; intros xs ys H1 H2; eauto.
  - inversion H2; subst; eauto.
  - inversion H1; subst; eauto.
    + apply subseq_reduce_both in H2. eauto.
    + inversion H2; subst; eauto.
Qed.

Lemma uniq_subseq_app : forall A (E1 E2 E3 : list (atom * A)),
    subsequence E1 E2 ->
    uniq E1 ->
    uniq (E3 ++ E2) ->
    uniq (E3 ++ E1).
Proof.
  intros A E1 E2 E3 H1 H2 H3.
  induction H1 as [| [x1 T1] | [x1 T1]]; simpl_env.
  - solve_uniq.
  - eapply IHsubsequence; solve_uniq.
  - apply uniq_insert_mid.
    + assert (H4 : uniq ys) by solve_uniq.
      pose proof (subseq_uniq H4 H1) as H5.
      apply IHsubsequence; solve_uniq.
    + solve_uniq.
    + solve_uniq.
Qed.

Lemma subseq_length : forall {A : Type} (xs ys : list A),
    subsequence xs ys ->
    length xs <= length ys.
Proof.
  intros A xs ys H1.
  induction H1; simpl; auto with arith.
Qed.

Lemma permute_subseq_equal : forall A (E1 E2 : list (atom * A)),
    Permutation E1 E2 ->
    subsequence E1 E2 ->
    E1 = E2.
Proof.
  intros A E1 E2 H1 H2; induction H2;
    try destruct x as [x1 T1];
    try destruct y as [x2 T2].
  - rewrite (Permutation_nil H1). reflexivity.
  - apply Permutation_length in H1. simpl in H1.
    apply subseq_length in H2. rewrite H1 in H2.
    exfalso. eapply Nat.nle_succ_diag_l. eauto.
  - apply Permutation_cons_inv in H1.
    f_equal. apply IHsubsequence; assumption.
Qed.

Lemma subseq_app_head : forall A (xs ys us vs : list A),
    subsequence xs ys ->
    subsequence us vs ->
    subsequence (xs ++ us) (ys ++ vs).
Proof.
  intros A xs ys us vs H1 H2.
  dependent induction H1 generalizing us vs; simpl; auto.
  - apply subseq_weaken_left; auto.
Qed.
