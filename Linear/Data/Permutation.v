Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Set Implicit Arguments.

Hint Constructors Permutation.

(* Decomposition Lemmas *)

Lemma permute_exists_mid : forall (A : Type) (x : A) (xs ys us : list A),
    Permutation (xs ++ x :: ys) us ->
    exists vs ws, vs ++ x :: ws = us /\
                  Permutation (xs ++ ys) (vs ++ ws).
Proof.
  intros A x xs ys us H1. remember (xs ++ x :: ys) as H2.
  generalize dependent ys. generalize dependent xs.
  induction H1 using Permutation_ind_bis; intros xs ys H2; subst.
  - exfalso. eapply app_cons_not_nil. eauto.
  - apply cons_eq_app in H2 as [[zs [H3 H4]] | [H3 H4]]; subst.
    + destruct (IHPermutation zs ys eq_refl) as [vs [ws [H5 H6]]]; subst.
      exists (x0 :: vs), ws. simpl. eauto.
    + exists nil, l'. inversion H4. eauto.
  - apply  cons_eq_app in H2 as [[zs [H3 H4]] | [H3 H4]]; subst.
    + apply cons_eq_app in H4 as [[qs [H5 H6]] | [H5 H6]]; subst.
      * destruct (IHPermutation qs ys eq_refl) as [vs [ws [H7 H8]]]; subst.
        exists (x0 :: y :: vs), ws. simpl. eauto.
      * exists nil, (y :: l'). inversion H6. simpl. eauto.
    + exists (x0 :: nil), l'. inversion H4. simpl. eauto.
  - destruct (IHPermutation1 xs ys eq_refl) as [qs [us [H3 H4]]]; subst.
    destruct (IHPermutation2 qs us eq_refl) as [vs [ws [H5 H6]]]; subst. eauto.
Qed.

Lemma permute_exists_cons : forall (A : Type) (x : A) (xs ys : list A),
    Permutation (x :: xs) ys ->
    exists vs ws, vs ++ x :: ws = ys /\
                  Permutation xs (vs ++ ws).
Proof.
  intros A x xs ys H1. rewrite_env (nil ++ x :: xs) in H1.
  destruct (permute_exists_mid _ _ _ H1) as [vs [ws [H2 H3]]].
  subst. exists vs, ws. simpl in H3. intuition.
Qed.    

(* Permutation Properties *)

Lemma dom_permute : forall (A : Type) (E1 E2 : list (atom * A)),
    Permutation E1 E2 ->
    dom E1 [=] dom E2.
Proof.
  intros A E1 E2 H1; induction H1;
    try destruct x as [x1 T1];
    try destruct y as [x2 T2];
    try solve [simpl; fsetdec].
Qed.

Lemma notin_permute : forall (A : Type) (x1 : atom) (E1 E2 : list (atom * A)),
    Permutation E1 E2 ->
    x1 `notin` dom E1 ->
    x1 `notin` dom E2.
Proof.
  intros A x1 E1 E2 H1 H2; induction H1;
    try destruct x as [y1 T1];
    try destruct y as [y2 T2];
    try solve [simpl in *; fsetdec].
Qed.

Lemma uniq_permute : forall (A : Type) (E1 E2 : list (atom * A)),
    Permutation E1 E2 ->
    uniq E1 ->
    uniq E2.
Proof.
  intros A E1 E2 H1 H2; induction H1;
    try destruct x as [x1 T1];
    try destruct y as [x2 T2]; auto.
  - pose proof (dom_permute H1). solve_uniq.
  - solve_uniq.
Qed.

Lemma disjoint_permute : forall {A : Type} (E1 E2 E3 : list (atom * A)),
    Permutation E1 E2 ->
    disjoint E1 E3 ->
    disjoint E2 E3.
Proof.
  unfold disjoint. intros A E1 E2 E3 H1 H2.
  rewrite (dom_permute H1) in H2. auto.
Qed.

Lemma binds_permute : forall A (E1 E2 : list (atom * A)) x1 T1,
    Permutation E1 E2 ->
    binds x1 T1 E1 ->
    binds x1 T1 E2.
Proof.
  intros A E1 E2 x1 T1 H1 H2.
  induction H1 as [| [x2 T2] | [x2 T2] [x3 T3] |]; auto.
  - analyze_binds H2.
  - analyze_binds H2.
Qed.

Hint Resolve dom_permute      : permutation.
Hint Resolve notin_permute    : permutation.
Hint Resolve uniq_permute     : permutation.
Hint Resolve disjoint_permute : permutation.
