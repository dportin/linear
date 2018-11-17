Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Linear.Language.

Set Implicit Arguments.

(* Metalib Tactics *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{x}}) in
  let C := gather_atoms_with (fun x : cont => dom x) in
  let D := gather_atoms_with (fun x : term => free_vars x) in
  constr:(A `union` B `union` C `union` D).

(* Substitution *)

Fixpoint subst e1 x1 v1 : term :=
  match e1 with
  | term_bvar n1       => term_bvar n1
  | term_fvar x2       => if x1 == x2 then v1 else term_fvar x2
  | term_bval q1 b1    => term_bval q1 b1
  | term_cond e1 e2 e3 => term_cond (subst e1 x1 v1) (subst e2 x1 v1) (subst e3 x1 v1)
  | term_abs q1 T1 e1  => term_abs q1 T1 (subst e1 x1 v1)
  | term_app e1 e2     => term_app (subst e1 x1 v1) (subst e2 x1 v1)
  end.

Notation "[ x1 ~> v1 ] e1" := (subst e1 x1 v1) (at level 68, right associativity).

(* Properties of Variable Opening and Substitution *)

Ltac destruct_eq_decs :=
  repeat (simpl in *; auto;
          match goal with
          | [ _ : context [ eq_dec ?A ?B ] |- _ ] =>
            destruct (eq_dec A B); subst
          | [ |- context [eq_dec ?A ?B] ]         =>
            destruct (eq_dec A B); subst
          end).

Lemma subst_fresh : forall x1 v1 e1,
    x1 `notin` free_vars e1 ->
    [x1 ~> v1] e1 = e1.
Proof.
  intros x1 v1 e1 H1; induction e1; simpl;
  try solve [f_equal; destruct_eq_decs].
  - destruct_eq_decs; fsetdec.
Qed.

Lemma subst_open_intro : forall x1 v1 e1,
    x1 `notin` free_vars e1 ->
    e1 ^^ v1 = [x1 ~> v1] e1 ^^ x1.
Proof.
  unfold open; intros x1 v1 e1; generalize 0.
  induction e1; simpl; intros n1 H1;
    try solve [f_equal; auto].
  - destruct_eq_decs. fsetdec.
  - destruct_eq_decs. fsetdec.
Qed.

Lemma open_rec_lc_core : forall e1 v1 v2 n1 n2,
    n1 <> n2 ->
    {n1 ~> v1} ({n2 ~> v2} e1) = {n2 ~> v2} e1 ->
    {n1 ~> v1} e1 = e1.
Proof.
  induction e1; simpl; intros v1 v2 n1 n2 H1 H2;
  try solve [inversion H2; f_equal; eauto].
  - destruct_eq_decs. congruence.
Qed.

Lemma free_vars_notin_open : forall e1 v1 x1 n,
    x1 `notin` free_vars v1 ->
    x1 `notin` free_vars e1 ->
    x1 `notin` free_vars ({n ~> v1} e1).
Proof.
  induction e1; simpl; intros v1 x1 m H1 H2; eauto.
  destruct (m == n); eauto.
Qed.

(* Locally Closed Terms *)

Inductive locally_closed : term -> Prop :=
  | lc_fvar : forall x1,
      locally_closed (term_fvar x1)
  | lc_bval : forall q1 b1,
      locally_closed (term_bval q1 b1)
  | lc_cond : forall e1 e2 e3,
      locally_closed e1 ->
      locally_closed e2 ->
      locally_closed e3 ->
      locally_closed (term_cond e1 e2 e3)
  | lc_abs : forall A1 q1 T1 e1,
      (forall x1, x1 `notin` A1 ->
                  locally_closed (e1 ^^ x1)) ->
      locally_closed (term_abs q1 T1 e1)
  | lc_app : forall e1 e2,
      locally_closed e1 ->
      locally_closed e2 ->
      locally_closed (term_app e1 e2).

Hint Constructors locally_closed.

(* Properties of Locally Closed Terms *)

Lemma open_rec_lc : forall e1 n1 v1,
    locally_closed e1 ->
    {n1 ~> v1} e1 = e1.
Proof.
  intros e1 n1 v1 H1. generalize dependent n1.
  induction H1; intros n1; simpl; f_equal; eauto.
  - pick fresh z1.
    eapply open_rec_lc_core with (n2 := 0); eauto.
Qed.

Lemma open_rec_subst : forall e1 x1 v1 v2 n1,
    locally_closed v2 ->
    [x1 ~> v2] ({n1 ~> v1} e1) = {n1 ~> [x1 ~> v2] v1} ([x1 ~> v2] e1).
Proof.
  induction e1; simpl; intros x1 v1 v2 n1 H1;
  f_equal; destruct_eq_decs.
  - erewrite open_rec_lc; eauto.
Qed.

Lemma subst_open_var : forall e1 x1 x2 v1,
    x1 <> x2 ->
    locally_closed v1 ->
    ([x2 ~> v1] e1) ^^ x1 = [x2 ~> v1] (e1 ^^ x1).
Proof.
  intros e1 x1 x2 v1 H1 H2. unfold open.
  rewrite open_rec_subst; auto.
  destruct_eq_decs. congruence.
Qed.

Lemma subst_preserves_lc : forall e1 x1 v1,
    locally_closed e1 ->
    locally_closed v1 ->
    locally_closed ([x1 ~> v1] e1).
Proof.
  intros e1 x1 v1 H1 H2; induction H1;
  simpl; eauto; try solve [destruct_eq_decs; eauto].
  - pick fresh z1 and apply lc_abs; intros; eauto.
    erewrite subst_open_var; eauto.
Qed.

Lemma typing_lc : forall U1 L1 e1 T1,
    typing U1 L1 e1 T1 -> locally_closed e1.
Proof.
  intros U1 L1 e1 T1 H1. induction H1; eauto.
Qed.

Lemma open_notin_free : forall e1 x1 v1 n,
    x1 `notin` free_vars ({n ~> v1} e1) ->
    x1 `notin` free_vars e1.
Proof.
  induction e1; simpl; intros; eauto.
Qed.

