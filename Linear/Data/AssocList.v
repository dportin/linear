Require Import Metalib.Metatheory.
Require Import Linear.Data.Subsequence.

Set Implicit Arguments.

(* Remove Operation *)

Fixpoint assoc_remove {A : Type} (x1 : atom) (E1 : list (atom * A)) : list (atom * A) :=
  match E1 with
  | nil            => nil
  | (x2, T2) :: E1 => if x1 == x2
                      then assoc_remove x1 E1
                      else (x2, T2) :: assoc_remove x1 E1
  end.

Lemma assoc_remove_notin : forall {A : Type} (E1 : list (atom * A)) x1,
    x1 `notin` dom E1 ->
    assoc_remove x1 E1 = E1.
Proof.
  induction E1 as [| [x2 v2] E1 IH]; intros x1 H1; simpl; auto.
  destruct (x1 == x2) as [| H2]; subst; analyze_binds H1.
  rewrite IH; auto.
Qed.

Lemma assoc_remove_dom_neq : forall {A : Type} (E1 : list (atom * A)) x1 x2,
    x1 `notin` dom E1 ->
    x1 `notin` dom (assoc_remove x2 E1).
Proof.
  induction E1 as [| [x3 v3] E1 IH]; intros x1 x2 H1; simpl; auto.
  destruct (x2 == x3) as [| H2]; subst; simpl in *; eauto.
Qed.

Lemma assoc_remove_uniq : forall {A : Type} (E1 : list (atom * A)) x1,
    uniq E1 ->
    uniq (assoc_remove x1 E1).
Proof.
  induction 1 as [| x2 T2]; simpl; auto.
  destruct (x1 == x2); subst; auto.
  constructor; eauto using assoc_remove_dom_neq.
Qed.

Lemma subseq_assoc_remove : forall A x1 (E1 E2 : list (atom * A)),
    subsequence E1 E2 ->
    subsequence (assoc_remove x1 E1) E2.
Proof.
  induction 1 as [| | [x2 P2]]; simpl; eauto.
  destruct (x1 == x2); subst; eauto.
Qed.

Lemma assoc_remove_notin_eq : forall A (E1 : list (atom * A)) x1,
    x1 `notin` dom (assoc_remove x1 E1).
Proof.
  induction E1 as [| [x2 T2] E1 IH]; intros x1; simpl; auto.
  - destruct (x1 == x2); subst; auto.
Qed.

Lemma assoc_remove_swap_cons : forall A (E1 E2 : list (atom * A)) x1 T1,
    x1 `notin` dom E1 ->
    (x1, T1) :: E1 = E2 ->
    E1 = assoc_remove x1 E2.
Proof.
  intros A E1 E2 x1 T1 H1 H2.
  destruct E2 as [| [x2 T2] E2].
  - discriminate.
  - inversion H2; subst; simpl.
    destruct (x2 == x2); [| congruence].
    rewrite (assoc_remove_notin _ H1). auto.
Qed.                                         

Lemma assoc_remove_notin_inv : forall A (E1 : list (atom * A)) x1 x2,
    x1 `notin` dom (assoc_remove x2 E1) ->
    x1 = x2 \/ x1 `notin` dom E1.
Proof.
  induction E1 as [| [x3 T3] E1 IH]; simpl; intros x1 x2 H1; auto.
  destruct (x2 == x3); subst.
  - destruct (x1 == x3) as [| H2]; subst; auto.
    apply IH in H1 as [? | H3]; subst; auto.
  - simpl in H1. pose proof (notin_add_2 _ _ _ H1) as H2.
    apply IH in H2 as [| H3]; subst; auto.
Qed.

Lemma assoc_remove_binds : forall A (E1 : list (atom * A)) x1 x2 T1,
    binds x1 T1 (assoc_remove x2 E1) ->
    x1 <> x2 /\ binds x1 T1 E1.
Proof.
  induction E1 as [| [x3 T3] E1 IH]; simpl; intros x1 x2 T1 H1; auto.
  destruct (x2 == x3) as [| H2]; subst.
  - apply IH in H1 as [H2 H3]; auto.
  - analyze_binds H1.
    apply IH in BindsTac as [H3 H4]; auto.
Qed.
     
Lemma assoc_remove_subseq_both : forall A (E1 E2 : list (atom * A)) x1,
    subsequence E1 E2 ->
    subsequence (assoc_remove x1 E1) (assoc_remove x1 E2).
Proof.
  intros A E1 E2 x1 H1.
  induction H1 as [| [x2 T2] | [x2 T2]]; simpl; auto.
  - destruct (x1 == x2); subst; auto.
  - destruct (x1 == x2); subst; auto.
Qed.

Lemma assoc_remove_subseq_left : forall A (E1 E2 : list (atom * A)) x1,
    subsequence E1 E2 ->
    subsequence (assoc_remove x1 E1) E2.
Proof.
  induction 1 as [| [x2 T2] | [x2 T2]]; simpl; auto.
  - destruct (x1 == x2); subst; auto.
Qed.  

Lemma assoc_remove_cons_eq : forall A (E1 : list (atom * A)) x1 T1,
    x1 `notin` dom E1 ->
    assoc_remove x1 ((x1 ~ T1) ++ E1) = E1.
Proof.
  intros A E1 x1 T1 H1.
  induction E1 as [| [x2 T2] E1 IH]; simpl in *.
  - destruct (x1 == x1); subst; congruence.
  - destruct (x1 == x1); subst; try congruence.
    destruct (x1 == x2); subst.
    + analyze_binds H1.
    + f_equal. auto.
Qed.

Lemma assoc_remove_mid_eq : forall A (E1 E2 : list (atom * A)) x1 T1,
    x1 `notin` dom (E1 ++ E2) ->
    assoc_remove x1 (E1 ++ (x1, T1) :: E2) = E1 ++ E2.
Proof.
  intros A E1 E2 x1 T1 H1.
  induction E1 as [| [x2 T2] E1 IH]; simpl in *.
  - destruct (x1 == x1); [subst | congruence].
    apply (assoc_remove_notin _ H1).
  - destruct (x1 == x2); [subst |].
    + analyze_binds H1.
    + f_equal. auto.
Qed.

(* Submap Relation *)

Definition submap {A : Type} (A1 A2 : list (var * A)) : Prop :=
  forall x1 y1, binds x1 y1 A1 -> binds x1 y1 A2.

Hint Unfold submap.

Lemma submap_nil : forall {A : Type} (E1 : list (atom * A)),
    submap E1 nil ->
    E1 = nil.
Proof.
  intros A [| [x1 v1] E1] H1; auto.
  - exfalso. eapply H1. eauto.
Qed.

Lemma submap_cons : forall {A : Type} (E1 E2 : list (atom * A)) x1 v1,
    submap E1 E2 ->
    submap ((x1 ~ v1) ++ E1) ((x1 ~ v1) ++ E2).
Proof.
  intros A E1 E2 x1 v1 H1 x2 v2 H2. analyze_binds H2.
Qed.

Lemma submap_trans : forall {A : Type} (E1 E2 E3 : list (atom * A)),
    submap E1 E2 ->
    submap E2 E3 ->
    submap E1 E3.
Proof.
  auto.
Qed.

Lemma submap_notin : forall {A : Type} (E1 E2 : list (atom * A)) x1,
    submap E1 E2 ->
    x1 `notin` dom E2 ->
    x1 `notin` dom E1.
Proof.
  intros A E1 E2 x1 H1 H2.
  destruct (binds_lookup _ x1 E1) as [[v1 H3] | H3].
  - apply H1 in H3. eauto.
  - intros H4. apply binds_In_inv in H4 as [v1 H4]. apply H3 in H4. tauto.
Qed.

Lemma uniq_submap_app : forall {A : Type} (E1 E2 E3 : list (atom * A)),
    submap E1 E2 ->
    uniq E1 ->
    uniq (E3 ++ E2) ->
    uniq (E3 ++ E1).
Proof.
  intros A E1 E2 E3 H1 H2 H3.
  induction E3 as [| [x1 T1] E3 IH]; simpl; auto.
  inversion H3. subst. constructor; auto.
  rewrite dom_app. apply notin_union_3; eauto.
  rewrite dom_app in H6. apply notin_union_2 in H6.
  eapply submap_notin; eauto.
Qed.

Lemma submap_assoc_remove : forall {A : Type} (E1 : list (atom * A)) x1,
    submap (assoc_remove x1 E1) E1.
Proof.
  induction E1 as [| [x2 T2] E1 IH]; simpl; intros x1 x3 T3 H1; auto.
  destruct (x1 == x2); subst.
  - apply IH in H1. auto.
  - analyze_binds H1. apply IH in BindsTac. auto.
Qed.

Lemma subseq_submap : forall A (E1 E2 : list (atom * A)),
    subsequence E1 E2 ->
    submap E1 E2.
Proof.
  induction 1 as [| [x2 T2] | [x2 T2]]; intros x1 T1 H1.
  - analyze_binds H1.
  - eapply binds_cons_3, subseq_binds; eauto.
  - analyze_binds H1.
Qed.

(* List Difference Operation *)

Fixpoint diff_list {A : Type} (E1 E2 : list (atom * A)) : list (atom * A) :=
  match E2 with
  | nil            => E1
  | (x1, T1) :: E2 => assoc_remove x1 (diff_list E1 E2)
  end.

Ltac destruct_eq_decs :=
  repeat (simpl in *; auto;
          match goal with
          | [ _ : context [ eq_dec ?A ?B ] |- _ ] =>
            destruct (eq_dec A B); subst
          | [ |- context [eq_dec ?A ?B] ]         =>
            destruct (eq_dec A B); subst
          end).

Lemma assoc_remove_swap : forall A (E1 : list (atom * A)) x1 x2,
    assoc_remove x1 (assoc_remove x2 E1) = assoc_remove x2 (assoc_remove x1 E1).
Proof.
  induction E1 as [| [x3 T3] E1 IH]; intros;
    destruct_eq_decs; congruence.
Qed.

Lemma assoc_remove_diff_eq : forall A (E1 E2 : list (atom * A)) x1 T1,
    assoc_remove x1 (diff_list ((x1, T1) :: E1) E2) = assoc_remove x1 (diff_list E1 E2).
Proof.
  induction E2 as [| [x2 T2] E2 IH]; intros x1 T1;
    destruct_eq_decs; simpl; try congruence.
  - rewrite assoc_remove_swap, IH, assoc_remove_swap. auto.
Qed.  

Lemma assoc_remove_diff_neq : forall A (E1 E2 : list (atom * A)) x1 x2 T1,
    x1 <> x2 ->
    x1 `notin` dom E2 ->
    assoc_remove x2 (diff_list ((x1, T1) :: E1) E2) = (x1, T1) :: assoc_remove x2 (diff_list E1 E2).
Proof.
  induction E2 as [| [x3 T3] E2 IH]; intros x1 x2 T1 H1 H2;
    destruct_eq_decs; simpl; try congruence.
  - rewrite IH; auto. destruct_eq_decs. congruence.
Qed.  

Lemma diff_list_nil : forall A (E1 : list (atom * A)),
    diff_list E1 E1 = nil.
Proof.
  induction E1 as [| [x1 T1] E1 IH]; auto.
  - simpl. rewrite assoc_remove_diff_eq, IH. auto.
Qed.

Lemma diff_list_equate_cons : forall A (E1 : list (atom * A)) x1 T1,
    x1 `notin` dom E1 ->
    diff_list ((x1, T1) :: E1) E1 = (x1 ~ T1).
Proof.
  destruct E1 as [| [x2 T2] E1]; intros x1 T1 H1; simpl; auto.
  - rewrite assoc_remove_diff_neq; auto.
    rewrite assoc_remove_diff_eq, diff_list_nil; auto.
Qed.

Lemma diff_list_equate_mid : forall A (E1 E2 : list (atom * A)) x1 T1,
    x1 `notin` dom (E1 ++ E2) ->
    diff_list (E1 ++ (x1, T1) :: E2) (E1 ++ E2) = (x1 ~ T1).
Proof.
  induction E1 as [| [x2 T2] E1 IH]; intros E2 x1 T1 H1; simpl. 
  - rewrite diff_list_equate_cons; auto.
  - rewrite assoc_remove_diff_eq, IH; destruct_eq_decs. fsetdec.
Qed.  

Lemma diff_list_notin_cons : forall A (E1 E2 : list (atom * A)) x1 T1,
    x1 `notin` dom E2 ->
    diff_list ((x1, T1) :: E1) E2 = (x1, T1) :: diff_list E1 E2.
Proof.
  intros A E1 E2 x1 T1 H1.
  induction E2 as [| [x2 T2] E2 IH]; simpl; auto.
  rewrite assoc_remove_diff_neq; auto.
Qed.

Lemma diff_list_notin_left : forall A (E1 E2 : list (atom * A)) x1,
    x1 `notin` dom E1 ->
    x1 `notin` dom (diff_list E1 E2).
Proof.
  intros A E1 E2 x1 H1.
  induction E2 as [| [x2 T2] E2 IH]; simpl; auto.
  - apply assoc_remove_dom_neq. auto.
Qed.

Lemma diff_list_nil_left : forall A (E1 : list (atom * A)),
    diff_list nil E1 = nil.
Proof.
  induction E1 as [| [x1 T1] E1 IH]; simpl; auto.
  - rewrite IH; auto.
Qed.

Lemma diff_list_subseq_nil : forall A (E1 E2 : list (atom * A)),
    subsequence E1 E2 ->
    diff_list E1 E2 = nil.
Proof.
  induction 1 as [| [x1 T1] | [x1 T1]]; simpl; auto.
  - apply diff_list_nil_left.
  - rewrite IHsubsequence; auto.
  - rewrite assoc_remove_diff_eq, IHsubsequence; auto.
Qed.

Lemma diff_list_binds_cons : forall A (E1 E2 : list (atom * A)) x1 T1,
    x1 `in` dom E2 ->
    diff_list ((x1, T1) :: E1) E2 = diff_list E1 E2.
Proof.
  induction E2 as [| [x2 T2] E2 IH]; simpl; intros x1 T1 H1.
  - fsetdec.
  - apply add_iff in H1 as [H1 | H1]; subst.
    + rewrite assoc_remove_diff_eq. auto.
    + rewrite (IH x1 T1 H1). auto.
Qed.

Lemma diff_list_notin_remove : forall A (E1 E2 : list (atom * A)) x1,
    x1 `notin` dom E1 ->
    diff_list E1 (assoc_remove x1 E2) = diff_list E1 E2.
Proof.
  induction E2 as [| [x2 T2] E2 IH]; simpl; intros x1 H1; auto.
  - destruct (x1 == x2) as [| H2]; subst; simpl.
    + rewrite IH, assoc_remove_notin; auto.
      apply diff_list_notin_left; auto.
    + rewrite IH; auto.
Qed.

Lemma diff_list_subseq : forall A (E1 E2 : list (atom * A)),
    subsequence (diff_list E1 E2) E1.
Proof.
  induction E2 as [| [x2 T2] E2 IH]; simpl; auto.
  - apply subseq_refl.
  - apply assoc_remove_subseq_left, IH.
Qed.

Lemma notin_dec : forall A (E1 : list (atom * A)) x1,
    x1 `notin` dom E1 \/ exists T1, binds x1 T1 E1.
Proof.
  induction E1 as [| [x2 T2] E1 IH]; intros x1; auto.
  destruct (x1 == x2) as [| H1]; subst.
  - right. exists T2. auto.
  - destruct (IH x1) as [H2 | [T1 H2]].
    + left. auto. 
    + right. exists T1. auto.
Qed.

Lemma subseq_diff_left : forall A (E1 E2 E3 : list (atom * A)),
    subsequence E1 E3 ->
    subsequence (diff_list E1 E2) E3.
Proof.
  induction 1 as [| [x1 T1] | [x1 T1]]; simpl; auto.
  - rewrite diff_list_nil_left. auto.
  - destruct (notin_dec E2 x1) as [H1 | [T2 H1]].
    + rewrite diff_list_notin_cons; auto.
    + rewrite diff_list_binds_cons; eauto using binds_In.
Qed.  

Lemma diff_list_uniq : forall A (E1 E2 : list (atom * A)),
    uniq E1 ->
    uniq (diff_list E1 E2).
Proof.
  induction E2 as [| [x1 T1] E2 IH]; simpl; intros H1; auto.
  - apply assoc_remove_uniq. auto.
Qed.    

Lemma binds_assoc_remove : forall A (E1 : list (atom * A)) x1 x2 T1,
    x1 <> x2 ->
    binds x1 T1 E1 ->
    binds x1 T1 (assoc_remove x2 E1).
Proof.
  induction E1 as [| [x3 T3] E1 IH]; simpl; intros x1 x2 T1 H1 H2.
  - analyze_binds H2.
  - destruct (x2 == x3); subst; auto.
    + analyze_binds H2.
    + analyze_binds H2.
Qed.

Lemma diff_list_binds_spec : forall A (E1 E2 : list (atom * A)) x1 T1,
    binds x1 T1 (diff_list E1 E2) <-> binds x1 T1 E1 /\ x1 `notin` dom E2.
Proof.
  induction E2 as [| [x2 T2] E2 IH]; simpl; intros x1 T1.
  - split; [intros H1 | intros [H1 H2]]; auto.
  - split; [intros H1 | intros [H1 H2]].
    + apply assoc_remove_binds in H1 as [H1 H2].
      apply IH in H2 as [H2 H3]. split; auto.
    + apply binds_assoc_remove; auto. apply IH; auto.
Qed.

Lemma diff_list_notin_spec : forall A (E1 E2 : list (atom * A)) x1,
    x1 `notin` dom (diff_list E1 E2) <-> x1 `notin` dom E1 \/ x1 `in` dom E2.
Proof.
  induction E2 as [| [x2 T2] E2 IH]; simpl; intros x1.
  - split; [intros | intros [? | ?]]; auto. fsetdec.
  - split; [intros H1 | intros [H1 | H1]].
    + apply assoc_remove_notin_inv in H1 as [| H1]; auto.
      apply IH in H1 as [? | ?]; auto.
    + apply assoc_remove_dom_neq.
      apply (diff_list_notin_left _ _ H1).
    + apply add_iff in H1 as [? | H1]; subst.
      * apply assoc_remove_notin_eq.
      * apply assoc_remove_dom_neq, IH; auto.
Qed.

(* Decomposition Lemmas *)

Lemma binds_inv : forall {A : Type} (E1 : list (atom * A)) x1 T1,
    binds x1 T1 E1 ->
    exists E2 E3, E1 = E2 ++ (x1 ~ T1) ++ E3.
Proof.
  induction E1 as [| [x2 T2] E1 IH];
  intros x1 T1 H1; simpl; analyze_binds H1.
  - exists nil, E1. auto.
  - destruct (IH x1 T1 BindsTac) as [E4 [E5 H1]]. subst.
    exists ((x2, T2) :: E4), E5. auto.
Qed.

Lemma assoc_equate_uniq : forall A (E1 E2 F1 F2 : list (atom * A)) (x1 : atom) (v1 v2 : A),
    uniq (E1 ++ (x1 ~ v1) ++ E2) ->
    E1 ++ (x1 ~ v1) ++ E2 = F1 ++ (x1 ~ v2) ++ F2 ->
    E1 = F1 /\ v1 = v2 /\ E2 = F2.
Proof.
  induction E1 as [| [x3 v3] E1 IH];
  intros E2 F1 F2 x1 v1 v2 H1 H2;
  destruct F1 as [| [x4 v4] F1];
  try solve [inversion H2; solve_uniq].
  - rewrite H2 in H1. inversion H2. solve_uniq.
  - inversion H1. inversion H2. subst.
    destruct (IH _ _ _ _ _ _ H3 H9). solve_uniq.
Qed.

Lemma assoc_equate_split_uniq : forall A (E1 E2 F1 F2 : list (atom * A)) (x1 x2 : atom) (v1 v2 : A),
    x1 <> x2 ->
    uniq (E1 ++ (x1 ~ v1) ++ E2) ->
    E1 ++ (x1 ~ v1) ++ E2 = F1 ++ (x2 ~ v2) ++ F2 ->
    exists G1 G2, F1 = G1 ++ (x1 ~ v1) ++ G2 \/
                  F2 = G1 ++ (x1 ~ v1) ++ G2.
Proof.
  induction E1 as [| [x3 v3] E1 IH];
  intros E2 F1 F2 x1 x2 v1 v2 H1 H2 H3;
  destruct F1 as [| [x4 v4] F1];
  inversion H3; subst; simpl in *.
  - congruence.
  - exists nil, F1. intuition.
  - exists E1, E2. intuition.
  - apply uniq_cons_iff in H2 as [H6 H7].
    destruct (IH _ _ _ _ _ _ _ H1 H6 H5) as [G1 [G2 [H8 | H8]]]; subst.
    + exists ((x4 ~ v4) ++ G1), G2. intuition.
    + exists G1, G2. intuition.
Qed.
