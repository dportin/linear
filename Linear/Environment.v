Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Linear.Language.
Require Import Linear.Data.AssocList.
Require Import Linear.Data.Permutation.
Require Import Linear.Data.Subsequence.
Set Implicit Arguments.

(* Permutations of Contexts *)

Lemma qual_cont_exact_permute : forall q1 E1 E2,
    Permutation E1 E2 ->
    qual_cont_exact q1 E1 ->
    qual_cont_exact q1 E2.
Proof.
  intros q1 E1 E2 H1 H2.
  induction H1 as [| [x1 T1] | [x1 T1] [x2 T2] |]; auto.
  - inversion H2. constructor. auto.
  - inversion H2. inversion H1. repeat constructor; auto.
Qed.

Lemma well_formed_cont_permute_un : forall q1 U1 U2 L1,
    Permutation U1 U2 ->
    well_formed_cont q1 U1 L1 ->
    well_formed_cont q1 U2 L1.
Proof.
  intros q1 U1 U2 L1 H1 H2.
  inversion H2; constructor; subst;
    try solve [eapply uniq_permute; eauto];
    try solve [eapply qual_cont_exact_permute; eauto].  
  apply uniq_app_iff in H as [? [? ?]]; apply uniq_app_iff;
  intuition eauto using uniq_permute, disjoint_permute.
Qed.

Lemma well_formed_cont_permute_lin : forall q1 U1 L1 L2,
    Permutation L1 L2 ->
    well_formed_cont q1 U1 L1 ->
    well_formed_cont q1 U1 L2.
Proof.
  intros q1 U1 L1 L2 H1 H2. inversion H2; subst.
  - rewrite (Permutation_nil H1). auto. 
  - constructor; eauto using qual_cont_exact_permute.
    apply uniq_app_iff in H as [? [? ?]]; apply uniq_app_iff;
    intuition eauto using uniq_permute, disjoint_permute.
Qed.

Lemma split_cont_permute : forall L1 L2 L3 L4,
    Permutation L1 L4 ->
    split_cont L1 L2 L3 ->
    exists L5 L6, split_cont L4 L5 L6 /\
                  Permutation L2 L5 /\
                  Permutation L3 L6.
Proof.
  intros L1 L2 L3 L4 H1 H2.
  dependent induction H1 generalizing L2 L3;
    try destruct x as [x1 T1];
    try destruct y as [x2 T2].
  - inversion H2. subst. eauto.
  - inversion H2; subst.
    + apply IHPermutation in H7 as [L4 [L5 [? [? ?]]]].
      exists ((x1 ~ lin P1) ++ L4), L5.
      repeat (constructor; eauto with permutation).
    + apply IHPermutation in H7 as [L4 [L5 [? [? ?]]]].
      exists L4, ((x1 ~ lin P1) ++ L5).
      repeat (constructor; eauto with permutation).
  - inversion H2; inversion H6; subst.
    + exists ((x1 ~ lin P0) ++ (x2 ~ lin P1) ++ E4), L3.
      repeat (constructor; auto).
    + exists ((x2 ~ lin P1) ++ E2), ((x1 ~ lin P0) ++ E5).
      repeat (constructor; auto).
    + exists ((x1 ~ lin P0) ++ E4), ((x2 ~ lin P1) ++ E3).
      repeat (constructor; auto).
    + exists L2, ((x1 ~ lin P0) ++ (x2 ~ lin P1) ++ E5).
      repeat (constructor; auto).
  - apply IHPermutation1 in H2 as [L4 [L5 [H2 [? ?]]]].
    apply IHPermutation2 in H2 as [L6 [L7 [H2 [? ?]]]].
    exists L6, L7. eauto.
Qed.

(* Properties of Context Split Relation *)

Lemma split_cont_dom : forall L1 L2 L3,
    split_cont L1 L2 L3 ->
    dom L1 [=] dom L2 `union` dom L3.
Proof.
  induction 1; simpl; fsetdec.
Qed.

Lemma split_cont_notin : forall L1 L2 L3 x1,
    x1 `notin` dom L1 ->
    split_cont L1 L2 L3 ->
    x1 `notin` dom L2 /\ x1 `notin` dom L3.
Proof.
  intros L1 L2 L3 x1 H1 H2.
  pose proof (split_cont_dom H2) as H3. solve_uniq.
Qed.

Lemma split_cont_disjoint : forall L1 L2 L3,
    split_cont L1 L2 L3 ->
    disjoint L2 L3.
Proof.
  unfold disjoint. intros L1 L2 L3 H1. induction H1; simpl.
  - fsetdec.
  - pose proof (split_cont_dom H1) as H2. fsetdec.
  - pose proof (split_cont_dom H1) as H2. fsetdec.
Qed.

Lemma split_cont_uniq : forall L1 L2 L3,
    split_cont L1 L2 L3 ->
    uniq L1 /\ uniq L2 /\ uniq L3.
Proof.
  intros L1 L2 L3 H1. induction H1; auto.
  - pose proof (split_cont_notin H H1) as [H5 H6].
    repeat split; solve_uniq.
  - pose proof (split_cont_notin H H1) as [H5 H6].
    repeat split; solve_uniq.
Qed.

Lemma split_cont_exact_lin : forall L1 L2 L3,
    split_cont L1 L2 L3 ->
    qual_cont_exact L L1 /\ qual_cont_exact L L2 /\ qual_cont_exact L L3.
Proof.
  intros L1 L2 L3 H1. induction H1; intuition eauto.
Qed.

Lemma split_cont_comm : forall L1 L2 L3,
    split_cont L1 L2 L3 ->
    split_cont L1 L3 L2.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma split_cont_uniq_app_left : forall E1 L1 L2 L3,
    split_cont L1 L2 L3 ->
    uniq (E1 ++ L1) ->
    uniq (E1 ++ L2).
Proof.
  intros E1 L1 L2 L3 H1 H2.
  pose proof (split_cont_dom H1) as H3.
  pose proof (split_cont_uniq H1) as [H4 [H5 H6]].
  apply uniq_app_iff in H2 as [H7 [H8 H9]].
  apply uniq_app_iff. repeat split; solve_uniq.
Qed.

Lemma split_cont_uniq_app_right : forall E1 L1 L2 L3,
    split_cont L1 L2 L3 ->
    uniq (E1 ++ L1) ->
    uniq (E1 ++ L3).
Proof.
  intros E1 L1 L2 L3 H1 H2.
  apply split_cont_comm in H1.
  eapply split_cont_uniq_app_left; eauto.
Qed.

Lemma split_cont_assoc_left : forall E1 E2 E3 E4 E5,
    split_cont E1 E2 E3 ->
    split_cont E2 E4 E5 ->
    exists E6, split_cont E1 E4 E6 /\ split_cont E6 E5 E3.
Proof.
  intros E1 E2 E3 E4 E5 H1 H2.
  generalize dependent E5. generalize dependent E4.
  induction H1; intros E4 E5 H2.
  - inversion H2. subst. exists nil. auto.
  - inversion H2; subst.
    + destruct (IHsplit_cont E6 E5 H8) as [E7 [H4 H5]]. eauto.
    + destruct (IHsplit_cont E4 E7 H8) as [E8 [H6 H9]].
      pose proof (split_cont_notin H H6) as [H3 H4]. eauto.
  - destruct (IHsplit_cont E4 E5 H2) as [E6 [H3 H4]].
    pose proof (split_cont_notin H H3) as [H5 H6]. eauto.
Qed.

Lemma split_cont_assoc_right : forall E1 E2 E3 E4 E5,
    split_cont E1 E2 E3 ->
    split_cont E3 E4 E5 ->
    exists E6, split_cont E1 E6 E5 /\
               split_cont E6 E2 E4.
Proof.
  intros E1 E2 E3 E4 E5 H1 H2.
  apply split_cont_comm in H1.
  apply split_cont_comm in H2.
  destruct (split_cont_assoc_left H1 H2) as [F1 [H3 H4]].
  exists F1. eauto using split_cont_comm.
Qed.

Lemma split_cont_binds_left : forall L1 L2 L3 x1 T1,
    split_cont L1 L2 L3 ->
    binds x1 T1 L2 ->
    binds x1 T1 L1.
Proof.
  intros L1 L2 L3 x1 T1 H1 H2. induction H1; auto.
  pose proof (split_cont_uniq H1) as [? [? ?]].
  pose proof (split_cont_notin H H1) as [? ?].
  analyze_binds_uniq H2; auto.
Qed.

Lemma split_cont_binds_right : forall L1 L2 L3 x1 T1,
    split_cont L1 L2 L3 ->
    binds x1 T1 L3 ->
    binds x1 T1 L1.
Proof.
  intros L1 L2 L3 x1 T1 H1 H2.
  apply split_cont_comm in H1.
  eapply split_cont_binds_left; eauto.
Qed.

Lemma split_cont_nil_left : forall L1 L2,
    split_cont L1 nil L2 ->
    L1 = L2.
Proof.
  intros L1 L2 H1.
  dependent induction H1; auto.
  rewrite IHsplit_cont; auto.
Qed.

Lemma split_cont_nil_right : forall L1 L2,
    split_cont L1 L2 nil ->
    L1 = L2.
Proof.
  intros L1 L2 H1.
  apply split_cont_comm in H1.
  apply split_cont_nil_left; auto.
Qed.

Lemma split_cont_right_nil : forall L1,
    uniq L1 ->
    qual_cont_exact L L1 ->
    split_cont L1 L1 nil.
Proof.
  induction L1 as [| [x1 T1] L1 IH]; intros H1 H2; auto.
  inversion H1. inversion H2. subst. constructor; eauto.
Qed.

Lemma split_cont_left_nil : forall L1,
    uniq L1 ->
    qual_cont_exact L L1 ->
    split_cont L1 nil L1.
Proof.
  intros L1 H1 H2.
  apply split_cont_comm.
  eapply split_cont_right_nil; eauto.
Qed.

Lemma split_cont_subcont_left : forall L1 L2 L3,
    split_cont L1 L2 L3 ->
    subcont L2 L1.
Proof.
  intros L1 L2 L3 H1 x1 T1 H2. induction H1; auto.
  destruct (split_cont_uniq H1) as [? [? ?]].
  destruct (split_cont_notin H H1) as [? ?].
  analyze_binds_uniq H2.
Qed.

Lemma split_cont_subcont_right : forall L1 L2 L3,
    split_cont L1 L2 L3 ->
    subcont L3 L1.
Proof.
  intros L1 L2 L3 H1.
  apply split_cont_comm in H1.
  eapply split_cont_subcont_left; eauto.
Qed.

Lemma split_cont_is_permute : forall L1 L2 L3,
    split_cont L1 L2 L3 ->
    Permutation L1 (L2 ++ L3).
Proof.
  intros L1 L2 L3 H1. induction H1; simpl; auto.
  - eapply Permutation_cons_app. eauto.
Qed.

Lemma split_cont_notin_left : forall L1 L2 L3 x1,
    split_cont L1 L2 L3 ->
    x1 `in` dom L2 ->
    x1 `notin` dom L3.
Proof.
  intros L1 L2 L3 x1 H1 H2.
  pose proof (split_cont_disjoint H1) as H3.
  unfold disjoint in H3. fsetdec.
Qed.

Lemma split_cont_notin_right : forall L1 L2 L3 x1,
    split_cont L1 L2 L3 ->
    x1 `in` dom L3 ->
    x1 `notin` dom L2.
Proof.
  intros L1 L2 L3 x1 H1 H2.
  apply split_cont_comm in H1.
  eapply split_cont_notin_left; eauto.
Qed.

Lemma split_cont_remove_left : forall L1 L2 L3 x1 T1,
    binds x1 T1 L2 ->
    split_cont L1 L2 L3 ->
    split_cont (assoc_remove x1 L1) (assoc_remove x1 L2) L3.
Proof.
  intros L1 L2 L3 x1 T1 H1 H2. induction H2; simpl; auto.
  - destruct (x1 == x0) as [| H3]; subst.
    + destruct (split_cont_notin H H2) as [H3 H4].
      repeat rewrite assoc_remove_notin; auto.
    + constructor. apply assoc_remove_dom_neq; eauto.
      apply IHsplit_cont. analyze_binds H1.
  - destruct (x1 == x0) as [| H3]; subst.
    + destruct (split_cont_notin H H2).
      exfalso. eapply binds_dom_contradiction; eauto.
    + constructor; eauto using assoc_remove_dom_neq.
Qed.

Lemma split_cont_remove_right : forall L1 L2 L3 x1 T1,
    binds x1 T1 L3 ->
    split_cont L1 L2 L3 ->
    split_cont (assoc_remove x1 L1) L2 (assoc_remove x1 L3).
Proof.
  intros L1 L2 L3 x1 T1 H1 H2.
  apply split_cont_comm.
  apply split_cont_comm in H2.
  eapply split_cont_remove_left; eauto.
Qed.

Lemma split_cont_invert_mid : forall L1 L2 L3 L4 x1 P1,
    split_cont (L1 ++ (x1 ~ lin P1) ++ L2) L3 L4 ->
    exists L5 L6, L3 = L5 ++ (x1 ~ lin P1) ++ L6 \/
                  L4 = L5 ++ (x1 ~ lin P1) ++ L6.
Proof.
  intros L1 L2 L3 L4 x1 P1 H1.
  dependent induction H1; try rename x into H2.
  - exfalso. eapply app_cons_not_nil. symmetry. apply H2.
  - apply cons_eq_app in H2 as [[L3 [? ?]] | [? ?]]; subst.
    + destruct (IHsplit_cont L3 L2 x1 P1 eq_refl) as [? [? [? | ?]]]; subst; eauto.
    + inversion H2. subst. exists nil, E2. auto.
  - apply cons_eq_app in H2 as [[L3 [? ?]] | [? ?]]; subst.
    + destruct (IHsplit_cont L3 L2 x1 P1 eq_refl) as [? [? [? | ?]]]; subst; eauto.
    + inversion H2. subst. exists nil, E3. auto.
Qed.

Lemma split_cont_remove_mid_left : forall L1 L2 L3 L4 L5 x1 P1,
    split_cont (L1 ++ (x1 ~ lin P1) ++ L2) (L3 ++ (x1 ~ lin P1) ++ L4) L5 ->
    split_cont (L1 ++ L2) (L3 ++ L4) L5.
Proof.
  intros L1 L2 L3 L4 L5 x1 P1 H1; dependent induction H1;
    try rename x into H2; try rename x2 into H3.
  - exfalso. eapply app_cons_not_nil. symmetry. apply H2.
  - apply cons_eq_app in H3 as [[F1 [? ?]] | [? ?]]; subst.
    + apply cons_eq_app in H2 as [[F2 [? ?]] | [? ?]]; subst.
      * simpl. constructor. solve_uniq. eapply IHsplit_cont; auto.
      * inversion H2. subst. analyze_binds H.
    + inversion H3. subst. 
      apply cons_eq_app in H2 as [[F2 [? ?]] | [? ?]]; subst.
      * pose proof (split_cont_notin H H1) as [H4 H5]. analyze_binds H4.
      * inversion H2. subst. assumption.
  - apply cons_eq_app in H2 as [[F1 [? ?]] | [? ?]]; subst.
    + simpl. constructor. solve_uniq. eapply IHsplit_cont; auto.
    + pose proof (split_cont_notin H H1) as [H3 H4].
      inversion H2. subst. analyze_binds H3.
Qed.

Lemma split_cont_remove_mid_right : forall L1 L2 L3 L4 L5 x1 P1,
    split_cont (L1 ++ (x1 ~ lin P1) ++ L2) L3 (L4 ++ (x1 ~ lin P1) ++ L5) ->
    split_cont (L1 ++ L2) L3 (L4 ++ L5).
Proof.
  intros L1 L2 L3 L4 L5 x1 P1 H1.
  apply split_cont_comm.
  apply split_cont_comm in H1.
  eapply split_cont_remove_mid_left; eauto.
Qed.

Lemma split_cont_notin_both : forall L1 L2 L3 x1,
    split_cont L1 L2 L3 ->
    x1 `notin` dom L2 ->
    x1 `notin` dom L3 ->
    x1 `notin` dom L1.
Proof.
  intros L1 L2 L3 x1 H1 H2 H3.
  pose proof (split_cont_dom H1). fsetdec.
Qed.

Lemma split_cont_subseq_diff : forall E1 E2 E3,
    uniq E1 ->
    qual_cont_exact L E1 ->
    subsequence E3 E2 ->
    subsequence E2 E1 ->
    split_cont (diff_list E1 E3) (diff_list E1 E2) (diff_list E2 E3).
Proof.
  intros E1 E2 E3 H1 H2 H3 H4.
  generalize dependent E3.
  induction H4 as [| [x1 T1] | [x1 T1]]; intros E3 H3; simpl.
  - inversion H3. subst. simpl.
    apply split_cont_right_nil; auto.
  - inversion H1. subst. inversion H2. subst.
    pose proof (subseq_notin_reverse H7 H4) as H8.
    pose proof (subseq_notin_reverse H8 H3) as H9.
    repeat rewrite diff_list_notin_cons; auto.
    constructor; eauto using diff_list_notin_left.
  - inversion H1. subst. inversion H2. subst.
    pose proof (subseq_notin_reverse H7 H4) as H8.
    rewrite assoc_remove_diff_eq. inversion H3; subst; simpl.
    + pose proof (diff_list_notin_left _ xs H7).
      rewrite assoc_remove_notin; auto. constructor; auto.
      eapply IHsubsequence with (E3 := nil); auto.
    + pose proof (subseq_notin_reverse H8 H9).
      pose proof (diff_list_notin_left _ xs H7).
      pose proof (diff_list_notin_left _ E3 H7).
      repeat rewrite diff_list_notin_cons; auto.
      rewrite assoc_remove_notin; auto. constructor; auto.
    + pose proof (subseq_notin_reverse H8 H9).
      repeat rewrite assoc_remove_diff_eq.
      repeat rewrite assoc_remove_notin; eauto using diff_list_notin_left.
Qed.

(* Properties of Type Occurrence Relation *)

Lemma qual_cont_exact_app_inv : forall E1 E2 q1,
    qual_cont_exact q1 (E1 ++ E2) ->
    qual_cont_exact q1 E1 /\ qual_cont_exact q1 E2.
Proof.
  induction E1 as [| [x1 T1] E1 IH]; intros E2 q1 H1; auto.
  inversion H1; subst. apply IH in H2 as [H2 H3].
  split; [constructor |]; auto.
Qed.

Lemma qual_cont_exact_weaken_left : forall E1 E2 q1,
    qual_cont_exact q1 E1 ->
    qual_cont_exact q1 E2 ->
    qual_cont_exact q1 (E1 ++ E2).
Proof.
  induction E1 as [| [x1 [[] P1]] E1 IH]; intros E2 q1 H1 H2; auto.
  - inversion H1. subst. constructor; auto.
  - inversion H1. subst. constructor; auto.
Qed.

Lemma qual_cont_exact_weaken_mid : forall E1 E2 E3 q1,
    qual_cont_exact q1 E2 ->
    qual_cont_exact q1 (E1 ++ E3) ->
    qual_cont_exact q1 (E1 ++ E2 ++ E3).
Proof.
  intros E1 E2 E3 q1 H1 H2.
  rewrite_env ((E1 ++ E2) ++ E3).
  eapply qual_cont_exact_permute.
  - eapply Permutation_app_tail.
    eapply Permutation_app_comm.
  - simpl_env. eapply qual_cont_exact_weaken_left; auto.
Qed.

Lemma qual_cont_exact_strengthen_mid : forall E1 E2 E3 q1,
    qual_cont_exact q1 (E1 ++ E2 ++ E3) ->
    qual_cont_exact q1 (E1 ++ E3).
Proof.
  intros E1 E2 E3 q1 H1.
  apply qual_cont_exact_app_inv in H1 as [H1 H2].
  apply qual_cont_exact_app_inv in H2 as [H2 H3].
  apply qual_cont_exact_weaken_left; auto.
Qed.

Lemma qual_cont_exact_strengthen_left : forall E1 E2 q1,
    qual_cont_exact q1 (E1 ++ E2) ->
    qual_cont_exact q1 E2.
Proof.
  intros E1 E2 q1 H1.
  rewrite_env (nil ++ E2).
  rewrite_env (nil ++ E1 ++ E2) in H1.
  eapply qual_cont_exact_strengthen_mid; eauto.
Qed.

Lemma qual_cont_exact_comm : forall E1 E2 q1,
    qual_cont_exact q1 (E1 ++ E2) ->
    qual_cont_exact q1 (E2 ++ E1).
Proof.
  intros E1 E2 q1 H1.
  eapply qual_cont_exact_permute.
  - apply Permutation_app_comm.
  - assumption.
Qed.

Lemma qual_cont_exact_replace_mid : forall E1 E2 F1 F2 q1,
    qual_cont_exact q1 F2 ->
    qual_cont_exact q1 (E1 ++ F1 ++ E2) ->
    qual_cont_exact q1 (E1 ++ F2 ++ E2).
Proof.
  intros E1 E2 F1 F2 q1 H1 H2.
  apply qual_cont_exact_strengthen_mid in H2.
  apply qual_cont_exact_weaken_mid; assumption.
Qed.

Lemma qual_cont_exact_subseq : forall E1 E2 q1,
    subsequence E1 E2 ->
    qual_cont_exact q1 E2 ->
    qual_cont_exact q1 E1.
Proof.
  intros E1 E2 q2 H1 H2.
  induction H1 as [| [x1 [q1 P1]] | [x1 [q1 P1]]]; auto.
  - inversion H2. subst. eauto.
  - inversion H2. subst. constructor; eauto.
Qed.

Lemma qual_cont_exact_diff : forall E1 E2 q1,
    qual_cont_exact q1 E1 ->
    qual_cont_exact q1 (diff_list E1 E2).
Proof.
  induction 1; simpl.
  - rewrite diff_list_nil_left. auto.
  - destruct (notin_dec E2 x1) as [H1 | [T1 H1]].
    + rewrite (diff_list_notin_cons _ _ _ H1). constructor; auto.
    + rewrite diff_list_binds_cons; eauto using binds_In.
Qed.

(* Properties of Well-Formed Typing Contexts *)

Lemma well_formed_cont_weaken_un_left : forall F1 U1 L1 q1,
    uniq (F1 ++ U1 ++ L1) ->
    qual_cont_exact U F1 ->
    well_formed_cont q1 U1 L1 ->
    well_formed_cont q1 (F1 ++ U1) L1.
Proof.
  intros F1 U1 L1 q1 H1 H2 H3. inversion H3; subst.
  - constructor; [solve_uniq |].
    eapply qual_cont_exact_weaken_left; eauto.
  - constructor; [solve_uniq | | assumption].
    eapply qual_cont_exact_weaken_left; eauto.
Qed.

Lemma well_formed_cont_weaken_un_mid : forall F1 U1 U2 L1 q1,
    uniq (U1 ++ F1 ++ U2 ++ L1) ->
    qual_cont_exact U F1 ->  
    well_formed_cont q1 (U1 ++ U2) L1 ->
    well_formed_cont q1 (U1 ++ F1 ++ U2) L1.
Proof.
  intros F1 U1 U2 L1 q1 H1 H2 H3.
  rewrite_env ((U1 ++ F1) ++ U2).
  eapply well_formed_cont_permute_un.
  + apply Permutation_app_tail.
    apply Permutation_app_comm.
  + simpl_env. eapply well_formed_cont_weaken_un_left; solve_uniq.
Qed.

Lemma well_formed_cont_strengthen_un_mid : forall U1 U2 U3 L1 q1,
    well_formed_cont q1 (U1 ++ U2 ++ U3) L1 ->
    well_formed_cont q1 (U1 ++ U3) L1.
Proof.
  intros U1 U2 U3 L1 q1 H1. inversion H1; subst.
  - constructor. solve_uniq.
    eauto using qual_cont_exact_strengthen_mid.
  - constructor; auto. solve_uniq.
    eauto using qual_cont_exact_strengthen_mid.
Qed.

Lemma well_formed_cont_strengthen_un_left : forall U1 U2 L1 q1,
    well_formed_cont q1 (U1 ++ U2) L1 ->
    well_formed_cont q1 U2 L1.
Proof.
  intros U1 U2 L1 q1 H1.
  rewrite_env (nil ++ U2).
  rewrite_env (nil ++ U1 ++ U2) in H1.
  eapply well_formed_cont_strengthen_un_mid; eauto.
Qed.

Lemma well_formed_cont_strengthen_lin_mid : forall U1 L1 L2 L3 q1,
    well_formed_cont q1 U1 (L1 ++ L2 ++ L3) ->
    well_formed_cont q1 U1 (L1 ++ L3).
Proof.
  intros U1 L1 L2 L3 q1 H1. inversion H1; subst.
  - apply nil_eq_app in H as [? ?]; subst.
    apply app_eq_nil in H2 as [? ?]. subst. auto.
  - constructor; auto. solve_uniq.
    eapply qual_cont_exact_strengthen_mid; eauto.
Qed.

Lemma well_formed_cont_strengthen_lin_left : forall U1 L1 L2 q1,
    well_formed_cont q1 U1 (L1 ++ L2) ->
    well_formed_cont q1 U1 L2.
Proof.
  intros U1 L1 L2 q1 H1.
  rewrite_env (nil ++ L2).
  rewrite_env (nil ++ L1 ++ L2) in H1.
  eapply well_formed_cont_strengthen_lin_mid; eauto.
Qed.

(* Unrestricted and Linear Contexts *)

Lemma qual_dec : forall (q1 q2 : qual),
    sumbool (q1 = q2) (q1 <> q2).
Proof.
  intros. decide equality.
Defined.

Fixpoint env (q1 : qual) (E1 : cont) : cont :=
  match E1 with
  | nil => nil
  | (x1, type_qual q2 P1) :: E1 => match qual_dec q1 q2 with
                                   | left  _ => (x1, type_qual q1 P1) :: env q1 E1
                                   | right _ => env q1 E1
                                   end
  end.

Notation env_un  := (env U) (only parsing).
Notation env_lin := (env L) (only parsing).

Lemma env_notin : forall E1 x1 q1,
    x1 `notin` dom E1 ->
    x1 `notin` dom (env q1 E1).
Proof.
  induction E1 as [| [x1 [[] P1]] E1 IH]; intros x2 [] H1; simpl; auto.
Qed.

Lemma env_uniq : forall E1 q1,
    uniq E1 ->
    uniq (env q1 E1).
Proof.
  induction E1 as [| [x1 [[] P1]] E1 IH]; intros [] H1;
    simpl; inversion H1; subst; eauto using env_notin.
Qed.

Lemma env_app : forall E1 E2 q1,
    env q1 (E1 ++ E2) = env q1 E1 ++ env q1 E2.
Proof.
  induction E1 as [| [x1 [[] P1]] E1 IH];
    intros E2 []; simpl; try rewrite IH; auto.
Qed.

Lemma subseq_env : forall E1 E2 q1,
    subsequence E1 E2 ->
    subsequence (env q1 E1) (env q1 E2).
Proof.
  induction 1 as [| [x1 [[] P1]] | [x1 [[] P1]]];
    try destruct q1; simpl; auto.
Qed.

Lemma binds_env : forall E1 x1 q1 P1,
    binds x1 (type_qual q1 P1) E1 ->
    binds x1 (type_qual q1 P1) (env q1 E1).
Proof.
  induction E1 as [| [x1 [q1 P1]] E1 IH]; intros x2 q2 P2 H1; simpl.
  - analyze_binds H1.
  - destruct (qual_dec q2 q1); subst.
    + analyze_binds H1.
    + analyze_binds H1. inversion BindsTacVal. subst. congruence.
Qed.

Lemma submap_env : forall E1 E2 q1,
    submap E1 E2 ->
    submap (env q1 E1) (env q1 E2).
Proof.
  induction E1 as [| [x1 [q1 P1]] E1 IH];
    simpl; intros E2 q3 H1 x2 [q2 P2] H2.
  - analyze_binds H2.
  - destruct q3, q1; simpl in H2;
      analyze_binds H2; try solve [eapply IH; eauto].
    + inversion BindsTacVal. subst. eapply binds_env, H1; auto.
    + inversion BindsTacVal. subst. eapply binds_env, H1; auto.
Qed.

Lemma qual_cont_exact_env : forall E1 q1,
    qual_cont_exact q1 (env q1 E1).
Proof.
  induction E1 as [| [x1 [[] P1]] E1 IH]; intros []; simpl; auto. 
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma well_formed_cont_env_un : forall E1,
    uniq E1 ->
    well_formed_cont U (env_un E1) nil.
Proof.
  intros E1 H1. constructor.
  - apply env_uniq. auto.
  - apply qual_cont_exact_env.
Qed.

Lemma assoc_remove_env_comm : forall E1 q1 x1,
    assoc_remove x1 (env q1 E1) = env q1 (assoc_remove x1 E1).
Proof.
  induction E1 as [| [x2 [q2 P2]] E1 IH]; simpl; intros q1 x1; auto.
  - destruct q1, q2; destruct_eq_decs; simpl.
    + f_equal. auto.
    + f_equal. auto.
Qed.

Lemma env_uniq_app : forall E1,
    uniq E1 ->
    uniq (env U E1 ++ env L E1).
Proof.
  induction E1 as [| [x1 [[] P1]] E1 IH]; intros H1; simpl; auto.
  - inversion H1; subst.
    pose proof (env_notin _ U H4).
    pose proof (env_notin _ L H4). auto.
  - inversion H1; subst.
    pose proof (env_notin _ U H4).
    pose proof (env_notin _ L H4).
    eapply uniq_permute. apply Permutation_middle. auto.
Qed.

