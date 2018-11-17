Require Import Metalib.Metatheory.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Linear.Language.
Require Import Linear.Environment.
Require Import Linear.Infrastructure.
Require Import Linear.Data.AssocList.
Require Import Linear.Data.Permutation.
Require Import Linear.Properties.Structural.

Set Implicit Arguments.

(* Properties of Typing Relation *)

Lemma typing_value_un : forall U1 L1 v1 T1,
    value_qual U v1 ->
    typing U1 L1 v1 T1 ->
    L1 = nil.
Proof.
  intros U1 L1 v1 T1 H1 H2.
  dependent induction H2; inversion H1; subst; auto.
  - inversion H; auto.
  - inversion H; auto.
Qed.

Lemma typing_fvar_un : forall U1 L1 x1 P1,
    typing U1 L1 (term_fvar x1) (un P1) ->
    L1 = nil.
Proof.
  inversion 1; auto.
Qed.

(* Properties of Store Variables *)

Lemma fresh_variable_notin_dom : forall S1 x1,
    fresh_variable x1 S1 ->
    x1 `notin` dom S1.
Proof.
  induction 1; auto.
Qed.

Lemma fresh_variable_notin_free : forall S1 x1 x2 v2,
    fresh_variable x1 S1 ->
    binds x2 v2 S1 ->
    x1 `notin` free_vars v2.
Proof.
  induction 1; intros H2; analyze_binds H2.
Qed.    

Lemma store_variables_fresh : forall S1 x1,
    x1 `notin` store_variables S1 ->
    fresh_variable x1 S1.
Proof.
  induction S1 as [| [x2 v2] S1 IH]; intros x1 H1; auto.
  - simpl in H1. constructor; auto.
Qed.

Lemma fresh_variable_exists : forall S1,
    exists x1, fresh_variable x1 S1.
Proof.
  intros S1. pick fresh x1 for (store_variables S1).
  apply store_variables_fresh in Fr. eauto.
Qed.

Lemma fresh_variable_substore : forall x1 S1 S2,
    substore S1 S2 ->
    fresh_variable x1 S2 ->
    fresh_variable x1 S1.
Proof.
  induction S1 as [| [x2 v2] S1 IH]; intros S2 H1 H2; auto.
  destruct (x1 == x2); subst.
  - pose proof (fresh_variable_notin_dom H2).
    exfalso. eapply binds_dom_contradiction; eauto.
  - econstructor; eauto using fresh_variable_notin_free.
Qed.

Lemma assoc_remove_fresh_neq : forall S1 x1 x2,
    x1 <> x2 ->
    fresh_variable x1 S1 ->
    fresh_variable x1 (assoc_remove x2 S1).
Proof.
  induction 2; simpl; auto.
  destruct_eq_decs; subst; auto.
  constructor; auto.
Qed.

(* Properties of Typing Store Relation *)

Lemma typing_store_exact_lin : forall S1 U1 L1,
    typing_store S1 U1 L1 ->
    qual_cont_exact L L1.
Proof.
  intros S1 U1 L1 H1. induction H1; auto.
  - pose proof (split_cont_exact_lin H2). intuition.
Qed.

Lemma typing_store_uniq : forall S1 U1 L1,
    typing_store S1 U1 L1 ->
    uniq S1.
Proof.
  intros S1 U1 L1 H1. induction H1; simpl; auto.
  - apply fresh_variable_notin_dom in H0. auto.
  - apply fresh_variable_notin_dom in H0. auto.
Qed.

Lemma typing_store_notin_cont : forall S1 U1 L1 x1,
    fresh_variable x1 S1 ->
    typing_store S1 U1 L1 ->
    x1 `notin` dom U1 /\ x1 `notin` dom L1.
Proof.
  induction 2; simpl.
  - fsetdec.
  - inversion H. subst. apply IHtyping_store in H12 as [? H14]. fsetdec.
  - inversion H. subst. apply IHtyping_store in H12 as [? H14].
    rewrite (split_cont_dom H3) in H14. fsetdec.
Qed.

Lemma typing_store_notin : forall S1 U1 L1 x1,
    typing_store S1 U1 L1 ->
    x1 `notin` dom S1 ->
    x1 `notin` dom U1 /\ x1 `notin` dom L1.
Proof.
  intros S1 U1 L1 x1 H1 H2.
  dependent induction H1 generalizing x1; simpl in *.
  - analyze_binds H2.
  - pose proof (notin_add_1 _ _ _ H5) as H6.
    pose proof (notin_add_2 _ _ _ H5) as H7.
    destruct (IHtyping_store x1 H7) as [H8 H9].
    destruct (split_cont_notin H9 H2) as [H10 H11].
    split; fsetdec.
  - pose proof (notin_add_1 _ _ _ H5) as H6.
    pose proof (notin_add_2 _ _ _ H5) as H7.
    destruct (IHtyping_store x1 H7) as [H8 H9].
    destruct (split_cont_notin H9 H2) as [H10 H11].
    split; fsetdec.
Qed.

Lemma typing_store_uniq_cont : forall S1 U1 L1,
    typing_store S1 U1 L1 ->
    uniq (U1 ++ L1).
Proof.
  induction 1; simpl; auto.
  - pose proof (typing_store_notin_cont H0 H3) as [? ?]. solve_uniq.
  - eapply uniq_permute.
    + apply Permutation_middle.
    + pose proof (typing_store_notin_cont H0 H3) as [? H6].
      pose proof (split_cont_notin H6 H2) as [? ?].
      pose proof (split_cont_uniq H2) as [? [? ?]].
      pose proof (split_cont_subcont_right H2).
      constructor; eauto using uniq_submap_app.
Qed.

Lemma typing_store_split_left_lin : forall S1 U1 L1 L2 L3,
    typing_store S1 U1 L1 ->
    split_cont L1 L2 L3 ->
    exists S2, typing_store S2 U1 L2 /\ substore S2 S1.
Proof.
  intros S1 U1 L1 L2 L3 H1 H2.
  dependent induction H1 generalizing L2 L3.
  - inversion H2. exists nil. auto.
  - destruct (IHtyping_store _ _ H5) as [S2 [H6 H7]].
    pose proof (fresh_variable_substore H7 H0) as H8.
    exists ((x1 ~ v1) ++ S2). split.
    + pose proof (split_cont_exact_lin H5) as [H9 [H10 H11]].
      pose proof (split_cont_uniq H5) as [H12 [H13 H14]].
      pose proof (split_cont_left_nil H13 H10). constructor; auto.
    + apply (submap_cons H7).
  - inversion H5; subst.
    + destruct (split_cont_assoc_right H2 H12) as [L5 [H13 H14]].
      destruct (IHtyping_store L5 L3 H13) as [S2 [H15 H16]].
      pose proof (fresh_variable_substore H16 H0) as H17.
      exists ((x1 ~ v1) ++ S2). split; eauto using submap_cons.
    + apply split_cont_comm in H2.
      destruct (split_cont_assoc_left H2 H12) as [L5 [H13 H14]].
      destruct (IHtyping_store L2 L5 H13) as [S2 [H15 H16]].
      exists S2. eauto.
Qed.

Lemma typing_store_split_right_lin : forall S1 U1 L1 L2 L3,
    typing_store S1 U1 L1 ->
    split_cont L1 L2 L3 ->
    exists S2, typing_store S2 U1 L3 /\ substore S2 S1.
Proof.
  intros S1 U1 L1 L2 L3 H1 H2.
  apply split_cont_comm in H2.
  eapply typing_store_split_left_lin; eauto.
Qed.

(* Inversion Lemmas *)

Lemma typing_store_invert_un : forall S1 U1 L1 x1 T1,
    typing_store S1 U1 L1 ->
    binds x1 T1 U1 ->
    exists v1, binds x1 v1 S1 /\ value_qual U v1.
Proof.
  intros S1 U1 L1 x1 T1 H1 H2. induction H1.
  - analyze_binds H2.
  - analyze_binds_uniq H2; eauto.
    + pose proof (typing_store_uniq_cont H4).
      pose proof (typing_store_notin_cont H0 H4) as [? ?]. solve_uniq.
    + destruct (IHtyping_store BindsTac) as [v2 [H7 H8]]. eauto.
  - destruct (IHtyping_store H2) as [v2 [H6 H7]]. eauto.
Qed.

Lemma typing_store_invert_lin : forall S1 U1 L1 x1 T1,
    typing_store S1 U1 L1 ->
    binds x1 T1 L1 ->
    exists v1, binds x1 v1 S1 /\ value_qual L v1.
Proof.
  intros S1 U1 L1 x1 T1 H1 H2. induction H1.
  - analyze_binds H2.
  - pose proof (split_cont_binds_right x1 T1 H3 H2) as H6.
    destruct (IHtyping_store H6) as [v2 [H7 H8]]. eauto.
  - analyze_binds_uniq H2; eauto.
    + pose proof (split_cont_uniq H3) as [? [? ?]].
      pose proof (typing_store_notin_cont H0 H4) as [? H9].
      pose proof (split_cont_notin H9 H3) as [? ?]. solve_uniq.
    + eapply split_cont_binds_right in BindsTac; eauto.
      destruct (IHtyping_store BindsTac) as [v2 [H7 H8]]. eauto.
Qed.

Lemma typing_invert_bool : forall U1 L1 v1 q1,
    value_qual q1 v1 ->
    typing U1 L1 v1 (type_qual q1 pretype_bool) ->
    exists b1, v1 = term_bval q1 b1.
Proof.
  repeat inversion 1. exists b1. reflexivity.
Qed.

Lemma typing_invert_arr : forall U1 L1 v1 q1 T1 T2,
    value_qual q1 v1 ->
    typing U1 L1 v1 (type_qual q1 (pretype_arr T1 T2)) ->
    exists e1, v1 = term_abs q1 T1 e1.
Proof.
  repeat inversion 1; exists e1; reflexivity.
Qed.

Lemma typing_store_invert_bool : forall S1 U1 L1 L2 L3 x1 q1 v1,
    binds x1 v1 S1 ->
    split_cont L1 L2 L3 ->
    typing_store S1 U1 L1 ->
    typing U1 L2 (term_fvar x1) (type_qual q1 pretype_bool) ->
    exists b1, v1 = term_bval q1 b1.
Proof.
  intros S1 U1 L1 L2 L3 x1 q1 v1 H1 H2 H3.
  generalize dependent L3. generalize dependent L2.
  induction H3; intros L4 L5 H6 H7.
  - analyze_binds H1.
  - pose proof (typing_store_uniq H4) as H8.
    pose proof (fresh_variable_notin_dom H0) as H9.
    analyze_binds_uniq H1.
    + inversion H7; [subst | analyze_binds H16].
      rewrite_env (nil ++ (x0 ~ un P1) ++ U1) in H1.
      apply assoc_equate_uniq in H1 as [? [? ?]]. subst.
      inversion H11. subst. apply typing_invert_bool in H5; auto.
      inversion H15. subst. solve_uniq.
    + apply split_cont_comm in H3.
      pose proof (split_cont_assoc_left H3 H6) as [L6 [H11 H12]].
      apply typing_strengthen_un_left in H7; eauto.
  - pose proof (typing_store_uniq H4) as H8.
    pose proof (fresh_variable_notin_dom H0) as H9.
    analyze_binds_uniq H1; inversion H6; subst.
    + inversion H7; subst. apply typing_invert_bool in H5; auto.
    + inversion H7; subst.
      * assert (H19 : binds x0 _ (U0 ++ (x0 ~ un pretype_bool) ++ U2)) by auto.
        destruct (typing_store_invert_un _ _ H4 H19) as [v1 [H20 H21]].
        exfalso. eapply binds_dom_contradiction; eauto.
      * exfalso. eapply (split_cont_notin_left H6); simpl; eauto.
    + inversion H7; subst. exfalso. eapply binds_dom_contradiction; eauto.
    + apply split_cont_comm in H3.
      pose proof (split_cont_assoc_left H3 H16) as [L5 [H17 H18]].
      specialize (IHtyping_store BindsTac L4 L5 H17 H7). eauto.
Qed.

Lemma typing_store_invert_arr : forall S1 U1 L1 L2 L3 x1 v1 q1 T1 T2,
    binds x1 v1 S1 ->
    split_cont L1 L2 L3 ->
    typing_store S1 U1 L1 ->
    typing U1 L2 (term_fvar x1) (type_qual q1 (pretype_arr T1 T2)) ->
    exists e1, v1 = term_abs q1 T1 e1.
Proof.
  intros S1 U1 L1 L2 L3 x1 v1 q1 T1 T2 H1 H2 H3 H4.
  generalize dependent L2. generalize dependent L3.
  induction H3; intros L5 L4 H6 H7.
  - inversion H6. analyze_binds H1.
  - pose proof (typing_store_uniq H4) as H8.
    pose proof (fresh_variable_notin_dom H0) as H9.
    analyze_binds_uniq H1.
    + inversion H7; [subst | analyze_binds H16].
      rewrite_env (nil ++ (x0 ~ un P1) ++ U1) in H1.
      rewrite_env (U0 ++ (x0 ~ un (pretype_arr T1 T2)) ++ U2) in H1.
      apply assoc_equate_uniq in H1 as [? [? ?]]; [subst | analyze_binds H16].
      * inversion H11. subst. eapply typing_invert_arr; eauto.
      * inversion H15. subst. solve_uniq.
    + apply split_cont_comm in H3.
      destruct (split_cont_assoc_left H3 H6) as [F1 [H11 H12]].
      apply typing_strengthen_un_left in H7; eauto.
  - pose proof (typing_store_uniq H4) as H8.
    pose proof (fresh_variable_notin_dom H0) as H9.
    analyze_binds_uniq H1; inversion H6; subst.
    + inversion H7. subst. eapply typing_invert_arr; eauto.
    + inversion H7; subst.
      * assert (H19 : binds x0 _ (U0 ++ (x0 ~ un (pretype_arr T1 T2)) ++ U2)) by auto.
        destruct (typing_store_invert_un _ _ H4 H19) as [e1 [H20 H21]].
        exfalso. eapply binds_dom_contradiction; eauto.
      * exfalso. eapply (split_cont_notin_left H6); simpl; eauto.
    + inversion H7. subst. exfalso. eapply binds_dom_contradiction; eauto.
    + apply split_cont_comm in H3.
      pose proof (split_cont_assoc_left H3 H16) as [L5 [H17 H18]]. eauto.
Qed.
      
(* Small-Step Evaluation Relation Satisfies Progress *)

Lemma eval_step_weaken : forall S1 S2 S3 e1 e2,
    eval_step S1 e1 S2 e2 ->
    substore S1 S3 ->
    exists S4 e3, eval_step S3 e1 S4 e3.
Proof.
  intros S1 S2 S3 e1 e2 H1 H2.
  dependent induction H1 generalizing S3;
  try solve [destruct (fresh_variable_exists S3) as [? ?]; eauto];
  try solve [edestruct IHeval_step as [? [? ?]]; eauto].
  - pick fresh x2 for (union (store_variables S3) (free_vars e1)).
    assert (H3 : x2 `notin` store_variables S3) by fsetdec.
    assert (H4 : x2 `notin` free_vars e1) by fsetdec.
    apply store_variables_fresh in H3. eauto.    
Qed.

Theorem eval_step_progress : forall S1 U1 L1 e1 T1,
    typing U1 L1 e1 T1 ->
    typing_store S1 U1 L1 ->
    reduced e1 S1 \/ exists S2 e2, eval_step S1 e1 S2 e2.
Proof.
  intros S1 U1 L1 e1 T1 H1 H2.
  dependent induction H1 generalizing S1.
  - assert (H3 : binds x1 (un P1) (U1 ++ (x1 ~ un P1) ++ U2)) by auto.
    destruct (typing_store_invert_un _ _ H2 H3) as [v1 [H4 H5]]. eauto.
  - assert (H3 : binds x1 (lin P1) (x1 ~ lin P1)) by auto.
    destruct (typing_store_invert_lin _ _ H2 H3) as [v1 [H4 H5]]. eauto.
  - right. destruct (fresh_variable_exists S1) as [x1 H1]. eauto.
  - destruct (typing_store_split_left_lin H2 H) as [S2 [H3 H4]].
    destruct (IHtyping1 S2 H3) as [H7 | [S4 [e4 H7]]].
    + inversion H7. subst. apply H4 in H1.
      destruct (typing_store_invert_bool _ H1 H H2 H1_) as [[] ?]; subst; eauto.
    + destruct (eval_step_weaken H7 H4) as [S5 [H8 H9]]. eauto.
  - destruct (typing_store_split_left_lin H2 H) as [S2 [H3 H4]].
    destruct (IHtyping1 S2 H3) as [H5 | [S3 [e3 H5]]].
    + inversion H5. subst. apply H4 in H1.
      destruct (typing_store_invert_arr _ H1 H H2 H1_) as [e3 H6]. subst.
      destruct (typing_store_split_right_lin H2 H) as [S3 [H6 H7]].
      destruct (IHtyping2 S3 H6) as [H8 | [S4 [e4 H8]]].
      * inversion H8. subst. eauto.
      * destruct (eval_step_weaken H8 H7) as [S5 [e5 H9]]. eauto.
    + destruct (eval_step_weaken H5 H4) as [S4 [e4 H6]]. eauto.
  - pick fresh x2 for (union (store_variables S1) (free_vars e1)).
    assert (H3 : x2 `notin` store_variables S1) by fsetdec.
    assert (H4 : x2 `notin` free_vars e1) by fsetdec.
    apply store_variables_fresh in H3. eauto.
  - pick fresh x2 for (union (store_variables S1) (free_vars e1)).
    assert (H3 : x2 `notin` store_variables S1) by fsetdec.
    assert (H4 : x2 `notin` free_vars e1) by fsetdec.
    apply store_variables_fresh in H3. eauto.
Qed.

(* Substitution Lemmas *)

Lemma typing_notin_free : forall U1 L1 e1 T1 x1,
    typing U1 L1 e1 T1 ->
    x1 `notin` union (dom U1) (dom L1) ->
    x1 `notin` free_vars e1.
Proof.
  intros U1 L1 e1 T1 x1 H1 H2. induction H1; simpl.
  - repeat rewrite dom_app in H2. simpl in H2. fsetdec.
  - simpl in H2. fsetdec.
  - fsetdec.
  - pose proof (split_cont_dom H) as H3.
    repeat apply notin_union_3.
    + eapply IHtyping1. fsetdec.
    + eapply IHtyping2. fsetdec.
    + eapply IHtyping3. fsetdec.
  - pose proof (split_cont_dom H) as H3. 
    repeat apply notin_union_3.
    + eapply IHtyping1. fsetdec.
    + eapply IHtyping2. fsetdec.
  - pick fresh z1 for (add x1 A1).
    eapply open_notin_free. eapply H1; eauto.
  - pick fresh z1 for (add x1 A1).
    eapply open_notin_free. eapply H1; eauto.
Qed.

Lemma typing_store_notin_free : forall S1 U1 L1 x1,
    typing_store S1 U1 L1 ->
    x1 `notin` dom S1 ->
    forall x2 v2, binds x2 v2 S1 ->
                  x1 `notin` free_vars v2.
Proof.
  intros S1 U1 L1 x1 H1 H2.
  dependent induction H1 generalizing x1; intros x2 v2 H6.
  - analyze_binds_uniq H6.
  - pose proof (typing_store_uniq H3) as H7.
    pose proof (fresh_variable_notin_dom H0) as H8.
    analyze_binds_uniq H6; simpl in *; eauto 2.
    inversion H; subst; simpl.
    + fsetdec.
    + pose proof (notin_add_2 _ _ _ H5) as H10.
      pose proof (typing_store_notin H3 H10) as [H11 H12].
      pose proof (split_cont_notin H12 H2) as [H13 H14].
      eapply typing_notin_free in H4. eauto. fsetdec.
  - pose proof (typing_store_uniq H3) as H7.
    pose proof (fresh_variable_notin_dom H0) as H8.
    analyze_binds_uniq H6; simpl in *; eauto 2.
    inversion H; subst; simpl.
    + fsetdec.
    + pose proof (notin_add_2 _ _ _ H5) as H10.
      pose proof (typing_store_notin H3 H10) as [H11 H12].
      pose proof (split_cont_notin H12 H2) as [H13 H14].
      eapply typing_notin_free in H4. eauto. fsetdec.
Qed.

Lemma typing_subst_un_mid : forall U1 U2 L1 L2 L3 x1 x2 e1 P1 T1,
    split_cont L1 L2 L3 ->
    typing (U1 ++ (x1 ~ un P1) ++ U2) L2 e1 T1 ->
    typing (U1 ++ U2) L3 (term_fvar x2) (un P1) ->
    typing (U1 ++ U2) L1 ([x1 ~> x2] e1) T1.
Proof.
  intros U1 U2 L1 L2 L3 x1 x2 e1 P1 T1 H1 H2 H3.
  pose proof (typing_fvar_un H3). subst.
  pose proof (split_cont_nil_right H1). subst L2.
  dependent induction H2; try rename x into H4; simpl.
  - inversion H. destruct (x1 == x0); subst.
    + apply assoc_equate_uniq in H4 as [? [? ?]]; auto.
      inversion H6. subst. assumption.
    + pose proof (typing_exact_un H3) as H6.
      pose proof (typing_uniq H3) as H7. simpl_env in H7.      
      apply assoc_equate_split_uniq in H4 as [F1 [F2 [? | ?]]]; subst; auto.
      * simpl_env. repeat constructor; [solve_uniq | | solve_uniq].
        simpl_env in H6. eauto using qual_cont_exact_strengthen_mid.
      * rewrite_env ((U1 ++ F1) ++ (x0 ~ un P0) ++ F2).
        repeat constructor; [solve_uniq | | solve_uniq].
        rewrite_env ((U1 ++ F1) ++ (x0 ~ un P0) ++ F2) in H6.
        eauto using qual_cont_exact_strengthen_mid.
  - inversion H. destruct (x1 == x0); subst.
    + analyze_binds H0.
    + repeat constructor; [solve_uniq | | solve_uniq].
      eauto using qual_cont_exact_strengthen_mid.
  - inversion H. subst. repeat constructor; [solve_uniq |].
    eauto using qual_cont_exact_strengthen_mid.
  - destruct (split_cont_uniq H) as [? [? ?]].
    destruct (split_cont_exact_lin H) as [? [? ?]].
    econstructor; only 1 : apply H; eauto using split_cont_right_nil.
  - destruct (split_cont_uniq H) as [? [? ?]].
    destruct (split_cont_exact_lin H) as [? [? ?]].
    econstructor; only 1: apply H; eauto using split_cont_right_nil.
  - eapply typing_abs_un with (A1 := add x1 (union A1 (dom (U1 ++ U2)))).
    + eauto using well_formed_cont_strengthen_un_mid.
    + intros z1 H4. rewrite subst_open_var; auto.
      rewrite_env (((z1 ~ un P0) ++ U1) ++ U2).
      eapply H1; auto. simpl_env. eapply typing_weaken_un; auto.
      * constructor; auto.
      * inversion H; solve_uniq.
  - eapply typing_abs_lin with (A1 := add x1 (union A1 (dom L1))).
    + eauto using well_formed_cont_strengthen_un_mid.
    + intros z1 H4. rewrite subst_open_var; auto.
      eapply H1; auto.
Qed.

Lemma typing_subst_un : forall U1 L1 L2 L3 x1 x2 e1 P1 T1,
    split_cont L1 L2 L3 ->
    typing ((x1 ~ un P1) ++ U1) L2 e1 T1 ->
    typing U1 L3 (term_fvar x2) (un P1) ->
    typing U1 L1 ([x1 ~> x2] e1) T1.
Proof.
  intros U1 L1 L2 L3 x1 x2 e1 P1 T1 H1 H2 H3.
  rewrite_env (nil ++ U1).
  rewrite_env (nil ++ (x1 ~ un P1) ++ U1) in H2.
  eapply typing_subst_un_mid; eauto.
Qed.

Lemma typing_subst_lin_mid : forall U1 L1 L2 L3 L4 x1 x2 e1 P1 T1,
    split_cont L1 (L2 ++ L3) L4 ->
    typing U1 (L2 ++ (x1 ~ lin P1) ++ L3) e1 T1 ->
    typing U1 L4 (term_fvar x2) (lin P1) ->
    typing U1 L1 ([x1 ~> x2] e1) T1.
Proof.
  intros U1 L1 L2 L3 L4 x1 x2 e1 P1 T1 H1 H2 H3.
  generalize dependent L1. inversion H3. subst.
  dependent induction H2; try rename x into H4; intros L1 H2; simpl.
  - exfalso. eapply app_cons_not_nil. symmetry. apply H4.
  - assert (L2 = nil /\ L3 = nil) as [? ?]; subst.
    apply cons_eq_app in H4 as [[L5 [? H7]] | [? H7]].
    exfalso. eapply app_cons_not_nil. symmetry. apply H7.
    subst. inversion H7. tauto.
    pose proof (split_cont_nil_left H2). subst.
    inversion H4. subst. destruct (x1 == x1); tauto.
  - exfalso. eapply app_cons_not_nil. symmetry. apply H4.
  - destruct (split_cont_invert_mid _ _ _ _ H) as [L5 [L6 [? | ?]]]; subst.
    + assert (x1 `in` dom (L5 ++ (x1 ~ lin P1) ++ L6)).
      rewrite dom_app. simpl. fsetdec.
      assert (x1 `notin` union (dom U1) (dom L4)). apply notin_union_3.
      apply typing_uniq in H2_. solve_uniq.
      eapply split_cont_notin_left; eauto.
      pose proof (split_cont_remove_mid_left _ _ _ _ _ _ H) as H8.
      eapply split_cont_notin_left with (x1 := x1) in H; auto.
      apply split_cont_comm in H2.
      destruct (split_cont_assoc_right H2 H8) as [L7 [H9 H10]].
      econstructor; eauto.
      * apply split_cont_comm in H10. eapply IHtyping1; eauto.
      * rewrite subst_fresh. auto. apply (typing_notin_free H2_0 H1).
      * rewrite subst_fresh. auto. apply (typing_notin_free H2_1 H1).
    + assert (x1 `in` dom (L5 ++ (x1 ~ lin P1) ++ L6)).
      rewrite dom_app. simpl. fsetdec.
      assert (x1 `notin` union (dom U1) (dom L0)). apply notin_union_3.
      apply typing_uniq in H2_1. solve_uniq.
      eapply split_cont_notin_right; eauto.
      pose proof (split_cont_remove_mid_right _ _ _ _ _ _ H) as H8.
      eapply split_cont_notin_right with (x1 := x1) in H; auto.
      destruct (split_cont_assoc_left H2 H8) as [L7 [H9 H10]].
      econstructor; eauto.
      * rewrite subst_fresh. eauto. apply (typing_notin_free H2_ H1).
  - destruct (split_cont_invert_mid _ _ _ _ H) as [L5 [L6 [? | ?]]]; subst.
    + assert (x1 `in` dom (L5 ++ (x1 ~ lin P1) ++ L6)).
      rewrite dom_app. simpl. fsetdec.
      assert (x1 `notin` union (dom U1) (dom L4)). apply notin_union_3.
      apply typing_uniq in H2_. solve_uniq.
      eapply split_cont_notin_left; eauto.
      pose proof (split_cont_remove_mid_left _ _ _ _ _ _ H) as H8.
      eapply split_cont_notin_left with (x1 := x1) in H; auto.
      apply split_cont_comm in H2.
      destruct (split_cont_assoc_right H2 H8) as [L7 [H9 H10]].
      econstructor; eauto.
      * apply split_cont_comm in H10. eapply IHtyping1; eauto.
      * rewrite subst_fresh. auto. apply (typing_notin_free H2_0 H1).
    + assert (x1 `in` dom (L5 ++ (x1 ~ lin P1) ++ L6)).
      rewrite dom_app. simpl. fsetdec.
      assert (x1 `notin` union (dom U1) (dom L0)). apply notin_union_3.
      apply typing_uniq in H2_0. solve_uniq.
      eapply split_cont_notin_right; eauto.
      pose proof (split_cont_remove_mid_right _ _ _ _ _ _ H) as H8.
      eapply split_cont_notin_right with (x1 := x1) in H; auto.
      destruct (split_cont_assoc_left H2 H8) as [L7 [H9 H10]].
      econstructor; eauto.
      * rewrite subst_fresh. eauto. apply (typing_notin_free H2_ H1).
  - pose proof (typing_uniq H3).
    apply typing_abs_un with (A1 := add x1 (add x2 (union A1 (dom U1)))).
    + inversion H; subst.
      * exfalso. eapply app_cons_not_nil. symmetry. apply H7.
      * constructor; auto.
        -- eapply uniq_permute. eapply Permutation_app_head.
           symmetry. eapply (split_cont_is_permute H2).
           assert (x2 `notin` dom (U1 ++ L2 ++ L3)).
           rewrite dom_app. apply notin_union_3. solve_uniq.
           eapply split_cont_notin_right. eauto. simpl. auto.
           solve_uniq.
        -- destruct (split_cont_exact_lin H2) as [? [? ?]]. auto.
    + intros z1 H7. rewrite subst_open_var; auto.
      inversion H5. subst. eapply H1; auto.
  - pose proof (typing_uniq H3).
    apply typing_abs_lin with (A1 := add x1 (union A1 (dom L1))).
    + inversion H; subst.
      * exfalso. eapply app_cons_not_nil. symmetry. apply H7.
      * constructor; auto.
        -- eapply uniq_permute. eapply Permutation_app_head.
           symmetry. eapply (split_cont_is_permute H2).
           assert (x2 `notin` dom (U1 ++ L2 ++ L3)).
           rewrite dom_app. apply notin_union_3. solve_uniq.
           eapply split_cont_notin_right. eauto. simpl. auto.
           solve_uniq.
        -- destruct (split_cont_exact_lin H2) as [? [? ?]]. auto.
    + intros z1 H7. rewrite subst_open_var; auto.
      inversion H5. subst. eapply H1; auto. constructor; auto.
Qed.

Lemma typing_subst_lin : forall U1 L1 L2 L3 x1 x2 e1 P1 T1,
    split_cont L1 L2 L3 ->
    typing U1 ((x1 ~ lin P1) ++ L2) e1 T1 ->
    typing U1 L3 (term_fvar x2) (lin P1) ->
    typing U1 L1 ([x1 ~> x2] e1) T1.
Proof.
  intros U1 L1 L2 L3 x1 x2 e1 P1 T1 H1 H2 H3.
  rewrite_env (nil ++ L1).
  rewrite_env (nil ++ (x1 ~ lin P1) ++ L2) in H2.
  eapply typing_subst_lin_mid; eauto. assumption.
Qed.

Lemma typing_store_binds_un : forall S1 U1 L1 x1 v1 T1,
    typing_store S1 U1 L1 ->
    binds x1 v1 S1 ->
    binds x1 T1 U1 ->
    typing U1 nil v1 T1.
Proof.
  intros S1 U1 L1 x1 v1 T1 H1 H2 H3.
  dependent induction H1 generalizing x1 v1 T1.
  - analyze_binds H2.
  - pose proof (typing_store_uniq H3) as H10.
    pose proof (fresh_variable_notin_dom H0) as H11.
    pose proof (typing_store_notin_cont H0 H3) as [H12 H13].
    pose proof (typing_store_uniq_cont H3) as H14.
    analyze_binds_uniq H5; analyze_binds_uniq H6.
    + eapply typing_weaken_un; [constructor | solve_uniq |]; eauto.
    + eapply typing_weaken_un; [constructor | solve_uniq |]; eauto.
  - pose proof (typing_store_uniq H3) as H10.
    pose proof (fresh_variable_notin_dom H0) as H11.
    analyze_binds_uniq H5; eauto.
    + pose proof (typing_store_notin_cont H0 H3) as [H12 H13].
      exfalso. eapply binds_dom_contradiction; eauto.
Qed.

Lemma typing_store_binds_lin : forall S1 U1 L1 x1 v1 T1,
    typing_store S1 U1 L1 ->
    binds x1 v1 S1 ->
    binds x1 T1 L1 ->
    exists L2 L3, typing_store (dealloc L x1 S1) U1 L2 /\
                  split_cont L2 L3 (dealloc L x1 L1) /\
                  typing U1 L3 v1 T1.
Proof.
  intros S1 U1 L1 x1 v1 T1 H1 H2 H3.
  dependent induction H1 generalizing x1 v1 T1; simpl.
  - analyze_binds H2. 
  - pose proof (typing_store_uniq H3) as H10.
    pose proof (fresh_variable_notin_dom H0) as H11.
    analyze_binds_uniq H5; destruct_eq_decs; try congruence.
    + destruct (typing_store_notin_cont H0 H3) as [H12 H13].
      exfalso. eapply binds_dom_contradiction; eauto.
    + exfalso. eapply binds_dom_contradiction; eauto.
    + destruct (IHtyping_store _ _ _ BindsTac H6) as [L4 [L5 [H12 [H13 H14]]]].
      exists L4, L5. repeat split; eauto.
      * eapply typing_store_cons_un; eauto.
        -- apply (assoc_remove_fresh_neq (not_eq_sym n) H0).
        -- destruct (split_cont_uniq H13) as [? [? ?]].
           destruct (split_cont_exact_lin H13) as [? [? ?]].
           apply (split_cont_left_nil H5 H15).
      * simpl_env. eapply typing_weaken_un; eauto.
        -- constructor; eauto.
        -- pose proof (typing_uniq H14).
           pose proof (assoc_remove_fresh_neq (not_eq_sym n) H0) as H15.
           destruct (typing_store_notin_cont H15 H12) as [H16 H17].
           destruct (split_cont_notin H17 H13) as [H18 H19]. solve_uniq.
  - pose proof (typing_store_uniq H3) as H10.
    pose proof (fresh_variable_notin_dom H0) as H11.
    pose proof (typing_store_notin_cont H0 H3) as [H12 H13].
    pose proof (split_cont_notin H13 H2) as [H14 H15].
    pose proof (split_cont_uniq H2) as [H16 [H17 H18]].
    destruct_eq_decs; analyze_binds_uniq H5; analyze_binds_uniq H6.
    + repeat rewrite assoc_remove_notin; eauto.
    + pose proof (split_cont_binds_right _ _ H2 BindsTac0) as H19.
      destruct (IHtyping_store _ _ _ BindsTac H19) as [L4 [L5 [H20 [H21 H22]]]].
      pose proof (split_cont_remove_right _ _ BindsTac0 H2) as H23.
      apply split_cont_comm in H21.
      destruct (split_cont_assoc_left H21 H23) as [M1 [H24 H25]].
      apply split_cont_comm in H25.
      exists ((x0 ~ lin P1) ++ M1), L5. repeat split; eauto.
      * econstructor; eauto using assoc_remove_fresh_neq.
      * pose proof(assoc_remove_fresh_neq (not_eq_sym n) H0) as H26.
        destruct (typing_store_notin_cont H26 H20) as [? H28].
        destruct (split_cont_notin H28 H24) as [? ?].
        constructor; assumption.
Qed.

Lemma typing_dealloc_fvar : forall U1 L1 L2 L3 x1 e1 P1 T1,
    split_cont L1 L2 L3 ->
    typing U1 L2 (term_fvar x1) (lin P1) ->
    typing U1 L3 e1 T1 ->
    typing U1 (dealloc L x1 L1) e1 T1.
Proof.
  intros U1 L1 L2 L3 x1 e1 P1 T1 H1 H2 H3.
  inversion H2. subst. eapply split_cont_remove_left in H1; eauto.
  simpl in H1. destruct (x1 == x1); [| congruence].
  rewrite <- (split_cont_nil_left H1) in H3. assumption.
Qed.

Lemma typing_store_dealloc_bval : forall S1 U1 L1 b1 x1,
    typing_store S1 U1 L1 ->
    binds x1 (term_bval L b1) S1 ->
    binds x1 (lin pretype_bool) L1 ->
    typing_store (dealloc L x1 S1) U1 (dealloc L x1 L1).
Proof.
  intros S1 U1 L1 b1 x1 H1 H2 H3.
  destruct (typing_store_binds_lin _ _ _ H1 H2 H3) as [F1 [F2 [H4 [H5 H6]]]].
  assert (H7 : F1 = dealloc L x1 L1).
  - inversion H6. subst. apply (split_cont_nil_left H5).
  - subst. assumption.
Qed.

(* Small-Step Evaluation Relation Satisfies Preservation *)

Lemma eval_step_preservation_split : forall S1 S2 U1 L1 L2 L3 e1 e2 T1,
    typing U1 L2 e1 T1 ->
    typing_store S1 U1 L1 ->
    split_cont L1 L2 L3 ->
    eval_step S1 e1 S2 e2 -> exists U2 L4 L5, typing U2 L5 e2 T1 /\
                                              typing_store S2 U2 L4 /\
                                              split_cont L4 L5 L3 /\
                                              subcont U1 U2 /\
                                              uniq (U2 ++ L4).
Proof.
  intros S1 S2 U1 L1 L2 L3 e1 e2 T1 H1 H2 H3 H4.
  dependent induction H1 generalizing S1 S2 L1 L3 e2;
    match goal with
    | [ H1 : eval_step S1 _ _ _ |- _ ] => inversion H1; subst
    end.
  - destruct (typing_store_notin_cont H8 H2). destruct q1.
    + exists ((x1 ~ un pretype_bool) ++ U1), L1, nil.
      inversion H. subst. intuition eauto.
      * rewrite_env (nil ++ (x1 ~ un pretype_bool) ++ U1). eauto.
      * destruct (split_cont_uniq H3) as [H10 [? ?]].
        pose proof (split_cont_exact_lin H3) as [H11 [? ?]].
        pose proof (split_cont_left_nil H10 H11). eauto.
      * pose proof (typing_store_uniq_cont H2). simpl. eauto.
    + exists U1, ((x1 ~ lin pretype_bool) ++ L3), (x1 ~ lin pretype_bool).
      inversion H. subst. intuition eauto. 
      * pose proof (split_cont_notin H1 H3) as [H10 H11].
        rewrite (split_cont_nil_left H3) in H3. constructor; eauto.
      * pose proof (typing_store_uniq_cont H2).
        rewrite <- (split_cont_nil_left H3).
        eapply uniq_permute. eapply Permutation_middle. eauto.
  - destruct (split_cont_assoc_left H3 H) as [M1 [H10 H11]].
    destruct (IHtyping1 _ _ _ _ _ H2 H10 H9) as [V1 [M2 [M3 [H12 [H13 [H14 [H16 H17]]]]]]].
    destruct (split_cont_assoc_right H14 H11) as [M4 [H18 H19]].
    destruct (split_cont_uniq H) as [H20 [H21 H22]].
    pose proof (typing_exact_un H12) as H23.
    pose proof (split_cont_subcont_right H19) as H24.
    pose proof (split_cont_subcont_left H18) as H25.
    pose proof (submap_trans H24 H25) as H26.
    pose proof (uniq_submap_app _ H26 H22 H17).
    exists V1, M2, M4. intuition eauto using typing_weaken_un_subcont.
  - pose proof (split_cont_assoc_left H3 H) as [M1 [H10 H11]].
    destruct (typing_store_invert_bool _ H9 H10 H2 H1_) as [b1 H12].
    inversion H12. subst. clear H12. destruct q1.
    + assert (L2 = nil) by (inversion H1_; auto). subst.
      pose proof (typing_store_uniq_cont H2).
      rewrite (split_cont_nil_left H) in H3.
      exists U1, L1, L4. repeat split; eauto.
    + assert (H12 : binds x1 (lin pretype_bool) L1).
      inversion H1_. subst. eapply split_cont_binds_left; eauto.
      pose proof (typing_store_dealloc_bval _ _ H2 H9 H12) as H13.
      pose proof (typing_store_uniq_cont H2) as H14.
      destruct (proj1 (uniq_app_iff _ _ _) H14) as [H15 [H16 H17]].
      exists U1, (dealloc L x1 L1), (dealloc L x1 L0). repeat split; eauto.
      * eapply typing_dealloc_fvar; eauto.
      * eapply split_cont_remove_left; eauto.
        inversion H1_. subst. eapply split_cont_binds_left; eauto.
      * eapply uniq_submap_app; eauto using submap_assoc_remove, assoc_remove_uniq.
  - pose proof (split_cont_assoc_left H3 H) as [M1 [H10 H11]].
    destruct (typing_store_invert_bool _ H9 H10 H2 H1_) as [b1 H12].
    inversion H12. subst. clear H12. destruct q1.
    + assert (L2 = nil) by (inversion H1_; auto). subst.
      pose proof (typing_store_uniq_cont H2).
      rewrite (split_cont_nil_left H) in H3.
      exists U1, L1, L4. repeat split; eauto.
    + assert (H12 : binds x1 (lin pretype_bool) L1).
      inversion H1_. subst. eapply split_cont_binds_left; eauto.
      pose proof (typing_store_dealloc_bval _ _ H2 H9 H12) as H13.
      pose proof (typing_store_uniq_cont H2) as H14.
      destruct (proj1 (uniq_app_iff _ _ _) H14) as [H15 [H16 H17]].
      exists U1, (dealloc L x1 L1), (dealloc L x1 L0). repeat split; eauto.
      * eapply typing_dealloc_fvar; eauto.
      * eapply split_cont_remove_left; eauto.
        inversion H1_. subst. eapply split_cont_binds_left; eauto.
      * eapply uniq_submap_app; eauto using submap_assoc_remove, assoc_remove_uniq.
  - destruct (split_cont_assoc_left H3 H) as [M1 [H10 H11]].
    destruct (IHtyping1 _ _ _ _ _ H2 H10 H8) as [V1 [M2 [M3 [H12 [H13 [H14 [H15 H16]]]]]]].
    destruct (split_cont_assoc_right H14 H11) as [M4 [H17 H18]].
    destruct (split_cont_uniq H) as [H19 [H20 H21]].
    pose proof (typing_exact_un H12) as H22.
    pose proof (split_cont_subcont_right H18) as H23.
    pose proof (split_cont_subcont_left H17) as H24.
    pose proof (submap_trans H23 H24) as H25.
    pose proof (uniq_submap_app _ H25 H21 H16).
    exists V1, M2, M4. intuition eauto using typing_weaken_un_subcont.
  - apply split_cont_comm in H.
    destruct (split_cont_assoc_left H3 H) as [M1 [H12 H13]].
    destruct (IHtyping2 _ _ _ _ _ H2 H12 H8) as [V1 [M2 [M3 [H14 [H15 [H16 [H17 H18]]]]]]].
    destruct (split_cont_assoc_right H16 H13) as [M4 [H19 H20]].
    destruct (split_cont_uniq H) as [H21 [H22 H23]].
    apply split_cont_comm in H20.
    pose proof (typing_exact_un H14) as H24.
    pose proof (split_cont_subcont_left H20) as H25.
    pose proof (split_cont_subcont_left H19) as H26.
    pose proof (submap_trans H25 H26) as H27.
    pose proof (uniq_submap_app _ H27 H23 H18).
    exists V1, M2, M4. intuition eauto using typing_weaken_un_subcont.
  - pose proof (split_cont_assoc_left H3 H) as [M1 [H10 H11]].
    destruct (typing_store_invert_arr _ H8 H10 H2 H1_) as [e1 H12].
    inversion H12. subst. clear H12. destruct q1.
    + assert (L2 = nil) by (inversion H1_; auto). subst.
      pose proof (split_cont_nil_left H). subst.
      pose proof (split_cont_nil_left H10). subst.
      pose proof (typing_store_uniq_cont H2).
      assert (binds x1 (un (pretype_arr T1 T2)) U1) as H12. inversion H1_; auto.
      pose proof (typing_store_binds_un _ _ _ H2 H8 H12) as H13.
      exists U1, M1, L4. repeat split; auto.
      inversion H13; subst; pick fresh z1.
      * rewrite subst_open_intro with (x1 := z1) by auto.
        eapply typing_subst_un; eauto.
      * rewrite subst_open_intro with (x1 := z1) by auto.
        eapply typing_subst_lin; eauto.
    + inversion H1_. subst.
      assert (binds x1 (lin (pretype_arr T1 T2)) L1) as H12.
      eapply split_cont_binds_left; eauto.
      destruct (typing_store_binds_lin _ _ _ H2 H8 H12) as [F1 [F2 [H13 [H14 H15]]]].
      assert (H16 : binds x1 (lin (pretype_arr T1 T2)) L0).
      eapply split_cont_binds_left; eauto.
      pose proof (split_cont_remove_left _ _ H16 H3) as H17.
      pose proof (split_cont_assoc_right H14 H17) as [F3 [H18 H19]].
      pose proof (typing_store_uniq_cont H13) as H20.
      exists U1, F1, F3. repeat split; eauto.
      inversion H15; subst; pick fresh z1.
      * pose proof (typing_fvar_un H1_0). subst.
        pose proof (split_cont_nil_right H). subst.
        rewrite subst_open_intro with (x1 := z1) by auto.
        eapply typing_subst_un; eauto. destruct_eq_decs. congruence.
      * rewrite subst_open_intro with (x1 := z1) by auto.
        eapply typing_subst_lin; eauto.
        eapply split_cont_remove_left with (x1 := x1) in H; eauto.
        simpl in H. destruct_eq_decs; [| congruence].
        rewrite (split_cont_nil_left H). assumption.
  - destruct (typing_store_notin_cont H11 H2) as [H13 H14].
    destruct (split_cont_notin H14 H3) as [H15 H16].
    destruct (split_cont_exact_lin H3) as [H17 [H18 H19]].
    destruct (split_cont_uniq H3) as [H20 [H21 H22]].
    pose proof (typing_store_uniq_cont H2) as H23.
    destruct q1; inversion H; subst.
    + exists ((x1 ~ un (pretype_arr (un P1) T2)) ++ U1), L1, nil.
      repeat split; simpl_env; eauto.
      * rewrite_env (nil ++ (x1 ~ un (pretype_arr (un P1) T2)) ++ U1).
        constructor; eauto.
      * rewrite <- (split_cont_nil_left H3) in H3. eauto.
    + exists U1, ((x1 ~ lin (pretype_arr (un P1) T2)) ++ L3), (x1 ~ lin (pretype_arr (un P1) T2)).
      repeat split; simpl_env; eauto.
      * econstructor; solve_uniq.
      * econstructor; eauto using split_cont_left_nil.
      * eapply uniq_permute. eapply Permutation_middle. simpl.
        pose proof (split_cont_subcont_right H3).
        constructor; eauto using uniq_submap_app.
  - destruct (typing_store_notin_cont H11 H2) as [H13 H14].
    destruct (split_cont_notin H14 H3) as [H15 H16].
    destruct (split_cont_exact_lin H3) as [H17 [H18 H19]].
    destruct (split_cont_uniq H3) as [H20 [H21 H22]].
    pose proof (typing_store_uniq_cont H2) as H23.
    destruct q1; inversion H; subst.
    + exists ((x1 ~ un (pretype_arr (lin P1) T2)) ++ U1), L1, nil.
      repeat split; simpl_env; eauto.
      * rewrite_env (nil ++ (x1 ~ un (pretype_arr (lin P1) T2)) ++ U1).
        constructor; eauto.
      * rewrite <- (split_cont_nil_left H3) in H3. eauto.
    + exists U1, ((x1 ~ lin (pretype_arr (lin P1) T2)) ++ L3), (x1 ~ lin (pretype_arr (lin P1) T2)).
      repeat split; simpl_env; eauto.
      * econstructor; solve_uniq.
      * econstructor; eauto using split_cont_left_nil.
      * eapply uniq_permute. eapply Permutation_middle. simpl.
        pose proof (split_cont_subcont_right H3).
        constructor; eauto using uniq_submap_app.
Qed.

Theorem eval_step_preservation : forall S1 S2 U1 L1 e1 e2 T1,
    typing U1 L1 e1 T1 ->
    typing_store S1 U1 L1 ->
    eval_step S1 e1 S2 e2 -> exists U2 L2, typing U2 L2 e2 T1 /\
                                           typing_store S2 U2 L2.
Proof.
  intros S1 S2 U1 L1 e1 e2 T1 H1 H2 H3.
  pose proof (typing_uniq H1) as H4.
  pose proof (typing_exact_lin H1) as H5.
  apply uniq_app_iff in H4 as [H6 [H7 H8]].
  pose proof (split_cont_right_nil H7 H5) as H9.
  destruct (eval_step_preservation_split H1 H2 H9 H3)
    as [U2 [L4 [L5 [H10 [H11 [H12 H13]]]]]].
  rewrite (split_cont_nil_right H12) in H11. eauto.
Qed.
