Require Import Metalib.Metatheory.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Sorting.Permutation.
Require Import Linear.Language.
Require Import Linear.Environment.
Require Import Linear.Infrastructure.
Require Import Linear.Data.AssocList.
Require Import Linear.Data.Subsequence.
Require Import Linear.Data.Permutation.

Set Implicit Arguments.

(* Basic Properties of Typing Relation *)

Lemma typing_uniq : forall U1 L1 e1 T1,
    typing U1 L1 e1 T1 ->
    uniq (U1 ++ L1).
Proof.
  intros U1 L1 e1 T1 H1; induction H1;
    try match goal with
        | [ H1 : well_formed_cont _ _ _ |- _ ] => inversion H1; subst
        end; simpl_env; auto.
  - pose proof (split_cont_dom H).
    destruct (split_cont_uniq H) as [? [? ?]]. solve_uniq.
  - pose proof (split_cont_dom H).
    destruct (split_cont_uniq H) as [? [? ?]]. solve_uniq.
Qed.

Lemma typing_disjoint : forall U1 L1 e1 T1,
    typing U1 L1 e1 T1 ->
    disjoint U1 L1.
Proof.
  intros U1 L1 e1 T1 H1.
  apply typing_uniq in H1. solve_uniq.
Qed.

Lemma typing_exact_un : forall U1 L1 e1 T1,
    typing U1 L1 e1 T1 ->
    qual_cont_exact U U1.
Proof.
  intros U1 L1 e1 T1 H1; induction H1;
    try match goal with
        | [ H1 : well_formed_cont _ _ _ |- _ ] => inversion H1; subst
        end; auto.
  - eapply qual_cont_exact_permute.
    + eapply Permutation_middle.
    + constructor; auto.
Qed.

Lemma typing_exact_lin : forall U1 L1 e1 T1,
    typing U1 L1 e1 T1 ->
    qual_cont_exact L L1.
Proof.
  intros U1 L1 e1 T1 H1; induction H1;
    try match goal with
        | [ H1 : well_formed_cont _ _ _ |- _ ] => inversion H1; subst
        end; simpl; auto.
  - repeat constructor.
  - destruct (split_cont_exact_lin H) as [? ?]. auto.
  - destruct (split_cont_exact_lin H) as [? ?]. auto.
Qed.

(* Typing Relation Satisfies Exchange *)

Hint Resolve qual_cont_exact_permute      : permutation.
Hint Resolve well_formed_cont_permute_un  : permutation.
Hint Resolve well_formed_cont_permute_lin : permutation.

Theorem typing_exchange_un : forall U1 U2 L1 e1 T1,
    Permutation U1 U2 ->
    typing U1 L1 e1 T1 ->
    typing U2 L1 e1 T1.
Proof.
  intros U1 U2 L1 e1 T1 H1 H2.
  generalize dependent U2; induction H2; intros U3 H2;
    try solve [econstructor; eauto 2 with permutation].
  - apply permute_exists_mid in H2 as [U4 [H3 [H4 H5]]];
      subst; constructor; eauto with permutation.
  - apply typing_abs_un with (A1 := A1).
    + eauto with permutation.
    + intros x1 H3. eapply H1; [| constructor]; eauto.
Qed.

Theorem typing_exchange_lin : forall U1 L1 L2 e1 T1,
    Permutation L1 L2 ->
    typing U1 L1 e1 T1 ->
    typing U1 L2 e1 T1.
Proof.
  intros U1 L1 L2 e1 T1 H1 H2.
  generalize dependent L2; induction H2; intros L4 H2;
  try solve [rewrite (Permutation_nil H2); eauto];
  try solve [apply (split_cont_permute H2) in H as [L5 [L6 [? [? ?]]]]; eauto].
  - rewrite (Permutation_length_1_inv H2). constructor; eauto.
  - apply typing_abs_un with (A1 := A1).
    + eauto with permutation.
    + intros x1 H3. eapply H1; eauto.
  - apply typing_abs_lin with (A1 := A1).
    + eauto with permutation.
    + intros x1 H3. eapply H1; [| constructor]; eauto.
Qed.
    
(* Typing Relation Satisfies Unrestricted Weakening *)

Theorem typing_weaken_un : forall F1 U1 L1 e1 T1,
  qual_cont_exact U F1 ->
  uniq (F1 ++ U1 ++ L1) ->
  typing U1 L1 e1 T1 ->
  typing (F1 ++ U1) L1 e1 T1.
Proof.
  intros F1 U1 L1 e1 T1 H1 H2 H3.
  generalize dependent F1; induction H3; intros F1 H2 H3.
  - rewrite_env ((F1 ++ U1) ++ (x1 ~ un P1) ++ U2).
    inversion H. subst. constructor; [| solve_uniq].
    rewrite_env (F1 ++ (U1 ++ U2)).
    apply well_formed_cont_weaken_un_left; solve_uniq.
  - inversion H. subst. constructor; [| solve_uniq].
    apply well_formed_cont_weaken_un_left; solve_uniq.
  - inversion H. subst. constructor.
    apply well_formed_cont_weaken_un_left; solve_uniq.
  - rewrite_env ((F1 ++ U1) ++ L1) in H3.
    pose proof (split_cont_uniq_app_left _ H H3) as H4. 
    pose proof (split_cont_uniq_app_right _ H H3) as H5.
    simpl_env in H4. simpl_env in H5. eauto.
  - rewrite_env ((F1 ++ U1) ++ L1) in H3.
    pose proof (split_cont_uniq_app_left _ H H3) as H4. 
    pose proof (split_cont_uniq_app_right _ H H3) as H5. 
    simpl_env in H4. simpl_env in H5. eauto.
  - apply typing_abs_un with (A1 := union A1 (dom (F1 ++ U1 ++ L1))).
    + eapply well_formed_cont_weaken_un_left; eauto.
    + intros x1 H4. eapply typing_exchange_un.
      * simpl. symmetry. apply Permutation_middle.
      * apply H1; auto. simpl_env. solve_uniq.
  - apply typing_abs_lin with (A1 := union A1 (dom (F1 ++ U1 ++ L1))).
    + eapply well_formed_cont_weaken_un_left; eauto.
    + intros x1 H4. eapply H1; auto. solve_uniq.
Qed.

Theorem typing_weaken_un_mid : forall F1 U1 U2 L1 e1 T1,
    qual_cont_exact U F1 ->
    uniq (U1 ++ F1 ++ U2 ++ L1) ->
    typing (U1 ++ U2) L1 e1 T1 ->
    typing (U1 ++ F1 ++ U2) L1 e1 T1.
Proof.
  intros F1 U1 U2 L1 e1 T1 H1 H2 H3.
  rewrite_env ((U1 ++ F1) ++ U2).
  eapply typing_exchange_un.
  + apply Permutation_app_tail.
    apply Permutation_app_comm.
  + simpl_env. eapply typing_weaken_un; solve_uniq.
Qed.

Lemma subcont_permute : forall {A : Type} (E1 E2 : list (atom * A)),
    uniq E1 ->
    uniq E2 ->
    submap E1 E2 ->
    exists E3, Permutation E2 (E3 ++ E1).
Proof.
  intros A E1 E2 H1 H2 H3. generalize dependent E2.
  induction E1 as [| [x1 T1] E1 IH]; intros E2 H2 H3.
  - exists E2. simpl_env. auto.
  - assert (H4 : binds x1 T1 ((x1 ~ T1) ++ E1)) by auto.
    apply H3 in H4. apply binds_inv in H4 as [E4 [E5 H5]]; subst.
    assert (H5 : submap E1 (E4 ++ E5)). intros x2 T2 H4.
    assert (H6 : binds x2 T2 ((x1 ~ T1) ++ E1)) by auto.
    apply H3 in H6. apply binds_remove_mid in H6. auto. intros H7.
    inversion H1. subst. eapply binds_dom_contradiction; eauto.
    inversion H1. subst. assert (H8 : uniq (E4 ++ E5)) by solve_uniq.
    destruct (IH H4 _ H8 H5) as [E6 H9]. exists E6. simpl.
    repeat rewrite <- Permutation_middle. auto.
Qed.

Theorem typing_weaken_un_subcont : forall U1 U2 L1 e1 T1,
    subcont U1 U2 ->
    qual_cont_exact U U2 ->
    uniq (U2 ++ L1) ->
    typing U1 L1 e1 T1 ->
    typing U2 L1 e1 T1.
Proof.
  intros U1 U2 L1 e1 T1 H1 H2 H3 H4.
  pose proof (typing_uniq H4) as H5.
  apply uniq_app_iff in H3 as [H6 [H7 H8]].
  apply uniq_app_iff in H5 as [H9 [H10 H11]].
  apply subcont_permute in H1 as [U3 H12]; auto.
  apply (typing_exchange_un (Permutation_sym H12)).
  apply typing_weaken_un; auto.
  - apply (qual_cont_exact_permute H12) in H2.
    apply qual_cont_exact_app_inv in H2 as [H2 H13]. auto.
  - rewrite_env ((U3 ++ U1) ++ L1). eapply uniq_permute.
    + rewrite <- H12. reflexivity.
    + apply uniq_app_iff. repeat split; auto.
Qed.

Theorem typing_weaken_un_subseq : forall U1 U2 L1 e1 T1,
    subsequence U1 U2 ->
    qual_cont_exact U U2 ->
    uniq (U2 ++ L1) ->
    typing U1 L1 e1 T1 ->
    typing U2 L1 e1 T1.
Proof.
  intros U1 U2 L1 e1 T1 H1 H2 H3 H4.
  apply subseq_submap in H1.
  eapply typing_weaken_un_subcont; eauto.
Qed.

(* Typing Relation Satisfies Unrestricted Strengthening *)

Theorem typing_strengthen_un_mid : forall U1 U2 L1 e1 T1 x1 P1,
    x1 `notin` free_vars e1 ->
    typing (U1 ++ (x1 ~ un P1) ++ U2) L1 e1 T1 ->
    typing (U1 ++ U2) L1 e1 T1.
Proof.
  intros U1 U2 L1 e1 T1 x1 P1 H1 H2.
  dependent induction H2; try rename x into H3.
  - simpl in H1. inversion H; subst.
    assert (H5 : x0 <> x1) by auto.
    assert (H6 : uniq (U0 ++ (x0 ~ un P0) ++ U3)) by solve_uniq.
    destruct (assoc_equate_split_uniq _ _ _ _ _ _ H5 H6 H3) as [F1 [F2 [? | ?]]].
    + subst. simpl_env. repeat constructor.
      -- rewrite H3 in H6. solve_uniq.
      -- assert (H7 : qual_cont_exact U (U0 ++ (x0 ~ un P0) ++ U3)).
         eapply qual_cont_exact_weaken_mid; [constructor |]; auto.
         rewrite H3 in H7. apply qual_cont_exact_app_inv in H7 as [H7 H8].
         rewrite_env ((F1 ++ F2) ++ U2). apply qual_cont_exact_weaken_left.
         ++ eapply qual_cont_exact_strengthen_mid; eauto.
         ++ eapply qual_cont_exact_strengthen_left; eauto.
      -- rewrite H3 in H6. solve_uniq.
    + subst. rewrite_env ((U1 ++ F1) ++ (x0 ~ un P0) ++ F2). repeat constructor.
      -- rewrite H3 in H6. solve_uniq.
      -- assert (H7 : qual_cont_exact U (U0 ++ (x0 ~ un P0) ++ U3)).
         eapply qual_cont_exact_weaken_mid; [constructor |]; auto.
         simpl_env. rewrite H3 in H7. rewrite app_assoc in H7.
         apply qual_cont_exact_app_inv in H7 as [H7 H8].
         apply qual_cont_exact_weaken_left.
         ++ eapply qual_cont_exact_strengthen_left.
            eapply qual_cont_exact_permute.
            eapply Permutation_app_comm. eauto.
         ++ eapply qual_cont_exact_strengthen_mid; eauto.
      -- rewrite H3 in H6. solve_uniq.
  - constructor; eauto using well_formed_cont_strengthen_un_mid.
  - constructor; eauto using well_formed_cont_strengthen_un_mid.
  - simpl in H1. econstructor; eauto.
  - simpl in H1. econstructor; eauto.
  - pick fresh z1 and apply typing_abs_un.
    + eapply well_formed_cont_strengthen_un_mid; eauto.
    + rewrite_env (((z1 ~ un P0) ++ U1) ++ U2).
      eapply H2 with (x3 := x1); simpl; eauto.
      eapply free_vars_notin_open; eauto.
  - pick fresh z1 and apply typing_abs_lin.
    + eapply well_formed_cont_strengthen_un_mid; eauto.
    + eapply H2 with (x3 := x1); simpl; auto.
      eapply free_vars_notin_open; eauto.
Qed.

Theorem typing_strengthen_un_left : forall U1 L1 e1 T1 x1 P1,
    x1 `notin` free_vars e1 ->
    typing ((x1 ~ un P1) ++ U1) L1 e1 T1 ->
    typing U1 L1 e1 T1.
Proof.
  intros U1 L1 e1 T1 x1 P1 H1 H2.
  rewrite_env (nil ++ U1).
  eapply typing_strengthen_un_mid; eauto.
Qed.

(* Typing Relation Satisfies Unrestricted Contraction *)

Theorem typing_contract_un_mid : forall U1 U2 L1 x1 x2 x3 e1 P1 T1,
    x3 `notin` dom (U1 ++ U2 ++ L1) ->
    typing (U1 ++ (x1 ~ un P1) ++ (x2 ~ un P1) ++ U2) L1 e1 T1 ->
    typing (U1 ++ (x3 ~ un P1) ++ U2) L1 ([x2 ~> x3] ([x1 ~> x3] e1)) T1.
Proof.
  intros U1 U2 L1 x1 x2 x3 e1 P1 T1 H1 H2.
  dependent induction H2; simpl.
  - rename x into H2. inversion H. subst. destruct_eq_decs.
    + apply assoc_equate_uniq in H2 as [H6 [H7 H8]]; [| solve_uniq].
      inversion H7. subst. constructor; eauto. simpl_env in H.
      eapply well_formed_cont_strengthen_un_mid; eauto.
    + apply assoc_equate_uniq in H2 as [H6 [H7 H8]]; [| solve_uniq].
      inversion H7. subst. constructor; eauto. simpl_env in H.
      eapply well_formed_cont_strengthen_un_mid; eauto.
    + rewrite_env ((U1 ++ (x1 ~ un P1)) ++ (x0 ~ un P1) ++ U2) in H2.
      apply assoc_equate_uniq in H2 as [H6 [H7 H8]]; [| solve_uniq].
      inversion H7. subst. constructor; eauto. simpl_env in H.
      eapply well_formed_cont_strengthen_un_mid; eauto.
    + assert (H5 : x0 <> x1) by auto.
      assert (H6 : uniq (U0 ++ (x0 ~ un P0) ++ U3)) by solve_uniq.
      destruct (assoc_equate_split_uniq _ _ _ _ _ _ H5 H6 H2) as [F1 [F2 [? | ?]]]; subst.
      * simpl_env. repeat constructor.
        -- simpl in H6. rewrite H2 in H6. solve_uniq.
        -- assert (H7 : qual_cont_exact U (x0 ~ un P0)) by (constructor; auto).
           pose proof (qual_cont_exact_weaken_mid _ _ H7 H4) as H8. simpl in H8.
           rewrite H2 in H8. apply qual_cont_exact_app_inv in H8 as [H8 H9].
           rewrite_env ((F1 ++ F2) ++ ((x3 ~ un P1) ++ U2)).
           apply qual_cont_exact_weaken_left.
           ++ eapply qual_cont_exact_strengthen_mid; eauto.
           ++ inversion H9. inversion H12. constructor; auto.
        -- simpl in H6. rewrite H2 in H6. solve_uniq.
      * apply cons_eq_app in H7 as [[F3 [? ?]] | [? ?]]; subst.
        -- rewrite_env ((U1 ++ (x3 ~ un P1) ++ F3) ++ (x0 ~ un P0) ++ F2).
           repeat constructor.
           ++ simpl in H6. rewrite H2 in H6. solve_uniq.
           ++ assert (H7 : qual_cont_exact U (x0 ~ un P0)) by (constructor; auto).
              pose proof (qual_cont_exact_weaken_mid _ _ H7 H4) as H8. simpl in H8.
              rewrite_env ((U1 ++ (x1 ~ un P1) ++ (x2 ~ un P1)) ++ (F3 ++ (x0 ~ un P0) ++ F2)) in H2.
              rewrite H2 in H8. apply qual_cont_exact_app_inv in H8 as [H8 H9].
              rewrite_env ((U1 ++ (x3 ~ un P1)) ++ (F3 ++ F2)).
              apply qual_cont_exact_weaken_left.
              ** apply qual_cont_exact_comm.
                 apply qual_cont_exact_comm in H8.
                 inversion H8. inversion H12. constructor; auto.
              ** eapply qual_cont_exact_strengthen_mid; eauto.
           ++ simpl in H6. rewrite H2 in H6. solve_uniq.
        -- inversion H8. congruence.
  - destruct_eq_decs; try solve [analyze_binds H0].
    inversion H; subst. repeat constructor.
    + solve_uniq.
    + rewrite_env (U1 ++ ((x1 ~ un P1) ++ (x2 ~ un P1)) ++ U2) in H3.
      simpl_env. eapply qual_cont_exact_replace_mid; [constructor |]; eauto.
    + solve_uniq.
  - inversion H. subst. repeat constructor.
    + solve_uniq.
    + rewrite_env (U1 ++ ((x1 ~ un P1) ++ (x2 ~ un P1)) ++ U2) in H2.
      simpl_env. eapply qual_cont_exact_replace_mid; [constructor |]; eauto.
  - repeat rewrite dom_app in H1. rewrite (split_cont_dom H) in H1.    
    econstructor; eauto.
    + eapply IHtyping1; solve_uniq.
    + eapply IHtyping2; solve_uniq.
    + eapply IHtyping3; solve_uniq. 
  - repeat rewrite dom_app in H1. rewrite (split_cont_dom H) in H1.
    econstructor; eauto.
    + eapply IHtyping1; solve_uniq.
    + eapply IHtyping2; solve_uniq.
  - pick fresh z1 and apply typing_abs_un.
    + rewrite_env (U1 ++ ((x1 ~ un P1) ++ (x2 ~ un P1)) ++ U2) in H.
      inversion H; subst; constructor; simpl_env; auto.
      * solve_uniq.
      * eapply qual_cont_exact_replace_mid; [constructor |]; eauto.
      * solve_uniq.
      * eapply qual_cont_exact_replace_mid; [constructor |]; eauto.
    + rewrite_env (((z1 ~ un P0) ++ U1) ++ (x3 ~ un P1) ++ U2).
      repeat rewrite subst_open_var; eauto.
  - pick fresh z1 and apply typing_abs_lin.
    + rewrite_env (U1 ++ ((x1 ~ un P1) ++ (x2 ~ un P1)) ++ U2) in H.
      inversion H; subst; constructor; simpl_env; auto.
      * solve_uniq.
      * eapply qual_cont_exact_replace_mid; [constructor |]; eauto.
      * solve_uniq.
      * eapply qual_cont_exact_replace_mid; [constructor |]; eauto.
    + simpl_env. repeat rewrite subst_open_var; eauto.
Qed.

Theorem typing_contract_un_left : forall U1 L1 x1 x2 x3 e1 P1 T1,
    x3 `notin` dom (U1 ++ L1) ->
    typing ((x1 ~ un P1) ++ (x2 ~ un P1) ++ U1) L1 e1 T1 ->
    typing ((x3 ~ un P1) ++ U1) L1 ([x2 ~> x3] ([x1 ~> x3] e1)) T1.
Proof.
  intros U1 L1 x1 x2 x3 e1 P1 T1 H1 H2.
  rewrite_env (nil ++ (x3 ~ un P1) ++ U1).
  rewrite_env (nil ++ ((x1 ~ un P1) ++ (x2 ~ un P1)) ++ U1) in H2.
  eapply typing_contract_un_mid; eauto.
Qed.
