Require Import Metalib.Metatheory.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Equality.
Require Import Linear.Language.
Require Import Linear.Environment.
Require Import Linear.Infrastructure.
Require Import Linear.Data.AssocList.
Require Import Linear.Data.Permutation.
Require Import Linear.Data.Subsequence.
Require Import Linear.Properties.Structural.
Require Import Linear.Properties.Soundness.

Set Implicit Arguments.

(* Context Difference *)

Inductive diff_cont : cont -> cont -> cont -> Prop :=
  | diff_cont_nil : forall E1,
      uniq E1 ->
      diff_cont E1 nil E1
  | diff_cons_un : forall E1 E2 E3 x1 P1,
      x1 `notin` dom E2 ->
      binds x1 (un P1) E3 ->
      diff_cont E1 E2 E3 ->
      diff_cont E1 ((x1 ~ un P1) ++ E2) (assoc_remove x1 E3)
  | diff_cons_lin : forall E1 E2 E3 x1 P1,
      x1 `notin` dom E2 ->
      x1 `notin` dom E3 ->
      diff_cont E1 E2 E3 ->
      diff_cont E1 ((x1 ~ lin P1) ++ E2) E3.

Hint Constructors diff_cont.

(* Algorithmic Typing Relation *)

Inductive typing_alg : cont -> term -> type -> cont -> Prop :=
  | typing_alg_unvar : forall E1 E2 x1 P1,
      uniq (E1 ++ E2) ->
      x1 `notin` dom (E1 ++ E2) ->
      typing_alg (E1 ++ (x1 ~ un P1) ++ E2) x1 (un P1) (E1 ++ (x1 ~ un P1) ++ E2)
  | typing_alg_linvar : forall E1 E2 x1 P1,
      uniq (E1 ++ E2) ->
      x1 `notin` dom (E1 ++ E2) ->
      typing_alg (E1 ++ (x1 ~ lin P1) ++ E2) x1 (lin P1) (E1 ++ E2)
  | typing_alg_bool : forall E1 q1 b1,
      uniq E1 ->
      typing_alg E1 (term_bval q1 b1) (type_qual q1 pretype_bool) E1
  | typing_alg_cond : forall E1 E2 E3 e1 e2 e3 q1 T1,
      typing_alg E1 e1 (type_qual q1 pretype_bool) E2 ->
      typing_alg E2 e2 T1 E3 ->
      typing_alg E2 e3 T1 E3 ->
      typing_alg E1 (term_cond e1 e2 e3) T1 E3
  | typing_alg_app : forall E1 E2 E3 e1 e2 q1 T1 T2,
      typing_alg E1 e1 (type_qual q1 (pretype_arr T1 T2)) E2 ->
      typing_alg E2 e2 T1 E3 ->
      typing_alg E1 (term_app e1 e2) T2 E3
  | typing_alg_abs_un : forall A1 E1 (* E2 *) e1 T1 T2,
      (forall x1, x1 `notin` A1 ->
                  exists E2, diff_cont E2 (x1 ~ T1) E1 /\
                             typing_alg ((x1 ~ T1) ++ E1) (e1 ^^ x1) T2 E2) ->
      typing_alg E1 (term_abs U T1 e1) (un (pretype_arr T1 T2)) E1
  | typing_alg_abs_lin : forall A1 E1 (* E2 *) E3 e1 T1 T2,
      (forall x1, x1 `notin` A1 ->
                  exists E2, diff_cont E2 (x1 ~ T1) E3 /\
                             typing_alg ((x1 ~ T1) ++ E1) (e1 ^^ x1) T2 E2) ->
      typing_alg E1 (term_abs L T1 e1) (lin (pretype_arr T1 T2)) E3.

Hint Constructors typing_alg.

(* Induction Principle for Algorithmic Typing Relation *)

Lemma typing_alg_induction : forall (P : cont -> term -> type -> cont -> Prop),
    (forall E1 E2 x1 P1,
        uniq (E1 ++ E2) ->
        x1 `notin` dom (E1 ++ E2) ->
        P (E1 ++ (x1 ~ un P1) ++ E2) x1 (un P1) (E1 ++ (x1 ~ un P1) ++ E2)) ->
    (forall E1 E2 x1 P1,
        uniq (E1 ++ E2) ->
        x1 `notin` dom (E1 ++ E2) ->
        P (E1 ++ (x1 ~ lin P1) ++ E2) x1 (lin P1) (E1 ++ E2)) ->
    (forall E1 q1 b1,
        uniq E1 ->
        P E1 (term_bval q1 b1) (type_qual q1 pretype_bool) E1) ->
    (forall E1 E2 E3 e1 e2 e3 q1 T1,
        typing_alg E1 e1 (type_qual q1 pretype_bool) E2 ->
        typing_alg E2 e2 T1 E3 ->
        typing_alg E2 e3 T1 E3 ->
        P E1 e1 (type_qual q1 pretype_bool) E2 ->
        P E2 e2 T1 E3 ->
        P E2 e3 T1 E3 ->
        P E1 (term_cond e1 e2 e3) T1 E3) ->
    (forall E1 E2 E3 e1 e2 q1 T1 T2,
        typing_alg E1 e1 (type_qual q1 (pretype_arr T1 T2)) E2 ->
        typing_alg E2 e2 T1 E3 ->
        P E1 e1 (type_qual q1 (pretype_arr T1 T2)) E2 ->
        P E2 e2 T1 E3 ->
        P E1 (term_app e1 e2) T2 E3) ->
    (forall A1 E1 e1 T1 T2,
        (forall x1, x1 `notin` A1 ->
                    exists E2, diff_cont E2 (x1 ~ T1) E1 /\
                               typing_alg ((x1 ~ T1) ++ E1) (e1 ^^ x1) T2 E2 /\
                               P ((x1 ~ T1) ++ E1) (e1 ^^ x1) T2 E2) ->
        P E1 (term_abs U T1 e1) (un (pretype_arr T1 T2)) E1) ->
    (forall A1 E1 E3 e1 T1 T2,
        (forall x1, x1 `notin` A1 ->
                    exists E2, diff_cont E2 (x1 ~ T1) E3 /\
                               typing_alg ((x1 ~ T1) ++ E1) (e1 ^^ x1) T2 E2 /\
                               P ((x1 ~ T1) ++ E1) (e1 ^^ x1) T2 E2) ->
        P E1 (term_abs L T1 e1) (lin (pretype_arr T1 T2)) E3) ->
    forall E1 e1 T1 E2, typing_alg E1 e1 T1 E2 -> P E1 e1 T1 E2.
Proof.
  intros P IH1 IH2 IH3 IH4 IH5 IH6 IH7.
  refine (fix F E1 e1 T1 E2 IH {struct IH} : P E1 e1 T1 E2 :=
            match IH with
            | @typing_alg_unvar E1 E2 x1 P1 H1 H2                => IH1 E1 E2 x1 P1 H1 H2
            | @typing_alg_linvar E1 E2 x1 P1 H1 H2               => IH2 E1 E2 x1 P1 H1 H2
            | @typing_alg_bool E1 q1 b1 H1                       => IH3 E1 q1 b1 H1
            | @typing_alg_cond E1 E2 E3 e1 e2 e3 q1 T1 H1 H2 H3  =>
              IH4 E1 E2 E3 e1 e2 e3 q1 T1 H1 H2 H3
                  (F E1 e1 (type_qual q1 (pretype_bool)) E2 H1)
                  (F E2 e2 T1 E3 H2)
                  (F E2 e3 T1 E3 H3)
            | @typing_alg_app E1 E2 E3 e1 e2 q1 T1 T2 H1 H2      =>
              IH5 E1 E2 E3 e1 e2 q1 T1 T2 H1 H2
                  (F E1 e1 (type_qual q1 (pretype_arr T1 T2)) E2 H1)
                  (F E2 e2 T1 E3 H2)
            | @typing_alg_abs_un A1 E1 e1 T1 T2 H1               => _
            | @typing_alg_abs_lin A1 E1 E3 e1 T1 T2 H1           => _
            end).
  - pick fresh z1 for A1. apply (IH6 A1 E1 e1 T1 T2). intros z2 H2.
    destruct (H1 z2 H2) as [F1 [? ?]]. exists F1; auto.
  - pick fresh z1 for A1. apply (IH7 A1 E1 E3 e1 T1 T2). intros z2 H2.
    destruct (H1 z2 H2) as [F1 [? ?]]. exists F1; auto.
Qed.

(* Properties of Context Difference *)

Lemma diff_cont_uniq : forall E1 E2 E3,
    diff_cont E1 E2 E3 ->
    uniq E1 /\ uniq E2 /\ uniq E3.
Proof.
  induction 1; intuition eauto using assoc_remove_uniq.
Qed.

Lemma diff_cont_binds : forall E1 E2 E3 x1 T1,
    binds x1 T1 E3 ->
    diff_cont E1 E2 E3 ->
    binds x1 T1 E1 /\ x1 `notin` dom E2.
Proof.
  intros E1 E2 E3 x1 T1 H1 H2. induction H2; auto.
  - apply assoc_remove_binds in H1 as [H3 H4].
    destruct (IHdiff_cont H4) as [H5 H6]. auto.
  - destruct (x0 == x1) as [| H3]; subst.
    + exfalso. eapply binds_dom_contradiction; eauto.
    + destruct (IHdiff_cont H1) as [H4 H5]. auto.
Qed.

Lemma diff_cont_subseq : forall E1 E2 E3,
    diff_cont E1 E2 E3 ->
    subsequence E3 E1.
Proof.
  induction 1; eauto.
  - apply subseq_refl.
  - apply subseq_assoc_remove. auto.
Qed.

Lemma diff_cont_equate_disjoint : forall E1 E2 E3,
    disjoint E1 E2 ->
    diff_cont E1 E2 E3 ->
    E1 = E3.
Proof.
  intros E1 E2 E3 H1 H2. induction H2; auto.
  - assert (H3 : disjoint E1 E2) by solve_uniq.
    assert (H4 : x1 `notin` dom E1) by solve_uniq.
    rewrite (IHdiff_cont H3) in H4.
    exfalso. eapply binds_dom_contradiction; eauto.
  - rewrite IHdiff_cont; solve_uniq.
Qed.

Lemma split_cont_subseq_left : forall L1 L2 L3,
    split_cont L1 L2 L3 ->
    subsequence L2 L1.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma split_cont_subseq_right : forall L1 L2 L3,
    split_cont L1 L2 L3 ->
    subsequence L3 L1.
Proof.
  induction 1; simpl; auto.
Qed.

(* Basic Properties of Algorithmic Typing Relation *)

Lemma typing_alg_uniq_left : forall E1 E2 e1 T1,
    typing_alg E1 e1 T1 E2 ->
    uniq E1.
Proof.
  intros E1 E2 e1 T1 H1.
  induction H1 using typing_alg_induction; auto.
  - pick fresh z1 for A1. destruct (H z1 Fr) as [? [? [? H1]]]. solve_uniq.
  - pick fresh z1 for A1. destruct (H z1 Fr) as [? [? [? H1]]]. solve_uniq.
Qed.

Lemma typing_alg_uniq_right : forall E1 E2 e1 T1,
    typing_alg E1 e1 T1 E2 ->
    uniq E2.
Proof.
  intros E1 E2 e1 T1 H1.
  induction H1 using typing_alg_induction; auto.
  - pick fresh z1 for A1. destruct (H z1 Fr) as [? [H1 ?]].
    destruct (diff_cont_uniq H1) as [? [? ?]]. auto.
  - pick fresh z1 for A1. destruct (H z1 Fr) as [? [H1 ?]].
    destruct (diff_cont_uniq H1) as [? [? ?]]. auto.
Qed.

(* Monotonicity of Algorithmic Typing Relation *)

Theorem typing_alg_monotone_un : forall E1 E2 e1 T1,
    typing_alg E1 e1 T1 E2 ->
    env_un E1 = env_un E2.
Proof.
  intros E1 E2 e1 T1 H1.
  induction H1 using typing_alg_induction; auto.
  - repeat rewrite env_app. simpl. auto.
  - transitivity (env U E2); auto.
  - transitivity (env U E2); auto.
  - pick fresh z1 for A1.
    destruct (H z1 Fr) as [E2 [H1 [H2 H3]]].
    pose proof (typing_alg_uniq_left H2).
    inversion H1; inversion H11; subst; auto.
    rewrite <- assoc_remove_env_comm.
    eapply assoc_remove_swap_cons.
    + apply env_notin. solve_uniq. 
    + apply H3.
Qed.

Theorem typing_alg_subseq : forall E1 E2 e1 T1,
    typing_alg E1 e1 T1 E2 ->
    subsequence E2 E1.
Proof.
  intros E1 E2 e1 T1 H1.
  induction H1 using typing_alg_induction;
    try solve [eapply subseq_refl];
    try solve [eapply subseq_trans; eauto].
  - apply subseq_cons_mid, subseq_refl.
  - pick fresh z1.
    assert (H1 : z1 `notin` A1) by auto.
    destruct (H z1 H1) as [E2 [H2 [H3 H4]]].
    inversion H2; inversion H11; subst.
    + assert (H13 : z1 `notin` dom E1) by auto.
      apply assoc_remove_subseq_both with (x1 := z1) in H4.
      rewrite <- (assoc_remove_notin _ H13).
      destruct_eq_decs; congruence.
    + assert (H13 : z1 `notin` dom E3) by auto.
      eapply subseq_remove_left_notin; eauto.
Qed.

Theorem typing_alg_monotone_lin : forall E1 E2 e1 T1,
    typing_alg E1 e1 T1 E2 ->
    subsequence (env_lin E2) (env_lin E1).
Proof.
  intros E1 E2 e1 T1 H1.
  eapply subseq_env, typing_alg_subseq; eauto.
Qed.

(* Algorithmic Typing Relation Satisfies Soundness *)

Lemma algorithmic_soundness_diff : forall E1 E2 E3 e1 T1,
    typing_alg E1 e1 T1 E2 ->
    diff_list (env_lin E1) (env_lin E2) = E3 ->
    typing (env_un E1) E3 e1 T1.
Proof.
  intros E1 E2 E3 e1 T1 H1 H2.
  generalize dependent E3.
  induction H1 using typing_alg_induction; intros E4 H1.
  - rewrite diff_list_nil in H1. subst.
    rewrite env_app. simpl. constructor.
    + rewrite <- env_app. apply well_formed_cont_env_un; auto.
    + rewrite <- env_app. apply env_notin; auto.
  - repeat rewrite env_app in H1. simpl in H1.
    rewrite diff_list_equate_mid in H1.
    + subst. rewrite env_app. simpl. constructor.
      * rewrite <- env_app. apply well_formed_cont_env_un; auto.
      * rewrite <- env_app. apply env_notin; auto.
    + rewrite <- env_app. apply env_notin; auto.
  - rewrite diff_list_nil in H1. subst. constructor.
    + apply well_formed_cont_env_un; auto.
  - rewrite <- H1. econstructor.
    + eapply split_cont_subseq_diff.
      * eapply env_uniq, (typing_alg_uniq_left H1_).
      * apply qual_cont_exact_env.
      * eapply subseq_env, (typing_alg_subseq H1_0).
      * eapply subseq_env, (typing_alg_subseq H1_).
    + eapply IHtyping_alg1; auto.
    + eapply typing_weaken_un_subseq.
      * eapply subseq_env, (typing_alg_subseq H1_).
      * eapply qual_cont_exact_env.
      * eapply uniq_subseq_app.
        -- apply subseq_diff_left, subseq_env, (typing_alg_subseq H1_).
        -- apply diff_list_uniq, env_uniq, (typing_alg_uniq_right H1_).
        -- apply env_uniq_app, (typing_alg_uniq_left H1_).
      * eapply IHtyping_alg2; auto.
    + eapply typing_weaken_un_subseq.
      * eapply subseq_env, (typing_alg_subseq H1_).
      * eapply qual_cont_exact_env.
      * eapply uniq_subseq_app.
        -- apply subseq_diff_left, subseq_env, (typing_alg_subseq H1_).
        -- apply diff_list_uniq, env_uniq, (typing_alg_uniq_right H1_).
        -- apply env_uniq_app, (typing_alg_uniq_left H1_).
      * eapply IHtyping_alg3; auto.
  - rewrite <- H1. econstructor.
    + eapply split_cont_subseq_diff.
      * eapply env_uniq, (typing_alg_uniq_left H1_).
      * apply qual_cont_exact_env.
      * eapply subseq_env, (typing_alg_subseq H1_0).
      * eapply subseq_env, (typing_alg_subseq H1_).
    + eapply IHtyping_alg1; auto.
    + eapply typing_weaken_un_subseq.
      * eapply subseq_env, (typing_alg_subseq H1_).
      * apply qual_cont_exact_env.
      * eapply uniq_subseq_app.
        -- apply subseq_diff_left, subseq_env, (typing_alg_subseq H1_).
        -- apply diff_list_uniq, env_uniq, (typing_alg_uniq_right H1_).
        -- apply env_uniq_app, (typing_alg_uniq_left H1_).
      * eapply IHtyping_alg2; auto.
  - rewrite diff_list_nil in H1. subst. destruct T1 as [[] P1].
    + pick fresh z1 and apply typing_abs_un.
      * pick fresh z1 for A1.
        destruct (H z1 Fr) as [F1 [H1 [H2 H3]]].
        destruct (diff_cont_uniq H1) as [H4 [H5 H6]].
        apply well_formed_cont_env_un; auto.
      * assert (H1 : z1 `notin` A1) by auto.
        destruct (H z1 H1) as [F1 [H2 [H3 H4]]].
        apply H4; simpl. apply diff_list_subseq_nil.
        apply (subseq_env L (diff_cont_subseq H2)).
    + pick fresh z1 and apply typing_abs_lin.
      * pick fresh z1 for A1.
        destruct (H z1 Fr) as [F1 [H1 [H2 H3]]].
        destruct (diff_cont_uniq H1) as [H4 [H5 H6]].
        apply well_formed_cont_env_un; auto.
      * assert (H1 : z1 `notin` A1) by auto.
        destruct (H z1 H1) as [F1 [H2 [H3 H4]]].
        apply H4; simpl. rewrite diff_list_notin_cons.
        -- f_equal. apply diff_list_subseq_nil.
           apply (subseq_env L (diff_cont_subseq H2)).
        -- inversion H2. inversion H11. apply env_notin; auto.
  - destruct T1 as [[] P1].
    + pick fresh z1 and apply typing_abs_un.
      * pick fresh z1 for A1.
        destruct (H z1 Fr) as [F1 [H2 [H3 H4]]]. constructor.
        -- pose proof (typing_alg_uniq_left H3) as H5.
           inversion H5. subst. eapply uniq_subseq_app.
           ++ apply subseq_diff_left, subseq_refl.
           ++ apply diff_list_uniq, env_uniq, H7.
           ++ apply env_uniq_app, H7.
        -- apply qual_cont_exact_env.
        -- rewrite <- H1. apply qual_cont_exact_diff.
           apply qual_cont_exact_env.
      * assert (H2 : z1 `notin` A1) by auto.
        assert (H3 : z1 `notin` dom E1) by auto.
        destruct (H z1 H2) as [F1 [H4 [H5 H6]]].
        apply H6. simpl. inversion H4. inversion H13. subst.
        -- pose proof (env_notin _ L H3) as H15.
           rewrite <- assoc_remove_env_comm.
           rewrite (diff_list_notin_remove _ _ H15). auto.
    + pick fresh z1 and apply typing_abs_lin.
      * pick fresh z1 for A1.
        destruct (H z1 Fr) as [F1 [H2 [H3 H4]]]. constructor.
        -- pose proof (typing_alg_uniq_left H3) as H5.
           inversion H5. subst. eapply uniq_subseq_app.
           ++ apply subseq_diff_left, subseq_refl.
           ++ apply diff_list_uniq, env_uniq, H7.
           ++ apply env_uniq_app, H7.
        -- apply qual_cont_exact_env.
        -- rewrite <- H1. apply qual_cont_exact_diff.
           apply qual_cont_exact_env.
      * assert (H2 : z1 `notin` A1) by auto.
        assert (H3 : z1 `notin` dom E3) by auto.
        destruct (H z1 H2) as [F1 [H4 [H5 H6]]].
        apply H6. simpl. inversion H4. inversion H13. subst.
        -- pose proof (env_notin _ L H3) as H15.
           rewrite diff_list_notin_cons; auto.
Qed.
           
Theorem algorithmic_soundness : forall E1 e1 T1 E2,
    typing_alg E1 e1 T1 E2 ->
    env_lin E2 = nil ->
    typing (env_un E1) (env_lin E1) e1 T1.
Proof.
  intros E1 e1 T1 E2 H1 H2.
  eapply algorithmic_soundness_diff.
  - apply H1.
  - rewrite H2. reflexivity.
Qed.

(* Algorithmic Typing Relation Satisfies Exchange *)

Definition respectful_permutations (E1 F1 E2 F2 : cont) : Prop :=
  Permutation E1 E2 /\
  Permutation F1 F2 /\
  subsequence F1 E1 /\
  subsequence F2 E2.

Lemma uniq_nodup : forall A (E1 : list (atom * A)),
    uniq E1 ->
    NoDup E1.
Proof.
  induction 1; constructor; auto.
  - intros H1. exfalso. eapply binds_dom_contradiction; eauto.
Qed.

Lemma uniq_permutation : forall A (E1 E2 : list (atom * A)),
    uniq E1 ->
    uniq E2 ->
    (forall x1 T1, binds x1 T1 E1 <-> binds x1 T1 E2) ->
    Permutation E1 E2.
Proof.
  intros A E1 E2 H1 H2 H3. apply NoDup_Permutation.
  - apply (uniq_nodup H1).
  - apply (uniq_nodup H2).
  - intros [x1 T1]. apply (H3 x1 T1).
Qed.

Lemma permute_diff_remainder : forall A (E1 E2 F2 : list (atom * A)),
    uniq E2 ->
    subsequence E1 E2 ->
    Permutation E2 F2 ->
    Permutation (diff_list F2 (diff_list E2 E1)) E1.
Proof.
  intros A E1 E2 F2 H1 H2 H3.
  pose proof (subseq_uniq H1 H2) as H4.
  pose proof (uniq_permute H3 H1) as H5.
  apply uniq_permutation; auto.
  - apply diff_list_uniq; auto.
  - intros x1 T1. split; intros H6.
    + apply diff_list_binds_spec in H6 as [H6 H7]; auto.
      apply diff_list_notin_spec in H7 as [H7 | H7].
      * pose proof (notin_permute H3 H7).
        exfalso. eapply binds_dom_contradiction; eauto.
      * apply binds_In_inv in H7 as [T2 H7].
        pose proof (subseq_binds H2 _ _ H7) as H8.
        pose proof (binds_permute _ _ H3 H8) as H9.
        rewrite (binds_unique _ _ _ _ _ H6 H9 H5). auto.
    + apply diff_list_binds_spec. split.
      * eapply binds_permute; eauto.
        eapply subseq_binds; eauto.
      * apply binds_In in H6.
        apply diff_list_notin_spec; auto.
Qed.

Lemma subseq_diff_remainder_disjoint : forall (E1 E2 E3 : cont),
    subsequence E1 E2 ->
    (forall x1 T1, binds x1 T1 E3 -> x1 `notin` dom E1) ->
    subsequence E1 (diff_list E2 E3).
Proof.
  intros E1 E2 E3 H1 H2.
  induction H1 as [| [x1 T1] | [x1 T1]]; auto.
  - destruct (notin_dec E3 x1) as [H3 | [T2 H3]].
    + rewrite diff_list_notin_cons; auto.
    + rewrite diff_list_binds_cons; eauto using binds_In.
  - destruct (notin_dec E3 x1) as [H3 | [T2 H3]].
    + rewrite diff_list_notin_cons; auto.
      apply subseq_both, IHsubsequence.
      intros x2 T2 H4. apply H2 in H4. auto.      
    + apply H2 in H3. analyze_binds H3.
Qed.

Lemma subseq_diff_remainder : forall (E1 E2 E3 F1 F3 : cont),
    uniq E3 ->
    Permutation E1 F1 ->
    Permutation E3 F3 ->
    subsequence F1 F3 ->
    subsequence E1 E2 ->
    subsequence E2 E3 ->
    subsequence F1 (diff_list F3 (diff_list E3 E2)).
Proof.
  intros E1 E2 E3 F1 F3 H1 H2 H3 H4 H5 H6.
  apply subseq_diff_remainder_disjoint; auto.
  intros x1 T1 H7. apply diff_list_binds_spec in H7 as [H7 H8].
  eapply notin_permute; eauto. eapply subseq_notin_reverse; eauto.
Qed.

Lemma exists_respectful_reordering : forall (E1 E2 E3 F1 F3 : cont),
    uniq E3 ->
    Permutation E1 F1 ->
    Permutation E3 F3 ->
    subsequence F1 F3 ->
    subsequence E1 E2 ->
    subsequence E2 E3 ->
    exists F2, Permutation F2 E2 /\
               subsequence F1 F2 /\
               subsequence F2 F3.
Proof.
  intros E1 E2 E3 F1 F3 H1 H2 H3 H4 H5 H6.
  exists (diff_list F3 (diff_list E3 E2)). repeat split.
  - apply permute_diff_remainder; auto.
  - eapply subseq_diff_remainder; eauto.
  - apply diff_list_subseq.
Qed.

Lemma diff_cont_permute_right_one : forall E1 E3 F3 x1 T1,
    Permutation E3 F3 ->
    subsequence E1 ((x1 ~ T1) ++ E3) ->
    diff_cont E1 (x1 ~ T1) E3 ->
    exists F1, diff_cont F1 (x1 ~ T1) F3 /\
               Permutation E1 F1 /\
               subsequence F1 ((x1 ~ T1) ++ F3).
Proof.
  intros E1 E3 F3 x1 T1 H1 H2 H3.
  destruct (diff_cont_uniq H3) as [H4 [H5 H6]].
  pose proof (uniq_permute H1 H6) as H7.
  inversion H3; inversion H13; subst.
  - assert (H8 : x1 `notin` dom F3).
    eapply notin_permute. apply H1.
    apply assoc_remove_notin_eq.
    exists ((x1 ~ un P1) ++ F3). repeat split.
    + rewrite <- (assoc_remove_cons_eq _ (un P1) H8) at 2.
      constructor; auto.
    + destruct (binds_inv _ _ _ H12) as [G1 [G2 H15]]; subst.
      symmetry. apply Permutation_cons_app. symmetry.
      simpl in H1. rewrite assoc_remove_mid_eq in H1; solve_uniq.
    + apply subseq_both, subseq_refl.
  - exists F3. repeat split; auto.
    + pose proof (notin_permute H1 H12).
      constructor; auto.
    + apply subseq_cons, subseq_refl.
Qed.

Lemma diff_cont_subseq_right_one : forall E1 E2 E3 x1 T1,
    x1 `notin` dom E3 ->
    subsequence E1 ((x1 ~ T1) ++ E3) ->
    diff_cont E1 (x1 ~ T1) E2 ->
    subsequence E1 ((x1 ~ T1) ++ E2).
Proof.
  intros E1 E2 E3 x1 T1 H1 H2 H3.
  pose proof (diff_cont_subseq H3) as H4.
  inversion H2; subst; auto.
  - pose proof (subseq_notin_reverse H1 H5) as H6.
    inversion H3; inversion H12; subst.
    + exfalso. eapply binds_dom_contradiction; eauto.
    + apply subseq_cons, subseq_refl.
  - inversion H3; inversion H11; subst.
    + simpl_env. rewrite assoc_remove_cons_eq.
      * apply subseq_both, subseq_refl.
      * inversion H12. auto.
    + analyze_binds H10.
Qed.

Theorem algorithmic_exchange : forall E1 E2 e1 T1 F1 F2,
    typing_alg E1 e1 T1 F1 ->
    respectful_permutations E1 F1 E2 F2 ->
    typing_alg E2 e1 T1 F2.
Proof.
  intros E1 E2 e1 T1 F1 F2 H1 [M1 [M2 [M3 M4]]].
  dependent induction H1 generalizing E2 F2 using typing_alg_induction.
  - destruct (permute_exists_mid _ _ _ M1) as [G1 [G2 [M5 M6]]]. subst.
    destruct (permute_exists_mid _ _ _ M2) as [G3 [G4 [M7 M8]]]. subst.
    pose proof (Permutation_trans (Permutation_sym M2) M1) as M9.
    rewrite (permute_subseq_equal M9 M4). constructor.
    + apply (uniq_permute M6 H).
    + apply (notin_permute M6 H0).
  - destruct (permute_exists_mid _ _ _ M1) as [G1 [G2 [M5 M6]]]. subst.
    pose proof (notin_permute M2 H0) as M7.
    pose proof (subseq_remove_mid_notin _ _ _ M7 M4) as M8.
    pose proof (Permutation_trans (Permutation_sym M2) M6) as M9.
    rewrite (permute_subseq_equal M9 M8). constructor.
    + apply (uniq_permute M6 H).
    + apply (notin_permute M6 H0).
  - pose proof (Permutation_trans (Permutation_sym M2) M1) as M5.
    rewrite (permute_subseq_equal M5 M4). constructor.
    + apply (uniq_permute M1 H).
  - pose proof (typing_alg_subseq H1_) as M5.
    pose proof (typing_alg_subseq H1_0) as M6.
    pose proof (typing_alg_uniq_left H1_) as M7.
    destruct (exists_respectful_reordering M7 M2 M1 M4 M6 M5) as [F1 [M8 [M9 M10]]].
    apply Permutation_sym in M8. eauto.
  - pose proof (typing_alg_subseq H1_) as M5.
    pose proof (typing_alg_subseq H1_0) as M6.
    pose proof (typing_alg_uniq_left H1_) as M7.
    destruct (exists_respectful_reordering M7 M2 M1 M4 M6 M5) as [F1 [M8 [M9 M10]]].
    apply Permutation_sym in M8. eauto.
  - pose proof (Permutation_trans (Permutation_sym M2) M1) as M5.
    rewrite (permute_subseq_equal M5 M4). clear M4 M5.
    pick fresh z1 and apply typing_alg_abs_un.
    destruct (H z1) as [G1 [M4 [M5 M6]]]; auto.
    pose proof (typing_alg_subseq M5) as M7.
    destruct (diff_cont_permute_right_one M1 M7 M4) as [G2 [M8 [M9 M10]]].
    exists G2. split; auto. apply M6; auto.
    + constructor; auto.
  - pick fresh z1 and apply typing_alg_abs_lin.
    destruct (H z1) as [G1 [M5 [M6 M7]]]; auto.
    assert (M8 : z1 `notin` dom E1) by auto.
    pose proof (typing_alg_subseq M6) as M9.
    pose proof (diff_cont_subseq_right_one M8 M9 M5) as M10.
    destruct (diff_cont_permute_right_one M2 M10 M5) as [G2 [M11 [M12 M13]]].
    exists G2. split; auto. apply M7; auto.
    + constructor; auto.
    + apply (subseq_trans M13), subseq_both, M4.
Qed.

(* Algorithmic Typing Relation Satisfies Completeness *)

Lemma algorithmic_completeness_diff : forall U1 L1 L2 L3 e1 T1,
    typing U1 L2 e1 T1 ->
    uniq (U1 ++ L1) ->
    split_cont L1 L2 L3 ->
    typing_alg (U1 ++ L1) e1 T1 (U1 ++ L3).
Proof.
  intros U1 L1 L2 L3 e1 T1 H1 H2 H3.
  dependent induction H1 generalizing L1 L3.
  - pose proof (split_cont_nil_left H3). subst.
    simpl_env. constructor; solve_uniq.
  - assert (H4 : binds x1 (lin P1) (x1 ~ lin P1)) by auto.
    pose proof (split_cont_binds_left _ _ H3 H4) as H5.
    pose proof (split_cont_remove_left _ _ H4 H3) as H6.
    destruct (binds_inv _ _ _ H5) as [F1 [F2 ?]]. subst.
    simpl in H6. destruct (x1 == x1); [| congruence].
    rewrite assoc_remove_mid_eq in H6; [| solve_uniq].
    pose proof (split_cont_nil_left H6). subst.
    rewrite_env ((U1 ++ F1) ++ (x1 ~ lin P1) ++ F2).
    rewrite_env ((U1 ++ F1) ++ F2).
    constructor; solve_uniq.
  - pose proof (split_cont_nil_left H3). subst. auto. 
  - pose proof (split_cont_assoc_left H3 H) as [F1 [H4 ?]].
    pose proof (split_cont_subcont_right H4) as H5.
    pose proof (split_cont_uniq H4) as [? [? H6]].
    pose proof (uniq_submap_app _ H5 H6 H2). eauto.
  - pose proof (split_cont_assoc_left H3 H) as [F1 [H4 ?]].
    pose proof (split_cont_subcont_right H4) as H5.
    pose proof (split_cont_uniq H4) as [? [? H6]].
    pose proof (uniq_submap_app _ H5 H6 H2). eauto.
  - inversion H; subst.
    + pose proof (split_cont_nil_left H3). subst.
      pick fresh z1 and apply typing_alg_abs_un.
      exists ((z1 ~ un P1) ++ U1 ++ L3). split.
      * erewrite <- assoc_remove_cons_eq; auto. constructor; auto.
      * eapply H1; auto. solve_uniq.
    + pick fresh z1 and apply typing_alg_abs_lin.
      exists ((z1 ~ un P1) ++ U1 ++ L3). split.
      * destruct (split_cont_uniq H3) as [H7 [H8 H9]].
        pose proof (split_cont_subcont_right H3) as H10.
        pose proof (uniq_submap_app _ H10 H9 H2) as H11.
        erewrite <- assoc_remove_cons_eq; auto. constructor; auto.
      * eapply H1; auto. solve_uniq.
  - inversion H; subst.
    + pose proof (split_cont_nil_left H3). subst.
      pick fresh z1 and apply typing_alg_abs_un.
      exists (U1 ++ L3). split.
      * constructor; auto.
      * eapply algorithmic_exchange.
        -- eapply H1 with (L1 := (z1 ~ lin P1) ++ L3); eauto.
        -- repeat split; simpl; auto.
           ++ apply Permutation_sym, Permutation_middle.
           ++ apply subseq_cons_mid, subseq_refl.
           ++ apply subseq_cons, subseq_refl.
    + pick fresh z1 and apply typing_alg_abs_lin.
      exists (U1 ++ L3). split.
      * destruct (split_cont_uniq H3) as [H7 [H8 H9]].
        pose proof (split_cont_subcont_right H3) as H10.
        pose proof (uniq_submap_app _ H10 H9 H2) as H11.
        constructor; auto.
      * eapply algorithmic_exchange.
        -- eapply H1 with (L1 := (z1 ~ lin P1) ++ L1); eauto.
        -- repeat split; simpl; auto.
           ++ apply Permutation_sym, Permutation_middle.
           ++ apply subseq_cons_mid, subseq_app_head.
              ** apply subseq_refl.
              ** apply (split_cont_subseq_right H3).
           ++ apply subseq_cons, subseq_app_head.
              ** apply subseq_refl.
              ** apply (split_cont_subseq_right H3).
Qed.

Theorem algorithmic_completeness : forall U1 L1 e1 T1,
    typing U1 L1 e1 T1 ->
    typing_alg (U1 ++ L1) e1 T1 U1.
Proof.
  intros U1 L1 e1 T1 H1. rewrite <- app_nil_r.
  pose proof (typing_uniq H1). destruct_uniq.
  pose proof (typing_exact_lin H1) as H2.
  eapply algorithmic_completeness_diff; eauto.
  eapply split_cont_right_nil; eauto.
Qed.
