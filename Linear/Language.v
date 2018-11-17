Require Import Metalib.Metatheory.
Require Import Linear.Data.AssocList.

(* Qualifiers. *)

Inductive qual : Set :=
  | U : qual
  | L : qual.

(* Qualifier Ordering *)

Inductive qual_ord : qual -> qual -> Prop :=
  | qual_base : qual_ord L U
  | qual_refl : forall q1, qual_ord q1 q1.

Hint Constructors qual_ord.

(* Types and Pretypes *)

Inductive type : Set :=
  | type_qual : qual -> pretype -> type
                                   
with pretype : Set :=
  | pretype_bool : pretype
  | pretype_prod : type -> type -> pretype
  | pretype_arr  : type -> type -> pretype.

Notation un P  := (type_qual U P).
Notation lin P := (type_qual L P).
  
(* Typing Contexts *)

Notation cont := (list (atom * type)).

(* Type Occurence Relation *)

Inductive qual_type_exact : qual -> type -> Prop :=
  | qual_type_exact_base : forall q1 P1,
      qual_type_exact q1 (type_qual q1 P1).

Inductive qual_cont_exact : qual -> cont -> Prop :=
  | qual_cont_exact_base : forall q1,
      qual_cont_exact q1 nil
  | qual_cont_exact_cons : forall q1 x1 P1 E1,
      qual_cont_exact q1 E1 ->
      qual_cont_exact q1 ((x1 ~ type_qual q1 P1) ++ E1).

Hint Constructors qual_cont_exact.
Hint Constructors qual_type_exact.

(* Well-Formed Typing Contexts *)

Inductive well_formed_cont : qual -> cont -> cont -> Prop :=
  | well_formed_cont_un : forall U1,
      uniq U1 ->
      qual_cont_exact U U1 ->
      well_formed_cont U U1 nil
  | well_formed_cont_lin : forall U1 L1,
      uniq (U1 ++ L1) ->
      qual_cont_exact U U1 ->
      qual_cont_exact L L1 ->
      well_formed_cont L U1 L1.

Hint Constructors well_formed_cont.

(* Locally Nameless Preterms *)

Inductive term : Set :=
  | term_bvar  : nat -> term
  | term_fvar  : var -> term
  | term_bval  : qual -> bool -> term
  | term_cond  : term -> term -> term -> term
  | term_abs   : qual -> type -> term -> term
  | term_app   : term -> term -> term.

Coercion term_bvar : nat >-> term.
Coercion term_fvar : var >-> term.

(* Free Variables *)

Fixpoint free_vars e1 : vars :=
  match e1 with
  | term_bvar n1       => {}
  | term_fvar x1       => singleton x1
  | term_bval q1 b1    => {}
  | term_cond e1 e2 e3 => free_vars e1 `union` free_vars e2 `union` free_vars e3
  | term_abs q1 T1 e1  => free_vars e1
  | term_app e1 e2     => free_vars e1 `union` free_vars e2
  end.

(* Variable Opening *)

Fixpoint open_rec e1 n1 v1 :=
  match e1 with
  | term_bvar n2       => if n1 == n2 then v1 else term_bvar n2
  | term_fvar x1       => term_fvar x1
  | term_bval q1 b1    => term_bval q1 b1
  | term_cond e1 e2 e3 => term_cond (open_rec e1 n1 v1) (open_rec e2 n1 v1) (open_rec e3 n1 v1)
  | term_abs q1 T1 e1  => term_abs q1 T1 (open_rec e1 (S n1) v1)
  | term_app e1 e2     => term_app (open_rec e1 n1 v1) (open_rec e2 n1 v1)
  end.

Definition open e1 v1 := open_rec e1 0 v1.

Notation "{ n1 ~> v1 } e1" := (open_rec e1 n1 v1) (at level 67, right associativity).
Notation "e1 ^^ v1"        := (open e1 v1) (at level 67, right associativity).

Hint Unfold open.
Hint Unfold open_rec.

(* Nondeterministic Context Split *)

Inductive split_cont : cont -> cont -> cont -> Prop :=
  | split_cont_nil :
      split_cont nil nil nil
  | split_cont_cons_left : forall E1 E2 E3 x1 P1,
      x1 `notin` dom E1 ->
      split_cont E1 E2 E3 ->
      split_cont ((x1 ~ lin P1) ++ E1) ((x1 ~ lin P1) ++ E2) E3
  | split_cont_cons_right : forall E1 E2 E3 x1 P1,
      x1 `notin` dom E1 ->
      split_cont E1 E2 E3 ->
      split_cont ((x1 ~ lin P1) ++ E1) E2 ((x1 ~ lin P1) ++ E3).

Hint Constructors split_cont.

(* Nondeterministic Typing Relation *)

Inductive typing : cont -> cont -> term -> type -> Prop :=
  | typing_fvar_un : forall U1 U2 x1 P1,
      well_formed_cont U (U1 ++ U2) nil ->
      x1 `notin` dom (U1 ++ U2) ->
      typing (U1 ++ (x1 ~ un P1) ++ U2) nil (term_fvar x1) (un P1)
  | typing_fvar_lin : forall U1 x1 P1,
      well_formed_cont U U1 nil ->
      x1 `notin` dom U1 ->
      typing U1 (x1 ~ lin P1) (term_fvar x1) (lin P1)
  | typing_bval : forall U1 q1 b1,
      well_formed_cont U U1 nil ->
      typing U1 nil (term_bval q1 b1) (type_qual q1 pretype_bool)
  | typing_cond : forall U1 L1 L2 L3 e1 e2 e3 q1 T1,
      split_cont L1 L2 L3 ->
      typing U1 L2 e1 (type_qual q1 pretype_bool) ->
      typing U1 L3 e2 T1 ->
      typing U1 L3 e3 T1 ->
      typing U1 L1 (term_cond e1 e2 e3) T1
  | typing_app : forall U1 L1 L2 L3 e1 e2 q1 T1 T2,
      split_cont L1 L2 L3 ->
      typing U1 L2 e1 (type_qual q1 (pretype_arr T1 T2)) ->
      typing U1 L3 e2 T1 ->
      typing U1 L1 (term_app e1 e2) T2
  | typing_abs_un : forall A1 U1 L1 e1 q1 P1 T2,
      well_formed_cont q1 U1 L1 ->
      (forall x1, x1 `notin` A1 ->
                  typing ((x1 ~ un P1) ++ U1) L1 (e1 ^^ x1) T2) ->
      typing U1 L1 (term_abs q1 (un P1) e1) (type_qual q1 (pretype_arr (un P1) T2))
  | typing_abs_lin : forall A1 U1 L1 e1 q1 P1 T2,
      well_formed_cont q1 U1 L1 ->
      (forall x1, x1 `notin` A1 ->
                  typing U1 ((x1 ~ lin P1) ++ L1) (e1 ^^ x1) T2) ->
      typing U1 L1 (term_abs q1 (lin P1) e1) (type_qual q1 (pretype_arr (lin P1) T2)).

Hint Constructors typing.

(* Program Stores *)

Notation store := (list (atom * term)).

(* Substores and Subcontexts *)

Notation subcont  := (@submap type) (only parsing).
Notation substore := (@submap term) (only parsing).

(* Store Variables *)

Fixpoint store_variables (S1 : store) : vars :=
  match S1 with
  | nil            => empty
  | (x1, v1) :: S1 => add x1 (free_vars v1 `union` store_variables S1)
  end.

Hint Unfold store_variables.

(* Fresh Store Variables *)

Inductive fresh_variable : atom -> store -> Prop :=
  | fresh_variable_nil  : forall x1,
      fresh_variable x1 nil
  | fresh_variable_cons : forall x1 x2 v1 S1,
      x1 <> x2 ->
      x1 `notin` free_vars v1 ->
      fresh_variable x1 S1 ->
      fresh_variable x1 ((x2 ~ v1) ++ S1).

Hint Constructors fresh_variable.

(* Qualified Values *)

Inductive value_qual : qual -> term -> Prop :=
  | value_qual_bool : forall q1 b1,
      value_qual q1 (term_bval q1 b1)
  | value_qual_abs  : forall q1 e1 T1,
      value_qual q1 (term_abs q1 T1 e1).

Hint Constructors value_qual.

(* Store Typing Relation *)

(* If v1 is an unrestricted value such that typing U1 L1 v1 T1 then T1 is unres-
   tricted and L1 = nil. Hence, L1 contributes no linear variables to the typing
   derivation in the unrestricted case. *)

Inductive typing_store : store -> cont -> cont -> Prop :=
  | typing_store_nil :
      typing_store nil nil nil
  | typing_store_cons_un : forall S1 U1 L1 x1 v1 P1,
      value_qual U v1 ->
      fresh_variable x1 S1 ->
      x1 `notin` free_vars v1 ->
      split_cont L1 nil L1 ->
      typing_store S1 U1 L1 ->
      typing U1 nil v1 (un P1) ->
      typing_store ((x1 ~ v1) ++ S1) ((x1 ~ un P1) ++ U1) L1
  | typing_store_cons_lin : forall S1 U1 L1 L2 L3 x1 v1 P1,
      value_qual L v1 ->
      fresh_variable x1 S1 ->
      x1 `notin` free_vars v1 ->
      split_cont L1 L2 L3 ->
      typing_store S1 U1 L1 ->
      typing U1 L2 v1 (lin P1) ->
      typing_store ((x1 ~ v1) ++ S1) U1 ((x1 ~ lin P1) ++ L3).

Hint Constructors typing_store.

(* Program Typing Relation *)

Inductive typing_program : store -> term -> Prop :=
  | typing_program_cont : forall S1 U1 L1 e1 T1,
      typing_store S1 U1 L1 ->
      typing U1 L1 e1 T1 ->
      typing_program S1 e1.

Hint Constructors typing_program.

(* Store Deallocation *)

Definition dealloc {A : Type} (q1 : qual) (x1 : var) (S1 : list (atom * A)) : list (atom * A) :=
  match q1 with
  | U => S1
  | L => assoc_remove x1 S1
  end.

Hint Unfold dealloc.

(* Call-By-Value Small-Step Evalution Relation *)

Inductive eval_step : store -> term -> store -> term -> Prop :=
  | eval_step_bool : forall S1 q1 (x1 : var) b1,
      fresh_variable x1 S1 ->
      eval_step S1 (term_bval q1 b1) ((x1 ~ (term_bval q1 b1)) ++ S1) x1
  | eval_step_cond : forall S1 S2 e1 e2 e3 e4,
      eval_step S1 e1 S2 e4 ->
      eval_step S1 (term_cond e1 e2 e3) S2 (term_cond e4 e2 e3)
  | eval_step_cond_true : forall S1 q1 (x1 : var) e1 e2,
      binds x1 (term_bval q1 true) S1 ->
      eval_step S1 (term_cond x1 e1 e2) (dealloc q1 x1 S1) e1
  | eval_step_cond_false : forall S1 q1 (x1 : var) e1 e2,
      binds x1 (term_bval q1 false) S1 ->
      eval_step S1 (term_cond x1 e1 e2) (dealloc q1 x1 S1) e2
  | eval_step_abs : forall S1 q1 T1 (x1 : var) e1,
      fresh_variable x1 S1 ->
      x1 `notin` free_vars e1 ->
      eval_step S1 (term_abs q1 T1 e1) ((x1 ~ (term_abs q1 T1 e1)) ++ S1) x1
  | eval_step_app_left : forall S1 S2 e1 e2 e3,
      eval_step S1 e1 S2 e3 ->
      eval_step S1 (term_app e1 e2) S2 (term_app e3 e2)
  | eval_step_app_right : forall S1 S2 (x1 : var) e1 e2,
      eval_step S1 e1 S2 e2 ->
      eval_step S1 (term_app x1 e1) S2 (term_app x1 e2)
  | eval_step_app_beta : forall S1 q1 T1 (x1 x2 : var) e1,
      binds x1 (term_abs q1 T1 e1) S1 ->
      eval_step S1 (term_app x1 x2) (dealloc q1 x1 S1) (e1 ^^ x2).

Hint Constructors eval_step.

(* Reduced Terms *)

Inductive reduced : term -> store -> Prop :=
  | reduced_fvar : forall x1 q1 v1 S1,
      value_qual q1 v1 ->
      binds x1 v1 S1 ->
      reduced (term_fvar x1) S1.

Hint Constructors reduced.
