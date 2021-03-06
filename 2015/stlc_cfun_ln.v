(***************************************************************************
* STLC in locally nameless style, based on formalization in the            *
* library _locally nameless_ *                                             *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Definitions *)

(* ********************************************************************** *)
(** ** Grammars *)

Inductive typ : Set :=
  | typ_var   : var -> typ
  | typ_arrow : typ -> typ -> typ.

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : trm -> trm
  | trm_cap  : trm -> trm            (* capsule lambda - closed *)
  | trm_app  : trm -> trm -> trm.

Coercion trm_bvar : nat >-> trm.
Coercion trm_fvar : var >-> trm.

(* ********************************************************************** *)
(** ** Opening *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_abs t1    => trm_abs (open_rec (S k) u t1)
  | trm_cap t1    => trm_cap (open_rec (S k) u t1)
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).

(* ********************************************************************** *)
(** ** Local closure *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (trm_abs t1)
  | term_cap: forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (trm_cap t1)
  | term_app : forall t1 t2,
      term t1 ->
      term t2 ->
      term (trm_app t1 t2).

(* ********************************************************************** *)
(** ** Semantics *)

Inductive value : trm -> Prop :=
  | value_abs : forall t1,
      term (trm_abs t1) -> value (trm_abs t1)
  | value_cap: forall t1,
      term (trm_cap t1) -> value (trm_cap t1).

Reserved Notation "t --> t'" (at level 68).

Inductive red : trm -> trm -> Prop :=
  | red_beta_abs : forall t1 t2,
      term (trm_abs t1) ->
      value t2 ->
      (trm_app (trm_abs t1) t2) --> (t1 ^^ t2)
  | red_beta_cap : forall t1 t2,
      term (trm_cap t1) ->
      value t2 ->
      (trm_app (trm_cap t1) t2) --> (t1 ^^ t2)
  | red_app_1 : forall t1 t1' t2,
      term t2 ->
      t1 --> t1' ->
      (trm_app t1 t2) --> (trm_app t1' t2)
  | red_app_2 : forall t1 t2 t2',
      value t1 ->
      t2 --> t2' ->
      (trm_app t1 t2) --> (trm_app t1 t2')

where "t --> t'" := (red t t').


(* ********************************************************************** *)
(** ** Environments *)

Definition ctx := env typ.

(* ********************************************************************** *)
(** ** Typing *)

Reserved Notation "E |= t ~: T" (at level 69).

Inductive typing : ctx -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      ok E ->
      binds x T E ->
      E |= (trm_fvar x) ~: T
  | typing_abs : forall L E U T t1,
      (forall x, x \notin L ->
        (E & x ~ U) |= t1 ^ x ~: T) ->
      E |= (trm_abs t1) ~: (typ_arrow U T)
  | typing_cap: forall L E U T t1,
      ok E ->
      (forall x, x \notin L ->
        (x ~ U) |= t1 ^ x ~: T) ->
      E |= (trm_cap t1) ~: (typ_arrow U T)
  | typing_app : forall S T E t1 t2,
      E |= t1 ~: (typ_arrow S T) ->
      E |= t2 ~: S ->
      E |= (trm_app t1 t2) ~: T

where "E |= t ~: T" := (typing E t T).


(* ********************************************************************** *)
(** ** Statement of theorems *)

Definition preservation_statement := forall E t t' T,
  E |= t ~: T ->
  t --> t' ->
  E |= t' ~: T.

Definition progress_statement := forall t T,
  empty |= t ~: T ->
     value t
  \/ exists t', t --> t'.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Infrastructure *)

(** ** Free variables *)

Fixpoint fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_abs t1    => (fv t1)
  | trm_cap t1    => (fv t1)
  | trm_app t1 t2 => (fv t1) \u (fv t2)
  end.

(* ********************************************************************** *)
(** ** Substitution *)

Reserved Notation "[ z ~> u ] t" (at level 69).

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs t1    => trm_abs ([ z ~> u ] t1)
  | trm_cap t1    => trm_cap ([ z ~> u ] t1)
  | trm_app t1 t2 => trm_app ([ z ~> u ] t1) ([ z ~> u ] t2)
  end

where "[ z ~> u ] t" := (subst z u t).


(* ********************************************************************** *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : ctx => dom x) in
  let D := gather_vars_with (fun x : trm => fv x) in
  constr:(A \u B \u C \u D).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.
Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.


(* ********************************************************************** *)
(** ** Automation *)

Hint Constructors term value red.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Safty *)


(* ********************************************************************** *)
(** ** lemmas *)

Lemma open_rec_term_core :forall t j v i u, i <> j ->
  {j ~> v}t = {i ~> u}({j ~> v}t) -> t = {i ~> u}t.
Proof.
  induction t; introv Neq Equ; simpls; inversion* Equ; fequals*.
  case_nat*. case_nat*.
Qed.

Lemma open_rec_term : forall t u,
  term t -> forall k, t = {k ~> u}t.
Proof.
  induction 1; intros; simpl; fequals*. unfolds open.
  pick_fresh x. apply* (@open_rec_term_core t1 0 (trm_fvar x)).
  pick_fresh x. apply* (@open_rec_term_core t1 0 (trm_fvar x)).
Qed.

Lemma subst_fresh : forall x t u,
  x \notin fv t ->  [x ~> u] t = t.
Proof. intros. induction t; simpls; fequals*. case_var*. Qed.

Lemma subst_open : forall x u t1 t2, term u ->
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; fequals*.
  case_nat*. case_var*. apply* open_rec_term.
Qed.

Lemma subst_open_var : forall x y u t, y <> x -> term u ->
  ([x ~> u]t) ^ y = [x ~> u] (t ^ y).
Proof. introv Neq Wu. rewrite* subst_open. simpl. case_var*. Qed.

Lemma subst_intro : forall x t u,
  x \notin (fv t) -> term u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite* subst_open.
  rewrite* subst_fresh. simpl. case_var*.
Qed.

(* ********************************************************************** *)
(** ** Preservation of local closure *)

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x).

Lemma term_abs_to_body : forall t1,
  term (trm_abs t1) -> body t1.
Proof. intros. unfold body. inversion* H. Qed.

Lemma term_cap_to_body : forall t1,
  term (trm_cap t1) -> body t1.
Proof. intros. unfold body. inversion* H. Qed.

Lemma body_to_term_abs : forall t1,
  body t1 -> term (trm_abs t1).
Proof. intros. inversion* H. Qed.

Hint Resolve term_abs_to_body term_cap_to_body body_to_term_abs.

Lemma subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simpls*.
  case_var*.
  apply_fresh term_abs. rewrite* subst_open_var.
  apply_fresh term_cap. rewrite* subst_open_var.
Qed.

Hint Resolve subst_term.

Lemma open_term : forall t u,
  body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@subst_intro y).
Qed.

Hint Resolve open_term.


(* ********************************************************************** *)
(** ** Regularity of relations *)

Lemma typing_regular : forall E e T,
  typing E e T -> ok E /\ term e.
Proof.
  split. induction* H.
  pick_fresh y. forwards~ : (H0 y).

  induction H; autos*.
Qed.

Lemma open_fv_subset: forall e x k,
  fv e \c fv ({k ~> x}e).
Proof. intros. gen k. induction e; intros; simpl.
  apply subset_empty_l.
  apply subset_refl.
  autos.
  autos.
  apply* subset_union_2.
Qed.

Lemma subset_trans: forall (T: Type) (a b c: fset T),
  a \c b -> b \c c -> a \c c.
Proof. unfolds subset. autos. Qed.

Lemma subset_strengthen: forall (T: Type) (a b: fset T) (x: T),
  a \c (b \u \{x}) -> x \notin a -> a \c b.
Proof. unfolds subset. intros. forwards K: (H x0 H1).
  rewrite in_union in K. destruct* K.
  rewrite in_singleton in H2. subst.
  tryfalse.
Qed.

Lemma typing_env_fv : forall E e T,
  typing E e T -> fv e \c dom E.
Proof. intros. induction* H; subst.
  (* var *)
  simpl. forwards~ K:  get_some_inv (binds_get H0).
  unfolds. intros. rewrite in_singleton in H1. subst*.
  (* abs *)
  simpl. pick_fresh x. forwards~ K: (H0 x).
  rewrite dom_concat in K. rewrite dom_single in K.
  assert (HI: fv t1 \c dom E \u \{x}).
    eapply subset_trans with (fv (t1 ^ x)).
    autos* open_fv_subset. autos.
  apply subset_strengthen with x; autos.
  (* cap *)
  simpl. pick_fresh x. forwards~ K: (H1 x).
  rewrite dom_single in K.
  assert (HI: fv t1 \c \{}).
    apply subset_strengthen with x; autos.
    rewrite union_empty_l.
    eapply subset_trans with (fv (t1 ^ x)).
    autos* open_fv_subset. autos.
  apply subset_trans with \{}; autos. apply subset_empty_l.
  (* app *)
  simpl. replace (dom E) with (dom E \u dom E) by (autos* union_same).
  apply subset_union_2; autos.
Qed.

Lemma typing_term_closed : forall e T,
  typing empty e T -> fv e = \{}.
Proof using.
  intros. apply typing_env_fv in H.
  rewrite dom_empty in H.
  apply* fset_extens. apply subset_empty_l.
Qed.

Lemma typing_cap_closed : forall E e T,
  typing E (trm_cap e) T -> fv e = \{}.
Proof.
  intros. inversions H.
  assert (HI: empty |= trm_cap e ~: typ_arrow U T0).
    apply typing_cap with L; autos.
  replace (fv e) with (fv (trm_cap e)) by autos.
  eapply typing_term_closed. exact HI.
Qed.

Lemma value_regular : forall e,
  value e -> term e.
Proof. induction 1; autos*. Qed.

Lemma red_regular : forall e e',
  red e e' -> term e /\ term e'.
Proof. induction 1; autos* value_regular. Qed.

Hint Extern 1 (ok ?E) =>
  match goal with
  | H: typing E _ _ |- _ => apply (proj1 (typing_regular H))
  end.

Hint Extern 1 (term ?t) =>
  match goal with
  | H: typing _ t _ |- _ => apply (proj2 (typing_regular H))
  | H: red t _ |- _ => apply (proj1 (red_regular H))
  | H: red _ t |- _ => apply (proj2 (red_regular H))
  | H: value t |- _ => apply (value_regular H)
  end.

(* ********************************************************************** *)
(** ** Checking that the main proofs still type-check *)

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T ->
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; intros G EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  apply* typing_cap.
  apply* typing_app.
Qed.

Lemma typing_subst : forall F E t T z u U,
  (E & z ~ U & F) |= t ~: T ->
  E |= u ~: U ->
  (E & F) |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. gen_eq G: (E & z ~ U & F). gen F.
  induction Typt; intros G Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs as y.
    rewrite* subst_open_var. apply_ih_bind* H0.
  assert (Hyp: E & G |= (trm_cap t1) ~: typ_arrow U0 T)
      by autos* typing_cap.
  forwards~ K : typing_cap_closed Hyp.
  rewrite* subst_fresh. rewrite* K.
  apply* typing_app.
Qed.

Lemma preservation_result : preservation_statement.
Proof.
  introv Typ. gen t'.
  induction Typ; intros t' Red; inversions Red.
  inversions Typ1. pick_fresh x. rewrite* (@subst_intro x).
   apply_empty* typing_subst.
  inversions Typ1. pick_fresh x. rewrite* (@subst_intro x).
   apply_empty* typing_subst.
   replace E with (empty & E) by (apply* concat_empty_l).
   apply* typing_weaken. rewrite* concat_empty_l.
   rewrite* concat_empty_l.
  apply* typing_app.
  apply* typing_app.
Qed.

Lemma progress_result : progress_statement.
Proof.
  introv Typ. gen_eq E: (empty:ctx). lets Typ': Typ.
  induction Typ; intros; subst.
  false* binds_empty_inv.
  left*. left*.
  right.
    destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
      inversions Typ1; inversions Val1. exists* (t0 ^^ t2).
      exists* (t0 ^^ t2).
      exists* (trm_app t1 t2').
    exists* (trm_app t1' t2).
Qed.
