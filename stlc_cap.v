(***************************************************************************
* STLC + effect-closed functions, based on formalization in the            *
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
  | typ_base         : typ
  | typ_eff          : typ
  | typ_arrow        : typ -> typ -> typ
  | typ_arrow_closed : typ -> typ -> typ.

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_app  : trm -> trm -> trm.

Coercion trm_bvar : nat >-> trm.
Coercion trm_fvar : var >-> trm.

(* ********************************************************************** *)
(** ** Opening *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_abs T t1    => trm_abs T (open_rec (S k) u t1)
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
  | term_abs : forall L T t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (trm_abs T t1)
  | term_app : forall t1 t2,
      term t1 ->
      term t2 ->
      term (trm_app t1 t2).

(* ********************************************************************** *)
(** ** Semantics *)

Inductive value : trm -> Prop :=
  | value_abs : forall t1 T,
      term (trm_abs T t1) -> value (trm_abs T t1).

Reserved Notation "t --> t'" (at level 68).

Inductive red : trm -> trm -> Prop :=
  | red_beta_abs : forall t1 t2 T,
      term (trm_abs T t1) ->
      value t2 ->
      (trm_app (trm_abs T t1) t2) --> (t1 ^^ t2)
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

Fixpoint closed_typ(t: typ) := match t with
  | typ_base            => true
  | typ_eff             => false
  | typ_arrow U V       => false
  | typ_arrow_closed U V => true   (* pure lambda abstraction *)
  end.

Fixpoint closed_env(E: ctx) := match E with
  | nil => nil
  | cons (x, T) E' => if closed_typ T then
                        cons (x, T) (closed_env E')
                      else
                        closed_env E'
  end.

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
      E |= (trm_abs U t1) ~: (typ_arrow U T)
  | typing_abs_closed: forall L E V e1 T1,
      ok E ->
      (forall x, x \notin L ->
         ((closed_env E) & x ~ V) |= (e1 ^ x) ~: T1) ->
      E |= (trm_abs V e1) ~: (typ_arrow_closed V T1)
  | typing_app : forall S T E t1 t2,
      E |= t1 ~: (typ_arrow S T) ->
      E |= t2 ~: S ->
      E |= (trm_app t1 t2) ~: T
  | typing_sub_abs: forall E e S T,
      E |= e ~: (typ_arrow_closed S T) -> E |= e ~: (typ_arrow S T)

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
  | trm_abs T t1    => (fv t1)
  | trm_app t1 t2 => (fv t1) \u (fv t2)
  end.

(* ********************************************************************** *)
(** ** Substitution *)

Reserved Notation "[ z ~> u ] t" (at level 69).

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs T t1    => trm_abs T ([ z ~> u ] t1)
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

Lemma term_abs_to_body : forall t1 T,
  term (trm_abs T t1) -> body t1.
Proof. intros. unfold body. inversion* H. Qed.

Lemma body_to_term_abs : forall t1 T,
  body t1 -> term (trm_abs T t1).
Proof. intros. inversion* H. Qed.

Hint Resolve term_abs_to_body body_to_term_abs.

Lemma subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simpls*.
  case_var*.
  apply_fresh term_abs. rewrite* subst_open_var.
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

  induction H; autos; eapply term_abs; eauto.
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
(** * Properties of environment *)
Lemma closed_env_dist: forall E F, closed_env (E & F) = closed_env E & closed_env F.
Proof. rewrite concat_def. intros. gen E. induction F; intros E; autos.
  rewrite LibList.app_cons. destruct a.
  simpl. destruct* (closed_typ t). rewrite LibList.app_cons. rewrite* <- IHF.
Qed.

Lemma closed_env_dom_subset : forall E, dom (closed_env E) \c dom E.
Proof. intros. induction E.
  simpl. apply subset_refl.
  destruct a. cases t; simpls;
   try match goal with
           [|- dom (cons _ _) \c dom (cons _ _)] =>
           repeat(rewrite cons_to_push);
             repeat(rewrite dom_to_push);
             repeat(rewrite dom_concat);
             autos* subset_union_2 subset_refl subset_trans
         | [|- dom _ \c dom (cons _ _)] =>
           rewrite cons_to_push; rewrite dom_push;
           autos* subset_trans IHE subset_union_weak_r
       end.
Qed.

Lemma closed_env_binds: forall E x v, ok E -> binds x v (closed_env E) -> binds x v E.
Proof. intros. induction E.
  simpl in *. autos.
  destruct a.
    simpl in *.  rewrite cons_to_push in *. destruct (closed_typ t).
      destruct (binds_push_inv H0).
        destruct H1. substs. apply* binds_push_eq.
        destruct H1. apply* binds_push_neq.
      rewrite <- concat_empty_r. apply binds_weaken; rewrite* concat_empty_r.
Qed.

Lemma closed_env_binds_in: forall E x T, closed_typ T = true ->
   binds x T E -> binds x T (closed_env E).
Proof. intros. induction E.
  (* nil *)
  rewrite <- empty_def in H0. destruct(binds_empty_inv H0).
  (* x::xs *)
  destruct a.
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv H0).
    destruct H1. inversions H2. rewrite* H.
    destruct H1. destruct* (closed_typ t).
Qed.

Lemma closed_env_ok : forall E,
  ok E -> ok (closed_env E).
Proof. intros. induction* E.
  destruct a. rewrite cons_to_push in H.
    destructs (ok_push_inv H). simpl. destruct* (closed_typ t).
    rewrite cons_to_push. apply ok_push. autos.
    lets: closed_env_dom_subset E. unfolds subset.
    unfolds notin. autos.
Qed.

Lemma closed_env_empty : closed_env empty = empty.
Proof. rewrite empty_def. reflexivity. Qed.

Lemma closed_env_single_true : forall x U, closed_typ U = true ->
  closed_env (x ~ U) = x ~ U.
Proof. intros.
  replace (x ~ U) with (empty & x ~ U) by rewrite* concat_empty_l.
  rewrite <- cons_to_push. simpls. rewrite H.
  rewrite closed_env_empty. reflexivity.
Qed.

Lemma closed_env_single_false : forall x U, closed_typ U = false ->
  closed_env (x ~ U) = empty.
Proof. intros.
  replace (x ~ U) with (empty & x ~ U) by rewrite* concat_empty_l.
  rewrite <- cons_to_push. simpls. rewrite H.
  rewrite closed_env_empty. reflexivity.
Qed.

Lemma closed_env_eq : forall E, closed_env (closed_env E) = closed_env E.
Proof. intros. induction E; autos.
  destruct a.
  simpls. remember (closed_typ t). symmetry in Heqb. destruct* b.
    simpls. rewrite* Heqb. rewrite* IHE.
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
  (* abs closed *)
  simpl. pick_fresh x. forwards~ K: H1 x.
  rewrite dom_concat in K. rewrite dom_single in K.
  forwards~ : subset_strengthen (subset_trans (@open_fv_subset e1 x 0) K).
  eapply subset_trans. apply H2. apply closed_env_dom_subset.
  (* app *)
  simpl. replace (dom E) with (dom E \u dom E) by (autos* union_same).
  apply subset_union_2; autos.
Qed.

(* ********************************************************************** *)
(** ** Checking that the main proofs still type-check *)

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T ->
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. gen_eq H: (E & G). gen E F G.
  induction Typ; intros; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  apply_fresh* typing_abs_closed as y.
    repeat(rewrite closed_env_dist in *). rewrite <- concat_assoc.
    apply* H1. rewrite* concat_assoc.
    rewrite concat_assoc. apply ok_push.
    repeat(rewrite <- closed_env_dist). apply* closed_env_ok.
    assert (Ha: y \notin dom E0 \u dom F \u dom G) by autos.
    intros HI. apply Ha. repeat(rewrite dom_concat in HI).
    repeat(rewrite in_union in *). rewrite or_assoc in HI. branches HI.
      branch 1. lets*: closed_env_dom_subset E0.
      branch 2. lets*: closed_env_dom_subset F.
      branch 3. lets*: closed_env_dom_subset G.
  apply* typing_app.
  apply* typing_sub_abs.
Qed.

Lemma typing_weakening_env : forall E F G e T,
  typing (E & (closed_env F) & G) e T ->
  ok (E & F & G) ->
  typing (E & F & G) e T.
Proof. intros. inductions H.
  apply* typing_var. binds_cases H0; autos.
    apply* binds_weaken. apply* binds_concat_left.
    apply binds_concat_right. apply* closed_env_binds.
    autos* ok_concat_inv_l ok_concat_inv_r.
  apply_fresh typing_abs as x.  apply_ih_bind* H0.
  apply_fresh typing_abs_closed as x. auto.
    repeat(rewrite closed_env_dist in *). rewrite closed_env_eq in *.
    apply_ih_bind* H1. rewrite* closed_env_eq. forwards~ : H0 x.
  apply* typing_app.
  apply* typing_sub_abs.
Qed.

Lemma typing_strengthen_env: forall E u U, value u -> typing E u U ->
  closed_typ U = true -> typing (closed_env E) u U.
Proof. intros. induction H0; simpls; inversion H1.
  apply typing_var. apply* closed_env_ok. apply* closed_env_binds_in.
  apply_fresh* typing_abs_closed as y. apply* closed_env_ok. rewrite* closed_env_eq.
  inversion H.
Qed.

Lemma typing_subst : forall F E t T z u U,
  value u ->
  (E & z ~ U & F) |= t ~: T ->
  E |= u ~: U ->
  (E & F) |= [z ~> u]t ~: T.
Proof.
  introv Hv Typt Typu. gen_eq G: (E & z ~ U & F). gen E F.
  induction Typt; intros; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs as y.
    rewrite* subst_open_var. apply_ih_bind* H0.
  apply_fresh typing_abs_closed as y. autos.
    rewrite* subst_open_var.
    (* if U is closed, then use IH; else  x is free in e1; *)
    repeat(rewrite closed_env_dist in *). remember (closed_typ U) as b. destruct b.
      (* closed_typ U = true *)
      symmetry in Heqb. rewrite* closed_env_single_true in H1. rewrite <- concat_assoc.
      apply* H1. apply* typing_strengthen_env.
      rewrite* concat_assoc.
      (* closed_typ U = false, z is free in e1 *)
      symmetry in Heqb. rewrite* closed_env_single_false in H0. rewrite concat_empty_r in H0.
      destruct (ok_middle_inv H). forwards~ HI: H0 y.
      rewrite* subst_fresh. lets: typing_env_fv HI. unfolds notin. intros HII.
      assert (HIII: z \in dom (closed_env E0 & closed_env F & y ~ V)) by unfolds* subset.
      repeat(rewrite dom_concat in HIII). repeat(rewrite in_union in HIII).
      rewrite dom_single in HIII. rewrite or_assoc in HIII. branches HIII.
        apply H2. lets*: closed_env_dom_subset E0.
        apply H3. lets*: closed_env_dom_subset F.
        rewrite in_singleton in H5. substs. apply* Fry. repeat(rewrite in_union).
          autos* in_singleton_self.
  apply* typing_app.
  apply* typing_sub_abs.
Qed.

Lemma preservation_result : preservation_statement.
Proof.
  introv Typ. gen t'.
  induction Typ; intros t' Red; inversions Red.
  inversions Typ1. pick_fresh x. rewrite* (@subst_intro x).
    apply_empty* typing_subst.

    inversions H4. pick_fresh x. rewrite* (@subst_intro x).
      apply_empty* typing_subst. rewrite <- (@concat_empty_l typ E).
      apply* typing_weakening_env. rewrite* concat_empty_l.
      rewrite* concat_empty_l.
  apply* typing_app.
  apply* typing_app.
  apply* typing_sub_abs.
  apply* typing_sub_abs.
  apply* typing_sub_abs.
Qed.

Lemma progress_result : progress_statement.
Proof.
  introv Typ. gen_eq E: (empty:ctx). lets Typ': Typ.
  inductions Typ; intros; subst; autos.
  false* binds_empty_inv.
  right.
    destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
      inversions Typ1; inversions Val1. exists* (t0 ^^ t2).
      exists* (t0 ^^ t2).
      exists* (trm_app t1 t2').
    exists* (trm_app t1' t2).
Qed.
