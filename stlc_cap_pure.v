(***************************************************************************
* STLC + pure effect-closed functions without =>, based on formalization   *
* in the library _locally nameless_                                        *
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
  | typ_stoic        : typ -> typ -> typ.

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
      term (trm_abs T t1) -> value (trm_abs T t1)
  | value_var : forall x, value (trm_fvar x).

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
  | typ_stoic U V       => true   (* pure lambda abstraction *)
  end.

Fixpoint pure(E: ctx) := match E with
  | nil => nil
  | cons (x, T) E' => if closed_typ T then
                        cons (x, T) (pure E')
                      else
                        pure E'
  end.

(* ********************************************************************** *)
(** ** Typing *)

Reserved Notation "E |= t ~: T" (at level 69).

Inductive typing : ctx -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      ok E ->
      binds x T E ->
      E |= (trm_fvar x) ~: T
  | typing_stoic: forall L E V e1 T1,
      ok E ->
      (forall x, x \notin L ->
         ((pure E) & x ~ V) |= (e1 ^ x) ~: T1) ->
      E |= (trm_abs V e1) ~: (typ_stoic V T1)
  | typing_app : forall S T E t1 t2,
      E |= t1 ~: (typ_stoic S T) ->
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

(* inhabitable env *)
Inductive inhabitable: ctx -> Prop :=
  | inhabitable_empty: inhabitable empty
  | inhabitable_push: forall x y z t T E,
                        inhabitable E ->
                        value t ->
                        x ~ typ_base & y ~ typ_eff |= t ~: T ->
                        z # E ->
                        inhabitable (E & z ~ T).


(* Capability-safe types are not capability producing, i.e. capable of
   creating an instance of E *)

Inductive capsafe: typ -> Prop :=
| capsafe_base: capsafe typ_base
| capsafe_eff_any: forall S T, caprod S -> capsafe (typ_stoic S T)
| capsafe_any_safe: forall S T, capsafe T -> capsafe (typ_stoic S T)

with caprod: typ -> Prop :=
 | caprod_eff: caprod typ_eff
 | caprod_safe_eff: forall S T, capsafe S -> caprod T -> caprod (typ_stoic S T).

Inductive healthy: ctx -> Prop :=
  | healthy_empty: healthy empty
  | healthy_push: forall x E T, capsafe T -> healthy E ->
                               x # E -> healthy (E & x ~ T).

Definition inhabitable_pure_healthy_statement := forall E,
  inhabitable E -> pure E = E -> healthy E.

Definition effect_safety_statement := forall E, healthy E ->
  ~exists e, typing E e typ_eff.

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

Lemma pure_closed: forall E x T, binds x T (pure E) -> closed_typ T = true.
Proof. intros. inductions E.
  simpls. rewrite <- empty_def in H. false* binds_empty_inv.
  destruct a. simpls. cases* (closed_typ t). rewrite cons_to_push in H.
  destruct (binds_push_inv H) as [Inv|Inv]; destruct Inv.
    substs*.
    apply* IHE.
Qed.

Lemma pure_dist: forall E F, pure (E & F) = pure E & pure F.
Proof. rewrite concat_def. intros. gen E. induction F; intros E; autos.
  rewrite LibList.app_cons. destruct a.
  simpl. destruct* (closed_typ t). rewrite LibList.app_cons. rewrite* <- IHF.
Qed.

Lemma pure_dom_subset : forall E, dom (pure E) \c dom E.
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

Lemma pure_binds: forall E x v, ok E -> binds x v (pure E) -> binds x v E.
Proof. intros. induction E.
  simpl in *. autos.
  destruct a.
    simpl in *.  rewrite cons_to_push in *. destruct (closed_typ t).
      destruct (binds_push_inv H0).
        destruct H1. substs. apply* binds_push_eq.
        destruct H1. apply* binds_push_neq.
      rewrite <- concat_empty_r. apply binds_weaken; rewrite* concat_empty_r.
Qed.

Lemma pure_binds_in: forall E x T, closed_typ T = true ->
   binds x T E -> binds x T (pure E).
Proof. intros. induction E.
  (* nil *)
  rewrite <- empty_def in H0. destruct(binds_empty_inv H0).
  (* x::xs *)
  destruct a.
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv H0).
    destruct H1. inversions H2. rewrite* H.
    destruct H1. destruct* (closed_typ t).
Qed.

Lemma pure_ok : forall E,
  ok E -> ok (pure E).
Proof. intros. induction* E.
  destruct a. rewrite cons_to_push in H.
    destructs (ok_push_inv H). simpl. destruct* (closed_typ t).
    rewrite cons_to_push. apply ok_push. autos.
    lets: pure_dom_subset E. unfolds subset.
    unfolds notin. autos.
Qed.

Lemma pure_empty : pure empty = empty.
Proof. rewrite empty_def. reflexivity. Qed.

Lemma pure_single_true : forall x U, closed_typ U = true ->
  pure (x ~ U) = x ~ U.
Proof. intros.
  replace (x ~ U) with (empty & x ~ U) by rewrite* concat_empty_l.
  rewrite <- cons_to_push. simpls. rewrite H.
  rewrite pure_empty. reflexivity.
Qed.

Lemma pure_single_false : forall x U, closed_typ U = false ->
  pure (x ~ U) = empty.
Proof. intros.
  replace (x ~ U) with (empty & x ~ U) by rewrite* concat_empty_l.
  rewrite <- cons_to_push. simpls. rewrite H.
  rewrite pure_empty. reflexivity.
Qed.

Lemma pure_eq : forall E, pure (pure E) = pure E.
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
  (* abs closed *)
  simpl. pick_fresh x. forwards~ K: H1 x.
  rewrite dom_concat in K. rewrite dom_single in K.
  forwards~ : subset_strengthen (subset_trans (@open_fv_subset e1 x 0) K).
  eapply subset_trans. apply H2. apply pure_dom_subset.
  (* app closed *)
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
  apply_fresh* typing_stoic as y.
    repeat(rewrite pure_dist in *). rewrite <- concat_assoc.
    apply* H1. rewrite* concat_assoc.
    rewrite concat_assoc. apply ok_push.
    repeat(rewrite <- pure_dist). apply* pure_ok.
    assert (Ha: y \notin dom E0 \u dom F \u dom G) by autos.
    intros HI. apply Ha. repeat(rewrite dom_concat in HI).
    repeat(rewrite in_union in *). rewrite or_assoc in HI. branches HI.
      branch 1. lets*: pure_dom_subset E0.
      branch 2. lets*: pure_dom_subset F.
      branch 3. lets*: pure_dom_subset G.
  apply* typing_app.
Qed.

Lemma typing_weakening_env : forall E F G e T,
  typing (E & (pure F) & G) e T ->
  ok (E & F & G) ->
  typing (E & F & G) e T.
Proof. intros. inductions H.
  apply* typing_var. binds_cases H0; autos.
    apply* binds_weaken. apply* binds_concat_left.
    apply binds_concat_right. apply* pure_binds.
    autos* ok_concat_inv_l ok_concat_inv_r.
  apply_fresh typing_stoic as x. auto.
    repeat(rewrite pure_dist in *). rewrite pure_eq in *.
    apply_ih_bind* H1. rewrite* pure_eq. forwards~ : H0 x.
  apply* typing_app.
Qed.

Lemma typing_strengthen_env: forall E u U, value u -> typing E u U ->
  closed_typ U = true -> typing (pure E) u U.
Proof. intros. induction H0; simpls; inversion H1.
  apply typing_var. apply* pure_ok. apply* pure_binds_in.
  apply_fresh* typing_stoic as y. apply* pure_ok. rewrite* pure_eq.
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
  apply_fresh typing_stoic as y. autos.
    rewrite* subst_open_var.
    (* if U is closed, then use IH; else  x is free in e1; *)
    repeat(rewrite pure_dist in *). remember (closed_typ U) as b. destruct b.
      (* closed_typ U = true *)
      symmetry in Heqb. rewrite* pure_single_true in H1. rewrite <- concat_assoc.
      apply* H1. apply* typing_strengthen_env.
      rewrite* concat_assoc.
      (* closed_typ U = false, z is free in e1 *)
      symmetry in Heqb. rewrite* pure_single_false in H0. rewrite concat_empty_r in H0.
      destruct (ok_middle_inv H). forwards~ HI: H0 y.
      rewrite* subst_fresh. lets: typing_env_fv HI. unfolds notin. intros HII.
      assert (HIII: z \in dom (pure E0 & pure F & y ~ V)) by unfolds* subset.
      repeat(rewrite dom_concat in HIII). repeat(rewrite in_union in HIII).
      rewrite dom_single in HIII. rewrite or_assoc in HIII. branches HIII.
        apply H2. lets*: pure_dom_subset E0.
        apply H3. lets*: pure_dom_subset F.
        rewrite in_singleton in H5. substs. apply* Fry. repeat(rewrite in_union).
          autos* in_singleton_self.
  apply* typing_app.
Qed.

Lemma preservation_result : preservation_statement.
Proof.
  introv Typ. gen t'.
  induction Typ; intros t' Red; inversions Red.

  inversions Typ1. inversions H3. pick_fresh x. rewrite* (@subst_intro x).
      apply_empty* typing_subst. rewrite <- (@concat_empty_l typ E).
      apply* typing_weakening_env. rewrite* concat_empty_l.
      rewrite* concat_empty_l.

      pick_fresh y. rewrite* (@subst_intro y).
      apply_empty* typing_subst. rewrite <- (@concat_empty_l typ E).
      apply* typing_weakening_env. rewrite* concat_empty_l.
      rewrite* concat_empty_l.

  apply* typing_app.
  apply* typing_app.
Qed.

Lemma progress_result : progress_statement.
Proof.
  introv Typ. gen_eq E: (empty:ctx). lets Typ': Typ.
  inductions Typ; intros; subst; autos.
  right.
    destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
      inversions Typ1; inversions Val1.
      false* binds_empty_inv.
      exists* (e1 ^^ t2).
      exists* (trm_app t1 t2').
    exists* (trm_app t1' t2).
Qed.

(* ********************************************************************** *)
(** * effect safety *)

Hint Constructors capsafe caprod.

Lemma capsafe_not_caprod : forall T, capsafe T -> ~ caprod T.
Proof. intros T H Hc. inductions T; inversions Hc. inversions H.
  inversions H; auto.
Qed.

Lemma capsafe_caprod_classic: forall T, capsafe T \/ caprod T.
Proof. intros T. inductions T. left*. right*. destruct* IHT2. Qed.

Lemma capsafe_decidable: forall T, capsafe T \/ ~ capsafe T.
Proof. intros. destruct (capsafe_caprod_classic T). left*.
  right. intros Hc. lets*: capsafe_not_caprod Hc.
Qed.

Lemma not_capsafe_caprod : forall T, ~capsafe T -> caprod T.
Proof. intros T H. inductions T; auto.
  false. apply* H. destruct* (capsafe_decidable T1).
  destruct* (capsafe_decidable T2).
    false. apply* H.
    false. apply* H.
Qed.

Lemma capsafe_closed_typ: forall T, capsafe T -> closed_typ T = true.
Proof. intros. inductions H; try reflexivity; try false; autos. Qed.

Lemma healthy_env_closed: forall E, healthy E -> pure E = E.
Proof. intros. inductions H.
  rewrite empty_def. reflexivity.
  rewrite <- cons_to_push. simpls. lets: capsafe_closed_typ H.
    rewrite* H2. rewrite* IHhealthy.
Qed.

Lemma healthy_env_capsafe : forall E S x, healthy E ->
   binds x S E ->  capsafe S.
Proof. introv H Hb. inductions H.
  false. apply* binds_empty_inv.
  destruct (binds_push_inv Hb).
    destruct H2. subst. autos.
    destruct H2. autos.
Qed.

Lemma healthy_env_term_capsafe: forall E t T,
  healthy E ->
  E |= t ~: T ->
  capsafe T.
Proof. intros. inductions H0.
  apply *healthy_env_capsafe.
  pick_fresh x. forwards~ : H1 x. destruct* (capsafe_decidable V).
    apply capsafe_any_safe. apply* (H2 x). rewrite* (healthy_env_closed H).
      apply* healthy_push.
      apply capsafe_eff_any. apply* not_capsafe_caprod.
  forwards~ : IHtyping1 H. forwards~ : IHtyping2 H. inversions* H0.
  lets*: capsafe_not_caprod S.
Qed.

Lemma effect_safety_result : effect_safety_statement.
Proof. intros E H He. destruct He.
  lets*: healthy_env_term_capsafe H0. inversions H1.
Qed.


(* This proof ensures that all inhabitable types are capsafe, thus
   justifies the definition of capsafe/caprod.

   This theorem assumes that all inhabitable types in the system can
   be inhabited by a value in the environment {x:B, y:E}. Note that
   variables are values in the system, thus B and E are inhabitable.

   If the term t is not a value, it should be able to take a step and
   preserves the type.

*)

Lemma inhabitable_capsafe: forall x y t T,
  typing (x ~ typ_base & y ~ typ_eff) t T -> value t ->
  capsafe T \/ T = typ_eff.
Proof. introv Typ Val. inductions Typ.
  destruct (binds_push_inv H0) as [Inv | Inv]; destruct Inv.
    subst. auto.
    destructs (binds_single_inv H2). subst. auto.
  pick_fresh z. forwards~ IH: H0 z. destruct (capsafe_decidable V) as [Case | Case].
    (* capsafe V -> healthy E -> capsafe T1 *)
    rewrite pure_dist, pure_single_true, pure_single_false, concat_empty_r in IH; auto.
    forwards~ Hcap : healthy_env_term_capsafe IH.
      rewrite <- concat_empty_l, concat_assoc. repeat(apply* healthy_push). apply healthy_empty.
    (* caprod V -> capsafe V -> T1 *)
    forwards~ Vcap : not_capsafe_caprod Case.
  inversion Val.
Qed.

Theorem inhabitable_pure_healthy: inhabitable_pure_healthy_statement.
Proof. introv In Pure. inductions In.
  apply healthy_empty.
  assert (Closed: closed_typ T = true).
    applys~ pure_closed (E & z ~ T) z.
    rewrite Pure. apply binds_tail.
  forwards~ IH: inhabitable_capsafe H0. destruct IH.
    rewrite pure_dist, pure_single_true in Pure; auto.
      rewrite <- ?cons_to_push in Pure. inversion Pure. rewrite H4.
      apply* healthy_push.
    substs. false*.
Qed.
