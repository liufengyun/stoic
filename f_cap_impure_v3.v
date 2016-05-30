(***************************************************************************
* System-F with capabilities                                               *
*  - with both -> and =>                                                   *
*  - type abstraction over E and =>                                        *
*  - subtyping                                                             *
* (based on the F<: implementation in locally-nameless project)            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.
Implicit Types X : var.

(* ********************************************************************** *)
(** * Description of the Language *)

(** Representation of pre-types *)

Inductive typ       : Set   :=
  | typ_bvar        : nat -> typ
  | typ_fvar        : var -> typ
  | typ_base        : typ
  | typ_eff         : typ
  | typ_arrow       : typ -> typ -> typ
  | typ_stoic       : typ -> typ -> typ
  | typ_all         : typ -> typ
  | typ_top         : typ.

(** Representation of pre-terms *)

Inductive trm : Set :=
  | trm_top  : trm
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_tabs : trm -> trm
  | trm_tapp : trm -> typ -> trm.

(** Opening up a type binder occuring in a type *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar J            => If K = J then U else (typ_bvar J)
  | typ_fvar X            => typ_fvar X
  | typ_base              => typ_base
  | typ_eff               => typ_eff
  | typ_top               => typ_top
  | typ_arrow T1 T2       => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_stoic T1 T2       => typ_stoic (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1            => typ_all (open_tt_rec (S K) U T1)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

(** Opening up a type binder occuring in a term *)

Fixpoint open_te_rec (K : nat) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_top       => trm_top
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | trm_app e1 e2 => trm_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | trm_tabs e1   => trm_tabs (open_te_rec (S K) U e1)
  | trm_tapp e1 V => trm_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  end.

Definition open_te t U := open_te_rec 0 U t.

(** Opening up a term binder occuring in a term *)

Fixpoint open_ee_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_top       => trm_top
  | trm_bvar i    => If k = i then f else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs V (open_ee_rec (S k) f e1)
  | trm_app e1 e2 => trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | trm_tabs e1 => trm_tabs (open_ee_rec k f e1)
  | trm_tapp e1 V => trm_tapp (open_ee_rec k f e1) V
  end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "T 'open_tt_var' X" := (open_tt T (typ_fvar X)) (at level 67).
Notation "t 'open_te_var' X" := (open_te t (typ_fvar X)) (at level 67).
Notation "t 'open_ee_var' x" := (open_ee t (trm_fvar x)) (at level 67).

(** Types as locally closeded pre-types *)

Inductive type : typ -> Prop :=
  | type_top : type typ_top
  | type_var : forall X,
      type (typ_fvar X)
  | type_base: type typ_base
  | type_eff: type typ_eff
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_stoic : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_stoic T1 T2)
  | type_all : forall L T2,
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
      type (typ_all T2).

(** Terms as locally closeded pre-terms *)

Inductive term : trm -> Prop :=
  | term_top : term trm_top
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L T e1,
      type T ->
      (forall x, x \notin L -> term (e1 open_ee_var x)) ->
      term (trm_abs T e1)
  | term_app : forall e1 e2,
      term e1 ->
      term e2 ->
      term (trm_app e1 e2)
  | term_tabs : forall L e1,
      (forall X, X \notin L -> term (e1 open_te_var X)) ->
      term (trm_tabs e1)
  | term_tapp : forall e1 T,
      term e1 ->
      type T ->
      term (trm_tapp e1 T).

(** Environment is an associative list of bindings. *)

(** Binding are either mapping type or term variables.
 [: X :] is a type variable asumption and [x ~: T] is
 a typing assumption *)

Inductive bind : Set :=
  | bind_tvar : bind
  | bind_typ : typ -> bind.

Notation "[: X :]" := (X ~ bind_tvar)
  (at level 23) : env_scope.
Notation "x ~: T" := (x ~ bind_typ T)
  (at level 24, left associativity) : env_scope.

Definition env := LibEnv.env bind.

(** Well-formedness of a pre-type T in an environment E: all the type
  variables of T must be bound via [: T :] in E. This predicates
  implies that T is a type *)

Inductive wft : env -> typ -> Prop :=
  | wft_top: forall E, wft E typ_top
  | wft_base: forall E, wft E typ_base
  | wft_eff: forall E, wft E typ_eff
  | wft_var : forall E X,
      binds X bind_tvar E ->
      wft E (typ_fvar X)
  | wft_arrow : forall E T1 T2,
      wft E T1 ->
      wft E T2 ->
      wft E (typ_arrow T1 T2)
  | wft_stoic : forall E T1 T2,
      wft E T1 ->
      wft E T2 ->
      wft E (typ_stoic T1 T2)
  | wft_all : forall L E T,
      (forall X, X \notin L ->
        wft (E & [: X :]) (T open_tt_var X)) ->
      wft E (typ_all T).

(** A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment
  it is pushed on to. *)

Inductive okt : env -> Prop :=
  | okt_empty :
      okt empty
  | okt_tvar : forall E X,
      okt E -> X # E -> okt (E & [: X :])
  | okt_typ : forall E x T,
      okt E -> wft E T -> x # E -> okt (E & x ~: T).

(* closed rules *)
Fixpoint closed_typ(t: typ) := match t with
  | typ_top             => true
  | typ_bvar _          => false  (* impossible, ill-formed *)
  | typ_fvar _          => false  (* could be E or => *)
  | typ_base            => true
  | typ_eff             => false
  | typ_arrow U V       => false
  | typ_stoic U V       => true   (* stoic lambda abstraction *)
  | typ_all T           => true   (* stoic type abstraction *)
  end.

Fixpoint pure(E: env) := match E with
  | nil => nil
  | cons (X, bind_tvar) E' => cons (X, bind_tvar) (pure E')
  | cons (x, bind_typ T) E' => if closed_typ T then
                               cons (x, bind_typ T) (pure E')
                             else
                               pure E'
    end.


(** Subtyping relation *)

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top: forall E S,
      okt E ->
      wft E S ->
      sub E S typ_top
  | sub_refl: forall E S,
      okt E ->
      wft E S ->
      sub E S S
  | sub_trans : forall E S T U,
      okt E ->
      sub E S T ->
      sub E T U ->
      sub E S U
  | sub_degen: forall E S T,
      okt E ->
      wft E S ->
      wft E T ->
      sub E (typ_stoic S T) (typ_arrow S T)
  | sub_arrow: forall E S1 S2 T1 T2,
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_stoic: forall E S1 S2 T1 T2,
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ_stoic S1 S2) (typ_stoic T1 T2)
  | sub_all : forall L E S1 S2,
      (forall X, X \notin L ->
          sub (E & [:X:]) (S1 open_tt_var X) (S2 open_tt_var X)) ->
      sub E (typ_all S1) (typ_all S2).

(** Typing relation *)

Reserved Notation "E |= t -: T" (at level 69).

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_top : forall E,
      okt E ->
      E |= trm_top -: typ_top
  | typing_var : forall E x T,
      okt E ->
      binds x (bind_typ T) E ->
      E |= (trm_fvar x) -: T
  | typing_abs : forall L E V e1 T1,
      (forall x, x \notin L ->
        (E & x ~: V) |= (e1 open_ee_var x) -: T1) ->
      E |= (trm_abs V e1) -: (typ_arrow V T1)
  | typing_stoic : forall L E V e1 T1,
      okt E ->
      (forall x, x \notin L ->
        ((pure E) & x ~: V) |= (e1 open_ee_var x) -: T1) ->
      E |= (trm_abs V e1) -: (typ_stoic V T1)
  | typing_sub : forall S E e T,
      E |= e -: S ->
      sub E S T ->
      E |= e -: T
  | typing_app : forall T1 E e1 e2 T2,
      E |= e1 -: (typ_arrow T1 T2) ->
      E |= e2 -: T1 ->
      E |= (trm_app e1 e2) -: T2
  | typing_tabs : forall L E e1 T1,
      okt E ->
      (forall X, X \notin L ->
        ((pure E) & [: X :]) |= (e1 open_te_var X) -: (T1 open_tt_var X)) ->
      E |= (trm_tabs e1) -: (typ_all T1)
  | typing_tapp : forall T1 E e1 T,
      wft E T ->
      E |= e1 -: (typ_all T1) ->
      E |= (trm_tapp e1 T) -: (open_tt T1 T)

where "E |= t -: T" := (typing E t T).

(** Values *)

Inductive value : trm -> Prop :=
  | value_top : value trm_top
  | value_abs  : forall V e1, term (trm_abs V e1) ->
                 value (trm_abs V e1)
  | value_tabs : forall e1, term (trm_tabs e1) ->
                 value (trm_tabs e1)
  | value_var : forall x, value (trm_fvar x).

(** One-step reduction *)

Reserved Notation "t --> t'" (at level 68).

Inductive red : trm -> trm -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      term e2 ->
      e1 --> e1' ->
      (trm_app e1 e2) --> (trm_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      e2 --> e2' ->
      (trm_app e1 e2) --> (trm_app e1 e2')
  | red_tapp : forall e1 e1' T,
      type T ->
      e1 --> e1' ->
      (trm_tapp e1 T) --> (trm_tapp e1' T)
  | red_abs : forall T e1 v2,
      term (trm_abs T e1) ->
      T <> typ_top ->
      value v2 ->
      (trm_app (trm_abs T e1) v2) --> (open_ee e1 v2)
  | red_top : forall T e1 e2,
      term (trm_abs T e1) ->
      T = typ_top ->
      value e2 ->
      (trm_app (trm_abs T e1) e2) --> (open_ee e1 trm_top)
  | red_tabs : forall e1 T,
      term (trm_tabs e1) ->
      type T ->
      red (trm_tapp (trm_tabs e1) T) (open_te e1 T)

where "t --> t'" := (red t t').

(* get environment for type vars *)
Fixpoint tvar_env (E: env) := match E with
  | nil => nil
  | (X, bind_tvar) :: E' => cons (X, bind_tvar) (tvar_env E')
  | _ :: E' => tvar_env E'
  end%list.

(** subseq is useful in formulation of weakening lemmas *)
Inductive subseq : env -> env -> Prop :=
  | subseq_base: subseq empty empty
  | subseq_ext: forall E F x T,  subseq E F -> subseq E (F & x ~: T)
  | subseq_cons: forall E F x b, tvar_env E = tvar_env F ->
                                 subseq E F -> subseq (E & x ~ b) (F & x ~ b).

(** Our goal is to prove preservation and progress *)

Definition preservation := forall E e e' T,
  E |= e -: T ->
  e --> e' ->
  E |= e' -: T.

Definition progress := forall e T,
  empty |= e -: T ->
     value e
  \/ exists e', e --> e'.

(* inhabitable environment *)
Inductive primitive: env -> Prop :=
  | primitive_base: forall x y, primitive (x ~: typ_base & y ~: typ_eff)
  | primitive_tvar: forall X E, primitive E -> primitive (E & [:X:])
  | primitive_typ: forall x X E, primitive E -> primitive (E & x ~: (typ_fvar X)).

Inductive inhabitable: env -> Prop :=
  | inhabitable_empty: inhabitable empty
  | inhabitable_tvar: forall X E,
                        inhabitable E ->
                        inhabitable (E & [:X:])
  | inhabitable_typ: forall z t T E F,
                        inhabitable E ->
                        primitive F ->
                        value t ->
                        F |= t -: T ->
                        inhabitable (E & z ~: T).

(* capsafe types are not capability producing, i.e. capable of creating an instance of E *)

Inductive capsafe: typ -> Prop :=
 | capsafe_top: capsafe typ_top
 | capsafe_base: capsafe typ_base
 | capsafe_eff_any_free: forall S T, type T -> caprod S -> capsafe (typ_arrow S T)
 | capsafe_any_safe_free: forall S T, type S -> capsafe T -> capsafe (typ_arrow S T)
 | capsafe_eff_any: forall S T, type T -> caprod S -> capsafe (typ_stoic S T)
 | capsafe_any_safe: forall S T, type S -> capsafe T -> capsafe (typ_stoic S T)
 | capsafe_all: forall T, type (typ_all T) ->
                          capsafe (open_tt T typ_eff) /\ capsafe (open_tt T typ_base) ->
                          capsafe (typ_all T)

with caprod: typ -> Prop :=
 | caprod_var: forall X, caprod (typ_fvar X)
 | caprod_eff: caprod typ_eff
 | caprod_safe_eff_free: forall S T, capsafe S -> caprod T -> caprod (typ_arrow S T)
 | caprod_safe_eff: forall S T, capsafe S -> caprod T -> caprod (typ_stoic S T)
 | caprod_all: forall T, type (typ_all T) ->
                         caprod (open_tt T typ_eff) \/ caprod (open_tt T typ_base) ->
                         caprod (typ_all T).

(* capsafe environment *)
Inductive healthy: env -> Prop :=
  | healthy_empty: healthy empty
  | healthy_typ: forall x E T, capsafe T -> healthy E ->
                               healthy (E & x ~: T)
  | healthy_tvar: forall X E, healthy E ->
                              healthy (E & [: X :]).

Definition inhabitable_pure_healthy_statement := forall E,
  inhabitable E -> pure E = E -> healthy E.

(* effect safety : it's impossible to construct a term of typ_eff in healthy environment  *)
Definition effect_safety_1 := forall E, healthy E ->
  ~exists e, E |= e -: typ_eff.

Definition effect_safety_2 := forall E t1 t2 T, healthy E ->
  pure E = E ->
  E |= (trm_app t1 t2) -: T  ->
  exists S1 S2, E |= t1 -: (typ_stoic S1 S2).

(* ********************************************************************** *)
(** * Additional Definitions Used in the Proofs *)

(** Computing free type variables in a type *)

Fixpoint fv_tt (T : typ) {struct T} : vars :=
  match T with
  | typ_bvar J            => \{}
  | typ_top               => \{}
  | typ_base              => \{}
  | typ_eff               => \{}
  | typ_fvar X            => \{X}
  | typ_arrow T1 T2       => (fv_tt T1) \u (fv_tt T2)
  | typ_stoic T1 T2       => (fv_tt T1) \u (fv_tt T2)
  | typ_all T1            => (fv_tt T1)
  end.

(** Computing free type variables in a term *)

Fixpoint fv_te (e : trm) {struct e} : vars :=
  match e with
  | trm_top       => \{}
  | trm_bvar i    => \{}
  | trm_fvar x    => \{}
  | trm_abs V e1  => (fv_tt V) \u (fv_te e1)
  | trm_app e1 e2 => (fv_te e1) \u (fv_te e2)
  | trm_tabs e1   => (fv_te e1)
  | trm_tapp e1 V => (fv_tt V) \u (fv_te e1)
  end.

(** Computing free term variables in a type *)

Fixpoint fv_ee (e : trm) {struct e} : vars :=
  match e with
  | trm_top       => \{}
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_abs V e1  => (fv_ee e1)
  | trm_app e1 e2 => (fv_ee e1) \u (fv_ee e2)
  | trm_tabs e1   => (fv_ee e1)
  | trm_tapp e1 V => (fv_ee e1)
  end.

(** Substitution for free type variables in types. *)

Fixpoint subst_tt (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top               => typ_top
  | typ_bvar J            => typ_bvar J
  | typ_base              => typ_base
  | typ_eff               => typ_eff
  | typ_fvar X            => If X = Z then U else (typ_fvar X)
  | typ_arrow T1 T2       => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_stoic T1 T2       => typ_stoic (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T             => typ_all (subst_tt Z U T)
  end.

(** Substitution for free type variables in terms. *)

Fixpoint subst_te (Z : var) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_top       => trm_top
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | trm_app e1 e2 => trm_app  (subst_te Z U e1) (subst_te Z U e2)
  | trm_tabs e1   => trm_tabs (subst_te Z U e1)
  | trm_tapp e1 V => trm_tapp (subst_te Z U e1) (subst_tt Z U V)
  end.

(** Substitution for free term variables in terms. *)

Fixpoint subst_ee (z : var) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_top       => trm_top
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs V e1  => trm_abs V (subst_ee z u e1)
  | trm_app e1 e2 => trm_app (subst_ee z u e1) (subst_ee z u e2)
  | trm_tabs e1   => trm_tabs (subst_ee z u e1)
  | trm_tapp e1 V => trm_tapp (subst_ee z u e1) V
  end.

(** Substitution for free type variables in environment. *)

Definition subst_tb (Z : var) (P : typ) (b : bind) : bind :=
  match b with
  | bind_tvar => bind_tvar
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.

(* ********************************************************************** *)
(** * Tactics *)

(** Constructors as hints. *)

Hint Constructors type term wft ok okt value red subseq sub.

Hint Resolve
  typing_var typing_app typing_tapp sub_refl sub_top sub_trans.

(** Gathering free names already used in the proofs *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv_te x) in
  let D := gather_vars_with (fun x : trm => fv_ee x) in
  let E := gather_vars_with (fun x : typ => fv_tt x) in
  let F := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u C \u D \u E \u F).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

(** These tactics help applying a lemma which conclusion mentions
  an environment (E & F) in the particular case when F is empty *)

Ltac get_env :=
  match goal with
  | |- wft ?E _ => E
  | |- typing ?E _ _ => E
  end.

Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) :=
  let E := get_env in rewrite <- (concat_empty_r E);
  eapply lemma; try rewrite concat_empty_r.

Tactic Notation "apply_empty" constr(F) :=
  apply_empty_bis (get_env) F.

Tactic Notation "apply_empty" "*" constr(F) :=
  apply_empty F; autos*.

(** Tactic to undo when Coq does too much simplification *)

Ltac unsimpl_map_bind :=
  match goal with |- context [ ?B (subst_tt ?Z ?P ?U) ] =>
    unsimpl ((subst_tb Z P) (B U)) end.

Tactic Notation "unsimpl_map_bind" "*" :=
  unsimpl_map_bind; autos*.

(* ********************************************************************** *)
(** * Properties of Set *)

(* ********************************************************************** *)

Lemma notin_union_inv: forall x E F,
  x \notin (E \u F) -> x \notin E /\ x \notin F.
Proof. intros. autos. Qed.

Lemma union_empty_inv: forall (A:Type) (a b: fset A),
   a \u b = \{} -> a = \{} /\ b = \{}.
Proof. intros. split.
  apply fset_extens. rewrite <- H. apply subset_union_weak_l. apply subset_empty_l.
  apply fset_extens. rewrite <- H. apply subset_union_weak_r. apply subset_empty_l.
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

Lemma subset_union : forall (T: Type) (a b c: fset T),
  a \u b \c c -> a \c c /\ b \c c.
Proof. intros. unfolds subset.
  split; intros x; specializes H x; rewrite in_union in H; auto.
Qed.

(* ********************************************************************** *)
(** * Properties of Substitutions *)

(* ********************************************************************** *)
(** ** Properties of type substitution in type *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_tt_rec_type_core : forall T j V U i, i <> j ->
  (open_tt_rec j V T) = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof.
  induction T; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_tt_rec_type : forall T U,
  type T -> forall k, T = open_tt_rec k U T.
Proof.
  induction 1; intros; simpl; f_equal*. unfolds open_tt.
  pick_fresh X. apply* (@open_tt_rec_type_core T2 0 (typ_fvar X)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_tt_fresh : forall Z U T,
  Z \notin fv_tt T -> subst_tt Z U T = T.
Proof.
  induction T; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P n, type P ->
  subst_tt X P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt X P T2) (subst_tt X P T1).
Proof.
  introv WP. generalize n.
  induction T1; intros k; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_tt_rec_type.
Qed.

Lemma subst_tt_open_tt : forall T1 T2 X P, type P ->
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof.
  unfold open_tt. autos* subst_tt_open_tt_rec.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_tt_open_tt_var : forall X Y U T, Y <> X -> type U ->
  (subst_tt X U T) open_tt_var Y = subst_tt X U (T open_tt_var Y).
Proof.
  introv Neq Wu. rewrite* subst_tt_open_tt.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_tt_intro : forall X T2 U,
  X \notin fv_tt T2 -> type U ->
  open_tt T2 U = subst_tt X U (T2 open_tt_var X).
Proof.
  introv Fr Wu. rewrite* subst_tt_open_tt.
  rewrite* subst_tt_fresh. simpl. case_var*.
Qed.

(* ********************************************************************** *)
(** ** Properties of type substitution in terms *)

Lemma open_te_rec_term_core : forall e j u i P ,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros; simpl in *; inversion H; f_equal*; f_equal*.
Qed.

Lemma open_te_rec_type_core : forall e j Q i P, i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
   e = open_te_rec i P e.
Proof.
  induction e; intros; simpl in *; inversion H0; f_equal*;
  match goal with H: ?i <> ?j |- ?t = open_tt_rec ?i _ ?t =>
   apply* (@open_tt_rec_type_core t j) end.
Qed.

Lemma open_te_rec_term : forall e U,
  term e -> forall k, e = open_te_rec k U e.
Proof.
  intros e U WF. induction WF; intros; simpl;
    f_equal*; try solve [ apply* open_tt_rec_type ].
  unfolds open_ee. pick_fresh x.
   apply* (@open_te_rec_term_core e1 0 (trm_fvar x)).
  unfolds open_te. pick_fresh X.
   apply* (@open_te_rec_type_core e1 0 (typ_fvar X)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_te_fresh : forall X U e,
  X \notin fv_te e -> subst_te X U e = e.
Proof.
  induction e; simpl; intros; f_equal*; autos* subst_tt_fresh.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_te_open_te : forall e T X U, type U ->
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T).
Proof.
  intros. unfold open_te. generalize 0.
  induction e; intros; simpls; f_equal*;
  autos* subst_tt_open_tt_rec.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_te_open_te_var : forall X Y U e, Y <> X -> type U ->
  (subst_te X U e) open_te_var Y = subst_te X U (e open_te_var Y).
Proof.
  introv Neq Wu. rewrite* subst_te_open_te.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_te_intro : forall X U e,
  X \notin fv_te e -> type U ->
  open_te e U = subst_te X U (e open_te_var X).
Proof.
  introv Fr Wu. rewrite* subst_te_open_te.
  rewrite* subst_te_fresh. simpl. case_var*.
Qed.


(* ********************************************************************** *)
(** ** Properties of term substitution in terms *)

Lemma open_ee_rec_term_core : forall e j v u i, i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_ee_rec_type_core : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; introv H; simpls; inversion H; f_equal*.
Qed.

Lemma open_ee_rec_term : forall u e,
  term e -> forall k, e = open_ee_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open_ee. pick_fresh x.
   apply* (@open_ee_rec_term_core e1 0 (trm_fvar x)).
  unfolds open_te. pick_fresh X.
   apply* (@open_ee_rec_type_core e1 0 (typ_fvar X)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_ee_fresh : forall x u e,
  x \notin fv_ee e -> subst_ee x u e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_ee_open_ee : forall t1 t2 u x, term u ->
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2).
Proof.
  intros. unfold open_ee. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_ee_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_ee_open_ee_var : forall x y u e, y <> x -> term u ->
  (subst_ee x u e) open_ee_var y = subst_ee x u (e open_ee_var y).
Proof.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall x u e,
  x \notin fv_ee e -> term u ->
  open_ee e u = subst_ee x u (e open_ee_var x).
Proof.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl. case_var*.
Qed.

(** Interactions between type substitutions in terms and opening
  with term variables in terms. *)

Lemma subst_te_open_ee_var : forall Z P x e,
  (subst_te Z P e) open_ee_var x = subst_te Z P (e open_ee_var x).
Proof.
  introv. unfold open_ee. generalize 0.
  induction e; intros; simpl; f_equal*. case_nat*.
Qed.

(** Interactions between term substitutions in terms and opening
  with type variables in terms. *)

Lemma subst_ee_open_te_var : forall z u e X, term u ->
  (subst_ee z u e) open_te_var X = subst_ee z u (e open_te_var X).
Proof.
  introv. unfold open_te. generalize 0.
  induction e; intros; simpl; f_equal*.
  case_var*. symmetry. autos* open_te_rec_term.
Qed.

(** Substitutions preserve local closedure. *)

Lemma subst_tt_type : forall T Z P,
  type T -> type P -> type (subst_tt Z P T).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* type_all as X. rewrite* subst_tt_open_tt_var.
Qed.

Lemma typ_all_open_tt_type: forall T U, type (typ_all T) -> type U -> type (open_tt T U).
Proof. intros. inversions H. pick_fresh X. forwards~ : H2 X.
  rewrite* (@subst_tt_intro X). apply* subst_tt_type.
Qed.

Lemma subst_te_term : forall e Z P,
  term e -> type P -> term (subst_te Z P e).
Proof.
  lets: subst_tt_type. induction 1; intros; simpl; auto.
  apply_fresh* term_abs as x. rewrite* subst_te_open_ee_var.
  apply_fresh* term_tabs as x. rewrite* subst_te_open_te_var.
Qed.

Lemma subst_ee_term : forall e1 Z e2,
  term e1 -> term e2 -> term (subst_ee Z e2 e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
  apply_fresh* term_tabs as Y. rewrite* subst_ee_open_te_var.
Qed.

Hint Resolve subst_tt_type typ_all_open_tt_type subst_te_term subst_ee_term.


(* ********************************************************************** *)
(** * Properties of well-formedness of a type in an environment *)

(** If a type is well-formed in an environment then it is locally closeded. *)

Lemma wft_type : forall E T,
  wft E T -> type T.
Proof.
  induction 1; eauto.
Qed.

(** Through weakening *)

Lemma wft_weaken : forall G T E F,
  wft (E & G) T ->
  ok (E & F & G) ->
  wft (E & F & G) T.
Proof.
  intros. gen_eq K: (E & G). gen E F G.
  induction H; intros; subst; eauto.
  (* case: var *)
  apply wft_var. apply* binds_weaken.
  (* case arrow *)
  (* case: all *)
  apply_fresh* wft_all as Y. apply_ih_bind* H0.
Qed.

(** Through strengthening *)

Lemma wft_strengthen : forall E F x U T,
 wft (E & x ~: U & F) T -> wft (E & F) T.
Proof.
  intros. gen_eq G: (E & x ~: U & F). gen F.
  induction H; intros F EQ; subst; auto.
  apply* wft_var.
  destruct (binds_concat_inv H) as [?|[? ?]].
    apply~ binds_concat_right.
    destruct (binds_push_inv H1) as [[? ?]|[? ?]].
      subst. false.
      apply~ binds_concat_left.
  (* todo: binds_cases tactic *)
  apply_fresh* wft_all as Y. apply_ih_bind* H0.
Qed.

(** Through type substitution *)

Lemma wft_subst_tb : forall F E Z P T,
  wft (E & [: Z :] & F) T ->
  wft E P ->
  ok (E & map (subst_tb Z P) F) ->
  wft (E & map (subst_tb Z P) F) (subst_tt Z P T).
Proof.
  introv WT WP. gen_eq G: (E & [: Z :] & F). gen F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt; auto.
  case_var*. apply_empty* wft_weaken.
    destruct (binds_concat_inv H) as [?|[? ?]].
      apply wft_var.
       apply~ binds_concat_right.
       replace bind_tvar with ((subst_tb Z P) bind_tvar) by reflexivity.
       apply~ binds_map.
      destruct (binds_push_inv H1) as [[? ?]|[? ?]].
        subst. false~.
        applys wft_var. apply* binds_concat_left.
  apply_fresh* wft_all as Y.
   unsimpl ((subst_tb Z P) bind_tvar).
   lets: wft_type.
   rewrite* subst_tt_open_tt_var.
   apply_ih_map_bind* H0.
Qed.

(** Through type reduction *)

Lemma wft_open : forall E U T,
  ok E ->
  wft E (typ_all T) ->
  wft E U ->
  wft E (open_tt T U).
Proof.
  introv Ok WA WU. inversions WA. pick_fresh X.
  autos* wft_type. rewrite* (@subst_tt_intro X).
  lets K: (@wft_subst_tb empty).
  specializes_vars K. clean_empty K. apply* K.
  (* todo: apply empty ? *)
Qed.

(* ********************************************************************** *)
(** * Relations between well-formed environment and types well-formed
  in environments *)

(** If an environment is well-formed, then it does not contain duplicated keys. *)

Lemma ok_from_okt : forall E,
  okt E -> ok E.
Proof.
  induction 1; auto.
Qed.

Hint Extern 1 (ok _) => apply ok_from_okt.

(** Extraction from a typing assumption in a well-formed environments *)

Lemma wft_from_env_has_typ : forall x U E,
  okt E -> binds x (bind_typ U) E -> wft E U.
Proof.
  induction E using env_ind; intros Ok B.
  false* binds_empty_inv.
  inversions Ok.
    false (empty_push_inv H0).
    destruct (eq_push_inv H) as [? [? ?]]. subst. clear H.
     destruct (binds_push_inv B) as [[? ?]|[? ?]]. subst.
       inversions H2.
       apply_empty* wft_weaken.
    destruct (eq_push_inv H) as [? [? ?]]. subst. clear H.
     destruct (binds_push_inv B) as [[? ?]|[? ?]]. subst.
       inversions H3. apply_empty* wft_weaken.
       apply_empty* wft_weaken.
Qed.

(** Extraction from a well-formed environment *)

Lemma wft_from_okt_typ : forall x T E,
  okt (E & x ~: T) -> wft E T.
Proof.
  intros. inversions* H.
  false (empty_push_inv H1).
  destruct (eq_push_inv H0) as [? [? ?]]. false.
  destruct (eq_push_inv H0) as [? [? ?]]. inversions~ H4.
Qed.

(** Automation *)

Lemma wft_weaken_right : forall T E F,
  wft E T ->
  ok (E & F) ->
  wft (E & F) T.
Proof.
  intros. apply_empty* wft_weaken.
Qed.

Hint Resolve wft_weaken_right.
Hint Resolve wft_strengthen.
Hint Resolve wft_from_okt_typ.
Hint Immediate wft_from_env_has_typ.
Hint Resolve wft_subst_tb.


(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

(** Inversion lemma *)

Lemma okt_push_inv : forall E X B,
  okt (E & X ~ B) -> exists T, B = bind_tvar \/ B = bind_typ T.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&?&?): (eq_push_inv H). subst. exists* (typ_fvar X).
    lets (?&?&?): (eq_push_inv H). subst*.
Qed.

Lemma okt_push_tvar_inv : forall E X,
  okt (E & [: X :]) -> okt E /\ X # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. inverts~ M.
    lets (?&?&?): (eq_push_inv H). false.
Qed.

Lemma okt_push_typ_inv : forall E x T,
  okt (E & x ~: T) -> okt E /\ wft E T /\ x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&?&?): (eq_push_inv H). false.
    lets (?&M&?): (eq_push_inv H). subst. inverts~ M.
Qed.

Lemma okt_push_typ_type : forall E x T,
  okt (E & x ~: T) -> type T.
Proof. intros. applys wft_type. forwards*: okt_push_typ_inv. Qed.

Hint Immediate okt_push_typ_type.

(** Through strengthening *)

Lemma okt_strengthen : forall x T (E F:env),
  okt (E & x ~: T & F) ->
  okt (E & F).
Proof.
 introv O. induction F using env_ind.
  rewrite concat_empty_r in *. lets*: (okt_push_typ_inv O).
  rewrite concat_assoc in *.
   lets (U&[?|?]): okt_push_inv O; subst.
      applys~ okt_tvar. apply IHF. applys* okt_push_tvar_inv.
      apply ok_from_okt in O.
      lets (? & H): (ok_push_inv O). eauto.

      applys~ okt_typ. apply IHF. applys* okt_push_typ_inv.
      applys* wft_strengthen.
      apply ok_from_okt in O.
      lets (? & H): (ok_push_inv O). eauto.
Qed.

Lemma okt_weaken : forall E F,
  okt (E & F) -> okt E.
Proof.
  induction F using env_ind; rew_env_concat; introv Okt. auto.
  lets(T & [H | H]): (okt_push_inv Okt); subst.
  apply IHF. lets*: okt_push_tvar_inv Okt.
  apply IHF. lets*: okt_push_typ_inv Okt.
Qed.

(** Through type substitution *)

Lemma okt_subst_tb : forall Z P (E F:env),
  okt (E & [: Z :] & F) ->
  wft E P ->
  okt (E & map (subst_tb Z P) F).
Proof.
 introv O W. induction F using env_ind.
  rewrite map_empty. rewrite concat_empty_r in *.
   lets*: (okt_push_tvar_inv O).
  rewrite map_push. rewrite concat_assoc in *.
   lets (U&[?|?]): okt_push_inv O; subst.
     lets*: (okt_push_tvar_inv O).
     lets*: (okt_push_typ_inv O).
      applys~ okt_typ; lets*: H.
Qed.

(** Automation *)

Hint Resolve okt_subst_tb wft_weaken.
Hint Immediate okt_strengthen.


(* ********************************************************************** *)
(** ** Environment is unchanged by substitution from a fresh name *)

Lemma notin_fv_tt_open : forall Y X T,
  X \notin fv_tt (T open_tt_var Y) ->
  X \notin fv_tt T.
Proof.
 introv. unfold open_tt. generalize 0.
 induction T; simpl; intros k Fr; auto.
 specializes IHT1 k. specializes IHT2 k. auto.
 specializes IHT1 k. specializes IHT2 k. auto.
 apply* IHT.
Qed.

Lemma notin_fv_wf : forall E X T,
  wft E T -> X # E -> X \notin fv_tt T.
Proof.
  induction 1; intros Fr; simpl; autos* notin_empty.
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H Fr.
  pick_fresh Y. apply* (@notin_fv_tt_open Y).
Qed.

Lemma map_subst_tb_id : forall G Z P,
  okt G -> Z # G -> G = map (subst_tb Z P) G.
Proof.
  induction 1; intros Fr; autorewrite with rew_env_map; simpl.
  auto.
  rewrite <- IHokt. reflexivity. eauto.
  rewrite <- IHokt. rewrite* subst_tt_fresh. apply* notin_fv_wf. eauto.
Qed.

(* ********************************************************************** *)
(** ** Regularity of relations *)

Lemma sub_regular : forall E S T,
  sub E S T -> okt E /\ wft E S /\ wft E T.
Proof.
  induction 1; autos*.
  split. pick_fresh X. forwards~: (H0 X). autos* okt_weaken.
  split; apply_fresh* wft_all as Y; forwards~: (H0 Y); iauto.
Qed.

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ term e.
Proof.
  induction 1; iauto.
  splits.
    pick_fresh y. specializes H0 y. destructs~ H0. destruct* (okt_push_typ_inv H0).
    apply_fresh* term_abs as y.
      pick_fresh y. specializes H0 y. destructs~ H0.
        forwards*: okt_push_typ_inv.
      specializes H0 y. destructs~ H0.
  splits.
    pick_fresh y. specializes H1 y. destructs~ H1.
    apply_fresh* term_abs as y.
      pick_fresh y. specializes H1 y. destructs~ H1.
        forwards*: okt_push_typ_inv.
      specializes H1 y. destructs~ H1.
  splits*.
    apply term_tabs with L. intros.
    specializes H1 X. destructs~ H1.
  splits*. destructs IHtyping.
     apply* term_tapp. apply* wft_type.
Qed.

(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> term t.
Proof.
  induction 1; autos*.
Qed.

(** The reduction relation is restricted to well-formed objects. *)

Lemma red_regular : forall t t',
  red t t' -> term t /\ term t'.
Proof.
  induction 1; split; autos* value_regular.
  inversions H. pick_fresh y. rewrite* (@subst_ee_intro y).
  inversions H. pick_fresh y. rewrite* (@subst_ee_intro y).
  inversions H. pick_fresh Y. rewrite* (@subst_te_intro Y).
Qed.

(** Automation *)

Hint Extern 1 (okt ?E) =>
  match goal with
  | H: typing _ _ _ |- _ => apply (proj31 (typing_regular H))
  end.

Hint Extern 1 (wft ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj33 (typing_regular H))
  end.

Hint Extern 1 (type ?T) =>
  let go E := apply (@wft_type E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  end.

Hint Extern 1 (term ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj32 (typing_regular H))
  | H: red ?e _ |- _ => apply (proj1 (red_regular H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular H))
  end.


(* ********************************************************************** *)
(** * Properties of environment *)

(** tvar_env properties *)

Lemma tvar_push_var: forall E x T, tvar_env (E & x ~: T) = tvar_env E.
Proof. intros. rewrite <- cons_to_push. simpl. auto. Qed.

Lemma tvar_push_tvar: forall E X, tvar_env (E & [:X:]) = tvar_env E & [:X:].
Proof. intros. rewrite <- cons_to_push. simpl. rewrite* cons_to_push. Qed.

Lemma tvar_pure : forall E, tvar_env E = tvar_env (pure E).
Proof. intros. inductions E; auto. destruct a. destruct b.
  simpl. rewrite* IHE.
  simpl. cases_if*.
Qed.

Lemma tvar_single_sub: forall X, tvar_env ([:X:]) = [:X:].
Proof. intros. rewrite single_def. reflexivity. Qed.

Lemma tvar_dist : forall E F, tvar_env (E & F) = tvar_env E & tvar_env F.
Proof. intros. inductions F.
  simpl. rewrite <- empty_def. repeat(rewrite concat_empty_r). auto.
  destruct a. destruct b; simpl.
    rewrite cons_to_push. rewrite concat_assoc. rewrite <- cons_to_push.
    simpl. rewrite* IHF. repeat(rewrite cons_to_push). rewrite* concat_assoc.

    rewrite cons_to_push. rewrite concat_assoc. rewrite <- cons_to_push.
    simpl. auto.
Qed.

Lemma tvar_binds : forall X E, binds X bind_tvar E ->
  binds X bind_tvar (tvar_env E).
Proof. introv HB. inductions E.
  rewrite <- empty_def in HB. false* binds_empty_inv.
  destruct a. destruct b.
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv HB) as [HC|HC]; destruct HC.
      inversions* H0. apply* binds_concat_left.
    simpl. rewrite cons_to_push in *. destruct (binds_push_inv HB) as [HC|HC]; destruct HC.
      inversions H0. auto.
Qed.


Lemma tvar_binds_equiv : forall X E, ok E -> binds X bind_tvar E <->
  binds X bind_tvar (tvar_env E).
Proof. introv OK. split.

  introv HB. inductions E.
  rewrite <- empty_def in HB. false* binds_empty_inv.
  destruct a. destruct b.
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv HB) as [HC|HC]; destruct HC.
      inversions* H0. apply* binds_concat_left.
    simpl. rewrite cons_to_push in *. destruct (binds_push_inv HB) as [HC|HC]; destruct HC.
      inversions H0. auto.

  introv HB. inductions E.
  simpls. rewrite <- empty_def in HB. false* binds_empty_inv.
  destruct a. destruct b.
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv HB) as [HC|HC]; destruct HC.
      inversions* H0. apply* binds_concat_left.
    simpls. rewrite cons_to_push in *. destruct (ok_push_inv OK).
      destruct (classic (X = v)). substs. forwards~ : IHE. false (binds_fresh_inv H1 H0).
      apply* binds_concat_left.
Qed.

Lemma tvar_wft : forall E F T, ok F -> tvar_env E = tvar_env F ->
  wft E T -> wft F T.
Proof. introv Ok Tv Wf. gen F. inductions Wf; intros; auto.
  apply wft_var. rewrite* tvar_binds_equiv.
    rewrite <- Tv. apply* tvar_binds.
  apply_fresh wft_all as X. auto. apply* H0.
    repeat(rewrite <- cons_to_push). simpl. rewrite* Tv.
Qed.

Lemma tvar_map: forall E Z P,
  tvar_env (map (subst_tb Z P) E) =
  map (subst_tb Z P) (tvar_env E).
Proof. intros. inductions E.
  simpl; rewrite <- empty_def, map_empty, empty_def. reflexivity.
  destruct a. destruct b; rewrite ?cons_to_push.

  rewrite ?map_push, tvar_dist, tvar_push_tvar, map_push. simpl.
    rewrite tvar_single_sub. rewrite* IHE.

  rewrite  map_push. simpl. rewrite ?tvar_push_var. auto.
Qed.

(** Properties of subsequence *)

Lemma subseq_refl: forall E, subseq E E.
Proof. intros. inductions E.
  rewrite* <- empty_def.
  destruct a. rewrite cons_to_push. apply* subseq_cons.
Qed.

Lemma subseq_empty: forall E, tvar_env E = empty -> subseq empty E.
Proof. intros. inductions E.
 rewrite* <- empty_def.
 destruct a. rewrite cons_to_push. destruct b.
   simpl in H. rewrite empty_def in H. inversion H.
   simpl in H. apply* subseq_ext.
Qed.

Hint Resolve subseq_refl subseq_empty.

Lemma subseq_trans : forall E F G,
 subseq E F -> subseq F G -> subseq E G.
Proof. intros. gen E. induction H0; intros; auto.
  inversions* H1.
    rewrite empty_def, <- cons_to_push in H4. inversion H4.
    rewrite <- ?cons_to_push in H2; inversions* H2.
    rewrite <- ?cons_to_push in H2; inversions* H2. apply* subseq_cons. rewrite* H3.
Qed.

Lemma subseq_extend: forall E F G,
  subseq F G -> subseq (E & F) (E & G).
Proof. introv Sub. inductions Sub; auto.
  rewrite concat_assoc. apply* subseq_ext.
  rewrite ?concat_assoc. apply* subseq_cons.
    rewrite ?tvar_dist, H. auto.
Qed.

Lemma subseq_empty_inv: forall L, subseq L empty -> L = empty.
Proof. introv Seq. inductions Seq; auto;
  rewrite <- cons_to_push in x; rewrite empty_def in x; inversion x.
Qed.

Lemma subseq_tvar: forall E F, subseq E F -> tvar_env E = tvar_env F.
Proof. introv Seq. inductions Seq; auto.
  rewrite* <- cons_to_push.
  destruct b; rewrite ?tvar_push_tvar, ?tvar_push_var, IHSeq; auto.
Qed.

Lemma subseq_concat: forall E F M N,
  subseq E M -> subseq F N -> subseq (E & F) (M & N).
Proof with eauto.
  introv Sub1 Sub2. inductions Sub2; auto.

  rewrite ?concat_empty_r...
  rewrite concat_assoc. apply* subseq_ext.
  rewrite ?concat_assoc. apply* subseq_cons.
    rewrite ?tvar_dist, H, (subseq_tvar Sub1). auto.
Qed.

Lemma subseq_pure: forall E, subseq (pure E) E.
Proof. intros. induction E; auto.
  destruct a. destruct b.
    simpl. rewrite ?cons_to_push. apply* subseq_cons.
      rewrite* <- tvar_pure.
    simpl. cases_if*; rewrite ?cons_to_push in *; auto.
      apply* subseq_cons. rewrite* <- tvar_pure.
Qed.

Lemma subseq_fresh: forall E F x, subseq E F ->
  x # F -> x # E.
Proof. intros. inductions H; auto. Qed.

Lemma subseq_ok : forall E F, ok F -> subseq E F -> ok E.
Proof. intros. induction H0; auto.
  destructs (ok_push_inv H). apply ok_push. auto. apply subseq_fresh with F; auto.
Qed.

Lemma subseq_push_inv: forall E F x u,
  ok F ->
  subseq (E & x ~ u) F ->
  binds x u F.
Proof. introv Ok Seq. inductions Seq; auto.
  rewrite empty_def, <- cons_to_push in x. inversion x.
  destruct (ok_push_inv Ok).  forwards~ : IHSeq H.
    destruct (classic (x = x0)). substs. false. autos* binds_fresh_inv.
    apply* binds_concat_left.
  rewrite <- ?cons_to_push in x. inversions x.  auto.
Qed.

Lemma subseq_push_eq_inv: forall E F x u v,
  ok F ->
  x # F ->
  subseq (E & x ~ u) (F & x ~ v) ->
  subseq E F /\ u = v.
Proof. introv Ok Fresh Seq. inductions Seq.
  rewrite empty_def, <- cons_to_push in x. inversions x.
  rewrite <- ?cons_to_push in x. inversions x.
  forwards~ : subseq_push_inv Ok Seq. false. autos* binds_fresh_inv.
  rewrite <- ?cons_to_push in x2, x. inversions x2. inversions x. auto.
Qed.

Lemma subseq_push_tvar_inv : forall E F X,
  subseq E (F & [:X:]) -> exists E', E = E' & [:X:] /\ subseq E' F.
Proof. introv Seq. inductions Seq.
  rewrite empty_def, <- cons_to_push in x. inversion x.
  rewrite <- ?cons_to_push in x. inversion x.
  rewrite <- ?cons_to_push in x. inversions x. iauto.
Qed.

Lemma subseq_single_inv : forall E v b,
  subseq E (v ~ b) -> E = empty \/ E = v ~ b.
Proof. introv Seq. inductions Seq; auto.
  rewrite <- cons_to_push, single_def in x. inversions x.
    rewrite <- empty_def in Seq. forwards~ : subseq_empty_inv Seq.
  rewrite <- cons_to_push, single_def in x. inversions x.
    rewrite <- empty_def in Seq. forwards~ : subseq_empty_inv Seq.
    right. rewrite H0, concat_empty_l; auto.
Qed.

Lemma subseq_length: forall E F, subseq E F -> length E <= length F.
Proof. introv Seq. inductions Seq; auto.
  rewrite <- cons_to_push. simpl. apply* le_S.
  rewrite <- ?cons_to_push. simpl. apply* le_n_S.
Qed.

Lemma subseq_false: forall F x v, subseq (F & x ~ v) F -> False.
Proof. introv Seq.
  lets : subseq_length Seq. rewrite <- cons_to_push in H. simpl in H.
  applys~ PeanoNat.Nat.nle_succ_diag_l H.
Qed.

Lemma subseq_binds: forall E F x b, ok F -> subseq E F ->
  binds x b E -> binds x b F.
Proof. intros. inductions H0; auto.
  destruct (classic (x = x0)); subst.
    destruct (ok_push_inv H). forwards~ : IHsubseq. false* binds_fresh_inv.
    apply* binds_push_neq.
  destruct (binds_push_inv H2). destruct H3. substs*.
    apply* binds_push_neq.
Qed.

Lemma subseq_okt : forall E F, okt F -> subseq E F -> okt E.
Proof. introv Ok Seq. inductions Seq; auto.
  destruct* (okt_push_typ_inv Ok).
  destruct b.
    destructs (okt_push_tvar_inv Ok). apply okt_tvar. auto.
      apply subseq_fresh with F; auto.
    destructs (okt_push_typ_inv Ok). apply okt_typ. auto.
      apply tvar_wft with F; auto. apply subseq_fresh with F; auto.
Qed.

(** pure properties *)

Lemma pure_closed: forall E x T, binds x (bind_typ T) (pure E) -> closed_typ T = true.
Proof. intros. inductions E.
  simpls. rewrite <- empty_def in H. false* binds_empty_inv.
  destruct a. simpls. destruct b; rewrite cons_to_push in *.

  destruct (binds_push_inv H); destruct H0. false. apply* IHE.

  cases* (closed_typ t). destruct (binds_push_inv H); destruct H0.
    inversions* H1.
    apply* IHE.
Qed.

Lemma pure_dist: forall E F, pure (E & F) = pure E & pure F.
Proof. rewrite concat_def. intros. gen E. induction F; intros E; autos.
  rewrite LibList.app_cons. destruct a. destruct b.
  simpl. rewrite LibList.app_cons. rewrite* <- IHF.
  simpl. destruct* (closed_typ t). rewrite LibList.app_cons. rewrite* <- IHF.
Qed.

Lemma pure_dom_subset : forall E, dom (pure E) \c dom E.
Proof. intros. induction E.
  simpl. apply subset_refl.
  destruct a. destruct b.
  simpl. repeat(rewrite cons_to_push). repeat(rewrite dom_push).
    eapply subset_trans. eapply subset_union_2.
    eapply subset_refl. exact IHE. apply subset_refl.
  simpl. destruct* (closed_typ t).
    repeat(rewrite cons_to_push; rewrite dom_push).
      apply* subset_union_2. apply subset_refl.
    rewrite cons_to_push. rewrite dom_push.
      eapply subset_trans. exact IHE. apply subset_union_weak_r.
Qed.

Lemma pure_binds: forall E x v, ok E -> binds x v (pure E) -> binds x v E.
Proof. intros. induction E.
  simpl in *. autos.
  destruct a. destruct b.
    simpl in *. rewrite cons_to_push in *. destruct (binds_push_inv H0).
      destruct H1. subst. apply binds_push_eq.
      destruct H1. apply* binds_push_neq.
    simpl in *.  rewrite cons_to_push in *. destruct (closed_typ t).
      destruct (binds_push_inv H0).
        destruct H1. substs. apply* binds_push_eq.
        destruct H1. apply* binds_push_neq.
      rewrite <- concat_empty_r. apply binds_weaken; rewrite* concat_empty_r.
Qed.

Lemma pure_binds_reverse: forall E X, binds X bind_tvar E -> binds X bind_tvar (pure E).
Proof. intros. induction E.
  simpl in *. autos.
  destruct a. destruct b.
    simpl in *. rewrite cons_to_push in *. destruct (binds_push_inv H).
      destruct H0. subst. apply binds_push_eq.
      destruct H0. apply* binds_push_neq.
    simpl in *. rewrite cons_to_push in *. destruct (binds_push_inv H). false H0.
      destruct H0. destruct* (closed_typ t).
Qed.

Lemma pure_binds_in: forall E x T, closed_typ T = true ->
   binds x (bind_typ T) E -> binds x (bind_typ T) (pure E).
Proof. intros. induction E.
  (* nil *)
  rewrite <- empty_def in H0. destruct(binds_empty_inv H0).
  (* x::xs *)
  destruct a. destruct b.
    (* bind_typ *)
    simpl. rewrite cons_to_push in *. destruct (binds_push_inv H0).
    destruct H1. inversion H2.
    destruct H1. apply* binds_push_neq.
    (* bind_typ *)
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv H0).
    destruct H1. inversions H2. rewrite* H.
    destruct H1. destruct* (closed_typ t).
Qed.

Lemma pure_wft: forall E V, ok E -> wft (pure E) V -> wft E V.
Proof. intros. remember (pure E) as G. gen E. induction H0; intros; substs; autos.
  apply wft_var. apply* pure_binds.
  apply_fresh* wft_all as Y. apply* H0. repeat(rewrite <- cons_to_push). autos.
Qed.

Lemma pure_wft_weaken: forall E F G V,
  ok (E & F & G) -> wft (E & (pure F) & G) V -> wft (E & F & G) V.
Proof. intros. inductions H0; intros; subst; autos.
  apply wft_var. binds_cases H0.
    apply binds_concat_left; autos. apply* binds_concat_left_ok.
    apply binds_concat_left; autos. apply* binds_concat_right. apply* pure_binds.
      lets*: ok_concat_inv_r (ok_concat_inv_l H).
    apply binds_concat_right. auto.
  apply_fresh wft_all as Y.
    assert (HI: ok (E & F & (G & [: Y :]))).
      rewrite concat_assoc. apply* ok_push.
    forwards~ HII: (H0 Y). apply HI.  rewrite* concat_assoc.
    rewrite* <- concat_assoc.
Qed.

Lemma pure_wft_reverse: forall E V, wft E V -> wft (pure E) V.
Proof. intros. inductions H; autos.
  apply wft_var. apply* pure_binds_reverse.
  apply_fresh* wft_all as Y. forwards~ HI: (H0 Y).
    rewrite pure_dist in HI. rewrite single_def in *. autos.
Qed.

Lemma pure_empty : pure empty = empty.
Proof. rewrite empty_def. reflexivity. Qed.

Lemma pure_single_true : forall x U, closed_typ U = true ->
  pure (x ~: U) = x ~: U.
Proof. intros.
  replace (x ~: U) with (empty & x ~: U) by rewrite* concat_empty_l.
  rewrite <- cons_to_push. simpls. rewrite H.
  rewrite pure_empty. reflexivity.
Qed.

Lemma pure_single_tvar : forall X, pure ([:X:]) = [:X:].
Proof. intros. replace ([:X:]) with (empty & [:X:]) by rewrite* concat_empty_l.
  rewrite <- cons_to_push. simpl. rewrite pure_empty. reflexivity.
Qed.

Lemma pure_single_false : forall x U, closed_typ U = false ->
  pure (x ~: U) = empty.
Proof. intros.
  replace (x ~: U) with (empty & x ~: U) by rewrite* concat_empty_l.
  rewrite <- cons_to_push. simpls. rewrite H.
  rewrite pure_empty. reflexivity.
Qed.

Lemma pure_okt : forall E,
  okt E -> okt (pure E).
Proof. intros. induction* E.
  destruct a. destruct b; simpl; rewrite cons_to_push in *.
  apply okt_tvar. apply IHE. lets*: okt_push_tvar_inv H.
  unfolds. lets(_ & HI): okt_push_tvar_inv H. autos* (pure_dom_subset E).
  destructs (okt_push_typ_inv H). destruct* (closed_typ t).
    apply okt_typ. apply* IHE. apply* pure_wft_reverse.
    lets: pure_dom_subset E. unfolds subset.
    unfolds notin. autos.
Qed.

Lemma subseq_pure_dist: forall E F,
  subseq E F -> subseq (pure E) (pure F).
Proof. introv Seq. inductions Seq.
  rewrite* empty_def.
  cases (closed_typ T).
    rewrite pure_dist, pure_single_true; auto.
    rewrite pure_dist, pure_single_false, concat_empty_r; auto.
  destruct b.
    rewrite ?pure_dist, ?pure_single_tvar. apply* subseq_concat.
    cases (closed_typ t).
      rewrite ?pure_dist, ?pure_single_true; auto. apply* subseq_concat.
      rewrite ?pure_dist, ?pure_single_false, ?concat_empty_r; auto.
Qed.

Lemma pure_eq : forall E, pure (pure E) = pure E.
Proof. intros. induction E; autos.
  destruct a. destruct b; autos.
  simpls. rewrite* IHE.
  simpls. remember (closed_typ t). symmetry in Heqb. destruct* b.
    simpls. rewrite* Heqb. rewrite* IHE.
Qed.

Lemma closed_subst_tt: forall T,
  closed_typ T = true ->
  forall Z P, closed_typ (subst_tt Z P T) = true.
Proof. intros. inductions T; inversions H; simpls; auto. Qed.

Lemma pure_map : forall E Z P,
  subseq (map (subst_tb Z P) (pure E)) (pure (map (subst_tb Z P) E)).
Proof. intros. inductions E.
  rewrite <- empty_def, pure_empty, map_empty, pure_empty. auto.

  destruct a; rewrite cons_to_push. destruct b.
  (* X *)
  rewrite pure_dist, pure_single_tvar, ?map_push, pure_dist. simpl.
  rewrite pure_single_tvar. apply* subseq_concat.
  (* x:T*)
    cases (closed_typ t).
    (* T pure *)
    rewrite pure_dist, pure_single_true, ?map_push, pure_dist; auto. simpl.
    rewrite pure_single_true. apply* subseq_concat.
    apply* closed_subst_tt.
    (* T impure *)
    rewrite pure_dist, pure_single_false, ?map_push, pure_dist, concat_empty_r; auto.
    simpl. cases (closed_typ (subst_tt Z P t)).
    rewrite* pure_single_true.
    rewrite* pure_single_false. rewrite* concat_empty_r.
Qed.

Lemma pure_map_eq : forall E Z P, exists M,
  pure (map (subst_tb Z P) E) = map (subst_tb Z P) M /\
  subseq (pure E) M /\ subseq M E.
Proof. intros. inductions E.
  exists (@empty bind). rewrite <- empty_def, pure_empty, map_empty, pure_empty; auto.

  destruct a; rewrite cons_to_push. destruct b.
  (* X *)
  destruct (IHE Z P) as [M [Eq [Seq1 Seq2]]]. exists (M & [:v:]).
  rewrite pure_dist, pure_single_tvar, ?map_push, pure_dist, Eq. simpl.
  rewrite pure_single_tvar. splits*; apply* subseq_concat.
  (* x:T*)
    destruct (IHE Z P) as [M [Eq [Seq1 Seq2]]].
    cases (closed_typ t).
    (* T pure *)
    exists (M & v ~: t).
    rewrite pure_dist, pure_single_true, ?map_push, pure_dist, Eq; auto. simpl.
    rewrite pure_single_true. splits*; apply* subseq_concat.
    apply* closed_subst_tt.
    (* T impure *)
    rewrite pure_dist, pure_single_false, ?map_push, pure_dist, concat_empty_r, Eq; auto.
    simpl. cases (closed_typ (subst_tt Z P t)).
    exists (M & v ~: t). splits*. rewrite map_push, pure_single_true; auto. apply* subseq_concat.
    exists M. splits*. rewrite* pure_single_false. rewrite* concat_empty_r.
Qed.

(* ********************************************************************** *)
(** * Properties of Subtyping *)


Lemma sub_stoic_inv: forall E T U1 U2,
  sub E T (typ_stoic U1 U2) ->
  exists S1 S2, T = typ_stoic S1 S2 /\ sub E U1 S1 /\ sub E S2 U2.
Proof. intros. gen_eq S: (typ_stoic U1 U2). gen U1 U2.
  inductions H; intros; substs; tryfalse; iauto.
  inversions H0. jauto.
  forwards~ : IHsub2 U1 U2. destruct H2 as [M1 [M2 Ha]].
    forwards~ : IHsub1 M1 M2; jauto.
  inversions* H1.
Qed.

Lemma sub_arrow_inv: forall E T U1 U2,
  sub E T (typ_arrow U1 U2) ->
  exists S1 S2, (T = typ_arrow S1 S2 \/ T = typ_stoic S1 S2) /\ sub E U1 S1 /\ sub E S2 U2.
Proof. intros.
  gen_eq S: (typ_arrow U1 U2).  gen U1 U2.
  inductions H; intros; substs; tryfalse; jauto.
  inversions H0. jauto.
  forwards~ : IHsub2 U1 U2. destruct* H2 as [M1 [M2 [Ha [Hb Hc]]]]. destruct* Ha.
    substs. forwards~ : IHsub1 M1 M2. forwards~ : IHsub2 U1 U2. jauto.
    substs. lets*: sub_stoic_inv H0. jauto.
  inversions H2. jauto.
  inversions H1. jauto.
Qed.

Lemma sub_all_inv: forall E T S L,
  sub E S (typ_all T) ->
  exists U, S = typ_all U /\
            (forall X, X \notin L -> sub (E & [: X :])
                                         (U open_tt_var X)
                                         (T open_tt_var X)).
Proof. admit. Qed.

Lemma sub_arrow_inv_sub: forall E S1 S2 U1 U2,
  sub E (typ_arrow S1 S2) (typ_arrow U1 U2) ->
  sub E U1 S1 /\ sub E S2 U2.
Proof. intros. lets: sub_arrow_inv H. destruct H0 as [S3 [S4 [H1 [H2 H3]]]].
  destruct H1 as [H4 | H4]; inversion* H4.
Qed.

Lemma sub_stoic_inv_sub: forall E S1 S2 U1 U2,
  sub E (typ_stoic S1 S2) (typ_stoic U1 U2) ->
  sub E U1 S1 /\ sub E S2 U2.
Proof. intros. lets: sub_stoic_inv H. destruct H0 as [S3 [S4 [H1 [H2 H3]]]].
  inversions* H1.
Qed.

Lemma sub_degen_inv_sub: forall E S1 S2 U1 U2,
  sub E (typ_stoic S1 S2) (typ_arrow U1 U2) ->
  sub E U1 S1 /\ sub E S2 U2.
Proof. intros. lets: sub_arrow_inv H. destruct H0 as [S3 [S4 [H1 [H2 H3]]]].
  destruct H1 as [H1 | H1]; inversions* H1.
Qed.

Lemma sub_degen_inv_false: forall E S1 S2 U1 U2,
  sub E (typ_arrow S1 S2) (typ_stoic U1 U2) -> False.
Proof. intros. lets: sub_stoic_inv H. false* H0. Qed.

Lemma sub_base_eq: forall E S, sub E S typ_base -> S = typ_base.
Proof. intros. inductions H; auto. Qed.

Lemma sub_top_eq: forall E S, sub E typ_top S -> S = typ_top.
Proof. intros. inductions H; auto. Qed.

Lemma sub_top_neq: forall E S T, sub E S T -> T <> typ_top -> S <> typ_top.
Proof. intros. inductions H; try solve [intros Hc; false]; auto. Qed.

Lemma sub_closed: forall E S T, sub E S T -> T <> typ_top ->
  closed_typ T = true -> closed_typ S = true.
Proof. intros. destruct T; auto.
  lets: sub_base_eq H. substs*.
  lets: sub_stoic_inv H. destruct H2 as [S1 [S2 [H2 _]]]. substs*.
  let L := gather_vars in lets: sub_all_inv L H.
    destruct H2 as [U [Ha _]]. substs*.
Qed.

Hint Resolve sub_degen_inv_false sub_base_eq.

(* ********************************************************************** *)
(** * Properties of Typing *)


(* ********************************************************************** *)
(** Weakening (5) *)

Lemma typing_weakening : forall E F G e T,
   typing (E & G) e T ->
   okt (E & F & G) ->
   typing (E & F & G) e T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as x. forwards~ K: (H x).
   apply_ih_bind (H0 x); eauto.
  apply_fresh* typing_stoic as x.
    repeat(rewrite pure_dist in *). rewrite <- concat_assoc.
    apply* H1. rewrite* concat_assoc. rewrite concat_assoc. repeat(rewrite <- pure_dist).
    apply okt_typ.  apply* pure_okt.
    forwards~ K: (H0 x). lets(Hk & _): typing_regular K. lets: wft_from_okt_typ Hk.
    apply pure_wft_reverse. apply* wft_weaken. apply* pure_wft. rewrite* pure_dist.
    assert (Ha: x \notin dom E \u dom F \u dom G) by autos.
    intros HI. apply Ha. repeat(rewrite pure_dist in HI). repeat(rewrite dom_concat in HI).
      repeat(rewrite in_union in *). rewrite or_assoc in HI.  branches HI.
     branch 1. lets*: pure_dom_subset E.
     branch 2. lets*: pure_dom_subset F.
     branch 3. lets*: pure_dom_subset G.
  apply* typing_degen.
  apply* typing_app.
  apply_fresh* typing_tabs as X.
    repeat(rewrite pure_dist in *). rewrite <- concat_assoc.
    apply* H1. rewrite* concat_assoc. rewrite concat_assoc. repeat(rewrite <- pure_dist).
    apply okt_tvar.  apply* pure_okt.
    forwards~ K: (H0 X). lets(Hk & _): typing_regular K.
    assert (Ha: X \notin dom E \u dom F \u dom G) by autos.
    intros HI. apply Ha. repeat(rewrite pure_dist in HI). repeat(rewrite dom_concat in HI).
      repeat(rewrite in_union in *). rewrite or_assoc in HI.  branches HI.
     branch 1. lets*: pure_dom_subset E.
     branch 2. lets*: pure_dom_subset F.
     branch 3. lets*: pure_dom_subset G.
  apply* typing_tapp.
Qed.

Lemma typing_wft: forall E e T, typing E e T -> wft E T.
Proof.
  intros. induction H. applys~ wft_from_env_has_typ x.
  pick_fresh x. forwards~ K: (H x). destructs (typing_regular K).
    apply* wft_arrow. forwards~ : H0 x. apply_empty* wft_strengthen.
  apply wft_stoic. pick_fresh x. forwards~: (H0 x).
    lets(H3 & _): (typing_regular H2). lets*: wft_from_okt_typ H3.
    apply* pure_wft.

    pick_fresh x. forwards~: (H1 x).
    rewrite <- (@concat_empty_r bind (x ~: V) ) in H2. rewrite concat_assoc in H2.
    lets: wft_strengthen H2. rewrite concat_empty_r in H3. apply* pure_wft.
  inverts* IHtyping.
  inverts* IHtyping1.
  let L := gather_vars in (apply* (@wft_all L)). intros.
    forwards~: (H1 X). rewrite <- (@concat_empty_l bind E).
    apply pure_wft_weaken; rewrite* concat_empty_l.
  apply* wft_open.
Qed.

Lemma typing_weakening_env : forall E F G e T,
  typing (E & (pure F) & G) e T ->
  okt (E & F & G) ->
  typing (E & F & G) e T.
Proof. intros. inductions H.
  apply* typing_var. binds_cases H0; autos.
    apply* binds_weaken. apply* binds_concat_left.
    apply binds_concat_right. apply* pure_binds.
    autos* ok_concat_inv_l ok_concat_inv_r ok_from_okt.
  apply_fresh* typing_abs as x.  forwards~ : H x.
    apply_ih_bind* H0. destructs (typing_regular H2).
    applys~ okt_typ. apply* pure_wft_weaken.
  apply_fresh typing_stoic as x. auto.
    repeat(rewrite pure_dist in *). rewrite pure_eq in *.
    apply_ih_bind* H1. rewrite* pure_eq. forwards~ : H0 x.
  apply* typing_degen.
  apply* typing_app.
  apply_fresh typing_tabs as X; auto.
    repeat(rewrite pure_dist in *). rewrite pure_eq in *.
    apply_ih_bind* H1. rewrite* pure_eq. forwards~ : H0 X.
  apply typing_tapp; auto. apply* pure_wft_weaken.
Qed.

Lemma typing_strengthen_env: forall E u U, value u -> typing E u U ->
  closed_typ U = true -> typing (pure E) u U.
Proof. intros. induction H0; simpls; inversion H1.
  apply typing_var. apply* pure_okt. apply* pure_binds_in.
  apply_fresh* typing_stoic as y. apply* pure_okt. rewrite* pure_eq.
  inversion H.
  apply_fresh* typing_tabs as y. apply* pure_okt. rewrite* pure_eq.
  inversion H.
Qed.


(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma open_tt_fv_subset: forall k U T,
  fv_tt T \c fv_tt (open_tt_rec k U T).
Proof. intros. gen k. induction T; intros; simpls;
  autos* subset_refl subset_empty_l subset_union_2.
Qed.

Lemma open_te_fv_subset: forall k U e,
  fv_te e \c fv_te (open_te_rec k U e).
Proof. intros. gen k. induction e; intros; simpls;
  autos* subset_empty_l subset_union_2 open_tt_fv_subset.
Qed.

Lemma open_ee_fv_subset: forall k u e,
  fv_ee e \c fv_ee (open_ee_rec k u e).
Proof. intros. gen k. induction e; intros; simpls;
  autos* subset_empty_l subset_refl subset_union_2.
Qed.

Lemma open_ee_te_fv_eq: forall k U e,
  fv_ee e = fv_ee (open_te_rec k U e).
Proof. intros. gen k. induction e; intros; simpls; autos.
  rewrites (IHe1 k).
  rewrites (IHe2 k).
  reflexivity.
Qed.

Lemma open_te_ee_fv_subset: forall k u e,
  fv_te e \c fv_te (open_ee_rec k u e).
Proof. intros. gen k. induction e; intros; simpls;
  autos* subset_empty_l subset_union_2 subset_refl.
Qed.

Lemma open_tt_tt_fv_subset: forall k T1 T2,
  fv_tt (open_tt_rec k T1 T2) \c fv_tt T1 \u fv_tt T2.
Proof. intros. gen k. induction T2; intros; simpls;
  autos* union_comm subset_empty_l subset_union_weak_r.
  destruct (prop_degeneracy (k = n)).
    (* k = n*)
    apply is_True_inv in H2. rewrite* If_l. apply subset_union_weak_l.
    (* k != n*)
    apply is_False_inv in H2. rewrite* If_r.

  lets*: (subset_union_2 (IHT2_1 k) (IHT2_2 k)).
  rewrite union_assoc in H2.
  rewrite union_comm in H2.
  replace ((fv_tt T1 \u fv_tt T2_1) \u fv_tt T1) with (fv_tt T1 \u fv_tt T2_1) in H2 by
    (rewrite union_comm; rewrite <- union_assoc; rewrite* union_same).
  rewrite union_assoc. rewrite*  union_comm.

  lets*: (subset_union_2 (IHT2_1 k) (IHT2_2 k)).
  rewrite union_assoc in H2.
  rewrite union_comm in H2.
  replace ((fv_tt T1 \u fv_tt T2_1) \u fv_tt T1) with (fv_tt T1 \u fv_tt T2_1) in H2 by
    (rewrite union_comm; rewrite <- union_assoc; rewrite* union_same).
  rewrite union_assoc. rewrite*  union_comm.
Qed.

Lemma wft_fv_tt: forall E T,
  wft E T -> fv_tt T \c dom E.
Proof.
  intros. induction H; simpls; autos* subset_empty_l.
  lets: get_some_inv (binds_get H). unfolds. intros.
    rewrite in_singleton in H2. rewrite* H2.
  replace (dom E) with (dom E \u dom E) by (autos* union_same). apply* subset_union_2.
  replace (dom E) with (dom E \u dom E) by (autos* union_same). apply* subset_union_2.
  pick_fresh X. forwards~ HI: (H0 X). rewrite dom_concat in HI. rewrite dom_single in HI.
    assert (HII: fv_tt T \c dom E \u \{X}).
      apply subset_trans with (fv_tt (T open_tt_var X)).
      autos* open_tt_fv_subset. autos.
    apply subset_strengthen with X; autos.
Qed.

Ltac solve_subsets :=
  match goal with
    | [|- _ \u _ \c dom ?E ] => rewrite <- union_same; eapply subset_trans;
                                apply* subset_union_2; apply pure_dom_subset
    | [|- _ \c dom ?E ] => eapply subset_trans; eauto; apply pure_dom_subset
    | [_: ?a \c ?E, _: ?b \c ?E |- ?a \u ?b \c ?E ] =>
      rewrite <- union_same; apply* subset_union_2
  end.

Ltac splits_solve_subsets := splits*; try solve_subsets.

Lemma typing_env_fv : forall E e T,
  typing E e T -> fv_te e \c dom E /\ fv_ee e \c dom E /\ fv_tt T \c dom E.
Proof. intros. inductions H; auto.
  (* var *)
  simpls. splits; try solve [autos* subset_empty_l wft_fv_tt].
    forwards~ K:  get_some_inv (binds_get H0). unfolds subset.
    intros. rewrite in_singleton in H1. subst*.
  (* abs *)
  simpl. pick_fresh x. forwards~ : H x. forwards~ : H0 x. destructs H2.
  rewrite dom_concat in *. rewrite dom_single in *.
  forwards~ : subset_strengthen (subset_trans (@open_te_ee_fv_subset 0 (trm_fvar x) e1) H2).
  forwards~ : subset_strengthen (subset_trans (@open_ee_fv_subset 0 (trm_fvar x) e1) H3).
  forwards~ : subset_strengthen H4.
  forwards~ : wft_fv_tt (wft_from_okt_typ (proj1 (typing_regular H1))).
  splits_solve_subsets.
  (* abs closed *)
  simpl. pick_fresh x. forwards~ : H0 x. forwards~ : H1 x. destructs H3.
  rewrite dom_concat in *. rewrite dom_single in *.
  forwards~ : subset_strengthen (subset_trans (@open_te_ee_fv_subset 0 (trm_fvar x) e1) H3).
  forwards~ : subset_strengthen (subset_trans (@open_ee_fv_subset 0 (trm_fvar x) e1) H4).
  forwards~ : subset_strengthen H5.
  forwards~ : wft_fv_tt (wft_from_okt_typ (proj1 (typing_regular H2))).
  splits_solve_subsets.
  (* app *)
  destructs IHtyping1. simpls. destruct (subset_union H3). destructs IHtyping2.
  splits_solve_subsets.
  (* tabs closed *)
  simpl. pick_fresh X. forwards~ : H1 X. destructs H2.
  rewrite dom_concat in *. rewrite dom_single in *.
  forwards~ : subset_strengthen (subset_trans (@open_te_fv_subset 0 (typ_fvar X) e1) H2).
  unfold open_te in H3. rewrite <- open_ee_te_fv_eq in H3. forwards~ : subset_strengthen H3.
  forwards~ : subset_strengthen (subset_trans (@open_tt_fv_subset 0 (typ_fvar X) T1) H4).
  splits_solve_subsets.
  (* tapp *)
  destructs IHtyping. simpls. lets: wft_fv_tt H. splits_solve_subsets.
  eapply subset_trans. apply open_tt_tt_fv_subset. solve_subsets.
Qed.

Lemma typing_through_subst_ee : forall U E F x T e u,
  value u ->
  typing (E & x ~: U & F) e T ->
  typing E u U ->
  typing (E & F) (subst_ee x u e) T.
Proof.
  introv Hv TypT TypU. inductions TypT; introv; simpl.
  case_var.
    binds_get H0. apply_empty* typing_weakening.
    binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H0. lets*: (typing_regular TypU).
  apply_fresh* typing_stoic as y. destruct (typing_regular TypU).
    rewrite* subst_ee_open_ee_var.
    (* if U is closed, then use IH; else  x is free in e1; *)
    repeat(rewrite pure_dist in *). remember (closed_typ U) as b. destruct b.
      (* closed_typ U = true *)
      symmetry in Heqb. rewrite* pure_single_true in H1.
      intros. rewrite <- concat_assoc. apply H1 with U; autos. rewrite* concat_assoc.
      apply* typing_strengthen_env.
      (* closed_typ U = false *)
      symmetry in Heqb. rewrite* pure_single_false in H0. rewrite concat_empty_r in H0.
      lets: ok_middle_inv (ok_from_okt H). forwards~ HI: H0 y.
      rewrite* subst_ee_fresh. destructs (typing_env_fv HI). unfolds notin. intros HII.
      assert (HIII: x \in dom (pure E & pure F & y ~: V)) by unfolds* subset.
      repeat(rewrite dom_concat in HIII). repeat(rewrite in_union in HIII).
      rewrite dom_single in HIII. rewrite or_assoc in HIII. destruct H4. branches HIII.
        apply H4. lets*: pure_dom_subset E.
        apply H8. lets*: pure_dom_subset F.
        rewrite in_singleton in H9. substs. apply* Fry. repeat(rewrite in_union).
          autos* in_singleton_self.
  apply* typing_degen.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.  destruct (typing_regular TypU).
    rewrite* subst_ee_open_te_var.
    (* if U is closed, then use IH; else  x is free in e1; *)
    repeat(rewrite pure_dist in *). remember (closed_typ U) as b. destruct b.
      (* closed_typ U = true *)
      symmetry in Heqb. rewrite* pure_single_true in H1.
      intros. rewrite <- concat_assoc. apply H1 with U; autos. rewrite* concat_assoc.
      apply* typing_strengthen_env.
      (* closed_typ U = false *)
      symmetry in Heqb. rewrite* pure_single_false in H0. rewrite concat_empty_r in H0.
      lets: ok_middle_inv (ok_from_okt H). forwards~ HI: H0 Y.
      rewrite* subst_ee_fresh. destructs (typing_env_fv HI). unfolds notin. intros HII.
      assert (HIII: x \in dom (pure E & pure F & [:Y:])) by unfolds* subset.
      repeat(rewrite dom_concat in HIII). repeat(rewrite in_union in HIII).
      rewrite dom_single in HIII. rewrite or_assoc in HIII. destruct H4. branches HIII.
        apply H4. lets*: pure_dom_subset E.
        apply H8. lets*: pure_dom_subset F.
        rewrite in_singleton in H9. substs. apply* FrY. repeat(rewrite in_union).
          autos* in_singleton_self.
  apply* typing_tapp.
Qed.


(************************************************************************ *)
(** Preservation by Type Substitution (11) *)

Lemma typing_through_subst_te_general : forall E F G Z e T P,
  subseq F G ->
  typing (E & [:Z:] & F) e T ->
  okt (E & [:Z:] & G) ->
  wft E P ->
  typing (E & map (subst_tb Z P) G) (subst_te Z P e) (subst_tt Z P T).
Proof.
  introv Seq Typ Ok Wf. gen G.
  inductions Typ; intros; simpls subst_tt; simpls subst_te.
  apply* typing_var. rewrite (@map_subst_tb_id E Z P); autos* okt_weaken.
    unsimpl (subst_tb Z P (bind_typ T)).
    rewrite <- map_concat. apply binds_map. binds_cases H0.
    apply binds_concat_left_ok; auto. apply ok_remove with ([:Z:]); auto.
    apply binds_concat_right. apply subseq_binds with F; auto.
    apply (ok_concat_inv_r (ok_from_okt Ok)).
  apply_fresh* typing_abs as y.
    unsimpl (subst_tb Z P (bind_typ V)).
    rewrite* subst_te_open_ee_var.  rewrite <- concat_assoc, <- map_push.
    applys~ H0 (F & y ~: V). rewrite* concat_assoc. apply* subseq_concat.
    rewrite concat_assoc. apply* okt_typ.
    forwards~ IH: H y. destructs (typing_regular IH). destructs (okt_push_typ_inv H1).
    apply tvar_wft with (E & [:Z:] & F); auto.
    rewrite ?tvar_dist, (subseq_tvar Seq); auto.
  apply_fresh* typing_stoic as y.
    unsimpl (subst_tb Z P (bind_typ V)).
    rewrite* subst_te_open_ee_var.
    forwards~ Map: pure_map_eq G Z P. destruct Map as [M Map]. destructs Map.
    rewrite pure_dist, H2, <- concat_assoc, <- map_push.
    applys~ H1 (pure E) (pure F & y ~: V) (M & y ~: V).
    rewrite ?pure_dist, pure_single_tvar, ?concat_assoc. reflexivity.
    apply* pure_wft_reverse.
    apply* subseq_concat. apply subseq_trans with (pure G); auto. apply* subseq_pure_dist.
    (*okt*)
    assert (okt (pure E & [:Z:] & M)) as OkM.
      apply subseq_okt with (pure E & [:Z:] & G).
      apply subseq_okt with (E & [:Z:] & G); auto.
      repeat(apply* subseq_concat; try apply subseq_pure; try apply subseq_refl).
      repeat(apply* subseq_concat; auto; try apply subseq_refl).
    rewrite concat_assoc. apply okt_typ. auto.
    (*wft*)
    apply tvar_wft with (E & [:Z:] & G); auto.
    rewrite ?tvar_dist, <- ?tvar_pure, (subseq_tvar H4). auto.
    forwards~ IH: H0 y. destructs (typing_regular IH). destructs (okt_push_typ_inv H5).
    apply tvar_wft with (pure (E & [:Z:] & F)); auto.
    rewrite <- tvar_pure, ?tvar_dist, (subseq_tvar Seq). auto.
    (* y fresh *)
    apply subseq_fresh with (E & [:Z:] & G); auto.
    repeat(apply subseq_concat; auto; try apply subseq_refl; try apply subseq_pure).
  apply* typing_degen.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    unsimpl (subst_tb Z P bind_tvar).
    rewrite* subst_te_open_te_var; eauto using wft_type.
    rewrite* subst_tt_open_tt_var; eauto using wft_type.
    forwards~ Map: pure_map_eq G Z P. destruct Map as [M Map]. destructs Map.
    rewrite pure_dist, H2, <- concat_assoc, <- map_push.
    applys~ H1 (pure E) (pure F & [:Y:]) (M & [:Y:]).
    rewrite ?pure_dist, pure_single_tvar, ?concat_assoc. reflexivity.
    apply* pure_wft_reverse.
    apply* subseq_concat. apply subseq_trans with (pure G); auto. apply* subseq_pure_dist.
    (*okt*)
    assert (okt (pure E & [:Z:] & M)) as OkM.
      apply subseq_okt with (pure E & [:Z:] & G).
      apply subseq_okt with (E & [:Z:] & G); auto.
      repeat(apply* subseq_concat; try apply subseq_pure; try apply subseq_refl).
      repeat(apply* subseq_concat; auto; try apply subseq_refl).
    rewrite concat_assoc. apply okt_tvar. auto.
    (* y fresh *)
    apply subseq_fresh with (E & [:Z:] & G); auto.
    repeat(apply subseq_concat; auto; try apply subseq_refl; try apply subseq_pure).
  rewrite* subst_tt_open_tt; eauto using wft_type. apply* typing_tapp.
    apply* wft_subst_tb. apply tvar_wft with (E & [:Z:] & F); auto.
    rewrite ?tvar_dist, (subseq_tvar Seq). auto.
Qed.

Lemma typing_through_subst_te : forall E F Z e T P,
  typing (E & [: Z :] & F) e T ->
  wft E P ->
  typing (E & map (subst_tb Z P) F) (subst_te Z P e) (subst_tt Z P T).
Proof.
  introv Typ Wft. destructs (typing_regular Typ).
  forwards~ : typing_through_subst_te_general P (subseq_refl F) Typ.
Qed.

(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen e'. induction Typ; introv Red;
   try solve [ inversion Red ].
  apply* typing_degen.
  (* case: app *)
  inversions Red; try solve [ apply* typing_app ].
  inversions Typ1. pick_fresh x. forwards~ K: (H2 x).
  rewrite* (@subst_ee_intro x).
    apply_empty typing_through_subst_ee; substs*.
    lets*: typing_regular Typ2.

  inversions H4. pick_fresh x. forwards~ K: (H8 x).
  rewrite* (@subst_ee_intro x).
    apply_empty typing_through_subst_ee; substs*.
    rewrite <- concat_empty_l at 1. rewrite concat_assoc.
    apply typing_weakening_env; rewrite* concat_empty_l.
    apply* okt_typ. apply* pure_wft.
    lets*: typing_regular Typ2.
  (* case: tapp *)
  inversions Red. try solve [ apply* typing_tapp ].
  inversions Typ. pick_fresh X. forwards~ : H6 X.
  rewrite* (@subst_te_intro X).
  rewrite* (@subst_tt_intro X).
  asserts_rewrite (E = E & map (subst_tb X T) empty).
    rewrite map_empty. rewrite~ concat_empty_r.
  apply* typing_through_subst_te. rewrite concat_empty_r.
  rewrite <- (@concat_empty_l bind E).
  apply typing_weakening_env. rewrite* concat_empty_l.
  rewrite concat_empty_l. apply* okt_tvar.
Qed.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)
(** Canonical Forms (14) *)

Lemma canonical_form_abs : forall t U1 U2,
  value t -> typing empty t (typ_arrow U1 U2) ->
  exists V, exists e1, t = trm_abs V e1.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  gen_eq T: (typ_arrow U1 U2). gen U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
  subst. false* binds_empty_inv.

  subst. inversions EQT. inversions* Val. inversion Typ.
  inversions Typ. false* binds_empty_inv.
Qed.

Lemma canonical_form_tabs : forall t U1,
  value t -> typing empty t (typ_all U1) ->
  exists e1, t = trm_tabs e1.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  gen_eq T: (typ_all U1). gen U1.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
  subst. false* binds_empty_inv.
Qed.

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (@empty bind). lets Typ': Typ.
  induction Typ; intros EQ; subst; autos.
  (* case: var *)
  (* false* binds_empty_inv. *)
  (* case: abs *)
  left*. apply value_abs. lets*: typing_regular Typ'.
  (* case: abs closed *)
  left*. apply value_abs. lets*: typing_regular Typ'.
  (* case: app *)
  right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    destruct* IHTyp2 as [Val2 | [e2' Rede2']].
    destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]].
      subst. exists* (open_ee e3 e2). apply* red_abs. lets*: typing_regular Typ1.
    exists* (trm_app e1' e2). apply* red_app_1. lets*: typing_regular Typ2.
  (* case: tabs_closed *)
  left*. apply* value_tabs. lets*: typing_regular Typ'.
  (* case: tapp *)
  right. destruct~ IHTyp as [Val1 | [e1' Rede1']].
    destruct (canonical_form_tabs Val1 Typ) as [e EQ].
      subst. exists* (open_te e T). apply* red_tabs. lets*: typing_regular Typ.
      autos* wft_type.
    exists (trm_tapp e1' T). apply* red_tapp. autos* wft_type.
Qed.

(* ********************************************************************** *)
(** * effect safety *)

(* ********************************************************************** *)
(** * Properties of Healthy Evnironment *)

Fixpoint degree_typ (T: typ) := match T with
  | typ_stoic T1 T2 => max (degree_typ T1) (degree_typ T2)
  | typ_arrow T1 T2 => max (degree_typ T1) (degree_typ T2)
  | typ_all T => S (degree_typ T)
  | _ => O
  end.

Fixpoint degree_trm (t: trm) := match t with
  | trm_abs _ t1  => degree_trm t1
  | trm_app t1 t2 => max (degree_trm t1) (degree_trm t2)
  | trm_tabs t1   => S (degree_trm t1)
  | trm_tapp t1 _ => degree_trm t1
  | _ => O
  end.

Lemma max_zero_inv: forall a b,
  max a b = 0 ->
  a = 0 /\ b = 0.
Proof. intros. destruct a; destruct b; eauto.
  simpl in H. inversion H.
Qed.

Lemma degree_typ_eq_open_tt_rec: forall T U k,
  degree_typ U = 0 ->
  degree_typ T = degree_typ (open_tt_rec k U T).
Proof. intros. inductions T; unfolds open_tt_rec; simpls; try reflexivity; eauto.
  unfolds open_tt. unfolds open_tt_rec. cases_if*.
Qed.

Lemma degree_typ_eq_open_tt: forall T U,
  degree_typ U = 0 ->
  degree_typ T = degree_typ (open_tt T U).
Proof. intros. unfolds open_tt. apply* degree_typ_eq_open_tt_rec. Qed.

Lemma degree_trm_eq_open_te_rec: forall t U k,
  degree_trm t = degree_trm (open_te_rec k U t).
Proof. intros. inductions t; simpls; try reflexivity; eauto.  Qed.

Lemma degree_trm_eq_open_te: forall t U,
  degree_trm t = degree_trm (open_te t U).
Proof. intros. unfolds open_te. apply* degree_trm_eq_open_te_rec. Qed.

Lemma degree_trm_eq_open_ee_rec: forall t u k,
  degree_trm u = 0 ->
  degree_trm t = degree_trm (open_ee_rec k u t).
Proof. intros. inductions t; simpls; try reflexivity; eauto. cases_if*. Qed.

Lemma degree_trm_eq_open_ee: forall t u,
  degree_trm u = 0 ->
  degree_trm t = degree_trm (open_ee t u).
Proof. intros. unfolds open_ee. apply* degree_trm_eq_open_ee_rec. Qed.

Scheme capsafe_mut := Induction for capsafe Sort Prop
with caprod_mut := Induction for caprod Sort Prop.

Lemma capsafe_regular: forall T, capsafe T -> type T.
  apply (capsafe_mut
           (fun T safeT => type T )
           (fun T prodT => type T )
        );  eauto.
Qed.

Lemma caprod_regular: forall T, caprod T -> type T.
  apply (caprod_mut
           (fun T safeT => type T )
           (fun T prodT => type T )
        );  eauto.
Qed.

Hint Constructors capsafe caprod.
Hint Immediate capsafe_regular caprod_regular.

Lemma capsafe_not_caprod_0 : forall T, capsafe T -> degree_typ T = 0 -> ~ caprod T.
  apply (capsafe_mut
           (fun T safeT => degree_typ T = 0 -> ~ caprod T )
           (fun T prodT => degree_typ T = 0 -> ~ capsafe T )
        ); intros; intros Hc; inversions Hc; eauto; try solve [simpls; false*];
  repeat match goal with
    | [ H: degree_typ _ = 0 |- _] =>
      simpl in H; forwards~ : max_zero_inv H; jauto
  end.
Qed.

Lemma capsafe_not_caprod_k : forall T k, degree_typ T <= k -> capsafe T -> ~ caprod T.
Proof. intros. gen T. inductions k; intros.
  lets: Le.le_n_0_eq H. apply* capsafe_not_caprod_0.
  inductions T; try solve [simpls; apply* IHk; apply le_0_n].
    inversions H0. intros Hc. inversions Hc.
      simpl in H. destruct (classic (degree_typ T1 = S k)).
        forwards~ : IHT1. rewrite* H0.
        lets: Max.max_lub_l H. forwards~ : IHk T1.
          autos* PeanoNat.Nat.le_neq PeanoNat.Nat.lt_succ_r.
      intros Hc. inversions Hc. destruct (classic (degree_typ T2 = S k)).
        forwards~ : IHT2. rewrite* H0.
        lets: Max.max_lub_r H. forwards~ : IHk T2.
          autos* PeanoNat.Nat.le_neq PeanoNat.Nat.lt_succ_r.
    inversions H0. intros Hc. inversions Hc.
      simpl in H. destruct (classic (degree_typ T1 = S k)).
        forwards~ : IHT1. rewrite* H0.
        lets: Max.max_lub_l H. forwards~ : IHk T1.
          autos* PeanoNat.Nat.le_neq PeanoNat.Nat.lt_succ_r.
      intros Hc. inversions Hc. destruct (classic (degree_typ T2 = S k)).
        forwards~ : IHT2. rewrite* H0.
        lets: Max.max_lub_r H. forwards~ : IHk T2.
          autos* PeanoNat.Nat.le_neq PeanoNat.Nat.lt_succ_r.
    inversions H0. destruct H3. intros Hc. simpl in H. lets: le_S_n H.
      inversions Hc. destruct H6.
        forwards~ : IHk (open_tt T typ_eff).
          rewrite* <- degree_typ_eq_open_tt.
        forwards~ : IHk (open_tt T typ_base). rewrite* <- degree_typ_eq_open_tt.
Qed.

Lemma capsafe_not_caprod : forall T, capsafe T -> ~ caprod T.
Proof. intros T. apply* capsafe_not_caprod_k. Qed.

Lemma capsafe_caprod_classic_0: forall T, type T -> degree_typ T = 0 -> capsafe T \/ caprod T.
Proof. introv Ht Hd. inductions T; iauto.
  inversions Ht.
  inversions Ht. match goal with
                   | [H: degree_typ _ = 0,
                         H1: context[capsafe _ \/ caprod _],
                             H2: context[capsafe _ \/ caprod _] |- _] =>
                     simpl in H; forwards~ R: max_zero_inv H; destruct H;
                     destruct* H1; destruct* H2
                 end.
  inversions Ht. match goal with
                   | [H: degree_typ _ = 0,
                         H1: context[capsafe _ \/ caprod _],
                             H2: context[capsafe _ \/ caprod _] |- _] =>
                     simpl in H; forwards~ R: max_zero_inv H; destruct H;
                     destruct* H1; destruct* H2
                 end.
  simpls. false*.
Qed.

Lemma capsafe_caprod_classic_k: forall T k, type T -> degree_typ T <= k -> capsafe T \/ caprod T.
Proof. introv Typ Deg. gen T. inductions k; intros.
  lets: Le.le_n_0_eq Deg. apply* capsafe_caprod_classic_0.
  inductions T; try solve [inversion Typ]; eauto.
    inversions Typ. simpl in Deg.
      forwards~ LT1: Max.max_lub_l Deg. forwards~ LT2: Max.max_lub_r Deg.
      match goal with
        | [H1: context[capsafe _ \/ caprod _],
               H2: context[capsafe _ \/ caprod _] |- _] =>
          destruct* H1; destruct* H2
      end.
    inversions Typ. simpl in Deg.
      forwards~ LT1: Max.max_lub_l Deg. forwards~ LT2: Max.max_lub_r Deg.
      match goal with
        | [H1: context[capsafe _ \/ caprod _],
               H2: context[capsafe _ \/ caprod _] |- _] =>
          destruct* H1; destruct* H2
      end.
    simpls. lets: le_S_n Deg.
      forwards~ IH1: IHk (open_tt T typ_eff).
        rewrite* <- degree_typ_eq_open_tt.
      forwards~ IH2: IHk (open_tt T typ_base).
        rewrite* <- degree_typ_eq_open_tt.
      destruct IH1; destruct IH2; eauto.
Qed.

Lemma capsafe_caprod_classic: forall T, type T -> capsafe T \/ caprod T.
Proof. intros. apply* capsafe_caprod_classic_k. Qed.

Lemma capsafe_decidable: forall T, type T -> capsafe T \/ ~ capsafe T.
Proof. intros. destruct (capsafe_caprod_classic H). left*.
  right. intros Hc. lets*: capsafe_not_caprod Hc.
Qed.

Lemma not_capsafe_caprod : forall T, type T -> ~capsafe T -> caprod T.
Proof. intros. destruct* (capsafe_caprod_classic H). Qed.

Lemma healthy_env_capsafe : forall E S x, healthy E ->
   binds x (bind_typ S) E ->  capsafe S.
Proof. introv H Hb. inductions H.
  false* binds_empty_inv.
  destruct (binds_push_inv Hb); jauto.
    destruct H1. inversions* H2.
  destruct (binds_push_inv Hb); jauto.
    destruct H0. inversions* H1.
Qed.

Lemma subst_tt_type_type_0: forall P Q T Z,
  degree_typ T = 0 -> type P -> type Q ->
  type (subst_tt Z P T) -> type (subst_tt Z Q T).
Proof. introv Deg TyP TyQ TyT. inductions T; try solve [simpls; eauto]; simpl.
  cases_if*.
  inversions TyT. simpl in Deg. lets*: max_zero_inv Deg.
  inversions TyT. simpl in Deg. lets*: max_zero_inv Deg.
  simpls. false*.
Qed.

Lemma subst_tt_type_type_k: forall P Q T Z k,
  degree_typ T <= k  -> type P -> type Q ->  type (subst_tt Z P T) -> type (subst_tt Z Q T).
Proof. introv Deg TyP TyQ TyT. gen T. inductions k; intros.
  (* k = 0*)
  lets: Le.le_n_0_eq Deg. forwards~ : subst_tt_type_type_0 TyP TyQ TyT.
  (* K > 0 *)
  inductions T; simpls; eauto.
  cases_if*.
  inversions TyT. forwards~ : Max.max_lub_l Deg. forwards~ : Max.max_lub_r Deg.
  inversions TyT. forwards~ : Max.max_lub_l Deg. forwards~ : Max.max_lub_r Deg.
  lets: le_S_n Deg. inversions TyT.
    apply_fresh type_all as X.
    match goal with
        | [HT: context[forall _, _ \notin ?L -> _] |- _] => forwards~ TyOpen: HT X
    end.
    unfolds open_tt.
    replace (typ_fvar X) with (subst_tt Z Q (typ_fvar X)) by
       (rewrite* subst_tt_fresh; simpls; autos).
    replace (typ_fvar X) with (subst_tt Z P (typ_fvar X)) in TyOpen by
       (rewrite* subst_tt_fresh; simpls; autos).
    rewrite <- subst_tt_open_tt_rec in *; auto.
    apply* IHk. rewrite* <- degree_typ_eq_open_tt_rec.
Qed.

Lemma subst_tt_type_type: forall P Q T Z,
  type P -> type Q ->  type (subst_tt Z P T) -> type (subst_tt Z Q T).
Proof. intros. remember (degree_typ T) as k.
   eapply subst_tt_type_type_k. symmetry in Heqk. apply* PeanoNat.Nat.eq_le_incl.
   exact H. auto. auto.
Qed.

Hint Resolve healthy_env_capsafe not_capsafe_caprod subst_tt_type_type.

Definition same_cap T1 T2 := (capsafe T1 /\ capsafe T2) \/ (caprod T1 /\ caprod T2).
Definition same_as_cap T1 T2 := (capsafe T1 -> capsafe T2) /\ (caprod T1 -> caprod T2).

Lemma same_cap_regular: forall T1 T2, same_cap T1 T2 -> type T1 /\ type T2.
Proof. introv H. destruct H; destruct H; split; autos* capsafe_regular caprod_regular. Qed.

Lemma same_cap_subst_tt_0: forall T Z P Q,
  degree_typ T = 0 -> same_cap P Q -> same_as_cap (subst_tt Z P T) (subst_tt Z Q T).
Proof. introv Deg Cap. inductions T; unfolds; autos.
  simpls; splits; cases_if*; unfolds same_cap; intros;
    destruct* Cap; false; autos* capsafe_not_caprod.
  simpl in Deg. lets DegInv: max_zero_inv Deg.
    destruct DegInv as [Z1 Z2].
    forwards~ A1: IHT1 Z Cap. forwards~ A2: IHT2 Z Cap. unfolds same_as_cap.
    destruct A1. destruct A2. destruct (same_cap_regular Cap).
    splits; introv Hyp; inversions Hyp; simpl.
      apply capsafe_eff_any_free; autos* subst_tt_type_type.
      apply capsafe_any_safe_free; autos* subst_tt_type_type.
    apply* caprod_safe_eff_free.
  simpl in Deg. lets DegInv: max_zero_inv Deg.
    destruct DegInv as [Z1 Z2].
    forwards~ A1: IHT1 Z Cap. forwards~ A2: IHT2 Z Cap. unfolds same_as_cap.
    destruct A1. destruct A2. destruct (same_cap_regular Cap).
    splits; introv Hyp; inversions Hyp; simpl.
      apply capsafe_eff_any; autos* subst_tt_type_type.
      apply capsafe_any_safe; autos* subst_tt_type_type.
    apply* caprod_safe_eff.
  simpls. false.
Qed.

Lemma same_cap_subst_tt_k: forall T Z P Q k,
  degree_typ T <= k -> same_cap P Q -> same_as_cap (subst_tt Z P T) (subst_tt Z Q T).
Proof. introv Deg Cap. gen T. inductions k; intros.
  lets: Le.le_n_0_eq Deg. apply* same_cap_subst_tt_0.

  inductions T; simpls; unfolds; autos.
  splits; cases_if*; unfolds same_cap; intros;
    destruct* Cap; false; autos* capsafe_not_caprod.

  simpl in Deg. lets LT1: Max.max_lub_l Deg. lets LT2: Max.max_lub_r Deg.
    forwards~ A1: IHT1. forwards~ A2: IHT2. unfolds same_as_cap.
    destruct A1. destruct A2. destruct (same_cap_regular Cap).
    splits; introv Hyp; inversions Hyp; simpl.
      apply capsafe_eff_any_free; autos* subst_tt_type_type.
      apply capsafe_any_safe_free; autos* subst_tt_type_type.
    apply* caprod_safe_eff_free.
  simpl in Deg. lets LT1: Max.max_lub_l Deg. lets LT2: Max.max_lub_r Deg.
    forwards~ A1: IHT1. forwards~ A2: IHT2. unfolds same_as_cap.
    destruct A1. destruct A2. destruct (same_cap_regular Cap).
    splits; introv Hyp; inversions Hyp; simpl.
      apply capsafe_eff_any; autos* subst_tt_type_type.
      apply capsafe_any_safe; autos* subst_tt_type_type.
    apply* caprod_safe_eff.

  split; introv Hyp. inversions Hyp. destruct H1. destruct (same_cap_regular Cap).
    apply capsafe_all. unsimpl (subst_tt Z Q (typ_all T)).  autos* subst_tt_type_type.
    lets: le_S_n Deg. split.
      replace typ_eff with (subst_tt Z Q typ_eff) by reflexivity.
        replace typ_eff with (subst_tt Z P typ_eff) in H by reflexivity.
        unfolds open_tt. rewrite <- subst_tt_open_tt_rec in *; auto.
        apply* IHk. rewrite* <- degree_typ_eq_open_tt_rec.
      replace typ_base with (subst_tt Z Q typ_base) by reflexivity.
        replace typ_base with (subst_tt Z P typ_base) in H1 by reflexivity.
        unfolds open_tt. rewrite <- subst_tt_open_tt_rec in *; auto.
        apply* IHk. rewrite* <- degree_typ_eq_open_tt_rec.
  inversions Hyp. destruct H1; destruct (same_cap_regular Cap).
    apply caprod_all. unsimpl (subst_tt Z Q (typ_all T)).  autos* subst_tt_type_type.
    lets: le_S_n Deg. left.
      replace typ_eff with (subst_tt Z Q typ_eff) by reflexivity.
        replace typ_eff with (subst_tt Z P typ_eff) in H by reflexivity.
        unfolds open_tt. rewrite <- subst_tt_open_tt_rec in *; auto.
        apply* IHk. rewrite* <- degree_typ_eq_open_tt_rec.
    apply caprod_all. unsimpl (subst_tt Z Q (typ_all T)).  autos* subst_tt_type_type.
    lets: le_S_n Deg. right.
      replace typ_base with (subst_tt Z Q typ_base) by reflexivity.
        replace typ_base with (subst_tt Z P typ_base) in H by reflexivity.
        unfolds open_tt. rewrite <- subst_tt_open_tt_rec in *; auto.
        apply* IHk. rewrite* <- degree_typ_eq_open_tt_rec.
Qed.

Lemma same_cap_subst_tt: forall T Z P Q,
  same_cap P Q -> same_as_cap (subst_tt Z P T) (subst_tt Z Q T).
Proof. intros. apply* same_cap_subst_tt_k. Qed.

Lemma capsafe_subst_tt_caprod: forall T Z P Q,
  caprod P -> caprod Q -> capsafe (subst_tt Z P T) -> capsafe (subst_tt Z Q T).
Proof. intros. forwards~ : same_cap_subst_tt T Z P Q. unfolds*. destruct* H2. Qed.

Lemma capsafe_subst_tt_capsafe: forall T Z P Q,
  capsafe P -> capsafe Q -> capsafe (subst_tt Z P T) -> capsafe (subst_tt Z Q T).
Proof.  intros. forwards~ : same_cap_subst_tt T Z P Q. unfolds*. destruct* H2. Qed.

Lemma capsafe_all_open_tt: forall T U, type U ->
  capsafe (typ_all T) -> capsafe (open_tt T U).
Proof. intros. inversions H0. destruct H3. destruct (capsafe_decidable H).
  pick_fresh X. rewrite* (@subst_tt_intro X). eapply capsafe_subst_tt_capsafe.
    apply capsafe_base. auto. rewrite* <- subst_tt_intro.
  pick_fresh X.  rewrite* (@subst_tt_intro X). eapply capsafe_subst_tt_caprod.
    apply caprod_eff.  auto. rewrite* <- subst_tt_intro.
Qed.

Lemma healthy_pure: forall E, healthy E -> healthy (pure E).
Proof. introv H. inductions E; simpls*.
  destruct a. destruct b; rewrite cons_to_push.
  inversions H. rewrite empty_def in H1. inversion H1.
    rewrite <- cons_to_push in H0. inversions H0.
    rewrite <- cons_to_push in H0. inversions H0.
    apply* healthy_tvar.
  inversions H. rewrite empty_def in H1. inversion H1.
    rewrite <- cons_to_push in H0. inversions H0.
    cases* (closed_typ t). apply* healthy_typ.
    rewrite <- cons_to_push in H0. inversion H0.
Qed.

Lemma healthy_env_term_capsafe_0: forall E t T,
  degree_trm t = 0 ->
  healthy E ->
  typing E t T ->
  capsafe T.
Proof. introv Deg H Typ. inductions Typ; intros; autos.
  apply* healthy_env_capsafe.
  pick_fresh x. forwards~ : H0 x.
    assert (HI: type V) by destruct* (typing_regular H2).
    destruct (capsafe_decidable HI). simpls.
      apply* capsafe_any_safe_free. apply* (H1 x). rewrite* <- degree_trm_eq_open_ee.
      apply* healthy_typ. lets*: not_capsafe_caprod H3.
      apply* capsafe_eff_any_free. autos* wft_type typing_wft.
  pick_fresh x. forwards~ : H1 x.
    assert (HI: type V) by destruct* (typing_regular H3).
    destruct (capsafe_decidable HI). simpls.
      apply* capsafe_any_safe. apply* (H2 x). rewrite* <- degree_trm_eq_open_ee.
      apply~ healthy_typ. apply* healthy_pure.
      lets*: not_capsafe_caprod H4.
      apply* capsafe_eff_any. autos* wft_type typing_wft.
  forwards~ IH: IHTyp. inversions* IH.
  simpl in Deg. lets Degs: max_zero_inv Deg. inversions Degs.
    forwards~ : IHTyp1. forwards~ : IHTyp2.
    inversions* H2. false. autos* capsafe_not_caprod.
  simpl in Deg. inversions Deg.
  simpl in Deg. forwards~ : IHTyp. apply* capsafe_all_open_tt. apply* wft_type.
Qed.

Lemma healthy_env_term_capsafe_k: forall E t T k,
  degree_trm t <= k ->
  healthy E ->
  typing E t T ->
  capsafe T.
Proof. introv Deg H Typ. gen t E T. inductions k; intros.
  lets: Le.le_n_0_eq Deg. apply* healthy_env_term_capsafe_0.

  inductions Typ; intros; autos.
  apply* healthy_env_capsafe.
  pick_fresh x. forwards~ Typ : H0 x.
    assert (HI: type V) by destruct* (typing_regular Typ).
    destruct (capsafe_decidable HI). simpls.
      apply* capsafe_any_safe_free. apply* (H1 x). rewrite* <- degree_trm_eq_open_ee.
      apply* healthy_typ. lets*: not_capsafe_caprod H2.
      apply* capsafe_eff_any_free. autos* wft_type typing_wft.
  pick_fresh x. forwards~ Typ: H1 x.
    assert (HI: type V) by destruct* (typing_regular Typ).
    destruct (capsafe_decidable HI). simpls.
      apply* capsafe_any_safe. apply* (H2 x). rewrite* <- degree_trm_eq_open_ee.
      apply~ healthy_typ. apply* healthy_pure.
      lets*: not_capsafe_caprod H3.
      apply* capsafe_eff_any. autos* wft_type typing_wft.
  forwards~ IH: IHTyp. inversions* IH.
  simpl in Deg. forwards~ LT1: Max.max_lub_l Deg. forwards~ LT2: Max.max_lub_r Deg.
    forwards~ : IHTyp1. forwards~ : IHTyp2.
    inversions* H0. false. autos* capsafe_not_caprod.
  simpl in Deg. lets: le_S_n Deg.
    pick_fresh X. forwards~ : H1 X.
    assert (HI: typing (pure E) (open_te e1 typ_base) (open_tt T1 typ_base)).
      rewrite <- concat_empty_r at 1. rewrite* (@subst_te_intro X).
      rewrite* (@subst_tt_intro X).
      replace empty with (map (subst_tb X typ_base) empty) by rewrite* map_empty.
      apply* typing_through_subst_te. rewrite* concat_empty_r.
    assert (HII: typing (pure E) (open_te e1 (typ_stoic typ_base typ_eff))
                        (open_tt T1 (typ_stoic typ_base typ_eff))).
      rewrite <- concat_empty_r at 1. rewrite* (@subst_te_intro X).
      rewrite* (@subst_tt_intro X).
      replace empty with (map (subst_tb X (typ_stoic typ_base typ_eff)) empty) by
          rewrite* map_empty.
      apply* typing_through_subst_te. rewrite* concat_empty_r.
    assert (HIII: typing (pure E) (trm_tabs e1) (typ_all T1)).
      apply* (@typing_tabs L). rewrite* pure_eq.
    lets HPure: healthy_pure H.
    forwards~ : IHk HI. rewrite* <- degree_trm_eq_open_te.
    forwards~ : IHk HII. rewrite* <- degree_trm_eq_open_te.
    apply capsafe_all. autos* wft_type typing_wft. splits*.
    rewrite* (@subst_tt_intro X).
      assert (caprod (typ_stoic typ_base typ_eff)) by apply* caprod_safe_eff.
      eapply capsafe_subst_tt_caprod; eauto. rewrite* <- subst_tt_intro.
  simpl in H. forwards~ : IHTyp. apply* capsafe_all_open_tt. apply* wft_type.
Qed.

Lemma healthy_env_term_capsafe: forall E t T,
  healthy E ->
  typing E t T ->
  capsafe T.
Proof. intros. apply* healthy_env_term_capsafe_k. Qed.

Lemma effect_safety_result_1 : effect_safety_1.
Proof. intros E H He. destruct He.
  lets*: healthy_env_term_capsafe H0. inversions H1.
Qed.

Axiom axiom_equiv_base : forall E S T t,
  typing E t (typ_stoic typ_base (typ_arrow S T)) ->
  typing E t (typ_stoic typ_base (typ_stoic S T)).

Axiom axiom_equiv_stoic : forall E U V S T t,
  typing E t (typ_stoic (typ_stoic U V) (typ_arrow S T)) ->
  typing E t (typ_stoic (typ_stoic U V) (typ_stoic S T)).

Axiom axiom_equiv_all : forall E U S T t,
  typing E t (typ_stoic (typ_all U) (typ_arrow S T)) ->
  typing E t (typ_stoic (typ_all U) (typ_stoic S T)).

Axiom axiom_poly : forall E U V S T t1 t2,
  typing E t1 (typ_stoic (typ_arrow U V) (typ_arrow S T)) ->
  typing E t2 (typ_stoic U V) ->
  typing E (trm_app t1 t2) (typ_stoic S T).

Axiom axiom_all_stoic : forall E T1 T2 t,
  typing E t (typ_all (typ_arrow T1 T2)) ->
  typing E t (typ_all (typ_stoic T1 T2)).

Lemma effect_polymorphism: forall E t T1 T2,
  healthy E -> pure E = E ->
  typing E t (typ_arrow T1 T2) ->
  typing E t (typ_stoic T1 T2).
Proof. introv HL Pure Typ.  inductions Typ; auto.
  rewrite <- Pure in H0. lets: pure_closed H0. false.
  apply* typing_stoic.
    assert (Typ: typing E (trm_abs T1 e1) (typ_arrow T1 T2)) by apply* typing_abs.
    destruct* (typing_regular Typ).
    rewrite* Pure.

  (* t = t1 t2 *)
  forwards~ : IHTyp1. destruct T0.
  lets Inv: typing_wft Typ2. inversion Inv.
  lets: healthy_env_term_capsafe HL Typ2. inversion H0.
  forwards~ : axiom_equiv_base H. apply* typing_app. apply* typing_degen.
  lets: healthy_env_term_capsafe HL Typ2. inversion H0.
  forwards~ : IHTyp2. apply* axiom_poly.
  forwards~ : axiom_equiv_stoic H. apply* typing_app. apply* typing_degen.
  forwards~ : axiom_equiv_all H. apply* typing_app. apply* typing_degen.

  (* t = t [T] *)
  destruct T0; try solve [inversion x].
  destruct n; unfolds open_tt, open_tt_rec; cases_if. substs.
  assert (Err: typing E (trm_tapp e1 typ_eff) typ_eff).
    replace typ_eff with (open_tt (typ_bvar 0) typ_eff) at 2.
    apply* typing_tapp.
    unfold open_tt. simpl. cases_if*.
  lets: healthy_env_term_capsafe HL Err. inversion H0.

  unfolds open_tt. simpl in x. inversion x. substs.
  forwards~ AX: axiom_all_stoic Typ.
  change (typing E (trm_tapp e1 T) (open_tt (typ_stoic T0_1 T0_2) T)).
  apply* typing_tapp.
Qed.

Lemma effect_safety_result_2 : effect_safety_2.
Proof. introv HL Pure Typ. inductions Typ; auto.
  apply* IHTyp.

  forwards~ : effect_polymorphism E t1 T1 T2. iauto.
Qed.

(* This proof ensures that all inhabitable types are capsafe, thus
   justifies the definition of capsafe/caprod.

   This theorem assumes that all inhabitable types in the system can
   be inhabited by a value in the environment {x:B, y:E}. Note that
   variables are values in the system, thus B and E are inhabitable.

   If the term t is not a value, it should be able to take a step and
   preserves the type.

*)

Theorem primitive_capsafe: forall E x T,
  primitive E ->
  binds x (bind_typ T) E ->
  capsafe T \/ closed_typ T = false.
Proof. introv Prim Bd. inductions Prim.
  destruct (binds_push_inv Bd) as [Inv | Inv]; destruct Inv.
    inversions H0. auto.
    destructs (binds_single_inv H0). inversions H2. auto.
  binds_cases Bd. auto.
  binds_cases Bd. auto. inversions EQ. auto.
Qed.

Theorem primitive_pure_healthy: forall E,
  primitive E -> healthy (pure E).
Proof. introv Prim. inductions Prim.
  rewrite pure_dist, pure_single_true, pure_single_false, concat_empty_r; auto.
    rewrite <- concat_empty_l. apply* healthy_typ. apply healthy_empty.
  rewrite ?pure_dist, pure_single_tvar; auto. apply* healthy_tvar.
  rewrite ?pure_dist, pure_single_false; auto. rewrite* concat_empty_r.
Qed.

Theorem inhabitable_capsafe: forall E t T,
  primitive E ->
  typing E t T -> value t ->
  capsafe T \/ closed_typ T = false.
Proof. introv Prim Typ Val. inductions Typ; auto.
  apply* primitive_capsafe.
  pick_fresh z. forwards~ IH: H0 z.
    lets (Ok&_): (typing_regular IH). lets (_&Wf&_): (okt_push_typ_inv Ok).
    lets TypV: wft_type Wf. lets TypT1: wft_type (typing_wft IH).
    destruct (capsafe_decidable TypV) as [Case | Case].
    (* capsafe V -> healthy E -> capsafe T1 *)
    forwards~ Hcap : healthy_env_term_capsafe IH.
      apply* healthy_typ. apply* primitive_pure_healthy.
    (* caprod V -> capsafe V -> T1 *)
    forwards~ Vcap : not_capsafe_caprod Case.
  inversion Val.
  pick_fresh X. forwards~ IH: H0 X.
    assert (Typ: typing E (trm_tabs e1) (typ_all T1))
      by apply* typing_tabs.
    left. apply capsafe_all. apply (wft_type (typing_wft Typ)).
    rewrite <- concat_empty_r in IH at 1.
    forwards~ Typ1: typing_through_subst_te typ_base IH.
    forwards~ Typ2: typing_through_subst_te (typ_stoic typ_base typ_eff) IH.
    rewrite map_empty, concat_empty_r in Typ1, Typ2.
    forwards~ Safe1 : healthy_env_term_capsafe Typ1. rewrite <- concat_empty_l.
      rewrite concat_empty_l. apply* primitive_pure_healthy.
    forwards~ Safe2 : healthy_env_term_capsafe Typ2. rewrite <- concat_empty_l.
      rewrite concat_empty_l. apply* primitive_pure_healthy.
    split; rewrite* (@subst_tt_intro X).
    applys~ capsafe_subst_tt_caprod (typ_stoic typ_base typ_eff).
  inversion Val.
Qed.

Theorem inhabitable_pure_healthy: inhabitable_pure_healthy_statement.
Proof. introv In Pure. inductions In.
  apply healthy_empty.
  apply* healthy_tvar. apply IHIn.
    rewrite <- ?cons_to_push in Pure. simpls. inversion Pure. rewrite* H0.
  assert (Closed: closed_typ T = true).
    applys~ pure_closed (E & z ~: T) z.
    rewrite Pure. apply binds_tail.
  forwards~ IH: inhabitable_capsafe H1. destruct IH.
    rewrite pure_dist, pure_single_true in Pure; auto.
      rewrite <- ?cons_to_push in Pure. inversion Pure. rewrite H4.
      apply* healthy_typ.
    substs. false*.
Qed.
