(***************************************************************************
* System-F pure with capabilities                                          *
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
  | typ_arrow_closed  : typ -> typ -> typ       (* effect closeded term abstraction *)
  | typ_all_closed    : typ -> typ.             (* effect closeded type abstraction *)

(** Representation of pre-terms *)

Inductive trm : Set :=
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
  | typ_arrow_closed T1 T2  => typ_arrow_closed (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all_closed T1       => typ_all_closed (open_tt_rec (S K) U T1)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

(** Opening up a type binder occuring in a term *)

Fixpoint open_te_rec (K : nat) (U : typ) (e : trm) {struct e} : trm :=
  match e with
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
  | type_var : forall X,
      type (typ_fvar X)
  | type_base: type typ_base
  | type_eff: type typ_eff
  | type_arrow_closed : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow_closed T1 T2)
  | type_all_closed : forall L T2,
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
      type (typ_all_closed T2).

(** Terms as locally closeded pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L V e1,
      type V ->
      (forall x, x \notin L -> term (e1 open_ee_var x)) ->
      term (trm_abs V e1)
  | term_app : forall e1 e2,
      term e1 ->
      term e2 ->
      term (trm_app e1 e2)
  | term_tabs : forall L e1,
      (forall X, X \notin L -> term (e1 open_te_var X)) ->
      term (trm_tabs e1)
  | term_tapp : forall e1 V,
      term e1 ->
      type V ->
      term (trm_tapp e1 V).

(** Environment is an associative list of bindings. *)

(** Binding are either mapping type or term variables.
 [: X :] is a type variable asumption and [x ~: T] is
 a typing assumption *)

Inductive bind : Set :=
  | bind_X : bind
  | bind_x : typ -> bind.

Notation "[: X :]" := (X ~ bind_X)
  (at level 23) : env_scope.
Notation "x ~: T" := (x ~ bind_x T)
  (at level 24, left associativity) : env_scope.

Definition env := LibEnv.env bind.

(** Well-formedness of a pre-type T in an environment E: all the type
  variables of T must be bound via [: T :] in E. This predicates
  implies that T is a type *)

Inductive wft : env -> typ -> Prop :=
  | wft_var : forall E X,
      binds X bind_X E ->
      wft E (typ_fvar X)
  | wft_arrow_closed : forall E T1 T2,
      wft E T1 ->
      wft E T2 ->
      wft E (typ_arrow_closed T1 T2)
  | wft_all_closed : forall L E T,
      (forall X, X \notin L ->
        wft (E & [: X :]) (T open_tt_var X)) ->
      wft E (typ_all_closed T).

(** A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment
  it is pushed on to. *)

Inductive okt : env -> Prop :=
  | okt_empty :
      okt empty
  | okt_X : forall E X,
      okt E -> X # E -> okt (E & [: X :])
  | okt_typ : forall E x T,
      okt E -> wft E T -> x # E -> okt (E & x ~: T).

(* closed rules *)
Fixpoint closed_typ(t: typ) := match t with
  | typ_bvar _          => false  (* impossible, ill-formed *)
  | typ_fvar _          => true
  | typ_base            => true
  | typ_eff             => false
  | typ_arrow_closed U V => true   (* pure lambda abstraction *)
  | typ_all_closed T     => true   (* pure type abstraction *)
  end.

Fixpoint closed_env(E: env) := match E with
  | nil => nil
  | cons (X, bind_X) E' => cons (X, bind_X) (closed_env E')
  | cons (x, bind_x T) E' => if closed_typ T then
                               cons (x, bind_x T) (closed_env E')
                             else
                               closed_env E'
    end.

(* capsafe types are not capability producing, i.e. capable of creating an instance of E *)
Inductive capsafe: typ -> Prop :=
| capsafe_B: capsafe typ_base
| capsafe_X: forall X, capsafe (typ_fvar X)
| capsafe_C_X: forall S T, type T -> caprod S -> capsafe (typ_arrow_closed S T)
| capsafe_X_S: forall S T, type S -> capsafe T -> capsafe (typ_arrow_closed S T)
| capsafe_A: forall L T, type (typ_all_closed T) ->
                         (forall X, X \notin L -> capsafe (T open_tt_var X)) ->
                         capsafe (typ_all_closed T)

with caprod: typ -> Prop :=
 | caprod_E: caprod typ_eff
 | caprod_S_C: forall S T, capsafe S -> caprod T -> caprod (typ_arrow_closed S T)
 | caprod_A: forall L T, type (typ_all_closed T) ->
                         (forall X, X \notin L -> caprod (T open_tt_var X)) ->
                         caprod (typ_all_closed T).

Inductive healthy: env -> Prop :=
  | healthy_empty: healthy empty
  | healthy_push_x: forall x E T, capsafe T -> healthy E ->
                                  x # E -> healthy (E & x ~: T)
  | healthy_push_X: forall X E, healthy E ->
                                  X # E -> healthy (E & [: X :]).


(** Typing relation *)

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      okt E ->
      binds x (bind_x T) E ->
      typing E (trm_fvar x) T
  | typing_abs_closed: forall L E V e1 T1,
      okt E ->
      (forall x, x \notin L ->
        typing ((closed_env E) & x ~: V) (e1 open_ee_var x) T1) ->
      typing E (trm_abs V e1) (typ_arrow_closed V T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_arrow_closed T1 T2) ->
      typing E e2 T1 ->
      typing E (trm_app e1 e2) T2
  | typing_tabs_closed : forall L E e1 T1,
      okt E ->
      (forall X, X \notin L ->
        typing ((closed_env E) & [: X :]) (e1 open_te_var X) (T1 open_tt_var X)) ->
      typing E (trm_tabs e1) (typ_all_closed T1)
  | typing_tapp : forall T1 E e1 T,
      wft E T -> capsafe T ->
      typing E e1 (typ_all_closed T1) ->
      typing E (trm_tapp e1 T) (open_tt T1 T).

(** Values *)

Inductive value : trm -> Prop :=
  | value_abs  : forall V e1, term (trm_abs V e1) ->
                 value (trm_abs V e1)
  | value_tabs : forall e1, term (trm_tabs e1) ->
                 value (trm_tabs e1).

(** One-step reduction *)

Inductive red : trm -> trm -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      term e2 ->
      red e1 e1' ->
      red (trm_app e1 e2) (trm_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (trm_app e1 e2) (trm_app e1 e2')
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (trm_tapp e1 V) (trm_tapp e1' V)
  | red_abs : forall V e1 v2,
      term (trm_abs V e1) ->
      value v2 ->
      red (trm_app (trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : forall e1 V,
      term (trm_tabs e1) ->
      type V ->
      red (trm_tapp (trm_tabs e1) V) (open_te e1 V).

(** Our goal is to prove preservation and progress *)

Definition preservation := forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.

Definition progress := forall e T,
  typing empty e T ->
     value e
  \/ exists e', red e e'.

(* effect safety : it's impossible to construct a term of typ_eff in pure environment  *)
Definition effect_safety := forall E, healthy E ->
  ~exists e, typing E e typ_eff.

(* ********************************************************************** *)
(** * Additional Definitions Used in the Proofs *)

(** Computing free type variables in a type *)

Fixpoint fv_tt (T : typ) {struct T} : vars :=
  match T with
  | typ_bvar J            => \{}
  | typ_base              => \{}
  | typ_eff               => \{}
  | typ_fvar X            => \{X}
  | typ_arrow_closed T1 T2 => (fv_tt T1) \u (fv_tt T2)
  | typ_all_closed T1      => (fv_tt T1)
  end.

(** Computing free type variables in a term *)

Fixpoint fv_te (e : trm) {struct e} : vars :=
  match e with
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
  | typ_bvar J            => typ_bvar J
  | typ_base              => typ_base
  | typ_eff               => typ_eff
  | typ_fvar X            => If X = Z then U else (typ_fvar X)
  | typ_arrow_closed T1 T2 => typ_arrow_closed (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all_closed T        => typ_all_closed (subst_tt Z U T)
  end.

(** Substitution for free type variables in terms. *)

Fixpoint subst_te (Z : var) (U : typ) (e : trm) {struct e} : trm :=
  match e with
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
  | bind_X => bind_X
  | bind_x T => bind_x (subst_tt Z P T)
  end.

(* ********************************************************************** *)
(** * Tactics *)

(** Constructors as hints. *)

Hint Constructors type term wft ok okt value red.

Hint Resolve
  typing_var typing_app typing_tapp.

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
  apply_fresh* type_all_closed as X. rewrite* subst_tt_open_tt_var.
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

Hint Resolve subst_tt_type subst_te_term subst_ee_term.


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
  apply_fresh* wft_all_closed as Y. apply_ih_bind* H0.
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
  apply_fresh* wft_all_closed as Y. apply_ih_bind* H0.
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
       replace bind_X with ((subst_tb Z P) bind_X) by reflexivity.
       apply~ binds_map.
      destruct (binds_push_inv H1) as [[? ?]|[? ?]].
        subst. false~.
        applys wft_var. apply* binds_concat_left.
  apply_fresh* wft_all_closed as Y.
   unsimpl ((subst_tb Z P) bind_X).
   lets: wft_type.
   rewrite* subst_tt_open_tt_var.
   apply_ih_map_bind* H0.
Qed.

(** Through type reduction *)

Lemma wft_open : forall E U T,
  ok E ->
  wft E (typ_all_closed T) ->
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
  okt E -> binds x (bind_x U) E -> wft E U.
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
  okt (E & X ~ B) -> exists T, B = bind_X \/ B = bind_x T.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&?&?): (eq_push_inv H). subst. exists* (typ_fvar X).
    lets (?&?&?): (eq_push_inv H). subst*.
Qed.

Lemma okt_push_X_inv : forall E X,
  okt (E & [: X :]) -> okt E /\ X # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. inverts~ M.
    lets (?&?&?): (eq_push_inv H). false.
Qed.

Lemma okt_push_x_inv : forall E x T,
  okt (E & x ~: T) -> okt E /\ wft E T /\ x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&?&?): (eq_push_inv H). false.
    lets (?&M&?): (eq_push_inv H). subst. inverts~ M.
Qed.

Lemma okt_push_x_type : forall E x T,
  okt (E & x ~: T) -> type T.
Proof. intros. applys wft_type. forwards*: okt_push_x_inv. Qed.

Hint Immediate okt_push_x_type.

(** Through strengthening *)

Lemma okt_strengthen : forall x T (E F:env),
  okt (E & x ~: T & F) ->
  okt (E & F).
Proof.
 introv O. induction F using env_ind.
  rewrite concat_empty_r in *. lets*: (okt_push_x_inv O).
  rewrite concat_assoc in *.
   lets (U&[?|?]): okt_push_inv O; subst.
      applys~ okt_X. apply IHF. applys* okt_push_X_inv.
      apply ok_from_okt in O.
      lets (? & H): (ok_push_inv O). eauto.

      applys~ okt_typ. apply IHF. applys* okt_push_x_inv.
      applys* wft_strengthen.
      apply ok_from_okt in O.
      lets (? & H): (ok_push_inv O). eauto.
Qed.

Lemma okt_weaken : forall E F,
  okt (E & F) -> okt E.
Proof.
  induction F using env_ind; rew_env_concat; introv Okt. auto.
  lets(T & [H | H]): (okt_push_inv Okt); subst.
  apply IHF. lets*: okt_push_X_inv Okt.
  apply IHF. lets*: okt_push_x_inv Okt.
Qed.

(** Through type substitution *)

Lemma okt_subst_tb : forall Z P (E F:env),
  okt (E & [: Z :] & F) ->
  wft E P ->
  okt (E & map (subst_tb Z P) F).
Proof.
 introv O W. induction F using env_ind.
  rewrite map_empty. rewrite concat_empty_r in *.
   lets*: (okt_push_X_inv O).
  rewrite map_push. rewrite concat_assoc in *.
   lets (U&[?|?]): okt_push_inv O; subst.
     lets*: (okt_push_X_inv O).
     lets*: (okt_push_x_inv O).
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
 apply* IHT.
Qed.

Lemma notin_fv_wf : forall E X T,
  wft E T -> X # E -> X \notin fv_tt T.
Proof.
  induction 1; intros Fr; simpl.
  eauto.
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H Fr.
  notin_simpl; auto.
  notin_simpl; auto. pick_fresh Y. apply* (@notin_fv_tt_open Y).
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
(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ term e.
Proof.
  induction 1; auto.
  splits.
    pick_fresh y. specializes H1 y. destructs~ H1.
    apply_fresh* term_abs as y.
      pick_fresh y. specializes H1 y. destructs~ H1.
        forwards*: okt_push_x_inv.
      specializes H1 y. destructs~ H1.
  splits*.
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
Lemma closed_env_dist: forall E F, closed_env (E & F) = closed_env E & closed_env F.
Proof. rewrite concat_def. intros. gen E. induction F; intros E; autos.
  rewrite LibList.app_cons. destruct a. destruct b.
  simpl. rewrite LibList.app_cons. rewrite* <- IHF.
  simpl. destruct* (closed_typ t). rewrite LibList.app_cons. rewrite* <- IHF.
Qed.

Lemma closed_env_dom_subset : forall E, dom (closed_env E) \c dom E.
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

Lemma closed_env_binds: forall E x v, ok E -> binds x v (closed_env E) -> binds x v E.
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

Lemma closed_env_binds_reverse: forall E x, binds x bind_X E -> binds x bind_X (closed_env E).
Proof. intros. induction E.
  simpl in *. autos.
  destruct a. destruct b.
    simpl in *. rewrite cons_to_push in *. destruct (binds_push_inv H).
      destruct H0. subst. apply binds_push_eq.
      destruct H0. apply* binds_push_neq.
    simpl in *. rewrite cons_to_push in *. destruct (binds_push_inv H). false H0.
      destruct H0. destruct* (closed_typ t).
Qed.

Lemma closed_env_binds_in: forall E x T, closed_typ T = true ->
   binds x (bind_x T) E -> binds x (bind_x T) (closed_env E).
Proof. intros. induction E.
  (* nil *)
  rewrite <- empty_def in H0. destruct(binds_empty_inv H0).
  (* x::xs *)
  destruct a. destruct b.
    (* bind_X *)
    simpl. rewrite cons_to_push in *. destruct (binds_push_inv H0).
    destruct H1. inversion H2.
    destruct H1. apply* binds_push_neq.
    (* bind_x *)
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv H0).
    destruct H1. inversions H2. rewrite* H.
    destruct H1. destruct* (closed_typ t).
Qed.

Lemma closed_env_wft: forall E V, ok E -> wft (closed_env E) V -> wft E V.
Proof. intros. remember (closed_env E) as G. gen E. induction H0; intros; subst.
  apply wft_var. apply* closed_env_binds.
  apply* wft_arrow_closed.
  apply_fresh* wft_all_closed as Y. apply* H0. repeat(rewrite <- cons_to_push). autos.
Qed.

Lemma closed_env_wft_weaken: forall E F G V,
  ok (E & F & G) -> wft (E & (closed_env F) & G) V -> wft (E & F & G) V.
Proof. intros. inductions H0; intros; subst.
  apply wft_var. binds_cases H0.
    apply binds_concat_left; autos. apply* binds_concat_left_ok.
    apply binds_concat_left; autos. apply* binds_concat_right. apply* closed_env_binds.
      lets*: ok_concat_inv_r (ok_concat_inv_l H).
    apply binds_concat_right. auto.
  apply* wft_arrow_closed.
  apply_fresh* wft_all_closed as Y.
    assert (HI: ok (E & F & (G & [: Y :]))).
      rewrite concat_assoc. apply* ok_push.
    forwards~ HII: (H0 Y). apply HI.  rewrite* concat_assoc.
    rewrite* <- concat_assoc.
Qed.

Lemma closed_env_wft_reverse: forall E V, wft E V -> wft (closed_env E) V.
Proof. intros. induction H.
  apply wft_var. apply* closed_env_binds_reverse.
  apply* wft_arrow_closed.
  apply_fresh* wft_all_closed as Y. forwards~ HI: (H0 Y).
    rewrite closed_env_dist in HI. rewrite single_def in *. autos.
Qed.

Lemma closed_env_empty : closed_env empty = empty.
Proof. rewrite empty_def. reflexivity. Qed.

Lemma closed_env_single_true : forall x U, closed_typ U = true ->
  closed_env (x ~: U) = x ~: U.
Proof. intros.
  replace (x ~: U) with (empty & x ~: U) by rewrite* concat_empty_l.
  rewrite <- cons_to_push. simpls. rewrite H.
  rewrite closed_env_empty. reflexivity.
Qed.

Lemma closed_env_single_tvar : forall X, closed_env ([:X:]) = [:X:].
Proof. intros. replace ([:X:]) with (empty & [:X:]) by rewrite* concat_empty_l.
  rewrite <- cons_to_push. simpl. rewrite closed_env_empty. reflexivity.
Qed.

Lemma closed_env_single_false : forall x U, closed_typ U = false ->
  closed_env (x ~: U) = empty.
Proof. intros.
  replace (x ~: U) with (empty & x ~: U) by rewrite* concat_empty_l.
  rewrite <- cons_to_push. simpls. rewrite H.
  rewrite closed_env_empty. reflexivity.
Qed.

Lemma closed_env_okt : forall E,
  okt E -> okt (closed_env E).
Proof. intros. induction* E.
  destruct a. destruct b; simpl; rewrite cons_to_push in *.
  apply okt_X. apply IHE. lets*: okt_push_X_inv H.
  unfolds. lets(_ & HI): okt_push_X_inv H. autos* (closed_env_dom_subset E).
  destructs (okt_push_x_inv H). destruct* (closed_typ t).
    apply okt_typ. apply* IHE. apply* closed_env_wft_reverse.
    lets: closed_env_dom_subset E. unfolds subset.
    unfolds notin. autos.
Qed.

Lemma closed_subst_tt: forall T,
  closed_typ T = true ->
  forall Z P, closed_typ P = true ->
              closed_typ (subst_tt Z P T) = true.
Proof. intros. inductions T; inversions H; simpls; auto. case_if*. Qed.

Lemma closed_subst_tt_false: forall T,
  closed_typ T = false ->
  forall Z P, closed_typ P = true ->
              closed_typ (subst_tt Z P T) = false.
Proof. intros. inductions T; inversions H; simpls; auto. Qed.

Lemma closed_env_map : forall E Z P, closed_typ P = true ->
  closed_env (map (subst_tb Z P) E) = map (subst_tb Z P) (closed_env E).
Proof. intros. induction E.
  simpl. rewrite <- empty_def. rewrite map_empty. apply closed_env_empty.
  destruct a. destruct b; simpl.
    repeat(rewrite cons_to_push). repeat(rewrite map_push). simpl.
      rewrite <- cons_to_push. simpl. rewrite cons_to_push. rewrite* IHE.
    repeat(rewrite cons_to_push). repeat(rewrite map_push). simpl.
      rewrite <- cons_to_push. simpl. remember (closed_typ t). destruct b; symmetry in Heqb.
      lets*: (@closed_subst_tt t Heqb Z P H). rewrite H0. rewrite map_push.
        rewrite <- cons_to_push. simpl. rewrite* IHE.
      lets*: (@closed_subst_tt_false t Heqb Z P H). rewrite* H0.
Qed.

Lemma closed_env_eq : forall E, closed_env (closed_env E) = closed_env E.
Proof. intros. induction E; autos.
  destruct a. destruct b; autos.
  simpls. rewrite* IHE.
  simpls. remember (closed_typ t). symmetry in Heqb. destruct* b.
    simpls. rewrite* Heqb. rewrite* IHE.
Qed.

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
  apply_fresh* typing_abs_closed as x.
    repeat(rewrite closed_env_dist in *). rewrite <- concat_assoc.
    apply* H1. rewrite* concat_assoc. rewrite concat_assoc. repeat(rewrite <- closed_env_dist).
    apply okt_typ.  apply* closed_env_okt.
    forwards~ K: (H0 x). lets(Hk & _): typing_regular K. lets: wft_from_okt_typ Hk.
    apply closed_env_wft_reverse. apply* wft_weaken. apply* closed_env_wft. rewrite* closed_env_dist.
    assert (Ha: x \notin dom E \u dom F \u dom G) by autos.
    intros HI. apply Ha. repeat(rewrite closed_env_dist in HI). repeat(rewrite dom_concat in HI).
      repeat(rewrite in_union in *). rewrite or_assoc in HI.  branches HI.
     branch 1. lets*: closed_env_dom_subset E.
     branch 2. lets*: closed_env_dom_subset F.
     branch 3. lets*: closed_env_dom_subset G.
  apply* typing_app.
  apply_fresh* typing_tabs_closed as X.
    repeat(rewrite closed_env_dist in *). rewrite <- concat_assoc.
    apply* H1. rewrite* concat_assoc. rewrite concat_assoc. repeat(rewrite <- closed_env_dist).
    apply okt_X.  apply* closed_env_okt.
    forwards~ K: (H0 X). lets(Hk & _): typing_regular K.
    assert (Ha: X \notin dom E \u dom F \u dom G) by autos.
    intros HI. apply Ha. repeat(rewrite closed_env_dist in HI). repeat(rewrite dom_concat in HI).
      repeat(rewrite in_union in *). rewrite or_assoc in HI.  branches HI.
     branch 1. lets*: closed_env_dom_subset E.
     branch 2. lets*: closed_env_dom_subset F.
     branch 3. lets*: closed_env_dom_subset G.
  apply* typing_tapp.
Qed.

Lemma typing_wft: forall E e T, typing E e T -> wft E T.
Proof.
  intros. induction H. applys~ wft_from_env_has_typ x.
  apply wft_arrow_closed. pick_fresh x. forwards~: (H0 x).
    lets(H3 & _): (typing_regular H2). lets*: wft_from_okt_typ H3.
    apply* closed_env_wft.

    pick_fresh x. forwards~: (H1 x).
    rewrite <- (@concat_empty_r bind (x ~: V) ) in H2. rewrite concat_assoc in H2.
    lets: wft_strengthen H2. rewrite concat_empty_r in H3. apply* closed_env_wft.
  inverts* IHtyping1.
  let L := gather_vars in (apply* (@wft_all_closed L)). intros.
    forwards~: (H1 X). rewrite <- (@concat_empty_l bind E).
    apply closed_env_wft_weaken; rewrite* concat_empty_l.
  apply* wft_open.
Qed.

Lemma typing_weakening_env : forall E F G e T,
  typing (E & (closed_env F) & G) e T ->
  okt (E & F & G) ->
  typing (E & F & G) e T.
Proof. intros. inductions H.
  apply* typing_var. binds_cases H0; autos.
    apply* binds_weaken. apply* binds_concat_left.
    apply binds_concat_right. apply* closed_env_binds.
    autos* ok_concat_inv_l ok_concat_inv_r ok_from_okt.
  apply_fresh typing_abs_closed as x. auto.
    repeat(rewrite closed_env_dist in *). rewrite closed_env_eq in *.
    apply_ih_bind* H1. rewrite* closed_env_eq. forwards~ : H0 x.
  apply* typing_app.
  apply_fresh typing_tabs_closed as X; auto.
    repeat(rewrite closed_env_dist in *). rewrite closed_env_eq in *.
    apply_ih_bind* H1. rewrite* closed_env_eq. forwards~ : H0 X.
  apply typing_tapp; auto. apply* closed_env_wft_weaken.
Qed.

Lemma typing_strengthen_env: forall E u U, value u -> typing E u U ->
  closed_typ U = true -> typing (closed_env E) u U.
Proof. intros. induction H0; simpls; inversion H1.
  apply typing_var. apply* closed_env_okt. apply* closed_env_binds_in.
  apply_fresh* typing_abs_closed as y. apply* closed_env_okt. rewrite* closed_env_eq.
  inversion H.
  apply_fresh* typing_tabs_closed as y. apply* closed_env_okt. rewrite* closed_env_eq.
  inversion H.
Qed.

(* ********************************************************************** *)
(** * Properties of Healthy Evnironment *)

Hint Constructors capsafe caprod.

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

Hint Immediate capsafe_regular caprod_regular.

Lemma capsafe_subst_tt: forall T,
  capsafe T -> forall Z P, capsafe P -> capsafe (subst_tt Z P T).
  apply (capsafe_mut
           (fun T safeT => forall Z P, capsafe P -> capsafe (subst_tt Z P T) )
           (fun T prodT => forall Z P, capsafe P -> caprod (subst_tt Z P T) )
        ); intros; simpls; eauto.
  case_if*.
  let L' := gather_vars in apply capsafe_A with L'; auto.
    unsimpl (subst_tt Z P (typ_all_closed T)). auto.
    intros. rewrite* subst_tt_open_tt_var.
  let L' := gather_vars in apply caprod_A with L'; auto.
    unsimpl (subst_tt Z P (typ_all_closed T)). auto.
    intros. rewrite* subst_tt_open_tt_var.
Qed.

Lemma caprod_subst_tt: forall T,
  caprod T -> forall Z P, capsafe P -> caprod (subst_tt Z P T).
  apply (caprod_mut
           (fun T safeT => forall Z P, capsafe P -> capsafe (subst_tt Z P T) )
           (fun T prodT => forall Z P, capsafe P -> caprod (subst_tt Z P T) )
        ); intros; simpls; eauto.
  case_if*.
  let L' := gather_vars in apply capsafe_A with L'; auto.
    unsimpl (subst_tt Z P (typ_all_closed T)). auto.
    intros. rewrite* subst_tt_open_tt_var.
  let L' := gather_vars in apply caprod_A with L'; auto.
    unsimpl (subst_tt Z P (typ_all_closed T)). auto.
    intros. rewrite* subst_tt_open_tt_var.
Qed.

Lemma capsafe_closed_typ: forall T, capsafe T -> closed_typ T = true.
Proof. intros. inductions H; try reflexivity; try false; autos. Qed.

Lemma capsafe_not_caprod : forall T, capsafe T -> ~ caprod T.
  apply (capsafe_mut
           (fun T safeT => ~ caprod T )
           (fun T prodT => ~ capsafe T )
        ); intros; intros Hc; inversions Hc; eauto.
  pick_fresh X. forwards~ : H X.
  pick_fresh X. forwards~ : H X.
Qed.

Lemma caprod_not_capsafe : forall T, caprod T -> ~ capsafe T.
  apply (caprod_mut
           (fun T safeT => ~ caprod T )
           (fun T prodT => ~ capsafe T )
        ); intros; intros Hc; inversions Hc; eauto.
  pick_fresh X. forwards~ : H X.
  pick_fresh X. forwards~ : H X.
Qed.

Lemma capsafe_caprod_classic: forall T, type T -> capsafe T \/ caprod T.
Proof. intros T Ht. inductions Ht; iauto.
  pick_fresh X. forwards~ : H0 X. destruct H1.
  left. apply capsafe_A with (L \u fv_tt T2). apply* type_all_closed.
    intros. forwards~ : capsafe_subst_tt H1 X (typ_fvar X0).
    rewrite* <- (@subst_tt_intro X) in H3.
  right. apply caprod_A with L. apply* type_all_closed.
    intros. forwards~ : caprod_subst_tt H1 X (typ_fvar X0).
    rewrite* <- (@subst_tt_intro X) in H3.
Qed.

Lemma capsafe_decidable: forall T, type T -> capsafe T \/ ~ capsafe T.
Proof. intros. destruct (capsafe_caprod_classic H). left*.
  right. intros Hc. lets*: capsafe_not_caprod Hc.
Qed.

Lemma not_capsafe_caprod : forall T, type T -> ~capsafe T -> caprod T.
Proof. intros. destruct* (capsafe_caprod_classic H). Qed.

Lemma healthy_env_closed: forall E, healthy E -> closed_env E = E.
Proof. intros. inductions H.
  rewrite empty_def. reflexivity.
  rewrite <- cons_to_push. simpls. lets: capsafe_closed_typ H.
    rewrite* H2. rewrite* IHhealthy.
  rewrite <- cons_to_push. simpls. rewrite* IHhealthy.
Qed.

Lemma healthy_env_capsafe : forall E S x, healthy E ->
   binds x (bind_x S) E ->  capsafe S.
Proof. introv H Hb. inductions H.
  false* binds_empty_inv.
  destruct (binds_push_inv Hb).
    destruct H2. inversions* H3.
    destruct H2. autos.
  destruct (binds_push_inv Hb).
    destruct H1. inversions* H2.
    destruct H1. autos.
Qed.

Hint Resolve capsafe_subst_tt capsafe_closed_typ.

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
Qed.

Lemma wft_fv_tt: forall E T,
  wft E T -> fv_tt T \c dom E.
Proof.
  intros. induction H; simpls.
  lets: get_some_inv (binds_get H). unfolds. intros.
    rewrite in_singleton in H1. rewrite* H1.
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
                                apply* subset_union_2; apply closed_env_dom_subset
    | [|- _ \c dom ?E ] => eapply subset_trans; eauto; apply closed_env_dom_subset
    | [_: ?a \c ?E, _: ?b \c ?E |- ?a \u ?b \c ?E ] =>
      rewrite <- union_same; apply* subset_union_2
  end.

Ltac splits_solve_subsets := splits*; try solve_subsets.

Lemma typing_env_fv : forall E e T,
  typing E e T -> fv_te e \c dom E /\ fv_ee e \c dom E /\ fv_tt T \c dom E.
Proof. intros. inductions H.
  (* var *)
  simpls. splits; try solve [autos* subset_empty_l wft_fv_tt].
    forwards~ K:  get_some_inv (binds_get H0). unfolds subset.
    intros. rewrite in_singleton in H1. subst*.
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
  apply_fresh* typing_abs_closed as y. destruct (typing_regular TypU).
    rewrite* subst_ee_open_ee_var.
    (* if U is closed, then use IH; else  x is free in e1; *)
    repeat(rewrite closed_env_dist in *). remember (closed_typ U) as b. destruct b.
      (* closed_typ U = true *)
      symmetry in Heqb. rewrite* closed_env_single_true in H1.
      intros. rewrite <- concat_assoc. apply H1 with U; autos. rewrite* concat_assoc.
      apply* typing_strengthen_env.
      (* closed_typ U = false *)
      symmetry in Heqb. rewrite* closed_env_single_false in H0. rewrite concat_empty_r in H0.
      lets: ok_middle_inv (ok_from_okt H). forwards~ HI: H0 y.
      rewrite* subst_ee_fresh. destructs (typing_env_fv HI). unfolds notin. intros HII.
      assert (HIII: x \in dom (closed_env E & closed_env F & y ~: V)) by unfolds* subset.
      repeat(rewrite dom_concat in HIII). repeat(rewrite in_union in HIII).
      rewrite dom_single in HIII. rewrite or_assoc in HIII. destruct H4. branches HIII.
        apply H4. lets*: closed_env_dom_subset E.
        apply H8. lets*: closed_env_dom_subset F.
        rewrite in_singleton in H9. substs. apply* Fry. repeat(rewrite in_union).
          autos* in_singleton_self.
  apply* typing_app.
  apply_fresh* typing_tabs_closed as Y.  destruct (typing_regular TypU).
    rewrite* subst_ee_open_te_var.
    (* if U is closed, then use IH; else  x is free in e1; *)
    repeat(rewrite closed_env_dist in *). remember (closed_typ U) as b. destruct b.
      (* closed_typ U = true *)
      symmetry in Heqb. rewrite* closed_env_single_true in H1.
      intros. rewrite <- concat_assoc. apply H1 with U; autos. rewrite* concat_assoc.
      apply* typing_strengthen_env.
      (* closed_typ U = false *)
      symmetry in Heqb. rewrite* closed_env_single_false in H0. rewrite concat_empty_r in H0.
      lets: ok_middle_inv (ok_from_okt H). forwards~ HI: H0 Y.
      rewrite* subst_ee_fresh. destructs (typing_env_fv HI). unfolds notin. intros HII.
      assert (HIII: x \in dom (closed_env E & closed_env F & [:Y:])) by unfolds* subset.
      repeat(rewrite dom_concat in HIII). repeat(rewrite in_union in HIII).
      rewrite dom_single in HIII. rewrite or_assoc in HIII. destruct H4. branches HIII.
        apply H4. lets*: closed_env_dom_subset E.
        apply H8. lets*: closed_env_dom_subset F.
        rewrite in_singleton in H9. substs. apply* FrY. repeat(rewrite in_union).
          autos* in_singleton_self.
  apply* typing_tapp.
Qed.


(************************************************************************ *)
(** Preservation by Type Substitution (11) *)

Lemma typing_through_subst_te : forall E F Z e T P,
  capsafe P ->
  typing (E & [: Z :] & F) e T ->
  wft E P ->
  typing (E & map (subst_tb Z P) F) (subst_te Z P e) (subst_tt Z P T).
Proof.
  introv Hcap Typ PsubQ.
  inductions Typ; introv; simpls subst_tt; simpls subst_te.
  apply* typing_var. rewrite* (@map_subst_tb_id E Z P).
   binds_cases H0; unsimpl_map_bind*. eauto using okt_weaken.
  apply_fresh* typing_abs_closed as y.
    repeat(rewrite closed_env_dist in *). rewrite closed_env_single_tvar in *.
    rewrite* subst_te_open_ee_var. rewrite* closed_env_map.
    unsimpl (subst_tb Z P (bind_x V)). rewrite <- concat_assoc. rewrite <- map_push.
    apply* H1. rewrite* concat_assoc. apply* closed_env_wft_reverse.
  apply* typing_app.
  apply_fresh* typing_tabs_closed as Y.
    repeat(rewrite closed_env_dist in *). rewrite closed_env_single_tvar in *.
    rewrite* subst_te_open_te_var; eauto using wft_type.
    rewrite* subst_tt_open_tt_var; eauto using wft_type.
    rewrite* closed_env_map. unsimpl (subst_tb Z P bind_X).
    rewrite <- concat_assoc. rewrite <- map_push.
    apply* H1. rewrite* concat_assoc. apply* closed_env_wft_reverse.
  rewrite* subst_tt_open_tt.
Qed.

(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen e'. induction Typ; introv Red;
   try solve [ inversion Red ].
  (* case: app *)
  inversions Red; try solve [ apply* typing_app ].
  inversions Typ1. pick_fresh x. forwards~ K: (H7 x).
  rewrite* (@subst_ee_intro x).
    apply_empty typing_through_subst_ee; substs*.
    rewrite <- (@concat_empty_l bind _). rewrite concat_assoc.
    apply typing_weakening_env. rewrite* concat_empty_l.
    rewrite concat_empty_l. apply* okt_typ.
    autos* typing_wft.
    lets*: typing_regular Typ2.
  (* case: tapp *)
  inversions Red. try solve [ apply* typing_tapp ].
  inversions Typ. pick_fresh X. forwards~ : H7 X.
  rewrite* (@subst_te_intro X).
  rewrite* (@subst_tt_intro X).
  asserts_rewrite (E = E & map (subst_tb X T) empty).
    rewrite map_empty. rewrite~ concat_empty_r.
  apply* typing_through_subst_te. rewrite concat_empty_r.
  rewrite <- (@concat_empty_l bind E).
  apply typing_weakening_env. rewrite* concat_empty_l.
  rewrite concat_empty_l. apply* okt_X.
Qed.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)
(** Canonical Forms (14) *)

Lemma canonical_form_abs : forall t U1 U2,
  value t -> typing empty t (typ_arrow_closed U1 U2) ->
  exists V, exists e1, t = trm_abs V e1.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  gen_eq T: (typ_arrow_closed U1 U2). gen U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
Qed.

Lemma canonical_form_tabs : forall t U1,
  value t -> typing empty t (typ_all_closed U1) ->
  exists e1, t = trm_tabs e1.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  gen_eq T: (typ_all_closed U1). gen U1.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
Qed.

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (@empty bind). lets Typ': Typ.
  induction Typ; intros EQ; subst; autos.
  (* case: var *)
  false* binds_empty_inv.
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
Qed.

(* ********************************************************************** *)
(** * effect safety *)

Lemma healthy_env_term_capsafe: forall E t T,
  healthy E ->
  typing E t T ->
  capsafe T.
Proof. intros. inductions H0.
  apply* healthy_env_capsafe.
  pick_fresh x. forwards~ : H1 x.
    assert (HI: type V) by destruct* (typing_regular H3).
    destruct (capsafe_decidable HI).
      apply* capsafe_X_S. apply* (H2 x). rewrite* (healthy_env_closed H).
      apply* healthy_push_x. lets*: not_capsafe_caprod H4.
      apply* capsafe_C_X. autos* wft_type typing_wft.
  forwards~ : IHtyping1 H. forwards~ : IHtyping2 H. inversions* H0.
    lets*: capsafe_not_caprod T1.
  assert (typing E (trm_tabs e1) (typ_all_closed T1)) by apply* typing_tabs_closed.
    let L' := gather_vars in apply capsafe_A with L'; autos* wft_type typing_wft.
    intros. apply* H2. rewrite* (healthy_env_closed H). apply* healthy_push_X.
  lets: IHtyping H. inversions H3. pick_fresh X. forwards~ : H6 X.
    forwards~ : capsafe_subst_tt H3 X T.
    rewrite* <- (@subst_tt_intro X) in H4.
Qed.

Lemma effect_safety_result : effect_safety.
Proof. intros E H He. destruct He.
  lets*: healthy_env_term_capsafe H0. inversions H1.
Qed.
