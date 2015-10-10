(***************************************************************************
* Preservation and Progress for System-F with Closed Functions             *
* - allow capture of type variables in closed functions                    *
*                                                                          *
* (based on the F<: implementation in locally-nameless project)            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.
Implicit Types X : var.

(* ********************************************************************** *)
(** * Description of the Language *)

(** Representation of pre-types *)

Inductive typ : Set :=
  | typ_bvar  : nat -> typ
  | typ_fvar  : var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all   : typ -> typ.

(** Representation of pre-terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_cap  : typ -> trm -> trm           (* capsule lambda - closed *)
  | trm_app  : trm -> trm -> trm
  | trm_tabs : trm -> trm
  | trm_tapp : trm -> typ -> trm.

(** Opening up a type binder occuring in a type *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar J      => If K = J then U else (typ_bvar J)
  | typ_fvar X      => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1   => typ_all (open_tt_rec (S K) U T1)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

(** Opening up a type binder occuring in a term *)

Fixpoint open_te_rec (K : nat) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | trm_cap V e1  => trm_cap  (open_tt_rec K U V)  (open_te_rec K U e1)
  | trm_app e1 e2 => trm_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | trm_tabs e1 => trm_tabs (open_te_rec (S K) U e1)
  | trm_tapp e1 V => trm_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  end.

Definition open_te t U := open_te_rec 0 U t.

(** Opening up a term binder occuring in a term *)

Fixpoint open_ee_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => If k = i then f else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs V (open_ee_rec (S k) f e1)
  | trm_cap V e1  => trm_cap V (open_ee_rec (S k) f e1)
  | trm_app e1 e2 => trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | trm_tabs e1 => trm_tabs (open_ee_rec k f e1)
  | trm_tapp e1 V => trm_tapp (open_ee_rec k f e1) V
  end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "T 'open_tt_var' X" := (open_tt T (typ_fvar X)) (at level 67).
Notation "t 'open_te_var' X" := (open_te t (typ_fvar X)) (at level 67).
Notation "t 'open_ee_var' x" := (open_ee t (trm_fvar x)) (at level 67).

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T2,
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
      type (typ_all T2).

(** Terms as locally closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L V e1,
      type V ->
      (forall x, x \notin L -> term (e1 open_ee_var x)) ->
      term (trm_abs V e1)
  | term_cap : forall L V e1,
      type V ->
      (forall x, x \notin L -> term (e1 open_ee_var x)) ->
      term (trm_cap V e1)
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

(* get environment for typing types *)
Fixpoint typ_env (E: env) := match E with
  | nil => nil
  | cons (X, bind_X) E' => cons (X, bind_X) (typ_env E')
  | cons (_, bind_x _) E' => typ_env E'
  end.

(** Well-formedness of a pre-type T in an environment E: all the type
  variables of T must be bound via [: T :] in E. This predicates
  implies that T is a type *)

Inductive wft : env -> typ -> Prop :=
  | wft_var : forall E X,
      binds X bind_X E ->
      wft E (typ_fvar X)
  | wft_arrow : forall E T1 T2,
      wft E T1 ->
      wft E T2 ->
      wft E (typ_arrow T1 T2)
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
  | okt_X : forall E X,
      okt E -> X # E -> okt (E & [: X :])
  | okt_typ : forall E x T,
      okt E -> wft E T -> x # E -> okt (E & x ~: T).

(** Typing relation *)

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      okt E ->
      binds x (bind_x T) E ->
      typing E (trm_fvar x) T
  | typing_abs : forall L E V e1 T1,
      (forall x, x \notin L ->
        typing (E & x ~: V) (e1 open_ee_var x) T1) ->
      typing E (trm_abs V e1) (typ_arrow V T1)
  | typing_cap: forall L E V e1 T1,   (* v2: allow capture type variable *)
      okt E ->
      (forall x, x \notin L ->
        typing ((typ_env E) & x ~: V) (e1 open_ee_var x) T1) ->
      typing E (trm_cap V e1) (typ_arrow V T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (trm_app e1 e2) T2
  | typing_tabs : forall L E e1 T1,
      (forall X, X \notin L ->
        typing (E & [: X :]) (e1 open_te_var X) (T1 open_tt_var X)) ->
      typing E (trm_tabs e1) (typ_all T1)
  | typing_tapp : forall T1 E e1 T,
      wft E T ->
      typing E e1 (typ_all T1) ->
      typing E (trm_tapp e1 T) (open_tt T1 T).

(** Values *)

Inductive value : trm -> Prop :=
  | value_abs  : forall V e1, term (trm_abs V e1) ->
                 value (trm_abs V e1)
  | value_cap  : forall V e1, term (trm_cap V e1) ->
                 value (trm_cap V e1)
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
  | red_cap : forall V e1 v2,
      term (trm_cap V e1) ->
      value v2 ->
      red (trm_app (trm_cap V e1) v2) (open_ee e1 v2)
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

(* ********************************************************************** *)
(** * Additional Definitions Used in the Proofs *)

(** Computing free type variables in a type *)

Fixpoint fv_tt (T : typ) {struct T} : vars :=
  match T with
  | typ_bvar J      => \{}
  | typ_fvar X      => \{X}
  | typ_arrow T1 T2 => (fv_tt T1) \u (fv_tt T2)
  | typ_all T1      => (fv_tt T1)
  end.

(** Computing free type variables in a term *)

Fixpoint fv_te (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{}
  | trm_abs V e1  => (fv_tt V) \u (fv_te e1)
  | trm_cap V e1  => (fv_tt V) \u (fv_te e1)
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
  | trm_cap V e1  => (fv_ee e1)
  | trm_app e1 e2 => (fv_ee e1) \u (fv_ee e2)
  | trm_tabs e1   => (fv_ee e1)
  | trm_tapp e1 V => (fv_ee e1)
  end.

Definition fv (e : trm) := (fv_te e) \u (fv_ee e).

(** Substitution for free type variables in types. *)

Fixpoint subst_tt (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar J      => typ_bvar J
  | typ_fvar X      => If X = Z then U else (typ_fvar X)
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T       => typ_all (subst_tt Z U T)
  end.

(** Substitution for free type variables in terms. *)

Fixpoint subst_te (Z : var) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | trm_cap V e1  => trm_cap  (subst_tt Z U V)  (subst_te Z U e1)
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
  | trm_cap V e1  => trm_cap V (subst_ee z u e1)
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

(** Substitutions preserve local closure. *)

Lemma subst_tt_type : forall T Z P,
  type T -> type P -> type (subst_tt Z P T).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* type_all as X. rewrite* subst_tt_open_tt_var.
Qed.

Lemma subst_te_term : forall e Z P,
  term e -> type P -> term (subst_te Z P e).
Proof.
  lets: subst_tt_type. induction 1; intros; simpl; auto.
  apply_fresh* term_abs as x. rewrite* subst_te_open_ee_var.
  apply_fresh* term_cap as x. rewrite* subst_te_open_ee_var.
  apply_fresh* term_tabs as x. rewrite* subst_te_open_te_var.
Qed.

Lemma subst_ee_term : forall e1 Z e2,
  term e1 -> term e2 -> term (subst_ee Z e2 e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
  apply_fresh* term_cap as y. rewrite* subst_ee_open_ee_var.
  apply_fresh* term_tabs as Y. rewrite* subst_ee_open_te_var.
Qed.

Hint Resolve subst_tt_type subst_te_term subst_ee_term.


(* ********************************************************************** *)
(** * Properties of well-formedness of a type in an environment *)

(** If a type is well-formed in an environment then it is locally closed. *)

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
       replace bind_X with ((subst_tb Z P) bind_X) by reflexivity.
       apply~ binds_map.
      destruct (binds_push_inv H1) as [[? ?]|[? ?]].
        subst. false~.
        applys wft_var. apply* binds_concat_left.
  apply_fresh* wft_all as Y.
   unsimpl ((subst_tb Z P) bind_X).
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
  induction 1.
  splits*.
  splits.
   pick_fresh y. specializes H0 y. destructs~ H0.
    forwards*: okt_push_x_inv.
   apply_fresh* term_abs as y.
     pick_fresh y. specializes H0 y. destructs~ H0.
      forwards*: okt_push_x_inv.
     specializes H0 y. destructs~ H0.
  splits*. apply_fresh* term_cap as y.
     pick_fresh y. specializes H1 y. destructs~ H1.
     lets*: okt_push_x_type H1.
     specializes H1 y. destructs~ H1.
  splits*.
  splits.
   pick_fresh y. specializes H0 y. destructs~ H0. lets*: (okt_push_X_inv H0).
     apply term_tabs with L. intros. apply* H0.
  splits*. lets(H1 & H2): IHtyping.
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
Lemma typ_env_dist: forall E F, typ_env (E & F) = typ_env E & typ_env F.
Proof. rewrite concat_def. intros. gen E. induction F; intros E; autos.
  rewrite LibList.app_cons. destruct a. destruct* b.
  simpl. rewrite LibList.app_cons. rewrite* <- IHF.
Qed.

Lemma typ_env_dom_subset : forall E, dom (typ_env E) \c dom E.
Proof. intros. induction E.
  simpl. apply subset_refl.
  destruct a. destruct b.
  simpl. repeat(rewrite cons_to_push). repeat(rewrite dom_push).
    eapply subset_trans. eapply subset_union_2.
    eapply subset_refl. exact IHE. apply subset_refl.
  simpl. rewrite cons_to_push. rewrite dom_push.
    eapply subset_trans. exact IHE. apply subset_union_weak_r.
Qed.

Lemma typ_env_okt : forall E,
  okt E -> okt (typ_env E).
Proof. intros. induction* E.
  destruct a. destruct b; simpl; rewrite cons_to_push in *.
  apply okt_X. apply IHE. lets*: okt_push_X_inv H.
  unfolds. lets(_ & HI): okt_push_X_inv H. autos* (typ_env_dom_subset E).
  apply IHE. lets*: okt_push_x_inv H.
Qed.

Lemma typ_env_binds: forall E x, ok E -> binds x bind_X (typ_env E) -> binds x bind_X E.
Proof. intros. induction E.
  simpl in *. autos.
  destruct a. destruct b.
    simpl in *. rewrite cons_to_push in *. destruct (binds_push_inv H0).
      destruct H1. subst. apply binds_push_eq.
      destruct H1. apply* binds_push_neq.
    simpl in *.  rewrite cons_to_push in *. apply binds_push_neq.
      autos* ok_concat_inv_l.
      intros Ha. subst. lets: IHE (ok_concat_inv_l H) H0.
      rewrite <- concat_empty_r in H. lets: ok_middle_inv_l H.
      apply (binds_fresh_inv H1 H2).
Qed.

Lemma typ_env_binds_reverse: forall E x, binds x bind_X E -> binds x bind_X (typ_env E).
Proof. intros. induction E.
  simpl in *. autos.
  destruct a. destruct b.
    simpl in *. rewrite cons_to_push in *. destruct (binds_push_inv H).
      destruct H0. subst. apply binds_push_eq.
      destruct H0. apply* binds_push_neq.
    simpl in *. rewrite cons_to_push in *. apply IHE.
      eapply binds_push_neq_inv. exact H.
      intros HI. subst. lets: binds_push_eq_inv H. inversion H0.
Qed.

Lemma typ_env_wft: forall E V, ok E -> wft (typ_env E) V -> wft E V.
Proof. intros. remember (typ_env E) as G. gen E. induction H0; intros; subst.
  apply wft_var. apply* typ_env_binds.
  apply* wft_arrow.
  apply_fresh* wft_all as Y. apply* H0. repeat(rewrite <- cons_to_push). autos.
Qed.

Lemma typ_env_wft_reverse: forall E V, wft E V -> wft (typ_env E) V.
Proof. intros. induction H.
  apply wft_var. apply* typ_env_binds_reverse.
  apply* wft_arrow.
  apply_fresh* wft_all as Y. forwards~ HI: (H0 Y).
    rewrite typ_env_dist in HI. rewrite single_def in *. autos.
Qed.

Lemma typ_env_map : forall E Z P, typ_env (map (subst_tb Z P) E) = map (subst_tb Z P) (typ_env E).
Proof. intros. induction E.
  simpl. rewrite <- empty_def. rewrite map_empty. rewrite empty_def. reflexivity.
  destruct a. destruct b; simpl.
    repeat(rewrite cons_to_push). repeat(rewrite map_push). simpl.
      rewrite <- cons_to_push. simpl. rewrite cons_to_push. rewrite* IHE.
    repeat(rewrite cons_to_push). repeat(rewrite map_push). simpl.
      rewrite <- cons_to_push. simpl. rewrite* IHE.
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
  apply_fresh* typing_abs as x. forwards~ K: (H x).
   apply_ih_bind (H0 x); eauto.
  apply_fresh* typing_cap as x. forwards~ K: (H0 x).
   assert (HI: okt(typ_env E & typ_env F & typ_env G)).
     apply typ_env_okt in Ok. repeat(rewrite typ_env_dist in Ok). autos.
   repeat(rewrite typ_env_dist in *).
   rewrite <- concat_assoc.
   apply* H1. rewrite* concat_assoc.
   rewrite concat_assoc. apply* okt_typ.
     unfolds. intros HII. repeat(rewrite dom_concat in HII).
     assert (Ha: x \notin dom E \u dom F \u dom G) by autos.
     apply Ha. repeat(rewrite in_union in *).
     rewrite or_assoc in HII. branches HII.
     branch 1. lets*: typ_env_dom_subset E.
     branch 2. lets*: typ_env_dom_subset F.
     branch 3. lets*: typ_env_dom_subset G.
  apply* typing_app.
  apply_fresh* typing_tabs as X. forwards~ K: (H X).
   apply_ih_bind (H0 X); eauto.
  apply* typing_tapp.
Qed.

Lemma typing_wft: forall E e T, typing E e T -> wft E T.
Proof.
  intros. induction H. applys~ wft_from_env_has_typ x.
  apply wft_arrow. pick_fresh x. forwards~: (H x).
    lets(H2 & _): (typing_regular H1). autos* (wft_from_okt_typ H2).
    pick_fresh x. forwards~: (H0 x). replace E with (E & empty) by rewrite* concat_empty_r.
    eapply wft_strengthen. rewrite* concat_empty_r.
  apply wft_arrow. pick_fresh x. forwards~: (H0 x).
    lets(H3 & _): (typing_regular H2). lets*: wft_from_okt_typ H3.
    apply* typ_env_wft.

    pick_fresh x. forwards~: (H1 x).
    replace (typ_env E & x~:V) with (typ_env E & x~:V & empty) in H2
      by (rewrite* concat_empty_r).
    apply wft_strengthen in H2. rewrite* concat_empty_r in H2. apply* typ_env_wft.
  inverts* IHtyping1.
  apply* (@wft_all L).
  apply* wft_open.
Qed.


(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma open_tt_fv_subset: forall k U T,
  fv_tt T \c fv_tt (open_tt_rec k U T).
Proof. intros. gen k. induction T; intros; simpl.
  apply subset_empty_l.
  apply subset_refl.
  apply* subset_union_2.
  autos.
Qed.

Lemma open_te_fv_subset: forall k U e,
  fv_te e \c fv_te (open_te_rec k U e).
Proof. intros. gen k. induction e; intros; simpls.
  apply subset_empty_l.
  apply subset_empty_l.
  apply* subset_union_2. apply open_tt_fv_subset.
  apply* subset_union_2. apply open_tt_fv_subset.
  apply* subset_union_2.
  autos.
  apply* subset_union_2. apply open_tt_fv_subset.
Qed.

Lemma open_ee_fv_subset: forall k u e,
  fv_ee e \c fv_ee (open_ee_rec k u e).
Proof. intros. gen k. induction e; intros; simpls.
  apply subset_empty_l.
  apply subset_refl.
  autos.
  autos.
  apply* subset_union_2.
  autos.
  autos.
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
Proof. intros. gen k. induction e; intros; simpls; autos.
  apply subset_empty_l.
  apply subset_empty_l.
  apply* subset_union_2. apply subset_refl.
  apply* subset_union_2. apply subset_refl.
  apply* subset_union_2.
  apply* subset_union_2. apply subset_refl.
Qed.

Lemma open_tt_tt_fv_subset: forall k T1 T2,
  fv_tt (open_tt_rec k T1 T2) \c fv_tt T1 \u fv_tt T2.
Proof. intros. gen k. induction T2; intros; simpls; autos.
  destruct (prop_degeneracy (k = n)).
    (* k = n*)
    apply is_True_inv in H. rewrite* If_l. apply subset_union_weak_l.
    (* k != n*)
    apply is_False_inv in H. rewrite* If_r. simpl. apply subset_empty_l.

  apply subset_union_weak_r.

  lets*: (subset_union_2 (IHT2_1 k) (IHT2_2 k)).
  rewrite union_assoc in H.
  rewrite union_comm in H.
  replace ((fv_tt T1 \u fv_tt T2_1) \u fv_tt T1) with (fv_tt T1 \u fv_tt T2_1) in H.
  rewrite union_assoc. rewrite union_comm. autos.

  rewrite union_comm. rewrite <- union_assoc.
  rewrite union_same. reflexivity.
Qed.


Lemma wft_fv_tt: forall E T,
  wft E T -> fv_tt T \c dom E.
Proof.
  intros. induction H.
  simpl. lets: get_some_inv (binds_get H).
  unfolds. intros. rewrite in_singleton in H1. rewrite* H1.
  simpl. replace (dom E) with (dom E \u dom E) by (autos* union_same).
  apply* subset_union_2.
  pick_fresh X. forwards~ HI: (H0 X). simpl. rewrite dom_concat in HI.
  rewrite dom_single in HI.

  assert (HII: fv_tt T \c dom E \u \{X}).
    apply subset_trans with (fv_tt (T open_tt_var X)).
    autos* open_tt_fv_subset. autos.

  apply subset_strengthen with X; autos.
Qed.

Lemma typing_env_fv : forall E e T,
  typing E e T -> fv e \c dom E /\ fv_tt T \c dom E.
Proof.  intros. induction* H; subst.
  (* var *)
  forwards~ K:  get_some_inv (binds_get H0).
  unfolds fv. simpl. split.
  rewrite* union_empty_l. unfolds. intros.
  rewrite in_singleton in H1. subst*.
  applys* wft_fv_tt.
  (* abs *)
  unfold fv. simpl. pick_fresh x. forwards~ (HI & HII) : (H0 x).
  unfold fv in HI. rewrite dom_concat in HI. rewrite dom_single in HI.
  unfold open_ee in HI.
  rewrite dom_concat in HII. rewrite dom_single in HII.
  assert (Ha: fv_te e1 \c dom E).
    apply subset_strengthen with x; autos.
    eapply subset_trans.
    eapply open_te_ee_fv_subset.
    eapply subset_trans.
    eapply subset_union_weak_l. exact HI.
  assert (Hb: fv_ee e1 \c dom E).
    apply subset_strengthen with x; autos.
    apply subset_trans with (fv_ee (open_ee_rec 0 (trm_fvar x) e1)).
    apply open_ee_fv_subset.
    eapply subset_trans.
    eapply subset_union_weak_r. exact HI.
  assert (Hc: fv_tt T1 \c dom E).
    apply subset_strengthen with x; autos.
  assert (Hd: fv_tt V \c dom E).
    forwards~ Htyp: (H x).
    destruct (typing_regular Htyp) as [He _].
    apply subset_strengthen with x; autos.
    rewrite <- dom_single with (v:= bind_x V). rewrite <- dom_concat.
    apply* wft_fv_tt; autos.

  split.

  rewrite <- union_same. apply* subset_union_2.
  rewrite <- union_same. apply* subset_union_2.
  rewrite <- union_same. apply* subset_union_2.

  (* cap *)
  unfold fv. simpl. pick_fresh x. forwards~ (HI & HII) : (H1 x).
  unfold fv in HI. rewrite dom_concat in HI.
  unfold open_ee in HI. rewrite dom_concat in HII.
  rewrite dom_single in *.
  assert (Ha: fv_te e1 \c dom (typ_env E)).
    apply subset_strengthen with x; autos.
    eapply subset_trans.
    eapply open_te_ee_fv_subset.
    eapply subset_trans.
    eapply subset_union_weak_l. exact HI.
  assert (Hb: fv_ee e1 \c dom (typ_env E)).
    apply subset_strengthen with x; autos.
    apply subset_trans with (fv_ee (open_ee_rec 0 (trm_fvar x) e1)).
    apply open_ee_fv_subset.
    eapply subset_trans.
    eapply subset_union_weak_r. exact HI.
  assert (Hc: fv_tt T1 \c dom (typ_env E)).
    apply subset_strengthen with x; autos.
  assert (Hd: fv_tt V \c dom (typ_env E)).
    forwards~ Htemp: (H0 x).
    destruct (typing_regular Htemp) as [He _].
    apply* wft_fv_tt.

  split.

  apply subset_trans with (dom (typ_env E)).
  rewrite <- union_same. apply* subset_union_2.
  rewrite <- union_same. apply* subset_union_2.
  apply typ_env_dom_subset.


  apply subset_trans with (dom (typ_env E)).
  rewrite <- union_same. apply* subset_union_2.
  apply typ_env_dom_subset.

  (* app *)
  destruct IHtyping1. destruct IHtyping2. unfolds fv.
  assert (Ha: fv_te e1 \c dom E).
    eapply subset_trans.
    eapply subset_union_weak_l. exact H1.
  assert (Hb: fv_ee e1 \c dom E).
    eapply subset_trans.
    eapply subset_union_weak_r. exact H1.
  assert (Hd: fv_tt T1 \c dom E).
    simpl in H2.
    eapply subset_trans.
    eapply subset_union_weak_l. exact H2.
  assert (He: fv_tt T2 \c dom E).
    simpl in H2.
    eapply subset_trans.
    eapply subset_union_weak_r. exact H2.
  assert (Hf: fv_te e2 \c dom E).
    eapply subset_trans.
    eapply subset_union_weak_l. exact H3.
  assert (Hg: fv_ee e2 \c dom E).
    eapply subset_trans.
    eapply subset_union_weak_r. exact H3.

  simpl. split.

  replace (dom E) with (dom E \u dom E) by (autos* union_same).
  apply* subset_union_2.

  replace (dom E) with (dom E \u dom E) by (autos* union_same).
  apply* subset_union_2.

  replace (dom E) with (dom E \u dom E) by (autos* union_same).
  apply* subset_union_2.

  assumption.

  (* tabs *)
  unfold fv. simpl. pick_fresh X. forwards~ (HI & HII) : (H0 X).
  unfold fv in HI. rewrite dom_concat in HI. rewrite dom_single in HI.
  unfold open_te in HI. rewrite <- open_ee_te_fv_eq in HI.
  unfold open_tt in HII. rewrite dom_concat in HII. rewrite dom_single in HII.
  assert (Ha: fv_te e1 \c dom E).
    apply subset_strengthen with X; autos.
    eapply subset_trans.
    eapply open_te_fv_subset.
    eapply subset_trans.
    eapply subset_union_weak_l. exact HI.
  assert (Hb: fv_ee e1 \c dom E).
    apply subset_strengthen with X; autos.
    eapply subset_trans.
    eapply subset_union_weak_r. exact HI.
  assert (Hc: fv_tt T1 \c dom E).
    apply subset_strengthen with X; autos.
    eapply subset_trans. eapply open_tt_fv_subset.
    exact HII.

  split.

  replace (dom E) with (dom E \u dom E) by (autos* union_same).
  apply* subset_union_2.

  assumption.

  (* tapp *)
  destruct IHtyping. unfold fv in H1. simpl in H2.
  assert (Ha: fv_te e1 \c dom E).
    eapply subset_trans.
    eapply subset_union_weak_l. exact H1.
  assert (Hb: fv_ee e1 \c dom E).
    eapply subset_trans.
    eapply subset_union_weak_r. exact H1.
  assert (Hc: fv_tt T \c dom E).
    apply* wft_fv_tt.

  unfold fv. simpl. split.

  replace (dom E) with (dom E \u dom E) by (autos* union_same).
  apply* subset_union_2.

  replace (dom E) with (dom E \u dom E) by (autos* union_same).
  apply* subset_union_2.

  eapply subset_trans.
  eapply open_tt_tt_fv_subset.
  replace (dom E) with (dom E \u dom E) by (autos* union_same).
  apply* subset_union_2.
Qed.

Lemma typing_term_closed : forall e T,
  typing empty e T -> fv e = \{} /\ fv_tt T = \{}.
Proof using.
  intros. apply typing_env_fv in H.
  rewrite dom_empty in H. destruct H.
  split.
  apply* fset_extens. apply subset_empty_l.
  apply* fset_extens. apply subset_empty_l.
Qed.

Lemma typing_cap_closed : forall e T E F x U V,
  typing (E & x ~: U & F) (trm_cap V e) T -> x \notin fv_ee e.
Proof. intros. inversion H. subst.
  repeat(rewrite typ_env_dist in H5).
  replace (typ_env (x ~: U)) with (@empty bind) in H5
    by (rewrite single_def; simpl; rewrite* empty_def).
  rewrite concat_empty_r in H5. rewrite <- typ_env_dist in H5.
  assert (HI: typing (E & F) (trm_cap V e) (typ_arrow V T1)).
    apply* typing_cap.
  destruct (typing_env_fv HI).
  unfold fv in H0. simpl in H0.
  lets: ok_middle_inv (ok_from_okt H3).
  rewrite <- notin_union in H2. rewrite <- dom_concat in H2.
  unfolds subset. intros Hc. apply H2. apply H0.
  rewrite in_union. right. autos.
Qed.

Lemma typing_through_subst_ee : forall U E F x T e u,
  typing (E & x ~: U & F) e T ->
  typing E u U ->
  typing (E & F) (subst_ee x u e) T.
Proof.
  introv TypT TypU. inductions TypT; introv; simpl.
  case_var.
    binds_get H0. apply_empty* typing_weakening.
    binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H0. lets*: (typing_regular TypU).
  apply_fresh* typing_cap as y.
    rewrite* subst_ee_fresh.
    repeat(rewrite typ_env_dist in H0).
    replace (typ_env (x ~: U)) with (@empty bind) in H0
      by (rewrite single_def; simpl; rewrite* empty_def).
    rewrite concat_empty_r in *.
    rewrite* typ_env_dist.
    assert (HI: typing (E & x ~: U & F) (trm_cap V e1) (typ_arrow V T1)).
      apply* typing_cap.
    lets*: typing_cap_closed HI.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    rewrite* subst_ee_open_te_var.
    apply_ih_bind* H0.  lets*: (typing_regular TypU).
  apply* typing_tapp.
Qed.


(************************************************************************ *)
(** Preservation by Type Substitution (11) *)

Lemma typing_through_subst_te : forall E F Z e T P,
  typing (E & [: Z :] & F) e T ->
  wft E P ->
  typing (E & map (subst_tb Z P) F) (subst_te Z P e) (subst_tt Z P T).
Proof.
  introv Typ PsubQ.
  inductions Typ; introv; simpls subst_tt; simpls subst_te.
  apply* typing_var. rewrite* (@map_subst_tb_id E Z P).
   binds_cases H0; unsimpl_map_bind*. eauto using okt_weaken.
  apply_fresh* typing_abs as y.
    unsimpl (subst_tb Z P (bind_x V)).
    rewrite* subst_te_open_ee_var.
    apply_ih_map_bind* H0.
  apply_fresh* typing_cap as y.
    unsimpl (subst_tb Z P (bind_x V)).
    rewrite* subst_te_open_ee_var. rewrite typ_env_dist.
    rewrite typ_env_map. apply_ih_map_bind* H1.
    repeat(rewrite typ_env_dist).
    replace (typ_env ([:Z:])) with ([:Z:])
      by (rewrite single_def; simpl; autos).
    rewrite concat_assoc. reflexivity.
    apply* typ_env_wft_reverse.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    unsimpl (subst_tb Z P bind_X).
    rewrite* subst_te_open_te_var; eauto using wft_type.
    rewrite* subst_tt_open_tt_var; eauto using wft_type.
    apply_ih_map_bind* H0.
  rewrite* subst_tt_open_tt; eauto using wft_type.
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
  inversions Typ1. pick_fresh x. forwards~ K: (H2 x).
  rewrite* (@subst_ee_intro x).
  apply_empty typing_through_subst_ee; substs*.
       lets*: typing_regular Typ2.

  inversions Typ1. pick_fresh x. forwards~ K: (H7 x).
  rewrite* (@subst_ee_intro x).
    apply_empty typing_through_subst_ee; substs*.
    rewrite <- (@concat_empty_l bind _).
    rewrite concat_assoc.
    apply* typing_weakening. rewrite* concat_empty_l.
    apply* okt_typ. rewrite* concat_empty_l.
    rewrite* concat_empty_l. autos* typing_wft.
    lets*: typing_regular Typ2.
  (* case: tapp *)
  inversions Red; try solve [ apply* typing_tapp ].
  inversions Typ. pick_fresh X. forwards~ K: (H5 X).
  rewrite* (@subst_te_intro X).
  rewrite* (@subst_tt_intro X).
  asserts_rewrite (E = E & map (subst_tb X T) empty).
    rewrite map_empty. rewrite~ concat_empty_r.
  apply* typing_through_subst_te.
  rewrite* concat_empty_r.
Qed.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)
(** Canonical Forms (14) *)

Lemma canonical_form_abs : forall t U1 U2,
  value t -> typing empty t (typ_arrow U1 U2) ->
  exists V, exists e1, t = trm_abs V e1 \/ t = trm_cap V e1.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  gen_eq T: (typ_arrow U1 U2). gen U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
Qed.

Lemma canonical_form_tabs : forall t U1,
  value t -> typing empty t (typ_all U1) ->
  exists e1, t = trm_tabs e1.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  gen_eq T: (typ_all U1). gen U1.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
Qed.

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (@empty bind). lets Typ': Typ.
  induction Typ; intros EQ; subst.
  (* case: var *)
  false* binds_empty_inv.
  (* case: abs *)
  left*. apply value_abs. lets*: typing_regular Typ'.
  left*. apply value_cap. lets*: typing_regular Typ'.
  (* case: app *)
  right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    destruct* IHTyp2 as [Val2 | [e2' Rede2']].
    destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]].
      subst. exists* (open_ee e3 e2). destruct EQ; subst.
        apply* red_abs. lets*: typing_regular Typ1.
        apply* red_cap. lets*: typing_regular Typ1.
    exists* (trm_app e1' e2). apply* red_app_1. lets*: typing_regular Typ2.
  (* case: tabs *)
  left*. apply* value_tabs. lets*: typing_regular Typ'.
  (* case: tapp *)
  right. destruct~ IHTyp as [Val1 | [e1' Rede1']].
    destruct (canonical_form_tabs Val1 Typ) as [e EQ].
      subst. exists* (open_te e T). apply* red_tabs. lets*: typing_regular Typ.
      autos* wft_type.
      exists* (trm_tapp e1' T). apply* red_tapp. autos* wft_type.
Qed.
