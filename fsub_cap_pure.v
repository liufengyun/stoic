(***************************************************************************
* Soundness and effect safety for F<: + capability w/o =>                  *
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
  | typ_top   : typ
  | typ_bvar  : nat -> typ
  | typ_fvar  : var -> typ -> typ
  | typ_base  : typ
  | typ_eff   : typ
  | typ_arrow : typ -> typ -> typ
  | typ_all   : typ -> typ -> typ.

(** Representation of pre-terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_tabs : typ -> trm -> trm
  | trm_tapp : trm -> typ -> trm.

(** Opening up a type binder occuring in a type *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top         => typ_top
  | typ_bvar J      => If K = J then U else (typ_bvar J)
  | typ_fvar X T    => typ_fvar X T
  | typ_base        => typ_base
  | typ_eff         => typ_eff
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1 T2   => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

(** Opening up a type binder occuring in a term *)

Fixpoint open_te_rec (K : nat) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | trm_app e1 e2 => trm_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | trm_tabs V e1 => trm_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
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
  | trm_tabs V e1 => trm_tabs V (open_ee_rec k f e1)
  | trm_tapp e1 V => trm_tapp (open_ee_rec k f e1) V
  end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "T 'open_tt_var' X U" := (open_tt T (typ_fvar X U)) (at level 67).
Notation "t 'open_te_var' X U" := (open_te t (typ_fvar X U)) (at level 67).
Notation "t 'open_ee_var' x" := (open_ee t (trm_fvar x)) (at level 67).

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_var : forall X T, type T ->
      type (typ_fvar X T)
  | type_base: type typ_base
  | type_eff: type typ_eff
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X, X \notin L -> type (open_tt T2 (typ_fvar X T1))) ->
      type (typ_all T1 T2).

(** Terms as locally closed pre-terms *)

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
  | term_tabs : forall L V e1,
      type V ->
      (forall X, X \notin L -> term (open_te e1 (typ_fvar X V))) ->
      term (trm_tabs V e1)
  | term_tapp : forall e1 V,
      term e1 ->
      type V ->
      term (trm_tapp e1 V).

(** Binding are either mapping type or term variables.
 [X ~<: T] is a subtyping asumption and [x ~: T] is
 a typing assumption *)

Inductive bind : Set :=
  | bind_sub : typ -> bind
  | bind_typ : typ -> bind.

Notation "X ~<: T" := (X ~ bind_sub T)
  (at level 23, left associativity) : env_scope.
Notation "x ~: T" := (x ~ bind_typ T)
  (at level 23, left associativity) : env_scope.

(** Environment is an associative list of bindings. *)

Definition env := LibEnv.env bind.

(** Well-formedness of a pre-type T in an environment E:
  all the type variables of T must be bound via a
  subtyping relation in E. This predicates implies
  that T is a type *)

Inductive wft : env -> typ -> Prop :=
  | wft_top : forall E,
      wft E typ_top
  | wft_var : forall U E X,
      wft E U ->
      binds X (bind_sub U) E ->
      wft E (typ_fvar X U)
  | wft_arrow : forall E T1 T2,
      wft E T1 ->
      wft E T2 ->
      wft E (typ_arrow T1 T2)
  | wft_all : forall L E T1 T2,
      wft E T1 ->
      (forall X, X \notin L ->
        wft (E & X ~<: T1) (open_tt T2 (typ_fvar X T1))) ->
      wft E (typ_all T1 T2).

(** A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment
  it is pushed on to. *)

Inductive okt : env -> Prop :=
  | okt_empty :
      okt empty
  | okt_sub : forall E X T,
      okt E -> wft E T -> X # E -> okt (E & X ~<: T)
  | okt_typ : forall E x T,
      okt E -> wft E T -> x # E -> okt (E & x ~: T).

(** Subtyping relation *)

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      okt E ->
      wft E S ->
      sub E S typ_top
  | sub_tvar : forall E X T,
      okt E ->
      wft E (typ_fvar X T) ->
      sub E (typ_fvar X T) T
  | sub_refl : forall E T,
      okt E ->
      wft E T ->
      sub E T T
  | sub_trans : forall E S U T,
      sub E S U -> sub E U T ->
      sub E S T
  | sub_arrow : forall E S1 S2 T1 T2,
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall X, X \notin L ->
                 sub (E & X ~<: T1) (open_tt S2 (typ_fvar X S1))
                     (open_tt T2 (typ_fvar X T1))) ->
      sub E (typ_all S1 S2) (typ_all T1 T2).

Fixpoint safe_bound(T: typ) := match T with
                                 | typ_top      => false
                                 | typ_eff      => false
                                 | typ_fvar _ U => safe_bound U
                                 | _ => true
                               end.

Fixpoint closed_typ(E: env)(t: typ) := match t with
  | typ_bvar _          => false  (* impossible, ill-formed *)
  | typ_fvar X T        => safe_bound T
  | typ_base            => true
  | typ_top             => true
  | typ_eff             => false
  | typ_arrow U V       => true
  | typ_all B T         => true
  end.

(* another more restrictive possibility: exclude X <: Top & its dependents from env *)
Fixpoint pure (E: env) := match E with
  | nil => nil
  | cons (X, bind_sub U) E' => cons (X, bind_sub U) (pure E')
  | cons (x, bind_typ T) E' => if closed_typ E T then
                                 cons (x, bind_typ T) (pure E')
                               else
                                 pure E'
   end.

(** Typing relation *)

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      okt E ->
      binds x (bind_typ T) E ->
      typing E (trm_fvar x) T
  | typing_abs: forall L E V e1 T1,
      okt E ->
      (forall x, x \notin L ->
        typing ((pure E) & x ~: V) (e1 open_ee_var x) T1) ->
      typing E (trm_abs V e1) (typ_arrow V T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (trm_app e1 e2) T2
  | typing_tabs : forall L E V e1 T1,
      (forall X, X \notin L ->
        typing ((pure E) & X ~<: V) (open_te e1 (typ_fvar X V)) (open_tt T1 (typ_fvar X V))) ->
      typing E (trm_tabs V e1) (typ_all V T1)
  | typing_tapp : forall T1 E e1 T T2,
      typing E e1 (typ_all T1 T2) ->
      sub E T T1 ->
      typing E (trm_tapp e1 T) (open_tt T2 T)
  | typing_sub : forall S E e T,
      typing E e S ->
      sub E S T ->
      typing E e T.

(** Values *)

Inductive value : trm -> Prop :=
  | value_abs  : forall V e1, term (trm_abs V e1) ->
                 value (trm_abs V e1)
  | value_tabs : forall V e1, term (trm_tabs V e1) ->
                 value (trm_tabs V e1).

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
  | red_tabs : forall V1 e1 V2,
      term (trm_tabs V1 e1) ->
      type V2 ->
      red (trm_tapp (trm_tabs V1 e1) V2) (open_te e1 V2).

(** Our goal is to prove preservation and progress *)

Definition preservation := forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.

Definition progress := forall e T,
  typing empty e T ->
     value e
  \/ exists e', red e e'.

(* capsafe types are not capability producing, i.e. capable of creating an instance of E *)

Inductive capsafe: env -> typ -> Prop :=
 | capsafe_B: forall E, capsafe E typ_base
 | capsafe_T: forall E, capsafe E typ_top
 | capsafe_X: forall E X T, wft E (typ_fvar X T) -> ~sub E typ_eff T -> capsafe E (typ_fvar X T)
 | capsafe_C_X: forall E S T, wft E T -> caprod E S -> capsafe E (typ_arrow S T)
 | capsafe_X_S: forall E S T, wft E S -> capsafe E T -> capsafe E (typ_arrow S T)
 | capsafe_A: forall E U T, wft E (typ_all U T) ->
                            (forall R, sub E R U -> capsafe E (open_tt T R)) ->
                            capsafe E (typ_all U T)

with caprod: env -> typ -> Prop :=
 | caprod_E: forall E, caprod E typ_eff
 | caprod_X: forall E X T, wft E (typ_fvar X T) -> sub E typ_eff T -> caprod E (typ_fvar X T)
 | caprod_S_C: forall E S T, capsafe E S -> caprod E T -> caprod E (typ_arrow S T)
 | caprod_A: forall E U T, wft E (typ_all U T) ->
                           (exists R, sub E R U /\ caprod E (open_tt T R)) ->
                           caprod E (typ_all U T).

Inductive healthy: env -> Prop :=
  | healthy_empty: healthy empty
  | healthy_push_x: forall x E T, capsafe E T -> healthy E ->
                                  healthy (E & x ~: T)
  | healthy_push_X: forall X T E, healthy E -> wft E T ->
                                healthy (E &  X ~<: T).

(* effect safety : it's impossible to construct a term of typ_eff in pure environment  *)
Definition effect_safety := forall E, healthy E ->
  ~exists e, typing E e typ_eff.


(* ********************************************************************** *)
(** * Additional Definitions Used in the Proofs *)

(** Computing free type variables in a type *)

Fixpoint fv_tt (T : typ) {struct T} : vars :=
  match T with
  | typ_top         => \{}
  | typ_base        => \{}
  | typ_eff         => \{}
  | typ_bvar J      => \{}
  | typ_fvar X R    => \{X} \u (fv_tt R)
  | typ_arrow T1 T2 => (fv_tt T1) \u (fv_tt T2)
  | typ_all T1 T2   => (fv_tt T1) \u (fv_tt T2)
  end.

(** Computing free type variables in a term *)

Fixpoint fv_te (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{}
  | trm_abs V e1  => (fv_tt V) \u (fv_te e1)
  | trm_app e1 e2 => (fv_te e1) \u (fv_te e2)
  | trm_tabs V e1 => (fv_tt V) \u (fv_te e1)
  | trm_tapp e1 V => (fv_tt V) \u (fv_te e1)
  end.

(** Computing free term variables in a type *)

Fixpoint fv_ee (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_abs V e1  => (fv_ee e1)
  | trm_app e1 e2 => (fv_ee e1) \u (fv_ee e2)
  | trm_tabs V e1 => (fv_ee e1)
  | trm_tapp e1 V => (fv_ee e1)
  end.

(** Substitution for free type variables in types. *)

Fixpoint subst_tt (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top         => typ_top
  | typ_base        => typ_base
  | typ_eff         => typ_eff
  | typ_bvar J      => typ_bvar J
  | typ_fvar X R    => If X = Z then U else (typ_fvar X (subst_tt Z U R))
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T1 T2   => typ_all (subst_tt Z U T1) (subst_tt Z U T2)
  end.

(** Substitution for free type variables in terms. *)

Fixpoint subst_te (Z : var) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | trm_app e1 e2 => trm_app  (subst_te Z U e1) (subst_te Z U e2)
  | trm_tabs V e1 => trm_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | trm_tapp e1 V => trm_tapp (subst_te Z U e1) (subst_tt Z U V)
  end.

(** Substitution for free term variables in terms. *)

Fixpoint subst_ee (z : var) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs V e1  => trm_abs V (subst_ee z u e1)
  | trm_app e1 e2 => trm_app (subst_ee z u e1) (subst_ee z u e2)
  | trm_tabs V e1 => trm_tabs V (subst_ee z u e1)
  | trm_tapp e1 V => trm_tapp (subst_ee z u e1) V
  end.

(** Substitution for free type variables in environment. *)

Definition subst_tb (Z : var) (P : typ) (b : bind) : bind :=
  match b with
  | bind_sub T => bind_sub (subst_tt Z P T)
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.

(* Update bound for variables *)
Definition rebound (X: var) (U: typ) := subst_tt X (typ_fvar X U).
Definition rebounds (X: var) (U: typ) := map (subst_tb X (typ_fvar X U)).

(* ********************************************************************** *)
(** * Tactics *)

(** Constructors as hints. *)

Hint Constructors type term wft ok okt value red.

Hint Resolve
  sub_top sub_refl sub_arrow
  typing_var typing_app typing_tapp typing_sub.

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
  | |- sub ?E _ _  => E
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
  pick_fresh X. apply* (@open_tt_rec_type_core T2 0 (typ_fvar X T1)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_tt_fresh : forall Z U T,
  Z \notin fv_tt T -> subst_tt Z U T = T.
Proof.
  induction T; simpl; intros; f_equal*.
  case_var*. forwards~ : IHT. rewrite* H0.
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

Lemma subst_tt_open_tt_var : forall X Y U R T, Y <> X -> type U -> type R ->
  open_tt (subst_tt X U T) (typ_fvar Y (subst_tt X U R)) = subst_tt X U (open_tt T (typ_fvar Y R)).
Proof.
  introv Neq Wu Wr. rewrite* subst_tt_open_tt.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_tt_intro : forall X T2 U R,
  X \notin fv_tt T2 -> type U -> type R ->
  open_tt T2 U = subst_tt X U (open_tt T2 (typ_fvar X R)).
Proof.
  introv Fr Wu Wr. rewrite* subst_tt_open_tt.
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
   apply* (@open_te_rec_type_core e1 0 (typ_fvar X V)).
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

Lemma subst_te_open_te_var : forall X Y U R e, Y <> X -> type U -> type R ->
  open_te (subst_te X U e) (typ_fvar Y (subst_tt X U R)) = subst_te X U (open_te e (typ_fvar Y R)).
Proof.
  introv Neq Wu Wr. rewrite* subst_te_open_te.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_te_intro : forall X U R e,
  X \notin fv_te e \u fv_tt R -> type U -> type R ->
  open_te e U = subst_te X U (open_te e (typ_fvar X R)).
Proof.
  introv Fr Wu Wr. rewrite* subst_te_open_te.
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
   apply* (@open_ee_rec_type_core e1 0 (typ_fvar X V)).
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

Lemma subst_ee_open_te_var : forall z u e X R, term u -> type R ->
  open_te (subst_ee z u e) (typ_fvar X R) = subst_ee z u (open_te e (typ_fvar X R)).
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
  apply (@wft_var U). apply* IHwft. apply* binds_weaken.
  (* case: all *)
  apply_fresh* wft_all as Y. apply_ih_bind* H1.
Qed.

(** Through narrowing *)

Lemma wft_narrow : forall V F U T E X,
  wft (E & X ~<: V & F) T ->
  ok (E & X ~<: U & F) ->
  wft (E & X ~<: U & F) T.
Proof.
  intros. gen_eq K: (E & X ~<: V & F). gen E F.
  induction H; intros; subst; eauto.
  destruct (binds_middle_inv H) as [K|[K|K]]; try destructs K.
    applys wft_var. apply* binds_concat_right.
    subst. applys wft_var. apply~ binds_middle_eq.
    applys wft_var. apply~ binds_concat_left.
     apply* binds_concat_left.
  apply_fresh* wft_all as Y. apply_ih_bind* H1.
Qed.

(** Through strengthening *)

Lemma wft_strengthen : forall E F x U T,
 wft (E & x ~: U & F) T -> wft (E & F) T.
Proof.
  intros. gen_eq G: (E & x ~: U & F). gen F.
  induction H; intros F EQ; subst; auto.
  apply* (@wft_var U0).
  destruct (binds_concat_inv H) as [?|[? ?]].
    apply~ binds_concat_right.
    destruct (binds_push_inv H1) as [[? ?]|[? ?]].
      subst. false.
      apply~ binds_concat_left.
  (* todo: binds_cases tactic *)
  apply_fresh* wft_all as Y. apply_ih_bind* H1.
Qed.

(** Through type substitution *)

Lemma wft_subst_tb : forall F Q E Z P T,
  wft (E & Z ~<: Q & F) T ->
  wft E P ->
  ok (E & map (subst_tb Z P) F) ->
  wft (E & map (subst_tb Z P) F) (subst_tt Z P T).
Proof.
  introv WT WP. gen_eq G: (E & Z ~<: Q & F). gen F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt; auto.
  case_var*.
    apply_empty* wft_weaken.
    destruct (binds_concat_inv H) as [?|[? ?]].
      apply (@wft_var (subst_tt Z P U)).
       apply~ binds_concat_right.
       unsimpl_map_bind. apply~ binds_map.
      destruct (binds_push_inv H1) as [[? ?]|[? ?]].
        subst. false~.
        applys wft_var. apply* binds_concat_left.
  apply_fresh* wft_all as Y.
   unsimpl ((subst_tb Z P) (bind_sub T1)).
   lets: wft_type.
   rewrite* subst_tt_open_tt_var.
   apply_ih_map_bind* H0.
Qed.

(** Through type reduction *)

Lemma wft_open : forall E U T1 T2,
  ok E ->
  wft E (typ_all T1 T2) ->
  wft E U ->
  wft E (open_tt T2 U).
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

(** Extraction from a subtyping assumption in a well-formed environments *)

Lemma wft_from_env_has_sub : forall x U E,
  okt E -> binds x (bind_sub U) E -> wft E U.
Proof.
  induction E using env_ind; intros Ok B.
  false* binds_empty_inv.
  inversions Ok.
    false (empty_push_inv H0).
    destruct (eq_push_inv H) as [? [? ?]]. subst. clear H.
     destruct (binds_push_inv B) as [[? ?]|[? ?]]. subst.
       inversions H3. apply_empty* wft_weaken.
       apply_empty* wft_weaken.
    destruct (eq_push_inv H) as [? [? ?]]. subst. clear H.
     destruct (binds_push_inv B) as [[? ?]|[? ?]]. subst.
       inversions H3.
       apply_empty* wft_weaken.
Qed.

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
       inversions H3.
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

Lemma wft_from_okt_sub : forall x T E,
  okt (E & x ~<: T) -> wft E T.
Proof.
  intros. inversions* H.
  false (empty_push_inv H1).
  destruct (eq_push_inv H0) as [? [? ?]]. inversions~ H4.
  destruct (eq_push_inv H0) as [? [? ?]]. false.
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
Hint Resolve wft_from_okt_typ wft_from_okt_sub.
Hint Immediate wft_from_env_has_sub wft_from_env_has_typ.
Hint Resolve wft_subst_tb.


(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

(** Inversion lemma *)

Lemma okt_push_inv : forall E X B,
  okt (E & X ~ B) -> exists T, B = bind_sub T \/ B = bind_typ T.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&?&?): (eq_push_inv H). subst*.
    lets (?&?&?): (eq_push_inv H). subst*.
Qed.

Lemma okt_push_sub_inv : forall E X T,
  okt (E & X ~<: T) -> okt E /\ wft E T /\ X # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. inverts~ M.
    lets (?&?&?): (eq_push_inv H). false.
Qed.

Lemma okt_push_sub_type : forall E X T,
  okt (E & X ~<: T) -> type T.
Proof. intros. applys wft_type. forwards*: okt_push_sub_inv. Qed.

Lemma okt_push_typ_inv : forall E x T,
  okt (E & x ~: T) -> okt E /\ wft E T /\ x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&?&?): (eq_push_inv H). false.
    lets (?&M&?): (eq_push_inv H). subst. inverts~ M.
Qed.

Lemma okt_push_typ_type : forall E X T,
  okt (E & X ~: T) -> type T.
Proof. intros. applys wft_type. forwards*: okt_push_typ_inv. Qed.

Hint Immediate okt_push_sub_type okt_push_typ_type.

(** Through narrowing *)

Lemma okt_narrow : forall V (E F:env) U X,
  okt (E & X ~<: V & F) ->
  wft E U ->
  okt (E & X ~<: U & F).
Proof.
  introv O W. induction F using env_ind.
  rewrite concat_empty_r in *. lets*: (okt_push_sub_inv O).
  rewrite concat_assoc in *.
   lets (T&[?|?]): okt_push_inv O; subst.
     lets (?&?&?): (okt_push_sub_inv O).
      applys~ okt_sub. applys* wft_narrow.
     lets (?&?&?): (okt_push_typ_inv O).
      applys~ okt_typ. applys* wft_narrow.
Qed.

(** Through strengthening *)

Lemma okt_strengthen : forall x T (E F:env),
  okt (E & x ~: T & F) ->
  okt (E & F).
Proof.
 introv O. induction F using env_ind.
  rewrite concat_empty_r in *. lets*: (okt_push_typ_inv O).
  rewrite concat_assoc in *.
   lets (U&[?|?]): okt_push_inv O; subst.
     lets (?&?&?): (okt_push_sub_inv O).
      applys~ okt_sub. applys* wft_strengthen.
     lets (?&?&?): (okt_push_typ_inv O).
      applys~ okt_typ. applys* wft_strengthen.
Qed.

(** Through type substitution *)

Lemma okt_subst_tb : forall Q Z P (E F:env),
  okt (E & Z ~<: Q & F) ->
  wft E P ->
  okt (E & map (subst_tb Z P) F).
Proof.
 introv O W. induction F using env_ind.
  rewrite map_empty. rewrite concat_empty_r in *.
   lets*: (okt_push_sub_inv O).
  rewrite map_push. rewrite concat_assoc in *.
   lets (U&[?|?]): okt_push_inv O; subst.
     lets (?&?&?): (okt_push_sub_inv O).
      applys~ okt_sub. applys* wft_subst_tb.
     lets (?&?&?): (okt_push_typ_inv O).
      applys~ okt_typ. applys* wft_subst_tb.
Qed.

(** Automation *)

Hint Resolve okt_narrow okt_subst_tb wft_weaken.
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
 specializes IHT1 k. specializes IHT2 (S k). auto.
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
  rewrite* <- IHokt. rewrite* subst_tt_fresh. apply* notin_fv_wf.
  rewrite* <- IHokt. rewrite* subst_tt_fresh. apply* notin_fv_wf.
Qed.

(* ********************************************************************** *)
(** ** Properties of set *)

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
(** * Properties of environment *)
Lemma pure_dist: forall E F, pure (E & F) = pure E & pure F.
Proof. rewrite concat_def. intros. gen E. induction F; intros E; autos.
  rewrite LibList.app_cons. destruct a. destruct* b.
  simpl. rewrite LibList.app_cons. rewrite* <- IHF.
Qed.

Lemma pure_dom_subset : forall E, dom (pure E) \c dom E.
Proof. intros. induction E.
  simpls. apply subset_refl.
  destruct a. destruct b.
  simpls. repeat(rewrite cons_to_push). repeat(rewrite dom_push).
    eapply subset_union_2. eapply subset_refl. eauto.
  simpls. rewrite cons_to_push. rewrite dom_push.
    eapply subset_trans. eauto. apply subset_union_weak_r.
Qed.

Lemma pure_binds: forall E U x, ok E ->
  binds x (bind_sub U) (pure E) ->
  binds x (bind_sub U) E.
Proof. intros. induction E.
  simpls. autos.
  destruct a. destruct b.
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv H0).
      destructs H1. inversions H2. apply binds_push_eq.
      destructs H1. apply* binds_push_neq.
    simpls. rewrite cons_to_push in *. apply binds_push_neq.
      autos* ok_concat_inv_l.
      intros Ha. subst. lets: IHE (ok_concat_inv_l H) H0.
      rewrite <- concat_empty_r in H. lets: ok_middle_inv_l H.
      apply (binds_fresh_inv H1 H2).
Qed.

Lemma pure_binds_reverse: forall E U x,
  binds x (bind_sub U) E -> binds x (bind_sub U) (pure E).
Proof. intros. induction E.
  simpl in *. autos.
  destruct a. destruct b.
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv H).
      destructs H0. inversions H1. apply binds_push_eq.
      destructs H0. apply* binds_push_neq.
    simpls. rewrite cons_to_push in *. apply IHE.
      eapply binds_push_neq_inv. exact H.
      intros HI. subst. lets: binds_push_eq_inv H. inversion H0.
Qed.

Lemma pure_no_var : forall x T E, ~binds x (bind_typ T) (pure E).
Proof. intros. intros H. induction E.
  simpl in H. rewrite <- empty_def in H. destruct (binds_empty_inv H).
  destruct a. destruct b; autos.
    simpl in H. apply IHE. rewrite cons_to_push in H. destruct (binds_push_inv H).
      destruct H0. subst. inversion H1.
      destruct* H0.
Qed.

Lemma pure_wft: forall E V, ok E -> wft (pure E) V -> wft E V.
Proof. intros. remember (pure E) as G. gen E. inductions H0; intros; subst; autos.
  eapply wft_var. apply* pure_binds.
  apply_fresh* wft_all as Y. apply* H1. repeat(rewrite <- cons_to_push). autos.
Qed.

Lemma pure_wft_weaken: forall E F G V,
  ok (E & F & G) -> wft (E & (pure F) & G) V -> wft (E & F & G) V.
Proof. intros. inductions H0; intros; subst; autos.
  eapply wft_var. binds_cases H0.
    apply binds_concat_left; autos. apply* binds_concat_left_ok.
    apply binds_concat_left; autos. apply* binds_concat_right. apply* pure_binds.
      lets*: ok_concat_inv_r (ok_concat_inv_l H).
    apply binds_concat_right. auto.
  apply_fresh* wft_all as Y.
    assert (HI: ok (E & F & (G & Y ~<: T1 ))).
      rewrite concat_assoc. apply* ok_push.
    forwards~ HII: (H1 Y). apply HI.  rewrite* concat_assoc.
    rewrite* <- concat_assoc.
Qed.

Lemma pure_wft_reverse: forall E V, wft E V -> wft (pure E) V.
Proof. intros. inductions H; autos.
  eapply wft_var. apply* pure_binds_reverse.
  apply_fresh* wft_all as Y. forwards~ HI: (H1 Y).
    rewrite pure_dist in HI. rewrite single_def in *. autos.
Qed.

Lemma pure_okt : forall E,
  okt E -> okt (pure E).
Proof. intros. induction* E.
  destruct a. destruct b; simpl; rewrite cons_to_push in *.
  apply okt_sub. apply IHE. lets*: okt_push_sub_inv H.
    lets(_ & HI & HII): okt_push_sub_inv H.
    autos* pure_wft_reverse.
    lets(_ & _ & HI): okt_push_sub_inv H.
    lets: pure_dom_subset E. unfolds subset.
    intros Ha. apply HI. autos.

  apply IHE. lets*: okt_push_typ_inv H.
Qed.

Lemma pure_map : forall E Z P, pure (map (subst_tb Z P) E) = map (subst_tb Z P) (pure E).
Proof. intros. induction E.
  simpl. rewrite <- empty_def. rewrite map_empty. rewrite empty_def. reflexivity.
  destruct a. destruct b; simpl.
    repeat(rewrite cons_to_push). repeat(rewrite map_push). simpl.
      rewrite <- cons_to_push. simpl. rewrite cons_to_push. rewrite* IHE.
    repeat(rewrite cons_to_push). repeat(rewrite map_push). simpl.
      rewrite <- cons_to_push. simpl. rewrite* IHE.
Qed.

Lemma pure_eq : forall E, pure (pure E) = pure E.
Proof. intros. induction E; autos.
  destruct a. destruct b; autos.
  simpl. rewrite* IHE.
Qed.

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

Lemma sub_regular : forall E S T,
  sub E S T -> okt E /\ wft E S /\ wft E T.
Proof.
  induction 1. autos*. autos*. autos*. jauto_set; auto. (* autos* too slow *)
  split. autos*. split;
   apply_fresh* wft_all as Y;
    forwards~: (H1 Y); apply_empty* (@wft_narrow T1).
Qed.

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ term e /\ wft E T.
Proof.
  induction 1.
  splits*.
  splits.
   pick_fresh y. specializes H0 y. destructs~ H0.
    forwards*: okt_push_typ_inv.
   apply_fresh* term_abs as y.
     pick_fresh y. specializes H0 y. destructs~ H0.
      forwards*: okt_push_typ_inv.
     specializes H0 y. destructs~ H0.
   pick_fresh y. specializes H0 y. destructs~ H0.
    apply* wft_arrow.
      forwards*: okt_push_typ_inv.
      apply_empty* wft_strengthen.
  splits*.
   apply_fresh* term_cap as y.
     pick_fresh y. specializes H1 y. destructs~ H1.
       forwards*: (okt_push_typ_inv H1).
     specializes H1 y. destructs~ H1.
   pick_fresh y. specializes H1 y. destructs~ H1.
     apply* wft_arrow.
       apply* pure_wft.
       apply* pure_wft.
       rewrite <- (@concat_empty_r bind (pure E)).
       eapply wft_strengthen. rewrite* concat_empty_r.
  splits*. destructs IHtyping1. inversion* H3.
  splits.
   pick_fresh y. specializes H0 y. destructs~ H0.
    forwards*: okt_push_sub_inv.
   apply_fresh* term_tabs as y.
     pick_fresh y. forwards~ K: (H0 y). destructs K.
       forwards*: okt_push_sub_inv.
     forwards~ K: (H0 y). destructs K. auto.
   apply_fresh* wft_all as Y.
     pick_fresh y. forwards~ K: (H0 y). destructs K.
      forwards*: okt_push_sub_inv.
     forwards~ K: (H0 Y). destructs K.
      forwards*: okt_push_sub_inv.
  splits*; destructs (sub_regular H0).
   apply* term_tapp. applys* wft_type.
   applys* wft_open T1.
  splits*. destructs~ (sub_regular H0).
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
  | H: sub _ _ _ |- _ => apply (proj31 (sub_regular H))
  | H: typing _ _ _ |- _ => apply (proj31 (typing_regular H))
  end.

Hint Extern 1 (wft ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj33 (typing_regular H))
  | H: sub E T _ |- _ => apply (proj32 (sub_regular H))
  | H: sub E _ T |- _ => apply (proj33 (sub_regular H))
  end.

Hint Extern 1 (type ?T) =>
  let go E := apply (@wft_type E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  end.

Hint Extern 1 (term ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj32 (typing_regular H))
  | H: red ?e _ |- _ => apply (proj1 (red_regular H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular H))
  end.

(** In parentheses are given the label of the corresponding
  lemma in the description of the POPLMark Challenge. *)

(* ********************************************************************** *)
(** * Properties of Subtyping *)

(* ********************************************************************** *)
(** Reflexivity (1) *)

Lemma sub_reflexivity : forall E T,
  okt E ->
  wft E T ->
  sub E T T .
Proof.
  introv Ok WI. lets W: (wft_type WI). gen E.
  induction W; intros; inversions WI; eauto.
  apply_fresh* sub_all as Y.
Qed.

(* ********************************************************************** *)
(** Weakening (2) *)

Lemma sub_weakening : forall E F G S T,
   sub (E & G) S T ->
   okt (E & F & G) ->
   sub (E & F & G) S T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok; auto.
  (* case: fvar trans *)
  apply* sub_trans_tvar. apply* binds_weaken.
  (* case: all *)
  apply_fresh* sub_all as Y. apply_ih_bind* H0.
Qed.

Lemma sub_weakening_env : forall E F G S T,
   sub (E & pure F & G) S T ->
   okt (E & F & G) ->
   sub (E & F & G) S T.
Proof. intros. inductions H; eauto.
  apply* sub_top. apply* pure_wft_weaken.
  apply* sub_refl_tvar. apply* pure_wft_weaken.
  apply* sub_trans_tvar.  binds_cases H.
    apply binds_concat_left; autos. apply* binds_concat_left_ok. eapply ok_concat_inv_l.
      eapply ok_from_okt. eauto.
    apply binds_concat_left; autos. apply* binds_concat_right. apply* pure_binds.
      lets*: ok_concat_inv_r (ok_concat_inv_l (ok_from_okt H1)).
    apply binds_concat_right. auto.
  apply_fresh* sub_all as X. lets: (H1 X).
    rewrite <- concat_assoc in H3. rewrite <- concat_assoc.
    apply* H3. rewrite concat_assoc. apply* okt_sub.
    destructs (sub_regular H). apply* pure_wft_weaken.
Qed.

(* ********************************************************************** *)
(** Narrowing and transitivity (3) *)

Section NarrowTrans.

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Hint Unfold transitivity_on.

Hint Resolve wft_narrow.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (E & Z ~<: Q & F) S T ->
  sub E P Q ->
  sub (E & Z ~<: P & F) S T.
Proof.
  introv TransQ SsubT PsubQ.
  inductions SsubT; introv.
  apply* sub_top.
  apply* sub_refl_tvar.
  tests EQ: (X = Z).
    lets M: (@okt_narrow Q).
    apply (@sub_trans_tvar P).
      asserts~ N: (ok (E & Z ~<: P & F)).
       lets: ok_middle_inv_r N.
       apply~ binds_middle_eq.
      apply TransQ.
        do_rew* concat_assoc (apply_empty* sub_weakening).
        binds_get H. autos*.
    apply* (@sub_trans_tvar U). binds_cases H; auto.
  apply* sub_arrow.
  apply_fresh* sub_all as Y. apply_ih_bind* H0.
Qed.

Lemma sub_transitivity : forall Q,
  transitivity_on Q.
Proof.
  intro Q. introv SsubQ QsubT. asserts* W: (type Q).
  gen E S T. set_eq Q' EQ: Q. gen Q' EQ.
  induction W; intros Q' EQ E S SsubQ;
    induction SsubQ; try discriminate; inversions EQ;
      intros T QsubT; inversions keep QsubT;
        eauto 4 using sub_trans_tvar.
  (* case: all / top -> only needed to fix well-formedness,
     by building back what has been deconstructed too much *)
  assert (sub E (typ_all S1 S2) (typ_all T1 T2)).
    apply_fresh* sub_all as y.
  autos*.
  (* case: all / all *)
  apply_fresh sub_all as Y. autos*.
  applys~ (H0 Y). lets: (IHW T1).
  apply_empty* (@sub_narrowing_aux T1).
Qed.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (E & Z ~<: Q & F) S T ->
  sub (E & Z ~<: P & F) S T.
Proof.
  intros.
  apply* sub_narrowing_aux.
  apply* sub_transitivity.
Qed.

End NarrowTrans.

(* ********************************************************************** *)
(** Type substitution preserves subtyping (10) *)

Lemma sub_through_subst_tt : forall Q E F Z S T P,
  sub (E & Z ~<: Q & F) S T ->
  sub E P Q ->
  sub (E & map (subst_tb Z P) F) (subst_tt Z P S) (subst_tt Z P T).
Proof.
  introv SsubT PsubQ.
  inductions SsubT; introv; simpl subst_tt.
  apply* sub_top.
  case_var.
    apply* sub_reflexivity.
    apply* sub_reflexivity.
     inversions H0. binds_cases H3.
      apply* (@wft_var U).
      apply* (@wft_var (subst_tt Z P U)). unsimpl_map_bind*.
   case_var.
    apply (@sub_transitivity Q).
      apply_empty* sub_weakening.
      rewrite* <- (@subst_tt_fresh Z P Q).
        binds_get H. autos*.
        apply* (@notin_fv_wf E).
    apply* (@sub_trans_tvar (subst_tt Z P U)).
      rewrite* (@map_subst_tb_id E Z P).
        binds_cases H; unsimpl_map_bind*.
  apply* sub_arrow.
  apply_fresh* sub_all as X.
   unsimpl (subst_tb Z P (bind_sub T1)).
   do 2 rewrite* subst_tt_open_tt_var.
   apply_ih_map_bind* H0.
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
  apply_fresh* typing_cap as x. repeat(rewrite pure_dist in *).
   assert (HI: okt(pure E & pure F & pure G)).
      apply pure_okt in Ok. repeat(rewrite pure_dist in Ok). autos.
   lets: H1 x. rewrite <- concat_assoc in H2. rewrite <- concat_assoc.
   apply* H2. rewrite concat_assoc. apply okt_typ. auto.
     apply* wft_weaken. forwards~: (H0 x). destructs (typing_regular H3).
       rewrite <- (@concat_empty_r bind (pure E & pure G)).
       eapply wft_strengthen. rewrite concat_empty_r. eauto.
     unfolds. intros HII. repeat(rewrite dom_concat in HII).
       assert (Ha: x \notin dom E \u dom F \u dom G) by autos. apply Ha.
       repeat(rewrite in_union in *). rewrite or_assoc in HII. branches HII.
       branch 1. lets*: pure_dom_subset E.
       branch 2. lets*: pure_dom_subset F.
       branch 3. lets*: pure_dom_subset G.
  apply* typing_app.
  apply_fresh* typing_tabs as X. forwards~ K: (H X).
   apply_ih_bind (H0 X); eauto.
  apply* typing_tapp. apply* sub_weakening.
  apply* typing_sub. apply* sub_weakening.
Qed.

Lemma typing_weakening_env : forall E F G e T,
  typing (E & (pure F) & G) e T ->
  okt (E & F & G) ->
  typing (E & F & G) e T.
Proof. intros. inductions H.
  apply* typing_var. destruct (binds_concat_inv H0).
    apply* binds_concat_right.
    destruct H2. apply* binds_concat_left. destruct (binds_concat_inv H3).
      destruct (pure_no_var _ H4). destruct H4.
      apply* binds_concat_left_ok. lets*: ok_concat_inv_l (ok_from_okt H1).
  apply_fresh* typing_abs as x. forwards~ K: (H x).
    apply_ih_bind (H0 x); eauto.
    destruct (typing_regular K). apply okt_typ; autos.
    lets(_ & HI & _): okt_push_typ_inv H2.
    apply* pure_wft_weaken.
  apply_fresh* typing_cap as x. repeat(rewrite pure_dist in *).
    rewrite pure_eq in H0. apply* H0.
  apply* typing_app.
  apply_fresh* typing_tabs as X. forwards~ K: (H X).
    apply_ih_bind (H0 X); eauto. apply* okt_sub.
    eapply pure_wft_weaken; autos. destructs (typing_regular K).
    eapply wft_from_okt_sub; eauto.
  apply* typing_tapp. apply* sub_weakening_env.
  eapply typing_sub. apply* IHtyping. apply* sub_weakening_env.
Qed.

(* ********************************************************************** *)
(** Strengthening (6) *)

Lemma sub_strengthening : forall x U E F S T,
  sub (E & x ~: U & F) S T ->
  sub (E & F) S T.
Proof.
  intros x U E F S T SsubT.
  inductions SsubT; introv; autos* wft_strengthen.
  (* case: fvar trans *)
  apply* (@sub_trans_tvar U0). binds_cases H; autos*.
  (* case: all *)
  apply_fresh* sub_all as X. apply_ih_bind* H0.
Qed.

Lemma sub_strengthening_env : forall E S T,
  sub E S T -> sub (pure E) S T.
Proof.  intros. inductions H; autos.
  apply sub_top. apply* pure_okt. apply* pure_wft_reverse.
  apply sub_refl_tvar. apply* pure_okt. apply* pure_wft_reverse.
  eapply sub_trans_tvar. eapply pure_binds_reverse. eauto. auto.
  apply sub_all with L. auto. intros. forwards~ : H1 X.
  rewrite pure_dist in H3.
  replace (pure (X ~<: T1)) with (X ~<: T1) in H3 by (rewrite* single_def).
  auto.
Qed.

(************************************************************************ *)
(** Preservation by Type Narrowing (7) *)

Lemma typing_narrowing : forall Q E F X P e T,
  sub E P Q ->
  typing (E & X ~<: Q & F) e T ->
  typing (E & X ~<: P & F) e T.
Proof.
  introv PsubQ Typ. gen_eq E': (E & X ~<: Q & F). gen E F.
  inductions Typ; introv PsubQ EQ; subst; simpl.
  binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  apply_fresh* typing_cap as y. repeat(rewrite pure_dist in *).
    rewrite <- concat_assoc. lets: H1 y. rewrite <- concat_assoc in H2.
    replace (pure (X ~<: P)) with (X ~<: P) by (rewrite* single_def).
    apply* H2. apply* sub_strengthening_env.
    replace (pure (X ~<: Q)) with (X ~<: Q) by (rewrite* single_def). auto.
  apply* typing_app.
  apply_fresh* typing_tabs as Y. apply_ih_bind* H0.
  apply* typing_tapp. apply* (@sub_narrowing Q).
  apply* typing_sub. apply* (@sub_narrowing Q).
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma open_tt_fv_subset: forall k U T,
  fv_tt T \c fv_tt (open_tt_rec k U T).
Proof. intros. gen k. induction T; intros; simpls.
  apply subset_empty_l.
  apply subset_empty_l.
  apply subset_refl.
  apply* subset_union_2.
  apply* subset_union_2.
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
  apply* subset_union_2. apply subset_refl.
Qed.

Lemma open_tt_tt_fv_subset: forall k T1 T2,
  fv_tt (open_tt_rec k T1 T2) \c fv_tt T1 \u fv_tt T2.
Proof. intros. gen k. induction T2; intros; simpls; autos.
  apply subset_empty_l.
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

  lets*: (subset_union_2 (IHT2_1 k) (IHT2_2 (S k))).
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
  intros. inductions H; simpls.
  apply subset_empty_l.
  lets: get_some_inv (binds_get H). unfolds subset. intros.
    rewrite in_singleton in H1. rewrite* H1.
  rewrite <- union_same. apply* subset_union_2.
  rewrite <- union_same. apply* subset_union_2.
    pick_fresh X. forwards~ HI: (H1 X). simpls. rewrite dom_concat in HI.
    rewrite dom_single in HI. eapply subset_strengthen. eapply subset_trans.
    apply open_tt_fv_subset. exact HI. autos.
Qed.

Lemma subtyping_env_fv : forall E S T, sub E S T ->
  fv_tt S \c dom E /\ fv_tt T \c dom E.
Proof. intros. inductions H; simpls.
  splits. apply* wft_fv_tt. apply subset_empty_l.
  lets*: wft_fv_tt H0.
  destructs IHsub. splits*. lets: get_some_inv (binds_get H).
    unfolds. intros. rewrite in_singleton in H4. subst*.
  destructs IHsub1. destructs IHsub2.
    splits; rewrite <- union_same; apply* subset_union_2.
  destruct IHsub. pick_fresh X. forwards~ HI: H1 X.
    rewrite dom_concat in HI. rewrite dom_single in HI. destruct HI.
    splits.
    rewrite <- union_same. apply* subset_union_2. apply subset_strengthen with X; autos.
      eapply subset_trans. apply open_tt_fv_subset. eauto.
    rewrite <- union_same. apply* subset_union_2. apply subset_strengthen with X; autos.
      eapply subset_trans. apply open_tt_fv_subset. eauto.
Qed.

Lemma typing_env_fv : forall E e T, typing E e T ->
  fv_ee e \c dom E /\ fv_te e \c dom E /\ fv_tt T \c dom E.
Proof. intros. inductions H; substs.
  (* var *)
  forwards~ HI:  get_some_inv (binds_get H0).
  simpls. splits.
  unfolds subset. intros. rewrite in_singleton in *. subst*.
  apply subset_empty_l.
  apply* wft_fv_tt.

  (* abs *)
  pick_fresh x. forwards~ (HI & HII & HIII): H0 x. simpls.
  rewrite dom_concat in *. rewrite dom_single in *.
  unfolds open_ee. unfolds open_te.

  assert (Ha: fv_tt V \c dom E).
    forwards~ Htyp: (H x).
    destruct (typing_regular Htyp) as [He _].
    apply subset_strengthen with x; autos.
    rewrite <- dom_single with (v:= bind_typ V). rewrite <- dom_concat.
    apply* wft_fv_tt; autos.

  splits.

  apply* subset_strengthen. eapply subset_trans. apply open_ee_fv_subset. exact HI.

  rewrite <- union_same. apply* subset_union_2. apply* subset_strengthen.
  eapply subset_trans. apply open_te_ee_fv_subset. exact HII.

  rewrite <- union_same. apply* subset_union_2. apply* subset_strengthen.

  (* cap *)
  pick_fresh x. forwards~ (HI & HII & HIII): H1 x. simpls.
  rewrite dom_concat in *. rewrite dom_single in *. unfolds open_ee.

  assert (Ha: fv_tt V \c dom (pure E)).
    forwards~ Htemp: (H0 x).
    destruct (typing_regular Htemp) as [He _].
    apply* wft_fv_tt.

  splits.

  apply* subset_strengthen. eapply subset_trans. apply open_ee_fv_subset.
  eapply subset_trans. eauto. apply subset_union_2.
    apply pure_dom_subset. apply subset_refl.

  rewrite <- union_same. apply* subset_union_2.
  eapply subset_trans. exact Ha. apply pure_dom_subset.
  apply* subset_strengthen. eapply subset_trans. apply open_te_ee_fv_subset.
    eapply subset_trans. eauto. apply subset_union_2.
      apply pure_dom_subset. apply subset_refl.

  rewrite <- union_same. apply* subset_union_2.
    eapply subset_trans. eauto. apply pure_dom_subset.
    apply* subset_strengthen. eapply subset_trans. eauto.
      apply subset_union_2. apply pure_dom_subset. apply subset_refl.

  (* app *)
  forwards(Ma & Mb & Mc): IHtyping1. forwards(Na & Nb & Nc): IHtyping2.
  simpls. splits.

  rewrite <- union_same. apply* subset_union_2.
  rewrite <- union_same. apply* subset_union_2.
  eapply subset_trans. apply subset_union_weak_r. exact Mc.

  (* tabs *)
  simpls. pick_fresh X. forwards~ (HI & HII & HIII) : (H0 X).
  rewrite dom_concat in *. rewrite dom_single in *.
  unfolds open_ee. unfolds open_te. unfolds open_tt.
  rewrite <- open_ee_te_fv_eq in HI.

  assert (Ha: fv_tt V \c dom E).
    forwards~ Htyp: (H X).
    destruct (typing_regular Htyp) as [He _].
    apply subset_strengthen with X; autos.
    rewrite <- dom_single with (v:= bind_sub V). rewrite <- dom_concat.
    apply* wft_fv_tt; autos.

  splits.

  eapply subset_strengthen. exact HI. autos.
  rewrite <- union_same. apply* subset_union_2. apply subset_strengthen with X; autos.
    eapply subset_trans. apply open_te_fv_subset. exact HII.
  rewrite <- union_same. apply* subset_union_2. apply subset_strengthen with X; autos.
    eapply subset_trans. apply open_tt_fv_subset. exact HIII.

  (* tapp *)
  lets(HI & HII & HIII): IHtyping. simpls.

  assert (Ha: fv_tt T \c dom E) by (lets*: subtyping_env_fv H0).

  splits; autos.

  rewrite <- union_same. apply* subset_union_2.
  eapply subset_trans. eapply open_tt_tt_fv_subset.
    rewrite <- union_same. apply* subset_union_2.
    eapply subset_trans. apply subset_union_weak_r. apply HIII.

  (* sub *)
  destructs IHtyping. splits; autos. lets*: subtyping_env_fv H0.
Qed.

Lemma typing_cap_closed_trm : forall e T E F x U V,
  typing (E & x ~: U & F) (trm_cap V e) T -> x \notin fv_ee e.
Proof. intros. inductions H;  eauto.
  repeat(rewrite pure_dist in *). lets: (ok_middle_inv (ok_from_okt H)).
  replace (pure (x ~: U)) with (@empty bind) in *
    by (rewrite single_def; simpl; rewrite* empty_def).
  rewrite concat_empty_r in *.
  assert (HI: typing (E & F) (trm_cap V e) (typ_arrow V T1)).
    apply* typing_cap. rewrite* pure_dist.
  destructs (typing_env_fv HI). simpls. rewrite <- notin_union in H2.
  unfolds subset. intros Hc. apply H2. rewrite <- dom_concat. autos.
Qed.

Lemma typing_cap_closed_typ : forall e V T,
  typing empty (trm_cap V e) (typ_arrow V T) ->
  forall X, X \notin fv_te e /\ X \notin fv_tt V /\ X \notin fv_tt T.
Proof. intros. lets(_ & HI & HII): typing_env_fv H.
  simpls. rewrite dom_empty in *. unfolds subset.
  specialize HI with X. specialize HII with X. rewrite in_union in *.
  splits; intros Hin; rewrite* <- (@in_empty var X).
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
    apply_ih_bind* H0.
  apply typing_cap with L; eauto.
    rewrite* subst_ee_fresh. repeat(rewrite pure_dist in *).
    replace (pure (x ~: U)) with (@empty bind) in *
      by (rewrite single_def; simpl; rewrite* empty_def).
    rewrite concat_empty_r in *. autos.
    eapply typing_cap_closed_trm. eapply typing_cap; eauto.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    rewrite* subst_ee_open_te_var.
    apply_ih_bind* H0.
  apply* typing_tapp. apply* sub_strengthening.
  apply* typing_sub. apply* sub_strengthening.
Qed.

(************************************************************************ *)
(** Preservation by Type Substitution (11) *)

Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (E & Z ~<: Q & F) e T ->
  sub E P Q ->
  typing (E & map (subst_tb Z P) F) (subst_te Z P e) (subst_tt Z P T).
Proof.
  introv Typ PsubQ.
  inductions Typ; introv; simpls subst_tt; simpls subst_te.
  apply* typing_var. rewrite* (@map_subst_tb_id E Z P).
   binds_cases H0; unsimpl_map_bind*.
  apply_fresh* typing_abs as y.
    unsimpl (subst_tb Z P (bind_typ V)).
    rewrite* subst_te_open_ee_var.
    apply_ih_map_bind* H0.
  apply_fresh* typing_cap as y.
    unsimpl (subst_tb Z P (bind_typ V)).
    rewrite* subst_te_open_ee_var. rewrite pure_dist.
    rewrite pure_map. apply_ih_map_bind* H1.
    repeat(rewrite pure_dist).
    replace (pure (Z ~<: Q)) with (Z ~<:Q) by (rewrite* single_def).
    rewrite concat_assoc. reflexivity.
    apply* sub_strengthening_env.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    unsimpl (subst_tb Z P (bind_sub V)).
    rewrite* subst_te_open_te_var.
    rewrite* subst_tt_open_tt_var.
    apply_ih_map_bind* H0.
  rewrite* subst_tt_open_tt. apply* typing_tapp.
    apply* sub_through_subst_tt.
  apply* typing_sub. apply* sub_through_subst_tt.
Qed.

(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)
(** Inversions for Typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (trm_abs S1 e1) T ->
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x \notin L ->
     typing (E & x ~: S1) (e1 open_ee_var x) S2 /\ sub E S2 U2.
Proof.
  introv Typ. gen_eq e: (trm_abs S1 e1). gen S1 e1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversions EQ.
  inversions* Sub. autos* (@sub_transitivity T).
Qed.

Lemma typing_inv_cap : forall E S1 e1 T,
  typing E (trm_cap S1 e1) T ->
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x \notin L ->
     typing (E & x ~: S1) (e1 open_ee_var x) S2 /\ sub E S2 U2.
Proof.
  introv Typ. gen_eq e: (trm_cap S1 e1). gen S1 e1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversions EQ.
  inversions* Sub. splits*. exists T1.
    let L1 := gather_vars in exists L1. split; auto.
    rewrite <- (@concat_empty_l bind E).
    apply typing_weakening_env. rewrite* concat_empty_l.
    rewrite concat_empty_l. apply* okt_typ.
  autos* (@sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (trm_tabs S1 e1) T ->
  forall U1 U2, sub E T (typ_all U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X \notin L ->
     typing (E & X ~<: U1) (e1 open_te_var X) (S2 open_tt_var X)
     /\ sub (E & X ~<: U1) (S2 open_tt_var X) (U2 open_tt_var X).
Proof.
  intros E S1 e1 T H. gen_eq e: (trm_tabs S1 e1). gen S1 e1.
  induction H; intros S1 b EQ U1 U2 Sub; inversion EQ.
  inversions Sub. splits. auto.
   exists T1. let L1 := gather_vars in exists L1.
   intros Y Fr. splits.
    apply_empty* (@typing_narrowing S1). auto.
  autos* (@sub_transitivity T).
Qed.

(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen e'. induction Typ; introv Red;
   try solve [ inversion Red ].
  (* case: app *)
  inversions Red; try solve [ apply* typing_app ].

  destruct~ (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* sub_reflexivity.
    pick_fresh X. forwards~ K: (P2 X). destruct K.
     rewrite* (@subst_ee_intro X).
     apply_empty (@typing_through_subst_ee V).
       apply* (@typing_sub S2). apply_empty* sub_weakening.
       autos*.

  destruct~ (typing_inv_cap Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* sub_reflexivity.
    pick_fresh X. forwards~ K: (P2 X). destruct K.
     rewrite* (@subst_ee_intro X).
     apply_empty (@typing_through_subst_ee V).
       apply* (@typing_sub S2). apply_empty* sub_weakening.
       autos*.

  (* case: tapp *)
  inversions Red; try solve [ apply* typing_tapp ].
  destruct~ (typing_inv_tabs Typ (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* sub_reflexivity.
    pick_fresh X. forwards~ K: (P2 X). destruct K.
     rewrite* (@subst_te_intro X).
     rewrite* (@subst_tt_intro X).
     (* todo: apply empty here *)
     asserts_rewrite (E = E & map (subst_tb X T) empty).
       rewrite map_empty. rewrite~ concat_empty_r.
     apply* (@typing_through_subst_te T1).
       rewrite* concat_empty_r.
  (* case sub *)
  apply* typing_sub.
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
    subst. inversion H.
      false (binds_empty_inv H0).
      inversions H0. forwards*: IHTyp.
Qed.

Lemma canonical_form_tabs : forall t U1 U2,
  value t -> typing empty t (typ_all U1 U2) ->
  exists V, exists e1, t = trm_tabs V e1.
Proof.
  introv Val Typ. gen_eq E: (@empty bind).
  gen_eq T: (typ_all U1 U2). gen U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inversion Val | inversion EQT | eauto ].
    subst. inversion H.
      false* binds_empty_inv.
      inversions H0. forwards*: IHTyp.
Qed.

(* ********************************************************************** *)
(** Progress Result (16) *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (@empty bind). lets Typ': Typ.
  induction Typ; intros EQ; subst.
  (* case: var *)
  false* binds_empty_inv.
  (* case: abs *)
  left*.
  (* case: cap *)
  left*.
  (* case: app *)
  right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    destruct* IHTyp2 as [Val2 | [e2' Rede2']].
      destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]].
        destruct EQ; subst; exists* (open_ee e3 e2).
  (* case: tabs *)
  left*.
  (* case: tapp *)
  right. destruct~ IHTyp as [Val1 | [e1' Rede1']].
    destruct (canonical_form_tabs Val1 Typ) as [S [e3 EQ]].
      subst. exists* (open_te e3 T).
      exists* (trm_tapp e1' T).
  (* case: sub *)
  autos*.
Qed.
