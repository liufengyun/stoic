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
  | typ_fvar  : var -> typ
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
  | typ_fvar X      => typ_fvar X
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

Notation "T 'open_tt_var' X" := (open_tt T (typ_fvar X)) (at level 67).
Notation "t 'open_te_var' X" := (open_te t (typ_fvar X)) (at level 67).
Notation "t 'open_ee_var' x" := (open_ee t (trm_fvar x)) (at level 67).

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_var : forall X,
      type (typ_fvar X)
  | type_base: type typ_base
  | type_eff: type typ_eff
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
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
      (forall X, X \notin L -> term (e1 open_te_var X)) ->
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
  | wft_base : forall E,
      wft E typ_base
  | wft_eff : forall E,
      wft E typ_eff
  | wft_var : forall U E X,
      binds X (bind_sub U) E ->
      wft E (typ_fvar X)
  | wft_arrow : forall E T1 T2,
      wft E T1 ->
      wft E T2 ->
      wft E (typ_arrow T1 T2)
  | wft_all : forall L E T1 T2,
      wft E T1 ->
      (forall X, X \notin L ->
        wft (E & X ~<: T1) (T2 open_tt_var X)) ->
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
  | sub_refl_base : forall E,
      okt E ->
      sub E typ_base typ_base
  | sub_refl_eff : forall E,
      okt E ->
      sub E typ_eff typ_eff
  | sub_refl_tvar : forall E X,
      okt E ->
      wft E (typ_fvar X) ->
      sub E (typ_fvar X) (typ_fvar X)
  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (typ_fvar X) T
  | sub_arrow : forall E S1 S2 T1 T2,
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall X, X \notin L ->
          sub (E & X ~<: T1) (S2 open_tt_var X) (T2 open_tt_var X)) ->
      sub E (typ_all S1 S2) (typ_all T1 T2).

(* length E + depth T is decreasing -- but actually we don't care -> and all,
   as their shape also determines whether they can be in pure environment *)
Fixpoint exposure (E: env)(T: typ) :=
  match T with
    | typ_fvar X => match E with
                      | nil => T  (* impossible if E is well-formed *)
                      | (Y, bind_sub U)::E' => If X = Y then exposure E' U else exposure E' T
                      | (_, bind_typ _)::E' => exposure E' T
                    end%list
    | _ => T         (* other type are safe to be in pure environment *)
  end.

(*T is exposure type -- without type var *)
Fixpoint safe_bound(T: typ) := match T with
                                 | typ_top      => false
                                 | typ_eff      => false
                                 | typ_fvar _   => false (* impossible, after exposure in well-formed env *)
                                 | _ => true
                               end.

Definition  closed_typ(E: env)(T: typ)  := match T with
  | typ_bvar _          => false  (* impossible, ill-formed *)
  | typ_fvar _          => safe_bound (exposure E T)
  | typ_base            => true
  | typ_top             => true
  | typ_eff             => false
  | typ_arrow _ _       => true
  | typ_all _ _         => true
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
      okt E ->
      (forall X, X \notin L ->
        typing (pure E & X ~<: V) (e1 open_te_var X) (T1 open_tt_var X)) ->
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

(* get environment for type vars *)
Fixpoint tvar_env (E: env) := match E with
  | nil => nil
  | cons (X, bind_sub U) E' => cons (X, bind_sub U) (tvar_env E')
  | cons (_, bind_typ _) E' => tvar_env E'
  end.

(** subseq is useful in formulation of weakening lemmas *)
Inductive subseq : env -> env -> Prop :=
  | subseq_base: subseq empty empty
  | subseq_ext: forall E F x T,  subseq E F -> subseq E (F & x ~: T)
  | subseq_cons: forall E F x b, tvar_env E = tvar_env F ->
                                 subseq E F -> subseq (E & x ~ b) (F & x ~ b).

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

(** problem: All X. All Y. X -> Y  should be caprod *)

Inductive capsafe: env -> typ -> Prop :=
 | capsafe_B: forall E, okt E -> capsafe E typ_base
 | capsafe_T: forall E, okt E -> capsafe E typ_top
 | capsafe_X: forall E X T, okt E -> binds X (bind_sub T) E ->
                            ~sub E typ_eff (exposure E T) ->
                            capsafe E (typ_fvar X)
 | capsafe_C_X: forall E S T, wft E T -> caprod E S -> capsafe E (typ_arrow S T)
 | capsafe_X_S: forall E S T, wft E S -> capsafe E T -> capsafe E (typ_arrow S T)
 | capsafe_A: forall E U T L, wft E (typ_all U T) ->
                              (forall X, X \notin L ->
                                         capsafe (E & X ~<: U) (T open_tt_var X)) ->
                              capsafe E (typ_all U T)

with caprod: env -> typ -> Prop :=
 | caprod_E: forall E, okt E -> caprod E typ_eff
 | caprod_X: forall E X T, okt E -> binds X (bind_sub T) E ->
                           sub E typ_eff (exposure E T) ->
                           caprod E (typ_fvar X)
 | caprod_S_C: forall E S T, capsafe E S -> caprod E T -> caprod E (typ_arrow S T)
 | caprod_A: forall E U T L, wft E (typ_all U T) ->
                           (forall X, X \notin L ->
                                      capsafe (E & X ~<: U) (T open_tt_var X)) ->
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
  | typ_fvar X      => \{X}
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
  | typ_fvar X      => If X = Z then U else (typ_fvar X)
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

(* ********************************************************************** *)
(** * Tactics *)

(** Constructors as hints. *)

Hint Constructors type term wft ok okt value red subseq.

Hint Resolve
  sub_top sub_refl_base sub_refl_eff sub_refl_tvar sub_arrow
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
  apply (@wft_var U). apply* binds_weaken.
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

Lemma wft_subst_tb_keep : forall F Q E Z P T,
  wft (E & Z ~<: Q & F) T ->
  wft E P ->
  ok (E & Z ~<: Q & map (subst_tb Z P) F) ->
  wft (E & Z ~<: Q & map (subst_tb Z P) F) (subst_tt Z P T).
Proof. introv Wf1 Wf2 Ok1.
  forwards~ Ok2 : ok_remove Ok1.
  forwards~ Wf3 : wft_subst_tb Wf1 Wf2 Ok2.
  apply wft_weaken; auto.
Qed.

Lemma wft_subst: forall E F Z Y P b T,
  wft E P ->
  ok (E & Y ~ b & F) ->
  wft (E & Y ~ b & F) T <-> wft (E & Y ~ subst_tb Z P b & F) T.
Proof.
  introv Wf Ok. split; introv WfU.

  inductions WfU; auto. binds_cases H.
    eapply wft_var. apply* binds_concat_left.
    inversions EQ. apply wft_var with (subst_tt Z P U). apply* binds_concat_left.
    eapply wft_var. apply* binds_concat_right.
  apply_fresh* wft_all as X. rewrite <- concat_assoc. apply* H0.
    rewrite concat_assoc. apply* ok_push.
    rewrite* concat_assoc.

  inductions WfU; auto. binds_cases H.
    eapply wft_var. apply* binds_concat_left. destruct b.
    rewrite EQ in B1. apply wft_var with t. apply* binds_concat_left.
    simpl in EQ. inversion EQ.
    eapply wft_var. apply* binds_concat_right.
  apply* wft_arrow.
  apply_fresh* wft_all as X. rewrite <- concat_assoc. applys~ H0 b P Y Z.
    rewrite concat_assoc. apply* ok_push.
    rewrite* concat_assoc.
Qed.

Lemma wft_subst_tb_same : forall F Q E Z P T,
  wft (E & Z ~<: Q & F) T ->
  wft E P ->
  ok (E & Z ~<: Q & map (subst_tb Z P) F) ->
  wft (E & Z ~<: Q & map (subst_tb Z P) F) T.
Proof.
  introv WT WP. gen_eq G: (E & Z ~<: Q & F). gen F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt; auto.
  binds_cases H; try solve [apply* wft_var].
    apply wft_var with (subst_tt Z P U).
    unsimpl (subst_tb Z P (bind_sub U)).
    apply binds_concat_right. apply binds_map; auto.
  apply_fresh* wft_all as Y.
    forwards~ IH: H0 Y (F & Y ~<: T1). rewrite* concat_assoc.
    rewrite map_push, concat_assoc. simpl. apply* ok_push.
    rewrite map_push, concat_assoc in IH. simpl in IH.
    rewrite <- (@concat_empty_r bind) at 1. rewrite wft_subst.
    rewrite concat_empty_r. exact IH.
    rewrite <- concat_assoc. apply_empty* wft_weaken.
    rewrite* concat_assoc.
    rewrite concat_empty_r. apply* ok_push.
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

Lemma okt_weaken : forall E x b, okt (E & x ~ b) -> okt E /\ x # E.
Proof. introv Ok. destruct b.
  forwards~ : okt_push_sub_inv Ok. iauto.
  forwards~ : okt_push_typ_inv Ok. iauto.
Qed.

Lemma okt_weaken_right : forall E F, okt (E & F) -> okt E.
Proof. introv Ok. inductions F.
  rewrite <- empty_def in Ok. rewrite concat_empty_r in Ok. auto.
  destruct a. rewrite cons_to_push in Ok. rewrite concat_assoc in Ok.
  lets*: okt_weaken Ok.
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

Lemma okt_subst_tb_keep : forall Q Z P (E F:env),
  okt (E & Z ~<: Q & F) ->
  wft E P ->
  okt (E & Z ~<: Q & map (subst_tb Z P) F).
Proof.
 introv O W. induction F using env_ind.
  rewrite map_empty. rewrite concat_empty_r in *.
   lets*: (okt_push_sub_inv O).
  rewrite map_push. rewrite concat_assoc in *.
   lets (U&[?|?]): okt_push_inv O; subst.
     lets (?&?&?): (okt_push_sub_inv O).
      applys~ okt_sub. applys* wft_subst_tb_keep.
     lets (?&?&?): (okt_push_typ_inv O).
      applys~ okt_typ. applys* wft_subst_tb_keep.
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
  induction 1; intros Fr; simpl; eauto.
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H Fr.
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

Lemma subset_union : forall (T: Type) (a b c: fset T),
  a \u b \c c -> a \c c /\ b \c c.
Proof. intros. unfolds subset.
  split; intros x; specializes H x; rewrite in_union in H; auto.
Qed.


(* ********************************************************************** *)
(** * Properties of pure environment *)

(** exposure properties *)

Lemma exposure_push_typ: forall E x U T, exposure (E & x ~: U) T = exposure E T.
Proof. intros. inductions E; rewrite <- cons_to_push; destruct* T. Qed.

Lemma exposure_push_sub_eq: forall E X U,
 exposure (E & X ~<: U) (typ_fvar X)  = exposure E U.
Proof. intros. inductions E; rewrite* <- cons_to_push; simpl; cases_if*. Qed.

Lemma exposure_push_sub_neq: forall E X Y U, X <> Y ->
 exposure (E & X ~<: U) (typ_fvar Y)  = exposure E (typ_fvar Y).
Proof. intros. inductions E; rewrite <- cons_to_push; simpl; cases_if*. Qed.

Definition is_tvar t := match t with typ_fvar _ => true | _ => false end.
Lemma exposure_nontvar: forall E T, is_tvar T = false ->  exposure E T = T.
Proof. intros. inductions E; destruct* T. simpl in H. inversion H. Qed.

Lemma exposure_weaken_right: forall E F T, okt (E & F) ->
  wft E T -> exposure E T = exposure (E & F) T.
Proof. introv Ok Wf. inductions F.
  rewrite <- empty_def. rewrite* concat_empty_r.

  destruct a. destruct T; try solve [repeat(rewrite exposure_nontvar); auto].
  rewrite cons_to_push in *. rewrite concat_assoc in *. destruct (okt_weaken Ok).
  rewrite <- cons_to_push. destruct* b. simpl. cases_if*.
    inversions Wf. false* (binds_fresh_inv H3).
Qed.

Lemma exposure_weaken: forall E F G T, okt (E & G) -> okt (E & F & G) ->
  wft (E & G) T -> exposure (E & G) T = exposure (E & F & G) T.
Proof. introv Ok1 Ok2 Wf. inductions G.

  rewrite <- empty_def in *. repeat(rewrite concat_empty_r in *).
  apply* exposure_weaken_right.

  destruct a. rewrite cons_to_push in *; repeat(rewrite concat_assoc in *).
  destructs (okt_weaken Ok1). destructs (okt_weaken Ok2).
  destruct T; try solve [repeat(rewrite exposure_nontvar); auto].
  repeat(rewrite <- cons_to_push). destruct* b; simpl. cases_if*.
    apply* IHG. inversions Wf. forwards~ : binds_push_neq_inv H6. apply* wft_var.
    apply* IHG. inversions Wf. destruct (binds_push_inv H5); destruct H3.
      inversion H4. apply* wft_var.
Qed.

Lemma exposure_wft : forall E T, okt E -> wft E T -> wft E (exposure E T).
Proof. introv Ok Wf. inductions E; try destruct* T.
  destruct a. destruct b; simpl; repeat(rewrite cons_to_push in *).
  cases_if; destructs (okt_push_sub_inv Ok); apply_empty* wft_weaken.
    apply* IHE. inversions Wf. forwards~ : binds_push_neq_inv H5. apply* wft_var.
  apply_empty* wft_weaken. destructs (okt_push_typ_inv Ok). apply* IHE.
    apply_empty* wft_strengthen.
Qed.

Lemma exposure_not_wft : forall E X, ok E -> ~ wft E (typ_fvar X) ->
  exposure E (typ_fvar X) = typ_fvar X.
Proof. introv OK NonWf. inductions E; auto.
  destruct a. destruct b; rewrite cons_to_push in OK; destruct (ok_push_inv OK).
    simpl. cases_if*.
      false. apply NonWf. rewrite* cons_to_push.
      apply* IHE. intros Wf. apply NonWf. inversions Wf.
        rewrite cons_to_push. apply* wft_var.
    simpl. apply* IHE. intros Wf. apply NonWf. inversions Wf.
      rewrite cons_to_push. apply* wft_var. destruct (classic (X = v)).
      subst*. false (binds_fresh_inv H3 H0).
      apply* binds_concat_left.
Qed.

Lemma exposure_binds: forall E X U, okt E -> binds X (bind_sub U) E ->
  exposure E (typ_fvar X) = exposure E U.
Proof. introv Ok Bind. inductions E.
  rewrite <- empty_def in Bind. false* binds_empty_inv.
  destruct a. rewrite cons_to_push in *.
  destruct (binds_push_inv Bind) as [Eq | EqN]; [destruct Eq | destruct EqN].
  destruct b; inversions H0. rewrite exposure_push_sub_eq.
    destruct t; try solve [repeat(rewrite exposure_nontvar); auto].
    rewrite <- cons_to_push. simpls. cases_if*.

  destruct b. rewrite* exposure_push_sub_neq.
    destructs (okt_push_sub_inv Ok). forwards~ Eq: IHE X U. rewrite Eq.
    forwards~ Wf: wft_from_env_has_sub H0.
    destruct U; try solve [repeat(rewrite* exposure_nontvar)].
    rewrite <- cons_to_push. simpls. cases_if*.
      inversions Wf. false. autos* binds_fresh_inv.

    destructs (okt_push_typ_inv Ok).
    repeat(rewrite exposure_push_typ). auto.
Qed.

Lemma exposure_tvar : forall E F T, tvar_env E = tvar_env F ->
  exposure E T = exposure F T.
Proof. introv Eq. gen F. inductions E; intros.
  simpls. destruct T; try solve [rewrite* exposure_nontvar].
    inductions F; auto. destruct a. destruct b.
    simpls. inversion Eq. simpls. auto.
  destruct a. destruct b. destruct T; try solve [repeat(rewrite* exposure_nontvar)].
    inductions F. simpl in Eq. inversion Eq. destruct a. destruct b.
      simpl in Eq. inversions Eq. simpl. cases_if*.
      simpl in Eq. auto.
    simpl in Eq. rewrite cons_to_push. rewrite* exposure_push_typ.
Qed.

(** tvar_env properties *)

Lemma tvar_push_typ: forall E x T, tvar_env (E & x ~: T) = tvar_env E.
Proof. intros. rewrite <- cons_to_push. simpl. auto. Qed.

Lemma tvar_push_sub: forall E X T, tvar_env (E & X ~<: T) = tvar_env E & X ~<: T.
Proof. intros. rewrite <- cons_to_push. simpl. rewrite* cons_to_push. Qed.

Lemma tvar_pure : forall E, tvar_env E = tvar_env (pure E).
Proof. intros. inductions E; auto. destruct a. destruct b.
  simpl. rewrite* IHE.
  simpl. cases_if*.
Qed.

Lemma tvar_single_sub: forall X T, tvar_env (X ~<: T) = X ~<: T.
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

(** closed_typ properties *)

Lemma closed_typ_push_typ: forall E x U T, closed_typ (E & x ~: U) T = closed_typ E T.
Proof. intros. inductions E; rewrite <- cons_to_push; destruct* T. Qed.

Lemma closed_typ_nontvar: forall E G T,
  is_tvar T = false ->
  closed_typ E T = closed_typ G T.
Proof. intros. destruct* T. false. Qed.

Lemma closed_typ_tvar : forall E F T, tvar_env E = tvar_env F ->
  closed_typ E T = closed_typ F T.
Proof. introv Eq. destruct T; try solve [apply* closed_typ_nontvar].
  simpl. forwards~ : exposure_tvar (typ_fvar v) Eq. rewrite* H.
Qed.

Lemma closed_typ_weaken_right: forall E F T, okt (E & F) -> wft E T ->
  closed_typ E T = closed_typ (E & F) T.
Proof. introv Ok Wf. inductions F.
  rewrite <- empty_def. rewrite* concat_empty_r.

  destruct a. rewrite cons_to_push, concat_assoc in *.
  destruct (okt_weaken Ok). destruct T; try solve [unfold closed_typ; autos].
  rewrite <- cons_to_push. destruct b; simpl. cases_if.
    inversions Wf. false* (binds_fresh_inv H3).
    rewrite* (exposure_weaken_right H Wf).
    rewrite* (exposure_weaken_right H Wf).
Qed.

Lemma closed_typ_weaken_left: forall E F T,
  closed_typ F T = true -> closed_typ (E & F) T = true.
Proof. introv Closed.
  destruct T; try solve [unfold closed_typ; auto].

  simpls. inductions F. simpls. false.

  destruct a. rewrite cons_to_push,concat_assoc in *.
  rewrite <- cons_to_push in *. destruct b; simpls. cases_if.
    destruct t; try solve [rewrite exposure_nontvar in *; autos].
    apply* IHF.
  apply* IHF.
  apply* IHF.
Qed.

Lemma closed_typ_weaken: forall E F G T, okt (E & G) -> okt (E & F & G) ->
   wft (E & G) T -> closed_typ (E & G) T = closed_typ (E & F & G) T.
Proof. introv Ok1 Ok2 Wf. inductions G.
  rewrite <- empty_def in *. repeat(rewrite concat_empty_r in *).
  apply* closed_typ_weaken_right.

  destruct a. repeat(rewrite cons_to_push in *); repeat(rewrite concat_assoc in *).
  destructs (okt_weaken Ok1). destructs (okt_weaken Ok2). destruct b.
  destructs (okt_push_sub_inv Ok1). destruct T; auto.
  repeat(rewrite <- cons_to_push). simpls. cases_if*.
    rewrite <- (exposure_weaken H H1); auto.
    rewrite <- (exposure_weaken H H1); auto. inversions Wf.
      forwards~ : binds_push_neq_inv H9. apply* wft_var.

  repeat(rewrite closed_typ_push_typ). apply* IHG. apply_empty* wft_strengthen.
Qed.

Lemma closed_typ_strengthen : forall E F x U T,
  closed_typ (E & x ~: U & F) T = closed_typ (E & F) T.
Proof. intros.
  apply closed_typ_tvar. rewrite ?tvar_dist, single_def.
  simpl. rewrite <- empty_def, concat_empty_r. auto.
Qed.

Lemma closed_typ_binds: forall X U E,
  okt E ->
  binds X (bind_sub U) E ->
  closed_typ E (typ_fvar X) = safe_bound (exposure E U).
Proof. introv Ok Bnd. simpl. gen X U. inductions E; intros.
  rewrite <- empty_def in *. false* binds_empty_inv.

  destruct a. rewrite cons_to_push in *. destruct (binds_push_inv Bnd).
  destruct H. substs. destructs (okt_push_sub_inv Ok).
  simpl. rewrite <- cons_to_push at 1.
  destruct U; try solve [simpl; case_if*; rewrite ?exposure_nontvar; simple; auto].
  simpl. cases_if. rewrite <- cons_to_push. simpl. cases_if*.

  destruct H. rewrite <- cons_to_push. destruct b.
  simpl. cases_if. destructs (okt_push_sub_inv Ok).
  destruct U; try solve [forwards~ IH: IHE H0; rewrite IH, ?exposure_nontvar; simple; auto].
  cases_if. forwards~ Wf: wft_from_env_has_sub H0. inversions Wf. false. autos* binds_fresh_inv.
  apply* IHE.

  simpl. destructs (okt_push_typ_inv Ok).
  destruct U; try solve [forwards~ IH: IHE H0; rewrite IH, ?exposure_nontvar; simple; auto].
Qed.


Lemma closed_typ_subst_tt: forall T E,
  closed_typ E T = true ->
  forall Z P, closed_typ E P = true ->
              closed_typ E (subst_tt Z P T) = true.
Proof. intros. inductions T; inversions H; simpls; auto. case_if*.
  rewrite H0. rewrite H2. reflexivity.
Qed.

(** pure properties *)

Lemma pure_empty : pure empty = empty.
Proof. rewrite empty_def. reflexivity. Qed.

Lemma pure_push_sub: forall E X U, pure (E & X ~<: U) = pure E & X ~<: U.
Proof. intros. rewrite <- cons_to_push. simpls. rewrite* cons_to_push. Qed.

Lemma pure_push_typ: forall E x U, pure (E & x ~: U) = pure E & x ~: U \/
 pure (E & x ~: U) = pure E.
Proof. intros. rewrite <- cons_to_push. simpls. cases_if*. rewrite* cons_to_push. Qed.

Lemma pure_push_typ_closed: forall E x U, closed_typ E U = true ->
  pure (E & x ~: U) = pure E & x ~: U.
Proof. intros. rewrite <- cons_to_push. simpls. cases_if*. rewrite* cons_to_push.
  rewrite cons_to_push, closed_typ_push_typ in H0. false.
Qed.

Lemma pure_push_typ_false: forall E x U, closed_typ E U = false ->
  pure (E & x ~: U) = pure E.
Proof. intros. rewrite <- cons_to_push. simpls. cases_if*. rewrite* cons_to_push.
  rewrite cons_to_push, closed_typ_push_typ in H0. false.
Qed.

Lemma pure_push_inv: forall E x b, pure (E & x ~ b) = pure E & x ~ b \/
 pure (E & x ~ b) = pure E.
Proof. intros. destruct b. lets*: pure_push_sub. lets*: pure_push_typ. Qed.

Lemma pure_dom_subset : forall E, dom (pure E) \c dom E.
Proof. intros. induction E.
  simpls. apply subset_refl.
  destruct a. destruct b.
  simpls. rewrite ?cons_to_push, ?dom_push.
    eapply subset_union_2. eapply subset_refl. eauto.
  simpls. cases_if*; rewrite ?cons_to_push, ?dom_push.
    eapply subset_union_2. eapply subset_refl. eauto.
    eapply subset_trans. eauto. apply subset_union_weak_r.
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
  apply subseq_refl.
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
  destruct b; rewrite ?tvar_push_sub, ?tvar_push_typ, IHSeq; auto.
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
  simpl. rewrite* <- empty_def.
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

Lemma subseq_push_sub_inv : forall E F X T,
  subseq E (F & X ~<: T) -> exists E', E = E' & X ~<: T /\ subseq E' F.
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

(** binding properties *)

Lemma binds_tvar : forall X E U, binds X (bind_sub U) E ->
  binds X (bind_sub U) (tvar_env E).
Proof. introv HB. inductions E.
  rewrite <- empty_def in HB. false* binds_empty_inv.
  destruct a. destruct b.
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv HB) as [HC|HC]; destruct HC.
      inversions* H0. apply* binds_concat_left.
    simpl. rewrite cons_to_push in *. destruct (binds_push_inv HB) as [HC|HC]; destruct HC.
      inversions H0. auto.
Qed.

Lemma binds_tvar_equiv : forall X E U, ok E -> binds X (bind_sub U) E <->
  binds X (bind_sub U) (tvar_env E).
Proof. introv OK. split. apply binds_tvar.

  introv HB. inductions E.
  simpls. rewrite <- empty_def in HB. false* binds_empty_inv.
  destruct a. destruct b.
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv HB) as [HC|HC]; destruct HC.
      inversions* H0. apply* binds_concat_left.
    simpls. rewrite cons_to_push in *. destruct (ok_push_inv OK).
      destruct (classic (X = v)). substs. forwards~ : IHE U. false (binds_fresh_inv H1 H0).
      apply* binds_concat_left.
Qed.

Lemma binds_subseq: forall E F x b, ok F -> subseq E F ->
  binds x b E -> binds x b F.
Proof. intros. inductions H0; auto.
  destruct (classic (x = x0)); subst.
    destruct (ok_push_inv H). forwards~ : IHsubseq. false* binds_fresh_inv.
    apply* binds_push_neq.
  destruct (binds_push_inv H2). destruct H3. substs*.
    apply* binds_push_neq.
Qed.

Lemma binds_pure: forall E v x, ok E ->
  binds x v (pure E) ->
  binds x v E.
Proof. intros. induction E.
  simpls. autos.
  destruct a. destruct b.
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv H0).
      destructs H1. inversions H2. apply binds_push_eq.
      destructs H1. apply* binds_push_neq.
    simpls. rewrite cons_to_push in H. cases_if*.
      rewrite cons_to_push in *. destruct (binds_push_inv H0); destruct H2.
        substs. apply binds_push_eq.
        apply* binds_push_neq.
      rewrite cons_to_push in *. destructs (ok_push_inv H).
        apply* binds_push_neq.
        intros Hc. substs. forwards~ : IHE. false* (binds_fresh_inv H4).
Qed.

Lemma binds_pure_reverse: forall E U x,
  binds x (bind_sub U) E -> binds x (bind_sub U) (pure E).
Proof. intros. induction E.
  simpl in *. autos.
  destruct a. destruct b.
    simpls. rewrite cons_to_push in *. destruct (binds_push_inv H).
      destructs H0. inversions H1. apply binds_push_eq.
      destructs H0. apply* binds_push_neq.
    rewrite cons_to_push in H. destruct (binds_push_inv H); destruct H0. inversion H1.
      simpls. cases_if*. rewrite cons_to_push. apply* binds_concat_left.
Qed.

(** wft properties *)

Lemma wft_tvar : forall E F T, ok F -> tvar_env E = tvar_env F ->
  wft E T -> wft F T.
Proof. introv Ok Tv Wf. gen F. inductions Wf; intros; auto.
  apply wft_var with U. rewrite* binds_tvar_equiv.
    rewrite <- Tv. apply* binds_tvar.
  apply_fresh wft_all as X. auto. apply* H0.
    repeat(rewrite <- cons_to_push). simpl. rewrite* Tv.
Qed.

Lemma wft_pure: forall E V, ok E -> wft (pure E) V <-> wft E V.
Proof. intros. split; intros.

  remember (pure E) as G. gen E. inductions H0; intros; subst; autos.
  eapply wft_var. apply* binds_pure.
  apply_fresh* wft_all as Y. apply* H1. repeat(rewrite <- cons_to_push). autos.

  inductions H0; autos.
  eapply wft_var. apply* binds_pure_reverse.
  apply_fresh* wft_all as Y. forwards~ : H2 Y.
    rewrite pure_push_sub in H3. auto.
Qed.

Lemma wft_pure_weaken: forall E F G V,
  ok (E & F & G) -> wft (E & (pure F) & G) V -> wft (E & F & G) V.
Proof. intros. inductions H0; intros; subst; autos.
  eapply wft_var. binds_cases H0.
    apply binds_concat_left; autos. apply* binds_concat_left_ok.
    apply binds_concat_left; autos. apply* binds_concat_right. apply* binds_pure.
      lets*: ok_concat_inv_r (ok_concat_inv_l H).
    apply binds_concat_right. auto.
  apply_fresh* wft_all as Y.
    assert (HI: ok (E & F & (G & Y ~<: T1 ))).
      rewrite concat_assoc. apply* ok_push.
    forwards~ HII: (H1 Y). apply HI.  rewrite* concat_assoc.
    rewrite* <- concat_assoc.
Qed.

Lemma wft_pure_reverse: forall E V, wft E V -> wft (pure E) V.
Proof. intros. inductions H; autos.
  eapply wft_var. apply* binds_pure_reverse.
  apply_fresh* wft_all as Y. forwards~ HI: (H1 Y).
    rewrite* pure_push_sub in HI.
Qed.

Lemma wft_subseq : forall E F T, ok F -> subseq E F ->
  wft E T -> wft F T.
Proof. introv Ok Seq Wf. gen T. inductions Seq; intros; auto.
  eapply wft_tvar with (E & x ~ b); eauto.
  repeat(rewrite <- cons_to_push). destruct b; auto. simpl; rewrite* H.
Qed.

(** okt properties *)

Lemma okt_pure : forall E,
  okt E -> okt (pure E).
Proof. intros. induction* E.
  destruct a. destruct b; simpl; rewrite cons_to_push in *.
  apply okt_sub. apply IHE. lets*: okt_push_sub_inv H.
    lets(_ & HI & HII): okt_push_sub_inv H.
    autos* wft_pure_reverse.
    lets(_ & _ & HI): okt_push_sub_inv H.
    lets: pure_dom_subset E. unfolds subset.
    intros Ha. apply HI. autos.

  lets(H1 & H2 & H3): okt_push_typ_inv H. cases_if*. rewrite cons_to_push.
  apply okt_typ. auto. apply* wft_pure_reverse.
    lets: pure_dom_subset E. unfolds subset. lets: H4 v.
    intros Hc. apply* H3.
Qed.

Lemma okt_subseq : forall E F, okt F -> subseq E F -> okt E.
Proof. introv Ok Seq. inductions Seq; auto.
  destruct* (okt_push_typ_inv Ok).
  destruct b.
    destructs (okt_push_sub_inv Ok). apply okt_sub. auto.
      apply wft_tvar with F; auto. apply subseq_fresh with F; auto.
    destructs (okt_push_typ_inv Ok). apply okt_typ. auto.
      apply wft_tvar with F; auto. apply subseq_fresh with F; auto.
Qed.

(** interplay of exposure, closed_typ, subseq, tvar_env  *)

Lemma exposure_pure: forall E T, exposure E T = exposure (pure E) T.
Proof. intros. inductions E; try solve [destruct* T].
  destruct a. destruct b. destruct T; auto.
    simpl. cases_if*.
    rewrite cons_to_push. rewrite exposure_push_typ.
    rewrite <- cons_to_push. simpl. cases_if*.
    rewrite cons_to_push. rewrite* exposure_push_typ.
Qed.

Lemma exposure_subseq: forall E F T, ok F -> subseq E F ->
  wft E T -> exposure E T = exposure F T.
Proof. introv Hf Seq Wf. gen T. inductions Seq; intros; auto.
  destructs (ok_push_inv Hf).
    destruct T0; try solve [rewrite ?exposure_nontvar; auto].
      rewrite <- cons_to_push. simpl. auto.
  destruct b; destructs (ok_push_inv Hf).
    destruct T; try solve [rewrite ?exposure_nontvar; auto].
      repeat(rewrite <- cons_to_push). simpl. cases_if*.
        destruct t; try solve [rewrite ?exposure_nontvar; auto].
        forwards~ : subseq_ok Seq. destruct* (classic (wft E (typ_fvar v))).
        assert (~ wft F (typ_fvar v)) as HWF.
          intros Fwf. inversions Fwf. apply H3. apply* wft_var. rewrite* binds_tvar_equiv.
          rewrite H. rewrite* <- binds_tvar_equiv.
        rewrite ?exposure_not_wft; auto.
        inversions Wf. forwards~ : binds_push_neq_inv H5. lets*: wft_var H3.
    rewrite ?exposure_push_typ; auto. apply* IHSeq. apply_empty* wft_strengthen.
Qed.

Lemma closed_typ_pure: forall E  T, closed_typ E T = closed_typ (pure E) T.
Proof. intros. inductions E. simpls. reflexivity.
  destruct a. destruct b.
  simpl. destruct T; auto. simpl. cases_if; rewrite* exposure_pure.
  rewrite cons_to_push, closed_typ_push_typ.
    rewrite <- cons_to_push. simpl. cases_if*. rewrite cons_to_push.
    rewrite* closed_typ_push_typ.
Qed.

Lemma pure_eq : forall E, pure (pure E) = pure E.
Proof. intros. induction E; autos.
  destruct a. destruct b; autos.
  simpl. rewrite* IHE.
  simpl. cases_if*. simpl. cases_if*. rewrite* IHE.
    rewrite cons_to_push, closed_typ_push_typ in H0.
    rewrite cons_to_push, closed_typ_push_typ in H.
    rewrite closed_typ_pure in H. false.
Qed.

Lemma subseq_pure_dist: forall E F, subseq E F ->
  subseq (pure E) (pure F).
Proof. introv Seq. inductions Seq; simpl; auto.
  apply subseq_refl.
  rewrite <- cons_to_push. simpl. cases_if*. rewrite* cons_to_push.
  rewrite <- ?cons_to_push. destruct b.
    simpl. rewrite ?cons_to_push. apply* subseq_cons. rewrite <- ?tvar_pure; auto.
    simpl. cases_if*; cases_if*; rewrite ?cons_to_push; auto.
    apply* subseq_cons. rewrite <- ?tvar_pure; auto.

    destruct t; tryfalse. simpls.
    lets: exposure_tvar (typ_fvar v) H. false.
Qed.

Lemma pure_binds_closed: forall E x T,
  okt E ->
  binds x (bind_typ T) E ->
  closed_typ E T = true ->
  binds x (bind_typ T) (pure E).
Proof. introv Ok Bnd Closed. induction E.
  rewrite <- empty_def in *. false* binds_empty_inv.

  destruct a. rewrite cons_to_push in *. destruct b.
    rewrite pure_push_sub. destruct (binds_push_inv Bnd).
      destruct H. inversion H0.
      destruct H. apply* binds_concat_left.
        destructs (okt_push_sub_inv Ok). apply* IHE.
        destruct T; auto. rewrite <- cons_to_push in Closed. simpls.
          cases_if*. forwards~ Wf: wft_from_env_has_typ H0.
          inversion Wf. false. autos* binds_fresh_inv.

    rewrite closed_typ_push_typ in Closed. destruct (binds_push_inv Bnd).
    destruct H. inversions H0. rewrite* pure_push_typ_closed.
    destruct H. destructs (okt_push_typ_inv Ok). forwards~ IH: IHE.
      apply* binds_subseq. apply ok_from_okt, okt_pure; auto.
      apply subseq_pure_dist, subseq_ext, subseq_refl.
Qed.

(* The following lemmas depend on subseq, thus are located here *)
Lemma pure_dist_two: forall E F,
  exists N, pure (E & F) = pure E & N  /\ subseq N F.
Proof. intros. gen E. inductions F; intros.
  exists (@empty bind). splits; try solve [rewrite <- empty_def, ?concat_empty_r; auto].

  destruct a. rewrite cons_to_push, concat_assoc in *.
  lets IH: IHF E. destruct IH as [N IH]. destructs IH.
  destruct (@pure_push_inv (E & F) v b) as [Case|Case]; rewrite Case.
    exists (N & v ~ b). splits; auto. rewrite H. rewrite* concat_assoc.
      destruct b; apply* subseq_cons; apply* subseq_tvar.
    destruct b.
      rewrite pure_push_sub, concat_def, single_def in Case. symmetry in Case.
      forwards~ : LibList.app_eq_self_inv_r Case. false.
      exists N. splits; auto.
Qed.

Lemma pure_cons_inv: forall E F M x v,
  pure (E & F) & x ~ v = pure E & M ->
  exists M', M = M' & x ~ v.
Proof. introv Eq. destruct M.
  destruct (pure_dist_two E F) as [N H]. destructs H.
  rewrite H, <- empty_def, ?concat_empty_r, <- concat_assoc, <- cons_to_push, concat_def in Eq.
  symmetry in Eq. forwards~ : LibList.app_eq_self_inv_r Eq. false.

  destruct p. rewrite cons_to_push, concat_assoc, <- ?cons_to_push in Eq.
  inversions Eq. exists M. rewrite* cons_to_push.
Qed.

Lemma pure_dist_three: forall E F G,
  exists M N, pure (E & F & G) = pure E & M & N  /\
              pure (E & F) = pure E & M /\
              subseq M F /\ subseq N G.
Proof. intros.
  forwards~ : pure_dist_two (E & F) G. destruct H as [N H]. destructs H.
  forwards~ : pure_dist_two E F.
  destruct H1 as [M H1]. destructs H1.
  exists M N. splits; auto.
    rewrite H. rewrite* H1.
Qed.

Lemma pure_dist_middle_sub: forall E X T G,
  exists N, pure (E & X ~<: T & G) = pure E & X ~<: T & N  /\
            subseq N G.
Proof. intros.
  forwards~ : pure_dist_three E (X ~<: T) G.
  destruct H as [M [N H]]. destructs H.
  exists N. splits; auto.

  inversions H1. rewrite empty_def, single_def in H5. inversion H5.
  rewrite <- cons_to_push, single_def in H3. inversions H3.
  rewrite <- cons_to_push, single_def in H3. inversions H3.
  simpls. rewrite <- empty_def in *. forwards~ : subseq_empty_inv H6.
  substs. rewrite concat_empty_l in *. rewrite* H.
Qed.

Lemma pure_dist_middle_typ: forall E F x U,
  (exists N, closed_typ E U = true /\
             pure (E & x ~: U & F) = pure E & x ~: U & N /\
             pure (E & F) = pure E & N /\
             subseq N F
  ) \/
  (exists N, closed_typ E U = false /\
             pure (E & x ~: U & F) = pure E & N /\
             pure (E & F) = pure E & N /\
             subseq N F
  ).
Proof. intros. inductions F.
  rewrite <- empty_def, ?concat_empty_r.
  cases (closed_typ E U).
    rewrite pure_push_typ_closed; auto. left. exists (@empty bind).
      splits; auto; rewrite* concat_empty_r.
    rewrite pure_push_typ_false; auto. right. exists (@empty bind).
      splits; auto; rewrite* concat_empty_r.

  destruct a. rewrite ?cons_to_push, ?concat_assoc.
  forwards~ IH : IHF x U.
  destruct IH as [Case | Case]; destruct Case as [N Case]; destructs Case.

  left. destruct b.
    rewrite ?pure_push_sub. exists (N & v ~<: t). splits; auto.
    rewrite H0, concat_assoc; auto.
    rewrite H1, concat_assoc; auto.
    apply* subseq_concat. apply subseq_refl.

    rewrite <- cons_to_push. simpl. cases_if; rewrite cons_to_push in *.
      rewrite closed_typ_push_typ, closed_typ_strengthen in H3.
      rewrite pure_push_typ_closed; auto. exists (N & v ~: t). splits; auto.
        rewrite H0, concat_assoc; auto.
        rewrite H1, concat_assoc; auto.
        apply* subseq_concat. apply subseq_refl.

      rewrite closed_typ_push_typ, closed_typ_strengthen in H3.
      rewrite pure_push_typ_false; auto. exists N. splits; auto.

  right. destruct b.
    rewrite ?pure_push_sub. exists (N & v ~<: t). splits; auto.
    rewrite H0, concat_assoc; auto.
    rewrite H1, concat_assoc; auto.
    apply* subseq_concat. apply subseq_refl.

    rewrite <- cons_to_push. simpl. cases_if; rewrite cons_to_push in *.
      rewrite closed_typ_push_typ, closed_typ_strengthen in H3.
      rewrite pure_push_typ_closed; auto. exists (N & v ~: t). splits; auto.
        rewrite H0, concat_assoc; auto.
        rewrite H1, concat_assoc; auto.
        apply* subseq_concat. apply subseq_refl.

      rewrite closed_typ_push_typ, closed_typ_strengthen in H3.
      rewrite pure_push_typ_false; auto. exists N. splits; auto.
Qed.

Lemma pure_dist_weaken: forall E F G, okt (E & G) -> okt (E & F & G) ->
  exists M N, pure (E & F & G) = pure E & M & N /\
              pure (E & G) = pure E & N /\
              subseq M F /\ subseq N G.
Proof. introv Ok1 Ok2. inductions G.
  rewrite <- empty_def, concat_empty_r in *.
  lets: pure_dist_two E F. destruct H as [N H]. destructs H.
  exists N (@empty bind). splits; rewrite ?concat_empty_r; auto.

  destruct a. rewrite ?cons_to_push, ?concat_assoc in *.
  destruct (okt_weaken Ok1). destruct (okt_weaken Ok2).
  forwards~ : IHG. destruct H3 as [M [N H3]]. destructs H3. destruct b.
    rewrite ?pure_push_sub. exists M (N & v ~<: t). splits; auto.
      rewrite H3. rewrite* concat_assoc.
      rewrite H4. rewrite* concat_assoc.
      apply* subseq_cons. apply* subseq_tvar.
    rewrite <- ?cons_to_push. simpl. cases_if*.
      cases_if*. rewrite ?cons_to_push in *. exists M (N & v ~: t).
      splits; auto. rewrite H3. rewrite* concat_assoc.
      rewrite H4. rewrite* concat_assoc.
      apply* subseq_cons. apply* subseq_tvar.

      rewrite cons_to_push in *. rewrite closed_typ_push_typ in *.
      destructs (okt_push_typ_inv Ok1). forwards~ : closed_typ_weaken H9 H1 H10. false.

      cases_if*. rewrite cons_to_push, closed_typ_push_typ in *.
      destructs (okt_push_typ_inv Ok1). forwards~ : closed_typ_weaken H9 H1 H10. false.
      exists M N. splits; auto. rewrite cons_to_push. apply* subseq_ext.
Qed.

Lemma pure_dist_weaken_pure: forall E F,
  exists M, pure (E & F) = pure E & M /\
            pure (E & pure F) = pure E & pure M /\
            pure F = pure M /\
            subseq M F.
Proof. intros. inductions F.
  simpl. rewrite <- empty_def, concat_empty_r in *.
  exists (@empty bind). splits; repeat(rewrite concat_empty_r); try rewrite* empty_def; auto.
     simpl. rewrite <- empty_def, concat_empty_r. auto. rewrite* <- empty_def.

  destruct a. destruct b.

  simpls. rewrite ?cons_to_push, ?concat_assoc in *.
  rewrite <- ?cons_to_push. simpl. rewrite ?cons_to_push in *.
  forwards~ : IHF. destruct H as [M H]. destructs H.
  exists (M & v ~<: t). splits; auto.
    rewrite concat_assoc. rewrite* H.
    rewrite H0. rewrite ?pure_push_sub, concat_assoc. auto.
    rewrite pure_push_sub, H1. auto.
    apply* subseq_cons. apply* subseq_tvar.

  simpls. cases_if*; rewrite cons_to_push, concat_assoc, closed_typ_push_typ in *.

  forwards~ : IHF. destruct H0 as [M H0]. destructs H0.
  rewrite <- cons_to_push. simpl. cases_if*; rewrite ?cons_to_push, ?concat_assoc in *.

  exists (M & v ~: t). splits; auto.
    rewrite H0. rewrite* concat_assoc.
    rewrite ?pure_push_typ_closed, concat_assoc, H1; auto.
      rewrite <- H. apply* closed_typ_tvar. apply* subseq_tvar.
      rewrite <- H4, closed_typ_push_typ. apply* closed_typ_tvar.
        rewrite ?tvar_dist, <- tvar_pure. auto.
    rewrite pure_push_typ_closed, H2; auto.
      rewrite <- H. apply* closed_typ_tvar. apply* subseq_tvar.
    apply* subseq_cons. apply* subseq_tvar.

  rewrite closed_typ_push_typ in *. forwards~ : closed_typ_weaken_left E H. false.

  forwards~ IH: IHF. destruct IH as [M IH]. destructs IH.
  rewrite <- cons_to_push. simpl. cases_if*; rewrite cons_to_push in *.
  rewrite closed_typ_push_typ in *. exists (M & v ~: t). splits; auto.
    rewrite H0, concat_assoc; auto.
    rewrite H1. rewrite* pure_push_typ_false.
      rewrite <- H. apply* closed_typ_tvar. apply* subseq_tvar.
    rewrite* pure_push_typ_false. rewrite <- H. apply* closed_typ_tvar. apply* subseq_tvar.
    apply* subseq_cons. apply* subseq_tvar.

  rewrite closed_typ_push_typ in *. exists M. splits; auto.
Qed.

Lemma pure_dist_weaken_pure2: forall E F G,
  exists M N, pure (E & F & G) = pure E & M & N /\
              pure (E & pure F & G) = pure E & pure M & N /\
              pure F = pure M /\
              subseq M F /\
              subseq N G.
Proof. intros. inductions G.
  rewrite <- empty_def, concat_empty_r in *.
  forwards~ : pure_dist_weaken_pure E F. destruct H as [M H]. destructs H.
  exists M (@empty bind). splits; repeat(rewrite concat_empty_r); auto.

  destruct a. destruct b; simpls;
  rewrite cons_to_push, concat_assoc in *.

  rewrite ?concat_assoc, ?pure_push_sub.
  forwards~ IH: IHG. destruct IH as [M [N IH]]. destructs IH.
  exists M (N & v ~<: t). splits; auto.
    rewrite concat_assoc, H; auto.
    rewrite concat_assoc, H0; auto.
    apply* subseq_cons. apply* subseq_tvar.

  rewrite <- cons_to_push. simpl.
  cases_if*; rewrite ?cons_to_push, ?concat_assoc in *.

  forwards~ IH: IHG. destruct IH as [M [N IH]]. destructs IH.
  rewrite closed_typ_push_typ in *. exists M (N & v ~: t). splits; auto.
    rewrite H0, concat_assoc; auto.
    rewrite pure_push_typ_closed, H1, concat_assoc; auto.
      rewrite <- H. apply* closed_typ_tvar.
      rewrite ?tvar_dist, <- tvar_pure; auto.
    apply* subseq_cons. apply* subseq_tvar.

  forwards~ IH: IHG. destruct IH as [M [N IH]]. destructs IH.
  rewrite closed_typ_push_typ in *. exists M N. splits; auto.
    rewrite pure_push_typ_false, H1; auto.
      rewrite <- H. apply* closed_typ_tvar.
      rewrite ?tvar_dist, <- tvar_pure; auto.
Qed.

Lemma subseq_pure_concat: forall E F M,
  pure (E & F) = pure E & M -> subseq M F.
Proof. introv Eq. inductions F.
  rewrite <- empty_def, concat_empty_r in Eq.
  rewrite concat_def in Eq. forwards~ : LibList.app_eq_self_inv_r Eq.
  substs*. rewrite* <- empty_def.

  destruct a. destruct b.
  rewrite cons_to_push, ?concat_assoc, ?pure_push_sub in Eq.
  forwards~ Inv : pure_cons_inv Eq. destruct Inv as [M' Inv]. substs.
  rewrite ?concat_assoc, ?pure_push_sub, <- ?cons_to_push in Eq.
  inversions Eq. forwards~ IH: IHF M'.
    rewrite ?cons_to_push. apply* subseq_cons. apply* subseq_tvar.

  rewrite ?cons_to_push, ?concat_assoc, <- cons_to_push in Eq. simpl in Eq.
  cases_if. rewrite cons_to_push in *. rewrite closed_typ_push_typ in H.

  forwards~ Inv : pure_cons_inv Eq. destruct Inv as [M' Inv]. substs.
  rewrite concat_assoc, <- ?cons_to_push in Eq. inversion Eq.
  apply* subseq_cons. apply* subseq_tvar.

  rewrite cons_to_push, closed_typ_push_typ in *. apply* subseq_ext.
Qed.

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

Lemma sub_regular : forall E S T,
  sub E S T -> okt E /\ wft E S /\ wft E T.
Proof.
  induction 1; autos*.
  split. autos*. split;
   apply_fresh* wft_all as Y;
    forwards~: (H1 Y); apply_empty* (@wft_narrow T1).
Qed.

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ term e /\ wft E T.
Proof.
  induction 1; try solve [splits*].
  splits*.
    apply_fresh* term_abs as y.
    pick_fresh y. specializes H1 y. destructs~ H1.
      forwards*: (okt_push_typ_inv H1).
    specializes H1 y. destructs~ H1.
    pick_fresh y. specializes H1 y. destructs~ H1.
      apply* wft_arrow.
      apply* wft_pure.
      apply* wft_pure.
      rewrite <- (@concat_empty_r bind (pure E)).
      eapply wft_strengthen. rewrite* concat_empty_r.
  splits*. destructs IHtyping1. inversion* H3.
  splits*.
    apply_fresh* term_tabs as y.
      pick_fresh y. forwards~ K: (H1 y). destructs K.
      forwards*: okt_push_sub_inv.
      forwards~ K: (H1 y). destructs K. auto.
    apply_fresh* wft_all as Y.
      pick_fresh y. forwards~ K: (H1 y). destructs K.
        forwards*: okt_push_sub_inv. destructs H5. apply* wft_pure.
      forwards~ K: (H1 Y). destructs K. apply* wft_pure.
        rewrite* pure_push_sub.
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
  apply* sub_refl_base.
  apply* sub_refl_eff.
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
  apply* sub_refl_base.
  apply* sub_refl_eff.
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
(** properties of pure environment related to subtyping *)

Lemma sub_weakening_env : forall E F G S T,
   sub (E & pure F & G) S T ->
   okt (E & F & G) ->
   sub (E & F & G) S T.
Proof. intros. inductions H; eauto.
  apply* sub_top. apply* wft_pure_weaken.
  apply* sub_refl_tvar. apply* wft_pure_weaken.
  apply* sub_trans_tvar.  binds_cases H.
    apply binds_concat_left; autos. apply* binds_concat_left_ok. eapply ok_concat_inv_l.
      eapply ok_from_okt. eauto.
    apply binds_concat_left; autos. apply* binds_concat_right. apply* binds_pure.
      lets*: ok_concat_inv_r (ok_concat_inv_l (ok_from_okt H1)).
    apply binds_concat_right. auto.
  apply_fresh* sub_all as X. lets: (H1 X).
    rewrite <- concat_assoc in H3. rewrite <- concat_assoc.
    apply* H3. rewrite concat_assoc. apply* okt_sub.
    destructs (sub_regular H). apply* wft_pure_weaken.
Qed.

Lemma sub_exposure: forall E P Q,
  okt E ->
  sub E P Q ->
  sub E (exposure E P) (exposure E Q).
Proof. introv Ok Sub. inductions Sub; try solve [rewrite ?exposure_nontvar; auto].
  replace (exposure E typ_top) with typ_top by (rewrite* exposure_nontvar).
    apply* sub_top. apply* exposure_wft.
  apply* sub_reflexivity. apply* exposure_wft.
  rewrite* (exposure_binds Ok H).
  rewrite ?exposure_nontvar; auto. apply* sub_all.
Qed.

Lemma safe_bound_sub: forall E P Q,
  okt E ->
  sub E P Q ->
  safe_bound (exposure E P) = false ->
  safe_bound (exposure E Q) = false.
Proof. introv Ok Sub Bound.
  inductions Sub; try solve [rewrite ?exposure_nontvar; simpls; auto];
    try solve [rewrite exposure_nontvar in Bound; auto; simpls; false]; auto.
  forwards~ Eq: exposure_binds Ok H. rewrite Eq in Bound. auto.
Qed.

Lemma closed_typ_narrowing: forall E F G X P Q T,
  okt (E & X ~<: Q & F) ->
  okt (E & X ~<: P & G) ->
  subseq F G ->
  sub E P Q ->
  closed_typ (E & X ~<: P & G) T = false ->
  closed_typ (E & X ~<: Q & F) T = false.
Proof. introv Ok1 Ok2 Seq Sub Closed. gen T. inductions Seq; intros.

  rewrite ?concat_empty_r in *.
  destruct T; try solve [unfold closed_typ; autos].
  rewrite <- ?cons_to_push in Closed |- *. simpls. cases_if*.
  destructs (okt_push_sub_inv Ok1). apply* safe_bound_sub.

  rewrite ?cons_to_push, ?concat_assoc, ?closed_typ_push_typ in *.
  destructs (okt_push_typ_inv Ok2). auto.

  destruct b; rewrite ?cons_to_push, ?concat_assoc in *.

  destructs (okt_push_sub_inv Ok1). destructs (okt_push_sub_inv Ok2).
  destruct T; try solve [unfold closed_typ; autos].
  rewrite <- ?cons_to_push in Closed |- *. simpls. cases_if*.
  rewrite ?cons_to_push, ?concat_assoc in *.
  destruct t; try solve [rewrite exposure_nontvar in Closed |- *; simpls; autos].
  forwards~ IH: IHSeq (typ_fvar v).
  rewrite ?cons_to_push, ?concat_assoc in *. forwards~ IH: IHSeq (typ_fvar v).

  destructs (okt_push_typ_inv Ok1). destructs (okt_push_typ_inv Ok2).
  rewrite closed_typ_push_typ in *. auto.
Qed.

Lemma sub_tvar : forall E F T1 T2, okt E -> okt F ->
  tvar_env E = tvar_env F ->
  sub E T1 T2 -> sub F T1 T2.
Proof. introv OkE OkF Tv Sub. gen F. inductions Sub; intros; autos.
  apply* sub_top. forwards~ : wft_tvar Tv H0.
  apply* sub_refl_tvar. forwards~ : wft_tvar Tv H0.
  apply* sub_trans_tvar. rewrite binds_tvar_equiv in *; auto. rewrite* <- Tv.
  apply_fresh sub_all as X. auto. apply* H0.
    apply* okt_sub. forwards~ : IHSub F.
    rewrite <- ?cons_to_push. simpl. rewrite* Tv.
Qed.

Lemma sub_subseq : forall E F T1 T2, okt F ->
  subseq E F -> sub E T1 T2 -> sub F T1 T2.
Proof. introv Ok Seq Sub. inductions Seq; auto.
  destructs (okt_push_typ_inv Ok). apply_empty* sub_weakening.
  apply sub_tvar with (E & x ~ b); auto.
    rewrite <- ?cons_to_push. destruct b; simpl; rewrite* H.
Qed.

Lemma sub_pure : forall E P Q, sub E P Q -> sub (pure E) P Q.
Proof. introv Sub. destructs (sub_regular Sub).
  eapply sub_tvar; eauto. apply* okt_pure. apply tvar_pure.
Qed.

Lemma sub_closed_left: forall E S T,
  sub E S T ->
  closed_typ E S = true ->
  closed_typ E T = true.
Proof. introv Sub Closed. inductions Sub; auto.
  destructs (sub_regular Sub). forwards~ Sb: closed_typ_binds H.
  rewrite Sb in Closed. apply IHSub.
  destruct U; try solve [auto; rewrite ?exposure_nontvar in Closed; auto].
  inversion H1.
Qed.

Lemma sub_unsafe_right: forall E S T,
  sub E S T ->
  closed_typ E T = false ->
  closed_typ E S = false.
Proof. introv Sub Closed. inductions Sub; auto; tryfalse.
  destructs (sub_regular Sub). forwards~ Sb: closed_typ_binds H.
  rewrite Sb. forwards~ IH: IHSub.
  destruct U; tryfalse; simpls; auto. inversion H1.
  rewrite* exposure_nontvar.
Qed.

Lemma pure_dist_narrow: forall E F G X P Q,
  okt (E & X ~<: Q & F) ->
  okt (E & X ~<: P & G) ->
  sub E P Q ->
  subseq F G ->
  exists M N, pure (E & X ~<: Q & F) = pure E & X ~<: Q & M /\
              pure (E & X ~<: P & G) = pure E & X ~<: P & N /\
              subseq M N /\
              subseq M F /\
              subseq N G.
Proof. introv Ok1 Ok2 Sub Seq. inductions Seq.
  rewrite ?concat_empty_r in *. exists (@empty bind) (@empty bind).
  rewrite ?pure_push_sub, ?concat_empty_r. splits; auto.

  rewrite concat_assoc in *. destructs (okt_push_typ_inv Ok2).
  forwards~ IH: IHSeq. destruct IH as [M [N IH]]. destructs IH.
  destruct (pure_push_typ (E & X ~<: P & F) x T) as [Pure | Impure].
    rewrite Pure. exists M (N & x ~: T). splits; auto.
      rewrite H3, concat_assoc; auto.
      apply* subseq_concat. apply subseq_refl.
    rewrite Impure. exists M N. splits; auto.

  destruct b.
  (* b = X <: T *)
  rewrite ?concat_assoc, ?pure_push_sub in *.
  destructs (okt_push_sub_inv Ok1). destructs (okt_push_sub_inv Ok2).
  forwards~ IH: IHSeq. destruct IH as [M [N IH]]. destructs IH.
  exists (M & x ~<: t) (N & x ~<: t). splits; auto.
    rewrite H6, concat_assoc; auto.
    rewrite H7, concat_assoc; auto.
    apply* subseq_concat. apply subseq_refl.
    apply* subseq_concat. apply subseq_refl.
    apply* subseq_concat. apply subseq_refl.

  (* b = X : T *)
  rewrite ?cons_to_push, ?concat_assoc in *.
  destructs (okt_push_typ_inv Ok1). destructs (okt_push_typ_inv Ok2).
  forwards~ IH: IHSeq. destruct IH as [M [N IH]]. destructs IH.
  rewrite ?concat_assoc, <- concat_assoc, <- ?cons_to_push.
  simpl. cases_if; rewrite ?cons_to_push, ?concat_assoc in *.

  destruct (pure_push_typ (E & X ~<: Q & E0) x t) as [Pure | Impure].
    rewrite Pure. exists (M & x ~: t) (N & x ~: t). splits; auto.
      rewrite H6, concat_assoc; auto.
      rewrite H7, concat_assoc; auto.
      apply* subseq_concat. apply subseq_refl.
      apply* subseq_concat. apply subseq_refl.
      apply* subseq_concat. apply subseq_refl.
    rewrite Impure. exists M (N & x ~: t). splits; auto.
      rewrite H7, concat_assoc; auto.
      apply* subseq_concat. apply subseq_refl.

  rewrite closed_typ_push_typ in *.
  rewrite pure_push_typ_false. exists M N. splits; auto.
  forwards~ : closed_typ_narrowing H0 H3 Seq Sub H11.
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
  apply_fresh* typing_abs as x.
    forwards~ : pure_dist_weaken H Ok. destruct H2 as [M [N H2]]. destructs H2.
    rewrite H2. rewrite <- concat_assoc. apply* H1.
    rewrite H3. rewrite* concat_assoc.
    rewrite concat_assoc. apply okt_typ.
      rewrite <- H2. apply* okt_pure.
      apply* wft_weaken. forwards~: (H0 x). destructs (typing_regular H6).
        rewrite* <- H3. rewrite <- H2. apply ok_from_okt. apply* okt_pure.
      rewrite <- H2. eapply subseq_fresh. eapply subseq_pure. auto.
  apply* typing_app.
  apply_fresh* typing_tabs as X.
    forwards~ : pure_dist_weaken H Ok. destruct H2 as [M [N H2]]. destructs H2.
    rewrite H2. rewrite <- concat_assoc. apply* H1.
    rewrite H3. rewrite* concat_assoc.
    rewrite concat_assoc. apply okt_sub.
      rewrite <- H2. apply* okt_pure.
      apply* wft_weaken. forwards~: (H0 X). destructs (typing_regular H6).
        rewrite* <- H3. rewrite <- H2. apply ok_from_okt. apply* okt_pure.
      rewrite <- H2. eapply subseq_fresh. eapply subseq_pure. auto.
  apply* typing_tapp. apply* sub_weakening.
  apply* typing_sub. apply* sub_weakening.
Qed.

Lemma typing_weakening_pure : forall E F G e T,
  typing (E & (pure F) & G) e T ->
  okt (E & F & G) ->
  typing (E & F & G) e T.
Proof. introv Typ Ok. inductions Typ.
  apply* typing_var. binds_cases H0; autos.
    apply* binds_weaken. apply* binds_concat_left.
    apply binds_concat_right. apply* binds_pure.
    autos* ok_concat_inv_l ok_concat_inv_r ok_from_okt.
  apply_fresh typing_abs as x. auto.
    forwards~ : pure_dist_weaken_pure2 E F G. destruct H2 as [M [N H2]].
      destruct H2. destruct H3. destructs H4.
    rewrite H2. rewrite <- concat_assoc. apply* H1.
    rewrite H3. rewrite* concat_assoc.
    rewrite concat_assoc. apply okt_typ.
      rewrite <- H2. apply* okt_pure.
      forwards~: (H0 x). destructs (typing_regular H7).
        destructs (okt_push_typ_inv H8).
        rewrite <- H2. applys~ wft_tvar H12. apply ok_from_okt. apply* okt_pure.
        rewrite <- ?tvar_pure, ?tvar_dist, <- ?tvar_pure; auto.
      rewrite <- H2. eapply subseq_fresh. eapply subseq_pure. auto.
  apply* typing_app.
  apply_fresh typing_tabs as X; auto.
    forwards~ : pure_dist_weaken_pure2 E F G. destruct H2 as [M [N H2]].
      destruct H2. destruct H3. destructs H4.
    rewrite H2. rewrite <- concat_assoc. apply* H1.
    rewrite H3. rewrite* concat_assoc.
    rewrite concat_assoc. apply okt_sub.
      rewrite <- H2. apply* okt_pure.
      forwards~: (H0 X). destructs (typing_regular H7).
        destructs (okt_push_sub_inv H8).
        rewrite <- H2. applys~ wft_tvar H12. apply ok_from_okt. apply* okt_pure.
        rewrite <- ?tvar_pure, ?tvar_dist, <- ?tvar_pure; auto.
      rewrite <- H2. eapply subseq_fresh. eapply subseq_pure. auto.
  apply* typing_tapp. apply* sub_weakening_env.
  eapply typing_sub. apply* IHTyp. apply* sub_weakening_env.
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
Proof. introv Sub. destructs (sub_regular Sub).
  lets: okt_pure H.
  apply sub_tvar with E; auto. apply tvar_pure.
Qed.

(************************************************************************ *)
(** Preservation by Type Narrowing (7) *)

Lemma typing_narrowing_general : forall Q E F G X P e T,
  sub E P Q ->
  subseq F G ->
  okt (E & X ~<: P & G) ->
  typing (E & X ~<: Q & F) e T ->
  typing (E & X ~<: P & G) e T.
Proof. introv Sub Seq Ok1 Typ. gen_eq E': (E & X ~<: Q & F). gen E F G.
  inductions Typ; intros; subst; simpl.
  binds_cases H0; apply* typing_var.
    rewrite <- concat_assoc, <- concat_empty_r. apply* binds_weaken.
      rewrite concat_empty_r, concat_assoc. auto.
    apply binds_concat_right. apply binds_subseq with F; auto.
      eapply ok_concat_inv_r, ok_from_okt. eauto.
  apply_fresh* typing_abs as y.
    forwards~ : pure_dist_narrow H Ok1 Sub Seq.
    destruct H2 as [M [N H2]]. destruct H2. destructs H3.
    rewrite H3. forwards~ : H1 y (pure E0) (M & y ~: V) (N & y ~: V).
      apply* sub_pure.
      apply* subseq_cons. apply* subseq_tvar.
      rewrite concat_assoc, <- H3.
        forwards~: (H0 y). destructs (typing_regular H7).
        destructs (okt_push_typ_inv H8). apply okt_typ. apply* okt_pure.
        apply wft_pure. apply* ok_from_okt. apply wft_narrow with Q; auto.
        rewrite wft_pure in H12; auto. eapply wft_subseq. apply* ok_from_okt.
        apply subseq_extend with (F := F) (G := G); auto. auto.
      eapply subseq_fresh. apply subseq_pure. auto.
      rewrite H2. rewrite concat_assoc. auto.
    rewrite concat_assoc in H7. auto.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    forwards~ : pure_dist_narrow H Ok1 Sub Seq.
    destruct H2 as [M [N H2]]. destruct H2. destructs H3.
    rewrite H3. forwards~ : H1 Y (pure E0) (M & Y ~<: V) (N & Y ~<: V).
      apply* sub_pure.
      apply* subseq_cons. apply* subseq_tvar.
      rewrite concat_assoc. rewrite <- H3.
        forwards~: (H0 Y). destructs (typing_regular H7).
        destructs (okt_push_sub_inv H8). apply okt_sub. apply* okt_pure.
        apply wft_pure. apply* ok_from_okt. apply wft_narrow with Q; auto.
        rewrite wft_pure in H12; auto. eapply wft_subseq. apply* ok_from_okt.
        apply subseq_extend with (F := F) (G := G); auto. auto.
      eapply subseq_fresh. apply subseq_pure. auto.
      rewrite H2. rewrite concat_assoc. auto.
    rewrite concat_assoc in H7. auto.
  apply* typing_tapp. eapply sub_subseq. auto. apply subseq_extend. eauto.
    apply* (@sub_narrowing Q).
  apply* typing_sub. eapply sub_subseq. auto. apply subseq_extend. eauto.
    apply* (@sub_narrowing Q).
Qed.

Lemma typing_narrowing : forall Q E F X P e T,
  sub E P Q ->
  typing (E & X ~<: Q & F) e T ->
  typing (E & X ~<: P & F) e T.
Proof. introv Sub Typ. destructs (typing_regular Typ).
  forwards~ Ok: okt_narrow P H.
  forwards~ : typing_narrowing_general Sub Ok Typ. apply subseq_refl.
Qed.

Lemma typing_abs_closed : forall E S e T,
  typing E (trm_abs S e) T -> closed_typ E T = true.
Proof. introv Typ. inductions Typ; auto.
  apply sub_closed_left with S0; auto.
Qed.

Lemma typing_tabs_closed : forall E S e T,
  typing E (trm_tabs S e) T -> closed_typ E T = true.
Proof. introv Typ. inductions Typ; auto.
  apply sub_closed_left with S0; auto.
Qed.

Lemma typing_strengthen_env: forall E u U,
  value u ->
  typing E u U ->
  typing (pure E) u U.
Proof. introv Val Typ. inductions Typ; try solve [inversion Val].
  apply_fresh* typing_abs as y. apply* okt_pure. rewrite* pure_eq.
  apply_fresh* typing_tabs as y. apply* okt_pure. rewrite* pure_eq.
  apply typing_sub with S. apply* IHTyp. apply* sub_pure.
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma open_tt_fv_subset: forall k U T,
  fv_tt T \c fv_tt (open_tt_rec k U T).
Proof. intros. gen k. induction T; intros; simpls;
  autos* subset_empty_l subset_union_2 subset_refl.
Qed.

Lemma open_te_fv_subset: forall k U e,
  fv_te e \c fv_te (open_te_rec k U e).
Proof. intros. gen k. induction e; intros; simpls;
  autos* subset_empty_l subset_union_2 subset_refl;
  try solve [apply* subset_union_2; apply open_tt_fv_subset].
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
Proof. intros. gen k. induction e; intros; simpls; autos;
  autos* subset_empty_l subset_refl subset_union_2.
Qed.

Lemma open_tt_tt_fv_subset: forall k T1 T2,
  fv_tt (open_tt_rec k T1 T2) \c fv_tt T1 \u fv_tt T2.
Proof. intros. gen k. induction T2; intros; simpls;
  autos* subset_empty_l subset_union_weak_r.

  cases_if; autos* subset_union_weak_l subset_empty_l.

  lets* IH: (subset_union_2 (IHT2_1 k) (IHT2_2 k)).
  rewrite union_assoc, union_comm in IH.
  replace ((fv_tt T1 \u fv_tt T2_1) \u fv_tt T1) with (fv_tt T1 \u fv_tt T2_1) in IH.
  rewrite union_assoc, union_comm; auto.
  rewrite union_comm, <- union_assoc,  union_same; auto.

  lets* IH: (subset_union_2 (IHT2_1 k) (IHT2_2 (S k))).
  rewrite union_assoc, union_comm in IH.
  replace ((fv_tt T1 \u fv_tt T2_1) \u fv_tt T1) with (fv_tt T1 \u fv_tt T2_1) in IH.
  rewrite union_assoc, union_comm; auto.
  rewrite union_comm, <- union_assoc, union_same; auto.
Qed.

Lemma wft_fv_tt: forall E T,
  wft E T -> fv_tt T \c dom E.
Proof.
  intros. inductions H; simpls; autos* subset_empty_l.

  lets BIND: get_some_inv (binds_get H). unfolds subset. introv H1.
    rewrite in_singleton in H1. rewrite* H1.
  rewrite <- union_same. apply* subset_union_2.
  rewrite <- union_same. apply* subset_union_2.
    pick_fresh X. forwards~ HI: (H1 X). simpls.
    rewrite dom_concat, dom_single in HI. eapply subset_strengthen. eapply subset_trans.
    apply open_tt_fv_subset. exact HI. autos.
Qed.

Lemma subtyping_env_fv : forall E S T, sub E S T ->
  fv_tt S \c dom E /\ fv_tt T \c dom E.
Proof. intros. inductions H; simpls; autos* subset_empty_l.
  splits. apply* wft_fv_tt. apply subset_empty_l.
  lets*: wft_fv_tt H0.
  destructs IHsub. splits*. lets BIND: get_some_inv (binds_get H).
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

Ltac solve_subsets :=
  match goal with
    | [|- _ \u _ \c dom ?E ] => rewrite <- union_same; eapply subset_trans;
                                apply* subset_union_2; apply pure_dom_subset
    | [|- _ \c dom ?E ] => eapply subset_trans; eauto; apply pure_dom_subset
    | [_: ?a \c ?E, _: ?b \c ?E |- ?a \u ?b \c ?E ] =>
      rewrite <- union_same; apply* subset_union_2
  end.

Ltac splits_solve_subsets := splits*; try solve_subsets.

Lemma typing_env_fv : forall E e T, typing E e T ->
  fv_ee e \c dom E /\ fv_te e \c dom E /\ fv_tt T \c dom E.
Proof. introv Typ. inductions Typ.
  (* var *)
  simpls. splits; try solve [autos* subset_empty_l wft_fv_tt].
    forwards~ K:  get_some_inv (binds_get H0). unfolds subset.
    intros. rewrite in_singleton in H1. subst*.
  (* abs closed *)
  simpl. pick_fresh x. forwards~ : H0 x. forwards~ : H1 x. destructs H3.
  rewrite dom_concat, dom_single in *.
  forwards~ : subset_strengthen (subset_trans (@open_te_ee_fv_subset 0 (trm_fvar x) e1) H4).
  forwards~ : subset_strengthen (subset_trans (@open_ee_fv_subset 0 (trm_fvar x) e1) H3).
  forwards~ : subset_strengthen H5.
  forwards~ : wft_fv_tt (wft_from_okt_typ (proj1 (typing_regular H2))).
  splits_solve_subsets.
  (* app *)
  destructs IHTyp1. simpls. destruct (subset_union H1). destructs IHTyp2.
  splits_solve_subsets.
  (* tabs closed *)
  simpl. pick_fresh X. forwards~ IH: H1 X. destructs IH.
  rewrite dom_concat, dom_single in *.
  forwards~ : subset_strengthen (subset_trans (@open_te_fv_subset 0 (typ_fvar X) e1) H3).
  unfold open_te in H2. rewrite <- open_ee_te_fv_eq in H2. forwards~ : subset_strengthen H2.
  forwards~ : subset_strengthen (subset_trans (@open_tt_fv_subset 0 (typ_fvar X) T1) H4).
  forwards~ IH : H0 X.
  forwards~ : wft_fv_tt (wft_from_okt_sub (proj1 (typing_regular IH))).
  splits_solve_subsets.
  (* tapp *)
  destructs IHTyp. simpls. forwards~ : wft_fv_tt E T. destruct (subset_union H2).
  splits_solve_subsets.
  eapply subset_trans. apply open_tt_tt_fv_subset. solve_subsets.
  (* sub *)
  destructs IHTyp. forwards: subtyping_env_fv H. splits_solve_subsets.
Qed.

Lemma typing_through_subst_ee : forall U E F x T e u,
  value u ->
  typing (E & x ~: U & F) e T ->
  typing E u U ->
  typing (E & F) (subst_ee x u e) T.
Proof.
  introv Val TypT TypU. inductions TypT; introv; simpl.
  case_var.
    binds_get H0. apply_empty* typing_weakening.
    binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    forwards~ Inv: pure_dist_middle_typ E F x U.
    destruct Inv as [[N Inv] | [N Inv]]; destructs Inv.
    (* if U is safe, then use IH *)
    rewrite H4. apply_ih_bind* H1. rewrite H3. reflexivity.
    apply* typing_strengthen_env.
    (* if U is not safe,  x is free in e1; *)
    rewrite H3 in H0. rewrite H4.
    forwards~ IH: H0 y. rewrite* subst_ee_fresh.
    destructs (typing_env_fv IH). destructs (ok_middle_inv (ok_from_okt H)).
    forwards~ : subseq_fresh (pure E) H9. apply subseq_pure.
    forwards~ : subseq_fresh N H10. rewrite ?dom_concat in H6.
    unfold subset in H6. intros Contra. forwards~ Inv: H6 Contra.
    rewrite ?in_union, or_assoc, dom_single, in_singleton in Inv.
    branches Inv; false. substs. assert (y \notin \{ y}) by auto. false* notin_same.
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    rewrite* subst_ee_open_te_var.
    forwards~ Inv: pure_dist_middle_typ E F x U.
    destruct Inv as [[N Inv] | [N Inv]]; destructs Inv.
    (* if U is safe, then use IH *)
    rewrite H4. apply_ih_bind* H1. rewrite H3. reflexivity.
    apply* typing_strengthen_env.
    (* if U is not safe,  x is free in e1; *)
    rewrite H3 in H0. rewrite H4.
    forwards~ IH: H0 Y. rewrite* subst_ee_fresh.
    destructs (typing_env_fv IH). destructs (ok_middle_inv (ok_from_okt H)).
    forwards~ : subseq_fresh (pure E) H9. apply subseq_pure.
    forwards~ : subseq_fresh N H10. rewrite ?dom_concat in H6.
    unfold subset in H6. intros Contra. forwards~ Inv: H6 Contra.
    rewrite ?in_union, or_assoc, dom_single, in_singleton in Inv.
    branches Inv; false. substs. assert (Y \notin \{ Y}) by auto. false* notin_same.
  apply* typing_tapp. apply* sub_strengthening.
  apply* typing_sub. apply* sub_strengthening.
Qed.

(************************************************************************ *)
(** Preservation by Type Substitution (11) *)

Lemma tvar_map: forall E Z P,
  tvar_env (pure (map (subst_tb Z P) E)) =
  tvar_env (map (subst_tb Z P) (pure E)).
Proof. intros. inductions E.
  simpl; rewrite <- empty_def, map_empty, empty_def. reflexivity.
  destruct a. destruct b; rewrite ?cons_to_push.

  rewrite pure_push_sub, ?map_push. simpl.
  rewrite ?tvar_dist, <- tvar_pure, <- (IHE Z P), <- tvar_pure.
  rewrite ?tvar_dist, tvar_single_sub. auto.

  rewrite <- ?tvar_pure, map_push. simpl. rewrite tvar_push_typ.
  destruct (pure_push_typ E v t); rewrite H.
  rewrite map_push. simpl. rewrite tvar_push_typ. rewrite <- IHE, <- tvar_pure. auto.
  rewrite <- IHE, <- tvar_pure. auto.
Qed.

Lemma pure_map: forall E F G Z P Q,
  okt (E & Z ~<: Q & F) ->
  sub E P Q ->
  subseq F G ->
  exists M N, pure (E & Z ~<: Q & F) = pure E & Z ~<: Q & M /\
              pure (E & F) = pure E & M /\
              pure (E & map (subst_tb Z P) G) = pure E & N /\
              N = map (subst_tb Z P) N /\
              subseq M N /\ subseq M F /\ subseq N (map (subst_tb Z P) G).
Proof. introv Ok Sub Seq. inductions Seq.
  rewrite ?concat_empty_r, map_empty in *. exists (@empty bind) (@empty bind).
  splits; auto; rewrite ?map_empty, ?concat_empty_r, ?pure_push_sub; auto.

  destruct IHSeq as [M [N IH]]; auto. destructs IH.
  rewrite map_push. simpl. rewrite ?concat_assoc.
  destruct (pure_push_typ (E & map (subst_tb Z P) F) x (subst_tt Z P T)).
  admit. admit. admit.
Qed.

Lemma typing_through_subst_te_general : forall Q E F G Z e T P,
  subseq F G ->
  typing (E & Z ~<: Q & F) e T ->
  sub E P Q ->
  okt (E & Z ~<: Q & G) ->
  typing (E & map (subst_tb Z P) G) (subst_te Z P e) (subst_tt Z P T).
Proof.
  introv Seq Typ Sub Ok. gen G.
  inductions Typ; intros; simpls subst_tt; simpls subst_te.
  apply* typing_var. rewrite* (@map_subst_tb_id E Z P).
    unsimpl (subst_tb Z P (bind_typ T)).
    rewrite <- map_concat. apply binds_map. binds_cases H0.
    apply binds_concat_left_ok; auto. apply ok_remove with (Z ~<: Q); auto.
    apply binds_concat_right. apply binds_subseq with F; auto.
    apply (ok_concat_inv_r (ok_from_okt Ok)).
  apply_fresh* typing_abs as y.
    unsimpl (subst_tb Z P (bind_typ V)).
    rewrite* subst_te_open_ee_var.
    forwards~ Map: pure_map H Sub Seq. destruct Map as [M [N Map]]. destructs Map.
    rewrite H4, H5, <- concat_assoc, <- map_push.
    applys~ H1 Q (pure E) (M & y ~: V) (N & y ~: V).
    rewrite H2, ?concat_assoc. reflexivity. apply* sub_pure.
    apply* subseq_concat. apply subseq_refl.
    rewrite concat_assoc.
    (*okt*)
    assert (okt (pure E & Z ~<: Q & N)) as OkN.
      apply okt_subseq with (pure E & Z ~<: Q & ( (map (subst_tb Z P) G))).
      apply okt_subst_tb_keep. apply okt_subseq with (E & Z ~<: Q & G); auto.
      repeat(apply* subseq_concat; try apply subseq_pure; try apply subseq_refl).
      apply* wft_pure. repeat(apply* subseq_concat; auto; try apply subseq_refl).
    apply okt_typ. auto.
    (*wft*)
    apply wft_tvar with (E & Z ~<: Q & (map (subst_tb Z P) G)); auto.
    rewrite ?tvar_dist, <- ?tvar_pure, (subseq_tvar H8). auto.
    apply wft_subst_tb_same.
    forwards~ IH: H0 y. destructs (typing_regular IH). destructs (okt_push_typ_inv H9).
    apply wft_tvar with (pure (E & Z ~<: Q & F)); auto.
    rewrite <- tvar_pure, ?tvar_dist, (subseq_tvar Seq). auto.
    destruct* (sub_regular Sub).
    apply* ok_concat_map.
    (* y fresh *)
    apply subseq_fresh with (E & Z ~<: Q & map (subst_tb Z P) G); auto.
    repeat(apply subseq_concat; auto; try apply subseq_refl; try apply subseq_pure).
  apply* typing_app.
  apply_fresh* typing_tabs as Y.
    unsimpl (subst_tb Z P (bind_sub V)).
    rewrite* subst_te_open_te_var.
    rewrite* subst_tt_open_tt_var.
    forwards~ Map: pure_map H Sub Seq. destruct Map as [M [N Map]]. destructs Map.
    rewrite H4, H5, <- concat_assoc, <- map_push.
    applys~ H1 Q (pure E) (M & Y ~<: V) (N & Y ~<: V).
    rewrite H2, ?concat_assoc. reflexivity. apply* sub_pure.
    apply* subseq_concat. apply subseq_refl.
    rewrite concat_assoc.
    (*okt*)
    assert (okt (pure E & Z ~<: Q & N)) as OkN.
      apply okt_subseq with (pure E & Z ~<: Q & ( (map (subst_tb Z P) G))).
      apply okt_subst_tb_keep. apply okt_subseq with (E & Z ~<: Q & G); auto.
      repeat(apply* subseq_concat; try apply subseq_pure; try apply subseq_refl).
      apply* wft_pure. repeat(apply* subseq_concat; auto; try apply subseq_refl).
    apply okt_sub. auto.
    (*wft*)
    apply wft_tvar with (E & Z ~<: Q & (map (subst_tb Z P) G)); auto.
    rewrite ?tvar_dist, <- ?tvar_pure, (subseq_tvar H8). auto.
    apply wft_subst_tb_same.
    forwards~ IH: H0 Y. destructs (typing_regular IH). destructs (okt_push_sub_inv H9).
    apply wft_tvar with (pure (E & Z ~<: Q & F)); auto.
    rewrite <- tvar_pure, ?tvar_dist, (subseq_tvar Seq). auto.
    destruct* (sub_regular Sub).
    apply* ok_concat_map.
    (* y fresh *)
    apply subseq_fresh with (E & Z ~<: Q & map (subst_tb Z P) G); auto.
    repeat(apply subseq_concat; auto; try apply subseq_refl; try apply subseq_pure).
  rewrite* subst_tt_open_tt. apply* typing_tapp.
    eapply sub_through_subst_tt; eauto. apply sub_subseq with (E & Z ~<: Q & F); auto.
    repeat(apply subseq_concat; auto; try apply subseq_refl; try apply subseq_pure).
  apply* typing_sub. eapply sub_through_subst_tt; eauto.
    apply sub_subseq with (E & Z ~<: Q & F); auto.
    repeat(apply subseq_concat; auto; try apply subseq_refl; try apply subseq_pure).
Qed.

Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (E & Z ~<: Q & F) e T ->
  sub E P Q ->
  typing (E & map (subst_tb Z P) F) (subst_te Z P e) (subst_tt Z P T).
Proof.
  introv Typ Sub. destructs (typing_regular Typ).
  forwards~ : typing_through_subst_te_general (subseq_refl F) Typ Sub.
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
