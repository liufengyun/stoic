(***************************************************************************
* Soundness Proof of System F + closed functions                           *
***************************************************************************)
Require Export SfLib.

Module F_CFUN.

Inductive ty : Type :=
  | TVar   : id -> ty
  | TArrow : ty -> ty -> ty
  | TAny   : id -> ty -> ty
  | TNat   : ty.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TVar"
  | Case_aux c "TArrow"
  | Case_aux c "TAny"
  | Case_aux c "TNat"].

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tcap : id -> ty -> tm -> tm        (* capsule lambda *)
  | ttabs : id -> tm -> tm             (* type abstraction *)
  | ttapp : tm -> ty -> tm             (* type application *)
  | tnat  : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar"
  | Case_aux c "tapp"
  | Case_aux c "tabs"
  | Case_aux c "tcap"
  | Case_aux c "ttabs"
  | Case_aux c "ttapp"
  | Case_aux c "tnat"
  | Case_aux c "tsucc"
  | Case_aux c "tpred"
  | Case_aux c "tmult"
  | Case_aux c "tif0" ].

Hint Constructors tm.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_cap : forall x T t,              (* capsule lambda *)
      value (tcap x T t)
  | v_ttabs : forall X t,
      value (ttabs X t)
  | v_nat : forall (n:nat),
      value (tnat n).

Hint Constructors value.

Reserved Notation "'[' X '|->' S ']' T" (at level 20).

Fixpoint subst_ty_ty (X:id) (S:ty) (T:ty) : ty :=
  match T with
    | TVar X' =>
      if eq_id_dec X X' then S else T
    | TArrow T1 T2 =>
      TArrow ([X|->S] T1) ([X|->S] T2)
    | TAny X' T2 =>
      TAny X' (if eq_id_dec X X' then T2 else [X|->S]  T2)
    | TNat => T
  end

where "'[' X '|->' S ']' T" := (subst_ty_ty X S T).

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst_tm_tm (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' =>
      if eq_id_dec x x' then s else t
  | tabs x' T t1 =>
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1))
  | tcap x' T t1 =>                      (* capsule lambda *)
      t
  | tapp t1 t2 =>
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttabs X t =>
      ttabs X ([x:=s] t)
  | ttapp t1 T1 =>
      ttapp ([x:=s] t1) T1
  | tnat n =>
      t
  | tsucc t1 =>
      tsucc ([x:=s] t1)
  | tpred t1 =>
      tpred ([x:=s] t1)
  | tmult t1 t2 =>
      tmult ([x:=s] t1) ([x:=s] t2)
  | tif0 t1 t2 t3 =>
      tif0 ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst_tm_tm x s t).


Reserved Notation "'[' X ':=>' S ']' t" (at level 20).

Fixpoint subst_ty_tm (X:id) (S:ty) (t:tm) : tm :=
  match t with
  | tvar x =>
      t
  | tabs x T t1 =>
      tabs x ([X|->S] T) ([X:=>S] t1)
  | tcap x T t1 =>                      (* capsule lambda *)
      tcap x ([X|->S] T) ([X:=>S] t1)
  | tapp t1 t2 =>
      tapp ([X:=>S] t1) ([X:=>S] t2)
  | ttabs X' t =>
      ttabs X (if eq_id_dec X X' then t else [X:=>S] t)
  | ttapp t1 T1 =>
      ttapp ([X:=>S] t1) ([X|->S] T1)
  | tnat n =>
      t
  | tsucc t1 =>
      tsucc ([X:=>S] t1)
  | tpred t1 =>
      tpred ([X:=>S] t1)
  | tmult t1 t2 =>
      tmult ([X:=>S] t1) ([X:=>S] t2)
  | tif0 t1 t2 t3 =>
      tif0 ([X:=>S] t1) ([X:=>S] t2) ([X:=>S] t3)
  end

where "'[' X ':=>' S ']' t" := (subst_ty_tm X S t).

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_AppCap : forall x T t12 v2,                  (* capsule lambda *)
         value v2 ->
         (tapp (tcap x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tapp v1 t2 ==> tapp v1  t2'
  | ST_TApp : forall t1 t1' T,
         t1 ==> t1' ->
         ttapp t1 T ==> ttapp t1' T
  | ST_TAppTAbs : forall X t12 T2,
         (ttapp (ttabs X t12) T2) ==> [X:=>T2]t12
  | ST_Succ : forall t1 t1',
         t1 ==> t1' ->
         tsucc t1 ==> tsucc t1'
  | ST_SuccNat : forall n,
         tsucc (tnat n) ==> tnat (S n)
  | ST_Pred : forall t1 t1',
         t1 ==> t1' ->
         tpred t1 ==> tpred t1'
  | ST_PredNat : forall n,
         tpred (tnat (S n)) ==> tnat n
  | ST_PredZero :
         tpred (tnat O) ==> tnat O
  | ST_MultNatNat : forall m n,
         tmult (tnat m) (tnat n) ==> tnat (m * n)
  | ST_Mult1 : forall t1 t2 t1',
          t1 ==> t1' ->
          tmult t1 t2 ==> tmult t1' t2
  | ST_Mult2 : forall t1 t2 t2',
          t2 ==> t2' ->
          tmult t1 t2 ==> tmult t1 t2'
  | ST_If0True : forall t2 t3,
          tif0 (tnat O) t2 t3 ==> t2
  | ST_If0False : forall n t2 t3,
          tif0 (tnat (S n)) t2 t3 ==> t3
  | ST_If0 : forall t1 t1' t2 t3,
          t1 ==> t1' ->
          tif0 t1 t2 t3 ==> tif0 t1' t2 t3

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs"
  | Case_aux c "ST_AppCap"
  | Case_aux c "ST_App1"
  | Case_aux c "ST_App2"
  | Case_aux c "ST_TApp"
  | Case_aux c "ST_TAppTAbs"
  | Case_aux c "ST_Succ"
  | Case_aux c "ST_SuccNat"
  | Case_aux c "ST_Pred"
  | Case_aux c "ST_PredNat"
  | Case_aux c "ST_PredZero"
  | Case_aux c "ST_MultNatNat"
  | Case_aux c "ST_Mult1"
  | Case_aux c "ST_Mult2"
  | Case_aux c "ST_If0True"
  | Case_aux c "ST_If0False"
  | Case_aux c "ST_If0"
  ].

Hint Constructors step.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 ->
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_Cap : forall Gamma x T11 T12 t12,             (* capsule lambda *)
      extend empty x T11 |- t12 \in T12 ->
      Gamma |- tcap x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- tapp t1 t2 \in T12
  | T_TAbs : forall Gamma X t2 T2,
      extend Gamma X (TVar X) |- t2 \in T2 ->
      Gamma |- ttabs X t2 \in TAny X T2
  | T_TApp : forall Gamma t1 X T12 T2,
      Gamma |- t1 \in TAny X T12 ->
      Gamma |- ttapp t1 T2 \in [X|->T2]T12
  | T_Nat : forall Gamma n,
       Gamma |- tnat n \in TNat
  | T_Succ : forall Gamma t1,
       Gamma |- t1 \in TNat ->
       Gamma |- tsucc t1 \in TNat
  | T_Pred : forall Gamma t1,
       Gamma |- t1 \in TNat ->
       Gamma |- tpred t1 \in TNat
  | T_Mult : forall Gamma t1 t2,
       Gamma |- t1 \in TNat ->
       Gamma |- t2 \in TNat ->
       Gamma |- tmult t1 t2 \in TNat
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TNat ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif0 t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var"
  | Case_aux c "T_Abs"
  | Case_aux c "T_Cap"
  | Case_aux c "T_App"
  | Case_aux c "T_TAbs"
  | Case_aux c "T_TApp"
  | Case_aux c "T_Nat"
  | Case_aux c "T_Succ"
  | Case_aux c "T_Pred"
  | Case_aux c "T_Mult"
  | Case_aux c "T_If0"
 ].

Hint Constructors has_type.

End F_CFUN.
