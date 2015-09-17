Require Export SfLib.

Module STLC_CFUN.

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat   : ty.

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tcap : id -> ty -> tm -> tm        (* capsule lambda *)
  | tnat  : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp"
    | Case_aux c "tabs" | Case_aux c "tnat"
    | Case_aux c "tcap" | Case_aux c "tsucc"
    | Case_aux c "tpred" | Case_aux c "tmult"
    | Case_aux c "tif0" ].

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_caps : forall x T t,
      value (tcap x T t)
  | v_nat : forall (n:nat),
      value (tnat n).

Hint Constructors value.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' =>
      if eq_id_dec x x' then s else t
  | tabs x' T t1 =>
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1))
  | tcap x' T t1 =>
      t
  | tapp t1 t2 =>
      tapp ([x:=s] t1) ([x:=s] t2)
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

where "'[' x ':=' s ']' t" := (subst x s t).

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_AppCap : forall x T t12 v2,
         value v2 ->
         (tapp (tcap x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tapp v1 t2 ==> tapp v1  t2'
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
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_AppCap"
    | Case_aux c "ST_App1" | Case_aux c "ST_App2"
    | Case_aux c "ST_Succ" | Case_aux c "ST_SuccNat"
    | Case_aux c "ST_Pred" | Case_aux c "ST_PredNat"
    | Case_aux c "ST_PredZero" | Case_aux c "ST_MultNatNat"
    | Case_aux c "ST_Mult1" | Case_aux c "ST_Mult2"
    | Case_aux c "ST_If0True" | Case_aux c "ST_If0False"
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
  | T_Cap : forall Gamma x T11 T12 t12,
      extend empty x T11 |- t12 \in T12 ->
      Gamma |- tcap x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- tapp t1 t2 \in T12
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
  [ Case_aux c "T_Var" | Case_aux c "T_Abs"
    | Case_aux c "T_Cap" | Case_aux c "T_App"
    | Case_aux c "T_Nat" | Case_aux c "T_Succ"
    | Case_aux c "T_Pred" | Case_aux c "T_Mult"
    | Case_aux c "T_If0"
 ].

Hint Constructors has_type.

Lemma canonical_forms_nat : forall t,
  empty |- t \in TNat ->
  value t ->
  exists n, t = tnat n.
Proof with eauto.
  intros t HT HVal.
  inversion HVal; subst; try inversion HT...
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u \/ t = tcap x T1 u.
Proof with eauto.
  intros t T1 T2 HT HVal.
  inversion HVal; subst.
  Case "v_abs".
    inversion HT. subst...
  Case "v_cap".
    inversion HT. subst...
  Case "v_nat".
    inversion HT.
Qed.

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T H1. remember empty as Gamma.
  has_type_cases(induction H1) Case; try(subst Gamma)...
  Case "T_Var".
    unfold empty in H. inversion H.
  Case "T_App". right.
    destruct IHhas_type1...
    SCase "value t1".
      destruct IHhas_type2...
      SSCase "value t2".
        destruct (canonical_forms_fun t1 T11 T12 H1_ H)...
        destruct H1 as [t [H1 | H1]].
        exists ([x:=t2] t).  rewrite H1...
        exists ([x:=t2] t).  rewrite H1...
      SSCase "t2 ==> t2'".
        destruct H0 as [t2' H0']...
    SCase "t1 ==> t1'".
      destruct H as [t1' H]...
  Case "T_Succ". right.
    destruct IHhas_type...
    SCase "value t1".
      destruct (canonical_forms_nat t1 H1 H) as [n H3]...
      exists (tnat (S n))...
      rewrite H3...
    SCase "t1 ==> t1'".
      destruct H as [t1' H]...
  Case "T_Pred". right.
    destruct IHhas_type...
    SCase "value t1".
      destruct (canonical_forms_nat t1 H1 H) as [n H3]...
      rewrite H3. destruct n...
    SCase "t1 ==> t1'".
      destruct H as [t1' H]...
  Case "T_Mult". right.
    destruct IHhas_type1...
    SCase "value t1".
      destruct IHhas_type2...
      SSCase "value t2".
        destruct (canonical_forms_nat t1 H1_ H) as [n H3]...
        destruct (canonical_forms_nat t2 H1_0 H0) as [m H4]...
        subst...
      SSCase "t2 ==> t2'".
        destruct H0 as [t2' H0]...
    SCase "t1 ==> t1'".
      destruct H as [t1' H]...
  Case "T_If0". right.
    destruct IHhas_type1...
    SCase "value t1".
      destruct (canonical_forms_nat t1 H1_ H) as [n H4]...
      rewrite H4. destruct n...
    SCase "t1 ==> t1'".
      destruct H as [t1' H]...
Qed.

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_cap : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tcap y T11 t12)
  | afi_succ : forall x t1,
      appears_free_in x t1 ->
      appears_free_in x (tsucc t1)
  | afi_pred : forall x t1,
      appears_free_in x t1 ->
      appears_free_in x (tpred t1)
  | afi_mult1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tmult t1 t2)
  | afi_mult2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tmult t1 t2)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif0 t1 t2 t3).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2"
  | Case_aux c "afi_abs"
  | Case_aux c "afi_cap"
  | Case_aux c "afi_succ"
  | Case_aux c "afi_pred"
  | Case_aux c "afi_mult1" | Case_aux c "afi_mult2"
  | Case_aux c "afi_if1" | Case_aux c "afi_if2"
  | Case_aux c "afi_if3" ].

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  afi_cases (induction H) Case;
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
  Case "afi_cap".
    inversion H1. subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; eauto.
    destruct H7 as [T H7]. inversion H7.
Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  has_type_cases (induction H) Case; intros; auto.
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to
       instantiate is [extend Gamma x T11] *)
    unfold extend. destruct (eq_id_dec x x1)...
  Case "T_App".
    apply T_App with T11...
Qed.

Lemma context_reorder : forall Gamma x y U V t T,
   x <> y ->
   (extend (extend Gamma x U) y V |- t \in T <->
    extend (extend Gamma y V) x U |- t \in T).
Proof with (eauto using extend_eq, extend_neq).
  intros. split; intros H1.
  Case "->".
    apply context_invariance with (extend (extend Gamma x U) y V)...
    intros. destruct (eq_id_dec x0 y).
    SCase "x0 = y".
      rewrite e. rewrite extend_eq. rewrite extend_neq...
    SCase "x0 <> y".
      rewrite extend_neq...
      destruct (eq_id_dec x0 x).
      SSCase "x0 = x".
        rewrite e. rewrite extend_eq...
      SSCase "x0 <> x".
        repeat(rewrite extend_neq)...
  Case "<-".
    apply context_invariance with (extend (extend Gamma y V) x U)...
    intros. destruct (eq_id_dec x0 x).
    SCase "x0 = x".
      rewrite e. rewrite extend_eq.
      rewrite extend_neq...
    SCase "x0 <> x".
      rewrite extend_neq...
      destruct (eq_id_dec x0 y).
      SSCase "x0 = y".
        rewrite e. rewrite extend_eq...
      SSCase "x0 <> y".
        repeat(rewrite extend_neq)...
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     extend Gamma x U |- t \in T ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in T.
Proof with eauto.
  intros. generalize dependent Gamma.
  generalize dependent T.
  t_cases(induction t) Case; intros; try(inversion H; subst; simpl)...
  Case "tvar".
    destruct (eq_id_dec x i)...
    SCase "x = i".
      rewrite e in H.
      inversion H. subst.
      rewrite extend_eq in H3. inversion H3.
      rewrite <- H2. apply context_invariance with empty...
      intros. apply (free_in_context x v U empty) in H1...
      destruct H1. solve by inversion.
    SCase "x <> i".
      inversion H. subst.
      rewrite extend_neq in H3...
  Case "tabs".
    destruct (eq_id_dec x i).
    SCase "x = i".
      apply context_invariance with (extend Gamma x U)...
      intros. inversion H1. subst.
      rewrite extend_neq...
    SCase "x <> i".
      inversion H. subst.
      apply T_Abs. apply (IHt T12).
      eapply context_reorder...
Qed.

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T H1 H2. generalize dependent T.
  step_cases(induction H2) Case; intros U H3;
    try(inversion H3; subst; eauto).
  Case "ST_AppAbs".
    inversion H4; subst.
    apply substitution_preserves_typing with (U := T11)...
  Case "ST_AppCap".
    inversion H4; subst.
    apply substitution_preserves_typing with (U := T11)...
Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros. unfold stuck. intros H1.
  destruct H1. induction H0; subst.
  Case "refl".
    apply progress in H. destruct H; auto.
  Case "step".
    apply IHmulti; try(apply preservation with x); eauto.
Qed.

End STLC_CFUN.
