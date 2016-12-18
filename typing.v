(* Coq development underlying the paper
   "Coinductive big-step operational semantics", 
   Xavier Leroy and Hervé Grall, 2007.

   Copyright 2005, 2006, 2007 Institut National de la Recherche en
   Informatique et Automatique.

   This file is distributed under the terms of the GNU Public License
   version 2, http://www.gnu.org/licenses/gpl.html *)

Require Import Classical.
Require Import semantics.

(** The type system **)

CoInductive type : Set :=
  | Tint: type
  | Tarrow: type -> type -> type.

Parameter typenv: Set.
Parameter env_empty: typenv.
Parameter env_get: var -> typenv -> option type.
Parameter env_set: var -> type -> typenv -> typenv.
Axiom env_get_empty: forall v, env_get v env_empty = None.
Axiom env_get_set: forall v1 v2 t e,
  env_get v1 (env_set v2 t e) =
  if var_eq v2 v1 then Some t else env_get v1 e.
Axiom env_exten: forall e1 e2,
  (forall x, env_get x e1 = env_get x e2) -> e1 = e2.

Lemma env_get_set_same: forall v t e,
  env_get v (env_set v t e) = Some t.
Proof. intros. rewrite env_get_set. case (var_eq v v); congruence. Qed.

Lemma env_get_set_other: forall v1 v2 t e,
  v2 <> v1 -> env_get v1 (env_set v2 t e) = env_get v1 e.
Proof. intros. rewrite env_get_set. case (var_eq v2 v1); congruence. Qed.

Inductive has_type: typenv -> term -> type -> Prop :=
  | has_type_var: forall e x t,
      env_get x e = Some t ->
      has_type e (Var x) t
  | has_type_const: forall e n,
      has_type e (Const n) Tint
  | has_type_fun: forall e x a t1 t2,
      has_type (env_set x t1 e) a t2 ->
      has_type e (Fun x a) (Tarrow t1 t2)
  | has_type_app: forall e a b t1 t2,
      has_type e a (Tarrow t1 t2) ->
      has_type e b t1 ->
      has_type e (App a b) t2.

Lemma has_type_weaken:
  forall e a t, has_type e a t ->
  forall e', 
    (forall x tx, env_get x e = Some tx -> env_get x e' = Some tx) ->
    has_type e' a t.
Proof.
  induction 1; intros.
  apply has_type_var. auto. 
  apply has_type_const.
  apply has_type_fun. apply IHhas_type. 
    intros until tx. repeat rewrite env_get_set. 
    case (var_eq x x0); intro. auto. auto. 
  apply has_type_app with t1. auto. auto.
Qed.

Lemma has_type_subst: forall x a ta b tb,
  has_type (env_set x tb env_empty) a ta ->
  has_type env_empty b tb ->
  has_type env_empty (subst x b a) ta.
Proof.
  assert (forall e a ta, has_type e a ta ->
          forall x e1 b tb, 
          (forall y, env_get y e = if var_eq x y then Some tb else env_get y e1) ->
          has_type env_empty b tb ->
          has_type e1 (subst x b a) ta).
    induction 1; intros; simpl.
    generalize (H0 x). 
    case (var_eq x0 x); intro.
    intro. replace t with tb. apply has_type_weaken with env_empty.
    auto. intros until tx. rewrite env_get_empty. congruence.
    congruence.
    intro. apply has_type_var. congruence.
    apply has_type_const.
    apply has_type_fun. 
    case (var_eq x0 x); intro.
      apply has_type_weaken with (env_set x t1 e). auto.
      intros until tx. repeat rewrite env_get_set. case (var_eq x x1); intro.
      auto. rewrite H0. case (var_eq x0 x1); intro. congruence. auto.
      apply IHhas_type with tb; auto.
      intros. repeat rewrite env_get_set. case (var_eq x y); intro.
      case (var_eq x0 y); congruence.
      auto.
    apply has_type_app with t1; eauto.
  intros. eapply H; eauto. 
  intros. apply env_get_set. 
Qed.

(** Type soundness using reduction semantics **)

Lemma red1_preservation:
  forall a b, red1 a b ->
  forall t, has_type env_empty a t -> has_type env_empty b t.
Proof.
  induction 1; intros.
  inversion H0. inversion H4. 
  apply has_type_subst with t1; auto.
  inversion H0. apply has_type_app with t1; eauto.
  inversion H1. apply has_type_app with t1; eauto.
Qed.

Lemma red1_progress:
  forall a t, has_type env_empty a t -> isvalue a \/ exists b, red1 a b.
Proof.
  induction a; intros.
  inversion H. rewrite env_get_empty in H2. discriminate.
  left; constructor.
  left; constructor.
  right. inversion H. subst a; subst b; subst t2.
  elim (IHa1 _ H3).
    (* a1 is a value *)
    intro. elim (IHa2 _ H5).
      (* a2 is a value *)
      intro. inversion H0; subst a1. inversion H3. 
      exists (subst x a2 a). constructor. auto. 
      (* a2 reduces *)
      intros [b2 RED2]. exists (App a1 b2). constructor; auto.
    (* a1 reduces *)
    intros [b1 RED1]. exists (App b1 a2). constructor; auto.
Qed.

Lemma red_preservation:
  forall a b, red a b ->
  forall t, has_type env_empty a t -> has_type env_empty b t.
Proof.
  induction 1; intros.
  auto.
  apply IHred. eapply red1_preservation; eauto. 
Qed.

Lemma soundness1:
  forall a b t,
  has_type env_empty a t -> red a b -> isvalue b \/ exists c, red1 b c.
Proof.
  intros. apply red1_progress with t. apply red_preservation with a; auto. 
Qed.

Lemma soundness2:
  forall a t,
  has_type env_empty a t -> (exists v, red a v /\ isvalue v) \/ redinf a.
Proof.
  intros. elim (red_or_redinf a). 
  intros [b [A B]]. left. exists b. split. auto. 
  elim (soundness1 _ _ _ H A). auto. intros [c RED]. elim (B c). auto.
  tauto.
Qed.

Lemma soundness3:
  forall a t,
  has_type env_empty a t -> exists v, cored a v /\ isvalue v.
Proof.
  intros. elim (soundness2 a t H). 
  intros [v [A B]]. exists v. split. apply red_cored; auto. auto.
  intro. exists (Const zero). split. apply redinf_cored; auto. constructor.
Qed.

CoInductive safered: term -> Prop :=
  | safered_value: forall v,
      isvalue v -> safered v
  | safered_step: forall a b,
      red1 a b -> safered b -> safered a.

Lemma soundness4:
  forall a t,
  has_type env_empty a t -> safered a.
Proof.
  cofix COINDHYP; intros.
  elim (red1_progress a t H). 
  intro. apply safered_value. auto.
  intros [b RED]. apply safered_step with b. auto. 
  apply COINDHYP with t. apply red1_preservation with a; auto. 
Qed.

(** Type soundness using big-step semantics **)

Lemma eval_preservation:
  forall a v, eval a v ->
  forall t, has_type env_empty a t -> has_type env_empty v t.
Proof.
  induction 1; intros.
  auto.
  auto.
  inversion H2.
  assert (has_type env_empty (Fun x c) (Tarrow t1 t)). eauto.
  assert (has_type env_empty vb t1). eauto.
  apply IHeval3. apply has_type_subst with t1.
  inversion H9. auto.
  auto.
Qed.

Lemma eval_or_not_eval:
  forall a, 
  (forall v, ~eval a v) \/ (exists v, eval a v).
Proof.
  intro. elim (classic (forall v, ~eval a v)); intro.
  left; auto.
  right. apply not_all_not_ex. assumption.
Qed.

Lemma evalinf_progress:
  forall a t,
  has_type env_empty a t -> (forall v, ~eval a v) -> evalinf a.
Proof.
  cofix COINDHYP. intros.
  destruct a.
  (* a = Var v: not typeable in empty env *)
  inversion H. rewrite env_get_empty in H3. discriminate.
  (* a = Const c: can evaluate *)
  elim (H0 (Const c)). constructor.
  (* a = Fun v a: can evaluate *)
  elim (H0 (Fun v a)). constructor.
  (* a = App a1 a2: the interesting case *)
  inversion H.
  elim (eval_or_not_eval a1).
    (* a1 does not evaluate *)
    intro. apply evalinf_app_l. 
    apply COINDHYP with (Tarrow t1 t); assumption.
    (* a1 evaluates to v1, which must be a function because of typing *)
    intros [v1 EV1]. 
    assert (has_type env_empty v1 (Tarrow t1 t)).
      eapply eval_preservation; eauto.
    assert (exists x, exists c, v1 = Fun x c).
      assert (isvalue v1). 
      eapply eval_isvalue; eauto.
      inversion H8; subst v1.
      inversion H7.
      exists x; exists a0; auto.
    elim H8; intros x [c EQ]. subst v1.
    elim (eval_or_not_eval a2).
    (* a2 does not evaluate *)
    intro. apply evalinf_app_r with (Fun x c). assumption.
    apply COINDHYP with t1; assumption.
    (* a2 evaluates *)
    intros [v2 EV2].
    elim (eval_or_not_eval (subst x v2 c)).
    (* function call does not evaluate *)
    intro. apply evalinf_app_f with x c v2. assumption. assumption.
    apply COINDHYP with t. 
    apply has_type_subst with t1. inversion H7; auto. 
    eapply eval_preservation; eauto. assumption.
    (* function call evaluates: application evaluates *)
    intros [v EV3]. elim (H0 v).
    apply eval_app with x c v2; auto.
Qed.

Lemma soundness5:
  forall a t,
  has_type env_empty a t -> (exists v, eval a v) \/ evalinf a.
Proof.
  intros. elim (eval_or_not_eval a); intro.
  right. apply evalinf_progress with t; auto. left; assumption.
Qed.

(** Filinski's counterexample to the conjecture **)

Definition vf : var := 1.
Definition vy : var := 2.
Definition vg : var := 3.

Definition Y :=
  Fun vf
    (App (Fun vx (App (Var vf) (App (Var vx) (Var vx))))
         (Fun vx (App (Var vf) (Fun vy (App (App (Var vx) (Var vx))
                                                 (Var vy)))))).

Lemma coeval_const_inv:
  forall n v, coeval (Const n) v -> v = Const n.
Proof.
  intros. inversion H. auto.
Qed.

Lemma coeval_fun_inv1:
  forall x a v, coeval (Fun x a) v -> v = Fun x a.
Proof.
  intros. inversion H. auto.
Qed.

Lemma coeval_fun_inv2:
  forall x a y b, coeval (Fun x a) (Fun y b) -> x = y /\ a = b.
Proof.
  intros; inversion H; split; auto.
Qed.

Lemma coeval_app_inv:
  forall a b v, coeval (App a b) v ->
  exists x, exists c, exists v',
  coeval a (Fun x c) /\ coeval b v' /\ coeval (subst x v' c) v.
Proof.
  intros; inversion H. exists x; exists c; exists vb; tauto.
Qed.

Ltac coevalinv :=
  match goal with
  | [ H: coeval (Const ?n) ?v |- _ ] =>
      let EQ := fresh "EQ" in
      (generalize (coeval_const_inv _ _ H); clear H; intro EQ; try (subst v))
  | [ H: coeval (Fun ?x ?a) (Fun ?y ?b) |- _ ] =>
      let EQ1 := fresh "EQ" in
      let EQ2 := fresh "EQ" in
      (generalize (coeval_fun_inv2 _ _ _ _ H); clear H;
       intros [EQ1 EQ2]; try (subst y); try (subst b))
  | [ H: coeval (Fun ?x ?a) ?v |- _ ] =>
      let EQ := fresh "EQ" in
      (generalize (coeval_fun_inv1 _ _ _ H); clear H;
       intros EQ; try (subst v))
  | [ H: coeval (App _ _) _ |- _ ] =>
      let EV1 := fresh in let EV2 := fresh in let EV3 := fresh in
      let x := fresh "x" in let c := fresh "c" in let v := fresh "v" in
      (generalize (coeval_app_inv _ _ _ H); clear H;
       intros [x [c [v [EV1 [EV2 EV3]]]]])
  end.      

Definition filinski1 :=
  Fun vf (Fun vx (App (Fun vg (Fun vy (App (Var vg) (Var vy))))
                      (App (Var vf) (Var vx)))).

Definition filinski :=
  App (App Y filinski1) (Const zero).

Definition filinski2 :=
       (App
          (App
             (Fun vx
                (App
                   (Fun vf
                      (Fun vx
                         (App (Fun vg (Fun vy (App (Var vg) (Var vy))))
                            (App (Var vf) (Var vx)))))
                   (Fun vy (App (App (Var vx) (Var vx)) (Var vy)))))
             (Fun vx
                (App
                   (Fun vf
                      (Fun vx
                         (App (Fun vg (Fun vy (App (Var vg) (Var vy))))
                            (App (Var vf) (Var vx)))))
                   (Fun vy (App (App (Var vx) (Var vx)) (Var vy))))))
          (Const zero)).

Lemma coeval_filinski_aux:
  forall v,
  coeval filinski2 v ->
  exists v', coeval filinski2 v' /\ v = Fun vy (App v' (Var vy)).
Proof.
  unfold filinski2; intros.
  coevalinv. coevalinv. coevalinv. coevalinv. coevalinv. simpl in H3.
  coevalinv. coevalinv. coevalinv. simpl in H1. coevalinv.
  simpl in H2. coevalinv. coevalinv. 
  exists v0; split.
  Focus 2. simpl in H1. coevalinv. auto.
  coevalinv. coevalinv. coevalinv. simpl in H3. assumption.
Qed.

Require Import Max.
Require Omega.

Fixpoint height_term (a: term) : nat :=
  match a with
  | Var _ => 1
  | Const _ => 1
  | Fun x b => S (height_term b)
  | App b c => S (max (height_term b) (height_term c))
  end.

Lemma not_coeval_filinski:
  forall v, ~(coeval filinski v).
Proof.
  assert (SZ: forall n v, height_term v < n -> coeval filinski2 v -> False).
  induction n; intros.
    assert False. omega. contradiction.
    elim (coeval_filinski_aux _ H0). intros v' [A B].
    apply IHn with v'; auto. 
    subst v. simpl in H. 
    generalize (le_max_l (height_term v') 1). omega.
  unfold not; intros.
  unfold filinski, filinski1, Y in H.
  coevalinv. 
  coevalinv. 
  coevalinv. 
  coevalinv. 
  coevalinv. 
  simpl in H3. coevalinv. 
  coevalinv. 
  coevalinv. 
  simpl in H1. coevalinv. 
  coevalinv. 
  coevalinv. 
  coevalinv. 
  coevalinv. 
  simpl in H4. coevalinv. 
  coevalinv. 
  coevalinv. 
  simpl in H1. coevalinv. 
  simpl in H3. coevalinv. 
  simpl in H2. coevalinv. 
  coevalinv. 
  coevalinv. simpl in H1. 
  coevalinv. 
  coevalinv. 
  simpl in H3. coevalinv. 
  coevalinv. 
  coevalinv. 
  coevalinv. 
  coevalinv. 
  coevalinv. 
  simpl in H3. 
  fold filinski2 in H3. apply SZ with (S (height_term v)) v.
  omega. assumption.
Qed.

