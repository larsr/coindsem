(* Coq development underlying the paper
   "Coinductive big-step operational semantics", 
   Xavier Leroy and Hervé Grall, 2007.

   Copyright 2005, 2006, 2007 Institut National de la Recherche en
   Informatique et Automatique.

   This file is distributed under the terms of the GNU Public License
   version 2, http://www.gnu.org/licenses/gpl.html *)

Require Import Classical.

(** The language **)

Definition var: Set := nat.

Lemma var_eq: forall (v1 v2: var), {v1=v2} + {v1<>v2}.
Proof.
  decide equality.
Defined.

Parameter const: Set.
Parameters zero one: const.

Inductive term: Set :=
  | Var: var -> term
  | Const: const -> term
  | Fun: var -> term -> term
  | App: term -> term -> term.

Fixpoint subst (x: var) (b: term) (a: term) {struct a}: term :=
  match a with
  | Var y => if var_eq x y then b else Var y
  | Const n => Const n
  | Fun y a1 => Fun y (if var_eq x y then a1 else subst x b a1)
  | App a1 a2 => App (subst x b a1) (subst x b a2)
  end.

Inductive isvalue: term -> Prop :=
  | isvalue_const: forall c,
      isvalue (Const c)
  | isvalue_fun: forall x a,
      isvalue (Fun x a).

(** Big-step semantics **)

Inductive eval: term -> term -> Prop :=
  | eval_const: forall c,
      eval (Const c) (Const c)
  | eval_fun: forall x a,
      eval (Fun x a) (Fun x a)
  | eval_app: forall a b x c vb v,
      eval a (Fun x c) ->
      eval b vb ->
      eval (subst x vb c) v ->
      eval (App a b) v.

Lemma eval_isvalue:
  forall a b, eval a b -> isvalue b.
Proof.
  induction 1; intros.
  constructor.
  constructor.
  auto.
Qed.

Lemma eval_deterministic:
  forall a v, eval a v -> forall v', eval a v' -> v' = v.
Proof.
  induction 1; intros.
    inversion H; auto.
    inversion H; auto.
    inversion H2.
      generalize (IHeval1 _ H5); intro. inversion H9. subst x0; subst c0.
      generalize (IHeval2 _ H6); intro. subst vb0.
      auto.
Qed.

Definition vx: var := 0.
Definition delta := Fun vx (App (Var vx) (Var vx)).
Definition omega := App delta delta.

Lemma not_eval_omega:
  forall v, ~(eval omega v).
Proof.
  assert (forall a v, eval a v -> a <> omega).
    induction 1; unfold omega.
    congruence.
    congruence.
    red; intro. injection H2; intros; subst a; subst b. clear H2.
    unfold delta in H. inversion H. subst x; subst c. clear H.
    unfold delta in H0. inversion H0. subst vb; clear H0.
    simpl in IHeval3. fold delta in IHeval3. fold omega in IHeval3. congruence.
  intros; red; intros. 
  elim (H _ _ H0). auto.
Qed.

CoInductive evalinf: term -> Prop :=
  | evalinf_app_l: forall a b,
      evalinf a ->
      evalinf (App a b)
  | evalinf_app_r: forall a b va,
      eval a va ->
      evalinf b ->
      evalinf (App a b)
  | evalinf_app_f: forall a b x c vb,
      eval a (Fun x c) ->
      eval b vb ->
      evalinf (subst x vb c) ->
      evalinf (App a b).

CoFixpoint evalinf_omega_1: evalinf omega :=
  let eval_delta : eval delta delta :=
    (eval_fun vx (App (Var vx) (Var vx))) in 
  evalinf_app_f delta delta vx (App (Var vx) (Var vx)) delta
    eval_delta
    eval_delta
    evalinf_omega_1.

Lemma evalinf_omega: evalinf omega.
Proof.
  cofix COINDHYP. unfold omega. eapply evalinf_app_f.
  unfold delta. apply eval_fun. 
  unfold delta. apply eval_fun.
  simpl. fold delta. fold omega. apply COINDHYP.
Qed.

Lemma eval_evalinf_exclusive:
  forall a v, eval a v -> evalinf a -> False.
Proof.
  induction 1; intros.
  inversion H.
  inversion H.
  inversion H2; auto.
    generalize (eval_deterministic _ _ H _ H5); intro. 
    inversion H8; subst x0; subst c0.
    generalize (eval_deterministic _ _ H0 _ H6); intro. subst vb0.
    auto.
Qed.

CoInductive coeval: term -> term -> Prop :=
  | coeval_const: forall c,
      coeval (Const c) (Const c)
  | coeval_fun: forall x a,
      coeval (Fun x a) (Fun x a)
  | coeval_app: forall a b x c vb v,
      coeval a (Fun x c) ->
      coeval b vb ->
      coeval (subst x vb c) v ->
      coeval (App a b) v.

Lemma eval_coeval:
  forall a v, eval a v -> coeval a v.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma coeval_omega: forall v, coeval omega v.
Proof.
  cofix COINDHYP. intro; unfold omega. eapply coeval_app.
  unfold delta. apply coeval_fun. 
  unfold delta. apply coeval_fun.
  simpl. fold delta. fold omega. apply COINDHYP.
Qed.

Lemma coeval_noteval_evalinf:
  forall a v, coeval a v -> ~(eval a v) -> evalinf a.
Proof.
  cofix COINDHYP. intros.
  inversion H. 
  subst a; subst v. elim H0. constructor.
  subst a; subst v. elim H0. constructor.
  elim (classic (eval a0 (Fun x c))); intro.
  elim (classic (eval b vb)); intro.
  elim (classic (eval (subst x vb c) v)); intro.
  elim H0. subst a. econstructor; eauto.
  eapply evalinf_app_f; eauto.
  eapply evalinf_app_r; eauto.
  eapply evalinf_app_l; eauto.
Qed.

Lemma coeval_eval_or_evalinf:
  forall a v, coeval a v -> eval a v \/ evalinf a.
Proof.
  intros. elim (classic (eval a v)); intro.
  left; auto.
  right. eapply coeval_noteval_evalinf; eauto.
Qed.

Lemma not_evalinf_coeval:
  ~(forall a, evalinf a -> exists v, coeval a v).
Proof.
  set (a := App omega (App (Const zero) (Const zero))).
  assert (evalinf a).
    unfold a. apply evalinf_app_l. apply evalinf_omega. 
  assert (forall v, ~(coeval a v)).
    unfold a; intro; red; intro. 
    inversion H0. inversion H4. inversion H9.
  red; intro. generalize (H1 a H). intros [v CO]. apply H0 with v; auto.
Qed.

Lemma eval_coeval_deterministic:
  forall a v, eval a v -> forall v', coeval a v' -> v' = v.
Proof.
  induction 1; intros.
  inversion H; auto.
  inversion H; auto.
  inversion H2. 
    generalize (IHeval1 _ H5); intro. inversion H9; subst x0; subst c0.
    generalize (IHeval2 _ H6); intro. subst vb0.
    auto.
Qed.

Lemma coeval_zerofun_omega:
  forall v, coeval (App (Fun vx (Const zero)) omega) v -> v = Const zero.
Proof.
  intros. inversion H. inversion H2. subst c. simpl in H5. 
  inversion H5. auto.
Qed.

(** Small-step semantics **)

Inductive red1: term -> term -> Prop :=
  | red1_beta: forall x a v,
      isvalue v ->
      red1 (App (Fun x a) v) (subst x v a)
  | red1_app_l: forall a1 a2 b,
      red1 a1 a2 ->
      red1 (App a1 b) (App a2 b)
  | red1_app_r: forall v b1 b2,
      isvalue v ->
      red1 b1 b2 ->
      red1 (App v b1) (App v b2).

Definition notred (a: term) : Prop := forall b, ~(red1 a b).

Lemma value_notred:
  forall a, isvalue a -> notred a.
Proof.
  induction 1; unfold notred; intros; red; intros; inversion H.
Qed.

Lemma red1_deterministic:
  forall a b, red1 a b -> forall c, red1 a c -> c = b.
Proof.
  induction 1; intros.
  inversion H0. auto. inversion H4. elim (value_notred v H b2 H5). 
  inversion H0. subst a1. inversion H. rewrite (IHred1 _ H4). auto.
    elim (value_notred a1 H3 a2 H).
  inversion H1. elim (value_notred b1 H5 b2 H0). 
    elim (value_notred v H a2 H5). 
    rewrite (IHred1 _ H6). auto.
Qed.

Inductive red: term -> term -> Prop :=
  | red_refl: forall a,
      red a a
  | red_step: forall a b c,
      red1 a b -> red b c -> red a c.

Lemma red_one: forall a b, red1 a b -> red a b.
Proof.
  intros. apply red_step with b. auto. apply red_refl.
Qed.

Lemma red_trans: forall a b c, red a b -> red b c -> red a c.
Proof.
  induction 1; intros. auto. apply red_step with b; auto. 
Qed.

CoInductive redinf: term -> Prop :=
  | redinf_intro: forall a b,
      red1 a b -> redinf b -> redinf a.

CoInductive cored: term -> term -> Prop :=
  | cored_refl: forall a,
      cored a a
  | cored_step: forall a b c,
      red1 a b -> cored b c -> cored a c.

Lemma cored_trans:
  forall a b c, cored a b -> cored b c -> cored a c.
Proof.
  cofix COINDHYP; intros.
  inversion H.
  assumption.
  apply cored_step with b0. auto. apply COINDHYP with b; auto.
Qed.

Lemma red_cored:
  forall a b, red a b -> cored a b.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma redinf_cored:
  forall a b, redinf a -> cored a b.
Proof.
  cofix COINDHYP. intros.
  inversion H. apply cored_step with b0; auto.
Qed.

Lemma cored_notred_redinf:
  forall a b, cored a b -> ~(red a b) -> redinf a.
Proof.
  cofix COINDHYP.
  intros. inversion H. subst b. elim H0. constructor.
  apply redinf_intro with b0. assumption.
  apply COINDHYP with b. assumption.
  red; intro. elim H0. apply red_step with b0; assumption.
Qed.

Lemma cored_red_or_redinf:
  forall a b, cored a b <-> red a b \/ redinf a.
Proof.
  intros. split; intro.
  elim (classic (red a b)); intro.
  left; auto.
  right. apply cored_notred_redinf with b; auto.
  elim H; intro. apply red_cored; auto. eapply redinf_cored; eauto.
Qed.

(** Connections between big-step and small-step semantics *)

Lemma red_app_l:
   forall a1 a2 b, red a1 a2 -> red (App a1 b) (App a2 b).
Proof.
  induction 1; intros. 
  apply red_refl.
  apply red_step with (App b0 b). apply red1_app_l; auto. auto.
Qed.

Lemma red_app_r:
   forall v a1 a2 , isvalue v -> red a1 a2 -> red (App v a1) (App v a2).
Proof.
  induction 2; intros. 
  apply red_refl.
  apply red_step with (App v b). apply red1_app_r; auto. auto.
Qed.

Lemma eval_red:
  forall a v, eval a v -> red a v.
Proof.
  induction 1.
  apply red_refl.
  apply red_refl.
  apply red_trans with (App (Fun x c) b).
    apply red_app_l. assumption.
  apply red_trans with (App (Fun x c) vb).
    apply red_app_r. constructor. assumption.
  apply red_trans with (subst x vb c).
    apply red_one. apply red1_beta. eapply eval_isvalue; eauto. 
  assumption.
Qed.

Lemma eval_value:
  forall v, isvalue v -> eval v v.
Proof.
  induction 1; intros. apply eval_const. apply eval_fun.
Qed.

Lemma red1_eval:
  forall a b, red1 a b -> forall v, eval b v -> eval a v.
Proof.
  induction 1; intros.
  eapply eval_app. apply eval_fun. apply eval_value; auto. assumption.
  inversion H0. eapply eval_app; eauto. 
  inversion H1. eapply eval_app; eauto. 
Qed.

Lemma red_eval:
  forall a v, red a v -> isvalue v -> eval a v.
Proof.
  induction 1; intros.
  apply eval_value. assumption.
  eapply red1_eval; eauto.
Qed.

Lemma infinite_progress_redinf:
  forall a,
  (forall b, red a b -> exists c, red1 b c) ->
  redinf a.
Proof.
  cofix COINDHYP; intros.
  assert (exists b, red1 a b). apply H. constructor. 
  elim H0; intros. apply redinf_intro with x. assumption. 
  apply COINDHYP. intros. 
  apply H. econstructor; eauto.
Qed.

Lemma red_or_redinf:
  forall a,
  (exists b, red a b /\ notred b) \/ redinf a.
Proof.
  intro. elim (classic (redinf a)); intro.
  right; assumption.
  left. 
  assert (~(forall b, red a b -> exists c, red1 b c)).
    red; intro. elim H. apply infinite_progress_redinf. assumption.
  generalize (not_all_ex_not term (fun b => red a b -> exists c, red1 b c) H0).
  intros [b A]. elim (imply_to_and _ _ A). intros. 
  exists b. split. assumption. 
  unfold notred. apply not_ex_all_not. assumption.
Qed.

Lemma evalinf_red1:
  forall a, evalinf a -> exists b, red1 a b /\ evalinf b.
Proof.
  induction a; intros; inversion H.
  (* function part evaluates infinitely *)
  elim (IHa1 H1). intros a1' [R E]. 
  exists (App a1' a2). split.
  constructor; auto.
  apply evalinf_app_l; auto.  
  (* function part evaluates finitely,
     argument evaluates infinitely *)
  elim (IHa2 H3). intros a2' [R E].
  generalize (eval_red _ _ H2). intro. inversion H4.
    (* function part was already a value *)
    exists (App va a2'). split.
    constructor.  eapply eval_isvalue; eauto. auto.
    apply evalinf_app_r with va. 
    apply eval_value. eapply eval_isvalue; eauto. auto.
    (* function part evaluates *)
    exists (App b0 a2). split. 
    constructor. auto.
    apply evalinf_app_r with va. 
    apply red_eval; auto. eapply eval_isvalue; eauto.
    auto.
  (* function and argument parts evaluate finitely,
     beta-redex evaluates infinitely *)
  generalize (eval_red _ _ H2). intro. inversion H5.
    (* function part was already a value *)
    generalize (eval_red _ _ H3). intro. inversion H8.
      (* argument part was already a value *)
      exists (subst x vb c). split.
      constructor. eapply eval_isvalue; eauto.
      auto.
      (* argument part reduces *)
      exists (App (Fun x c) b0). split.
      constructor. constructor. auto.
      apply evalinf_app_f with x c vb.
      constructor. 
      apply red_eval; auto. eapply eval_isvalue; eauto.
      auto.
    (* function part reduces *)
    exists (App b0 a2). split.
    constructor. auto.
    apply evalinf_app_f with x c vb.
    apply red_eval; auto. constructor.
    auto. auto.
Qed.

Lemma evalinf_redinf:
  forall a, evalinf a -> redinf a.
Proof.
  cofix COINDHYP. intros. 
  elim (evalinf_red1 _ H). intros b [R E].
  apply redinf_intro with b. auto. apply COINDHYP. auto.
Qed.

Lemma redinf_app_l:
  forall a a', red a a' ->
  forall b, redinf (App a b) -> redinf (App a' b).
Proof.
  induction 1; intros. assumption. 
  apply IHred. inversion H1. 
  replace (App b b0) with b1. assumption. 
  apply red1_deterministic with (App a b0); auto.
  constructor; auto.
Qed.

Lemma redinf_app_r:
  forall b b', red b b' ->
  forall a, isvalue a -> redinf (App a b) -> redinf (App a b').
Proof.
  induction 1; intros. assumption.
  apply IHred. auto. inversion H2. 
  replace (App a0 b) with b0. assumption. 
  apply red1_deterministic with (App a0 a); auto.
  constructor; auto.
Qed.

Lemma redinf_evalinf:
  forall a, redinf a -> evalinf a.
Proof.
  cofix COINDHYP.
  intros. 
  destruct a; try (inversion H; inversion H0; fail).
  elim (red_or_redinf a1). 
  (* a1 evaluates finitely *)
  intros [n1 [REDM1 NOTRED1]]. 
  generalize (redinf_app_l _ _ REDM1 _ H). intro REDINF1.
  assert (ISVAL1: isvalue n1). 
    inversion REDINF1. inversion H0.
    constructor.
    elim (NOTRED1 _ H6).
    assumption.
  elim (red_or_redinf a2).
  (* a2 evaluates finitely as well *)
  intros [n2 [REDM2 NOTRED2]].
  generalize (redinf_app_r _ _ REDM2 _ ISVAL1 REDINF1). intro REDINF2.
  assert (exists x, exists c,
            n1 = Fun x c /\ isvalue n2 /\ redinf (subst x n2 c)).
    inversion REDINF2. inversion H0.
    subst b. exists x; exists a0. tauto.
    elim (NOTRED1 _ H6).
    elim (NOTRED2 _ H7).
  elim H0; intros x [c [A [B C]]]. subst n1; clear H0.
  apply evalinf_app_f with x c n2. 
    apply red_eval; assumption.
    apply red_eval; assumption.
    apply COINDHYP. assumption.
  (* a2 evaluates infinitely *)
  intro REDINF2. apply evalinf_app_r with n1. 
    apply red_eval; assumption.
    apply COINDHYP. assumption.
  (* a1 evaluates infinitely *)
  intro REDINF1. apply evalinf_app_l. 
    apply COINDHYP. assumption.
Qed.

Lemma coeval_value:
  forall a v, isvalue a -> coeval a v -> a = v.
Proof.
  intros. inversion H; subst a; inversion H0; auto.
Qed.

Lemma coeval_value_or_red1:
  forall a v, coeval a v ->
  isvalue a \/ exists b, red1 a b /\ coeval b v.
Proof.
  induction a; intros; inversion H.
  (* constant *)
  left; constructor.
  (* function *)
  left; constructor.
  (* application *)
    subst a; subst b; subst v0. right.
    generalize (IHa1 _ H2). intros [ISVAL1 | [a1' [RED1 EVAL1]]].
    (* function part is a value *)
    generalize (coeval_value _ _ ISVAL1 H2); intro; subst a1.
    generalize (IHa2 _ H3). intros [ISVAL2 | [a2' [RED2 EVAL2]]].
    (* argument part is a value *)    
    generalize (coeval_value _ _ ISVAL2 H3); intro; subst a2.
    exists (subst x vb c). split. 
    apply red1_beta. auto.
    auto.
    (* argument part reduces *)
    exists (App (Fun x c) a2'). split.
    apply red1_app_r. auto. auto.
    eapply coeval_app; eauto.
    (* function part reduces *)
    exists (App a1' a2). split.
    apply red1_app_l. auto.
    eapply coeval_app; eauto.
Qed.

Lemma coeval_cored:
  forall a v, coeval a v -> cored a v.
Proof.
  cofix COINDHYP; intros.
  generalize (coeval_value_or_red1 a v H).
  intros [ISVAL | [b [RED COEV]]].
  generalize (coeval_value _ _ ISVAL H); intro; subst a.
  apply cored_refl.
  apply cored_step with b. assumption. apply COINDHYP. assumption.
Qed.

Lemma not_cored_coeval:
  ~(forall a b, cored a b -> isvalue b -> coeval a b).
Proof.
  red; intro.
  pose (id := Fun vx (Var vx)).
  pose (omega0 := App (Fun vx (Const zero)) omega).
  assert (cored omega0 id). 
    apply redinf_cored. apply evalinf_redinf.
    unfold omega0. eapply evalinf_app_r. constructor.
    apply evalinf_omega.
  assert (isvalue id). unfold id; constructor.
  assert (coeval omega0 id). auto.
  generalize (coeval_zerofun_omega _ H2). unfold id. congruence.
Qed.

