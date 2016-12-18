(* Coq development underlying the paper
   "Coinductive big-step operational semantics", 
   Xavier Leroy and Hervé Grall, 2007.

   Copyright 2005, 2006, 2007 Institut National de la Recherche en
   Informatique et Automatique.

   This file is distributed under the terms of the GNU Public License
   version 2, http://www.gnu.org/licenses/gpl.html *)

Require Import List.
Require Import Omega.

(** Syntax and big-step semantics with de Bruijn indices,
    closures, and environments. **)

Parameter const: Set.

Inductive term: Set :=
  | Var: nat -> term
  | Const: const -> term
  | Fun: term -> term
  | App: term -> term -> term.

Inductive value: Set :=
  | Int: const -> value
  | Clos: term -> list value -> value.

Definition env := list value.

Inductive eval: env -> term -> value -> Prop :=
  | eval_Var: forall e n v,
      nth_error e n = Some v ->
      eval e (Var n) v
  | eval_Const: forall e i,
      eval e (Const i) (Int i)
  | eval_Fun: forall e a,
      eval e (Fun a) (Clos a e)
  | eval_App: forall e a b ca ea vb v,
      eval e a (Clos ca ea) ->
      eval e b vb ->
      eval (vb :: ea) ca v ->
      eval e (App a b) v.

CoInductive evalinf: env -> term -> Prop :=
  | evalinf_App_l: forall e a b,
      evalinf e a ->
      evalinf e (App a b)
  | evalinf_App_r: forall e a b v,
      eval e a v ->
      evalinf e b ->
      evalinf e (App a b)
  | evalinf_App_f: forall e a b ca ea vb,
      eval e a (Clos ca ea) ->
      eval e b vb ->
      evalinf (vb :: ea) ca ->
      evalinf e (App a b).

CoInductive coeval: env -> term -> value -> Prop :=
  | coeval_Var: forall e n v,
      nth_error e n = Some v ->
      coeval e (Var n) v
  | coeval_Const: forall e i,
      coeval e (Const i) (Int i)
  | coeval_Fun: forall e a,
      coeval e (Fun a) (Clos a e)
  | coeval_App: forall e a b ca ea vb v,
      coeval e a (Clos ca ea) ->
      coeval e b vb ->
      coeval (vb :: ea) ca v ->
      coeval e (App a b) v.

(** Abstract machine and compilation scheme **)

Inductive instr: Set :=
  | INop: instr
  | IVar: nat -> instr
  | IConst: const -> instr
  | IClosure: list instr -> instr
  | IApp: instr
  | IReturn: instr.

Definition code := list instr.

Fixpoint compile (a: term) (k: code) {struct a} : code :=
  match a with
  | Var n => IVar n :: k
  | Const i => IConst i :: k
  | Fun b => IClosure (compile b (IReturn :: nil)) :: k
  | App b c => (*INop ::*) compile b (compile c (IApp :: k))
  end.

Inductive mvalue: Set :=
  | MInt: const -> mvalue
  | MClos: code -> list mvalue -> mvalue.

Definition menv := list mvalue.

Inductive slot : Set :=
  | Slot_value: mvalue -> slot
  | Slot_return: code -> menv -> slot.

Definition stack := list slot.

Inductive transition: code -> menv -> stack ->
                      code -> menv -> stack -> Prop :=
  | trans_INop: forall k e s,
      transition (INop :: k) e s
                 k e s
  | trans_IVar: forall n k e s v,
      nth_error e n = Some v ->
      transition (IVar n :: k) e s
                 k e (Slot_value v :: s)
  | trans_IConst: forall n k e s,
      transition (IConst n :: k) e s
                 k e (Slot_value (MInt n) :: s)
  | trans_IClosure: forall c k e s,
      transition (IClosure c :: k) e s 
                 k e (Slot_value (MClos c e) :: s)
  | trans_IApp: forall k e v k' e' s,
      transition (IApp :: k) e (Slot_value v :: Slot_value (MClos k' e') :: s)
                 k' (v :: e') (Slot_return k e :: s)
  | trans_IReturn: forall k e v k' e' s,
      transition (IReturn :: k) e (Slot_value v :: Slot_return k' e' :: s)
                 k' e' (Slot_value v :: s).

(* Zero, one or several transitions *)
Inductive trans: code -> menv -> stack ->
                  code -> menv -> stack -> Prop :=
  | trans_refl: forall k1 e1 s1,
      trans k1 e1 s1 k1 e1 s1
  | trans_step: forall k1 e1 s1 k2 e2 s2 k3 e3 s3,
      transition k1 e1 s1 k2 e2 s2 ->
      trans k2 e2 s2 k3 e3 s3 ->
      trans k1 e1 s1 k3 e3 s3.

(* One or several transitions *)
Inductive transplus: code -> menv -> stack ->
                     code -> menv -> stack -> Prop :=
  | transplus_base: forall k1 e1 s1 k2 e2 s2,
      transition k1 e1 s1 k2 e2 s2 ->
      transplus k1 e1 s1 k2 e2 s2
  | transplus_step: forall k1 e1 s1 k2 e2 s2 k3 e3 s3,
      transition k1 e1 s1 k2 e2 s2 ->
      transplus k2 e2 s2 k3 e3 s3 ->
      transplus k1 e1 s1 k3 e3 s3.

Lemma transplus_transitive:
  forall k1 e1 s1 k2 e2 s2 k3 e3 s3,
  transplus k1 e1 s1 k2 e2 s2 ->
  transplus k2 e2 s2 k3 e3 s3 ->
  transplus k1 e1 s1 k3 e3 s3.
Proof.
  induction 1; intros; eapply transplus_step; eauto.
Qed.

Lemma transplus_trans:
  forall k1 e1 s1 k2 e2 s2,
  transplus k1 e1 s1 k2 e2 s2 ->
  trans k1 e1 s1 k2 e2 s2.
Proof.
  induction 1; eapply trans_step; eauto. apply trans_refl.
Qed.

(* Infinitely many transitions *)
CoInductive transinf: code -> menv -> stack -> Prop :=
  | transinf_intro: forall k1 e1 s1 k2 e2 s2,
      transition k1 e1 s1 k2 e2 s2 ->
      transinf k2 e2 s2 ->
      transinf k1 e1 s1.

(* Same, with a finite number of stuttering steps *)
CoInductive transinfN: nat -> code -> menv -> stack -> Prop :=
  | transinfN_stutter: forall n k e s,
      transinfN n k e s ->
      transinfN (S n) k e s
  | transinfN_perform: forall n1 k1 e1 s1 n2 k2 e2 s2,
      transplus k1 e1 s1 k2 e2 s2 ->
      transinfN n2 k2 e2 s2 ->
      transinfN n1 k1 e1 s1.

Lemma decompose_transinfN:
  forall n k e s,
  transinfN n k e s ->
  exists n', exists k', exists e', exists s',
  transition k e s k' e' s' /\ transinfN n' k' e' s'.
Proof.
  intros until s.
  assert (
    forall m n, m > n ->
    transinfN n k e s ->
    exists n', exists k', exists e', exists s',
    transition k e s k' e' s' /\ transinfN n' k' e' s').
  induction m; intros.
  cut False; [contradiction | omega].
  inversion H0. 
  (* No transition, use induction hypothesis *)
  eapply IHm; eauto. omega.
  (* One transition, we're done *)
  inversion H1. 
  exists n2; exists k2; exists e2; exists s2.
  split. assumption. assumption.
  (* Several transitions, we're done *)
  exists 0; exists k3; exists e3; exists s3.
  split. assumption. eapply transinfN_perform; eauto.
  (* Use inductive assert *)
  intros; eauto.
Qed.

Lemma transinfN_transinf:
  forall n k e s,
  transinfN n k e s -> transinf k e s.
Proof.
  cofix COINDHYP; intros.
  generalize (decompose_transinfN _ _ _ _ H).
  intros [n' [k' [e' [s' [T TINF]]]]].
  apply transinf_intro with k' e' s'. assumption. 
  apply COINDHYP with n'; assumption.
Qed.

(* Zero, one, several or infinitely many transitions *)

CoInductive cotrans: code -> menv -> stack ->
                     code -> menv -> stack -> Prop :=
  | cotrans_refl: forall k e s,
      cotrans k e s k e s
  | cotrans_step: forall k1 e1 s1 k2 e2 s2 k3 e3 s3,
      transition k1 e1 s1 k2 e2 s2 ->
      cotrans k2 e2 s2 k3 e3 s3 ->
      cotrans k1 e1 s1 k3 e3 s3.

CoInductive cotransN: nat -> code -> menv -> stack ->
                      code -> menv -> stack -> Prop :=
  | cotransN_perform: forall n k1 e1 s1 k2 e2 s2,
      transition k1 e1 s1 k2 e2 s2 ->
      cotransN n k1 e1 s1 k2 e2 s2
  | cotransN_trans: forall n n' k1 e1 s1 k2 e2 s2 k3 e3 s3,
      cotransN n k1 e1 s1 k2 e2 s2 ->
      cotransN n' k2 e2 s2 k3 e3 s3 ->
      cotransN (S n) k1 e1 s1 k3 e3 s3.

Lemma decompose_cotransN:
  forall n k1 e1 s1 k3 e3 s3,
  cotransN n k1 e1 s1 k3 e3 s3 ->
  transition k1 e1 s1 k3 e3 s3 \/
  exists k2, exists e2, exists s2, exists n2,
  transition k1 e1 s1 k2 e2 s2 /\ cotransN n2 k2 e2 s2 k3 e3 s3.
Proof.
  induction n; intros.
  (* n = 0 *)
  inversion H. left. auto.
  (* n = S n' *)
  inversion H. left. auto.
  right. 
  elim (IHn _ _ _ _ _ _ H1).
  intros. exists k2; exists e2; exists s2; exists n'. split. auto. auto.
  intros [k' [e' [s' [n'' [A B]]]]]. 
  exists k'; exists e'; exists s'; exists (S n''). split. auto.
  eapply cotransN_trans; eauto.
Qed.

Lemma cotransN_cotrans:
  forall n k1 e1 s1 k2 e2 s2,
  cotransN n k1 e1 s1 k2 e2 s2 ->
  cotrans k1 e1 s1 k2 e2 s2.
Proof.
  cofix COINDHYP.
  intros. elim (decompose_cotransN _ _ _ _ _ _ _ H).
  intro. eapply cotrans_step. eauto. apply cotrans_refl.
  intros [k' [e' [s' [n' [A B]]]]].
  apply cotrans_step with k' e' s'. assumption.
  apply COINDHYP with n'. assumption.
Qed.

(** Compiler correctness, terminating programs **)

Fixpoint compile_value (v: value) : mvalue :=
  match v with
  | Int n => MInt n
  | Clos a e =>
      let fix compenv (e: env) : menv :=
        match e with
        | nil => nil
        | v :: e' => compile_value v :: compenv e'
        end in
      MClos (compile a (IReturn :: nil)) (compenv e)
  end.

Fixpoint compile_env (e: env) : menv :=
   match e with
   | nil => nil
   | v :: e' => compile_value v :: compile_env e'
   end.

Lemma find_var_match:
  forall e n v,
  nth_error e n = Some v ->
  nth_error (compile_env e) n = Some (compile_value v).
Proof.
  induction e; destruct n; simpl; intros.
  discriminate.
  discriminate.
  unfold Specif.value in *; congruence.
  auto.
Qed.

Lemma compile_eval:
  forall e a v,
  eval e a v ->
  forall k s,
  transplus (compile a k) (compile_env e) s
            k (compile_env e) (Slot_value (compile_value v) :: s).
Proof.
  induction 1; simpl; intros.
  (* Var *)
  apply transplus_base. constructor. apply find_var_match; auto.
  (* Const *)
  apply transplus_base. constructor. 
  (* Closure *)
  apply transplus_base. constructor. 
  (* App *)
  eapply transplus_transitive; eauto.
  eapply transplus_transitive; eauto.
  eapply transplus_step.
    change (compile_value (Clos ca ea))
      with (MClos (compile ca (IReturn :: nil)) (compile_env ea)).
    constructor. 
  eapply transplus_transitive; eauto.
  apply transplus_base. constructor.
Qed.

(** Compiler correctness, non-terminating programs **)

Fixpoint left_app_height (a: term) : nat :=
  match a with
  | App b c => S(left_app_height b)
  | _ => 0
  end.

Lemma compile_evalinf_aux:
  forall e a k s,
  evalinf e a ->
  transinfN (left_app_height a) (compile a k) (compile_env e) s.
Proof.
  cofix COINDHYP. intros.
  inversion H; simpl.
  (* Left subterm diverges *)
  apply transinfN_stutter. 
  apply COINDHYP. auto. 
  (* Right subterm diverges *)
  apply transinfN_perform with (left_app_height b)
                       (compile b (IApp :: k))
                       (compile_env e)
                       (Slot_value (compile_value v) :: s).
  apply compile_eval; auto.
  apply COINDHYP; auto.  
  (* Application diverges *)
  apply transinfN_perform with (left_app_height ca)
                       (compile ca (IReturn :: nil))
                       (compile_env (vb :: ea))
                       (Slot_return k (compile_env e) :: s).
  apply transplus_transitive with
    (compile b (IApp :: k)) (compile_env e)
    (Slot_value (compile_value (Clos ca ea)) :: s).
  apply compile_eval; auto.
  apply transplus_transitive with
    (IApp :: k) (compile_env e)
    (Slot_value (compile_value vb) :: Slot_value (compile_value (Clos ca ea)) :: s).
  apply compile_eval; auto.
  apply transplus_base. simpl. fold compile_env. constructor. 
  apply COINDHYP; auto.
Qed.

Lemma compile_evalinf:
  forall e a k s,
  evalinf e a ->
  transinf (compile a k) (compile_env e) s.
Proof.
  intros. apply transinfN_transinf with (left_app_height a).
  apply compile_evalinf_aux. auto.
Qed.

(** Compiler correctness, using [coeval] and [cotrans] **)

Lemma compile_coeval_aux:
  forall e a v,
  coeval e a v ->
  forall k s,
  cotransN (left_app_height a)
         (compile a k) (compile_env e) s
         k (compile_env e) (Slot_value (compile_value v) :: s).
Proof.
  cofix COINDHYP. intros.
  inversion H; simpl.
  (* Var *)
  apply cotransN_perform. constructor. apply find_var_match; auto.
  (* Const *)
  apply cotransN_perform. constructor. 
  (* Closure *)
  apply cotransN_perform. constructor. 
  (* App *)
  apply cotransN_trans with
     (S (left_app_height b))
     (compile b (IApp :: k)) (compile_env e)
     (Slot_value (compile_value (Clos ca ea)) :: s).
  apply COINDHYP. assumption.
  apply cotransN_trans with
     (S 0)
     (IApp :: k) (compile_env e)
     (Slot_value (compile_value vb) ::
      Slot_value (compile_value (Clos ca ea)) :: s).
  apply COINDHYP. assumption.
  apply cotransN_trans with
     (S (left_app_height ca))
     (compile ca (IReturn :: nil)) (compile_env (vb :: ea))
     (Slot_return k (compile_env e) :: s).
  apply cotransN_perform.
    change (compile_value (Clos ca ea))
      with (MClos (compile ca (IReturn :: nil)) (compile_env ea)).
    simpl compile_env. constructor.
  apply cotransN_trans with
    0
    (IReturn :: nil)
    (compile_env (vb :: ea))
    (Slot_value (compile_value v) :: Slot_return k (compile_env e) :: s).
  apply COINDHYP. assumption.
  apply cotransN_perform.
  constructor.
Qed.

Lemma compile_coeval:
  forall e a v k s,
  coeval e a v ->
  cotrans (compile a k) (compile_env e) s
          k (compile_env e) (Slot_value (compile_value v) :: s).
Proof.
  intros. apply cotransN_cotrans with (left_app_height a).
  apply compile_coeval_aux. assumption.
Qed.

