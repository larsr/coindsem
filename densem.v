(* Coq development underlying the paper
   "Coinductive big-step operational semantics", 
   Xavier Leroy and Hervé Grall, 2007.

   Copyright 2005, 2006, 2007 Institut National de la Recherche en
   Informatique et Automatique.

   This file is distributed under the terms of the GNU Public License
   version 2, http://www.gnu.org/licenses/gpl.html *)

Require Import Classical.
Require Import semantics.
Require Import Omega.
Require Import Arith.
Require Import Max.
Hint Resolve le_refl le_trans le_max_l le_max_r.

(** Connections with a simple form of denotational semantics. **)

Inductive result : Set :=
  | Bottom: result                (* time out *)
  | Error: result                 (* run-time type error *)
  | Result: term -> result.       (* successful termination *)

Definition step (rec: term -> result) (a: term) : result :=
  match a with
  | Var v => Error
  | Const n => Result (Const n)
  | Fun v b => Result (Fun v b)
  | App b c =>
      match rec b with
      | Bottom => Bottom
      | Error => Error
      | Result vb =>
          match rec c with
          | Bottom => Bottom
          | Error => Error
          | Result vc =>
              match vb with
              | Fun x d => rec (subst x vc d)
              | _ => Error
              end
          end
      end
  end.

Fixpoint compute (n: nat) : term -> result :=
  match n with
  | O => (fun a => Bottom)
  | S n1 => step (compute n1)
  end.

Definition evaluates (a: term) (r: result) : Prop :=
  exists n, forall m, n <= m -> compute m a = r.

Lemma evaluates_unique:
  forall a r1 r2, evaluates a r1 -> evaluates a r2 -> r1 = r2.
Proof.
  intros a r1 r2 [n1 C1] [n2 C2].
  rewrite <- (C1 (max n1 n2)).
  rewrite <- (C2 (max n1 n2)).
  auto.
  auto. auto.
Qed.

Inductive result_le: result -> result -> Prop :=
  | result_le_refl:
      forall r, result_le r r
  | result_le_bot:
      forall r, result_le Bottom r.

Lemma step_increasing:
  forall (rec1 rec2: term -> result),
  (forall a, result_le (rec1 a) (rec2 a)) ->
  (forall a, result_le (step rec1 a) (step rec2 a)).
Proof.
  intros. destruct a; simpl; try constructor.
  generalize (H a1); intro; inversion H0; try constructor.
  destruct (rec1 a1); try constructor.
  generalize (H a2); intro; inversion H2; try constructor.
  destruct (rec1 a2); try constructor.
  destruct t; auto || constructor.
Qed.

Lemma compute_increasing:
  forall n1 n2 a, n1 <= n2 -> result_le (compute n1 a) (compute n2 a).
Proof.
  induction n1; simpl; intros.
  constructor.
  destruct n2. elimtype False; omega.
  simpl. apply step_increasing. 
  intros. apply IHn1. omega.
Qed.

Lemma evaluates_total:
  forall a, exists r, evaluates a r.
Proof.
  intro. elim (classic (forall n, compute n a = Bottom)); intros.
  exists Bottom; exists 0; intros; auto.
  assert (exists n, compute n a <> Bottom).
    change (exists n, ~((fun m => compute m a = Bottom) n)).
    apply not_all_ex_not. assumption.
  destruct H0 as [n EQ].
  exists (compute n a); exists n; intros.
  generalize (compute_increasing _ _ a H0); intro. 
  inversion H1. auto. congruence.
Qed.

Lemma evaluates_limsup:
  forall a r n,  evaluates a r -> result_le (compute n a) r.
Proof.
  intros a r n [m COMP]. 
  assert (n <= m \/ m <= n). omega. elim H; intros.
  rewrite <- (COMP m). apply compute_increasing. auto. omega.
  rewrite <- (COMP n). constructor. auto.
Qed.

Lemma evaluates_compute_either:
  forall a r n, evaluates a r -> compute n a = Bottom \/ compute n a = r.
Proof.
  intros. generalize (evaluates_limsup _ _ n H); intro.
  inversion H0; auto.
Qed.

Lemma compute_converges:
  forall n a v, compute n a = Result v -> evaluates a (Result v).
Proof.
  intros. exists n. intros. 
  generalize (compute_increasing n m a H0); rewrite H; intro. 
  inversion H1; auto.
Qed.

Lemma compute_gets_stuck:
  forall n a, compute n a = Error -> evaluates a Error.
Proof.
  intros. exists n. intros. 
  generalize (compute_increasing n m a H0); rewrite H; intro. 
  inversion H1; auto.
Qed.

Ltac caseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Lemma compute_diverges:
  forall a, evaluates a Bottom -> forall n, compute n a = Bottom.
Proof.
  intros. elim (evaluates_compute_either a Bottom n H); congruence.
Qed.

Lemma converges_eval:
  forall a v, evaluates a (Result v) -> eval a v.
Proof.
  assert (forall n a v, compute n a = Result v -> eval a v).
    induction n; intros until v; destruct a; simpl; try congruence.
    intro. inversion H. constructor.
    intro. inversion H. constructor.
    caseEq (compute n a1); try congruence.
    intros v1 COMP1.
    caseEq (compute n a2); try congruence.
    intros v2 COMP2.
    destruct v1; try congruence. intro COMP3.
    econstructor; eauto.
  intros a v [n COMP]. apply H with n. apply COMP. omega.
Qed.

Lemma eval_converges:
  forall a v, eval a v -> evaluates a (Result v).
Proof.
  induction 1.
  apply compute_converges with 1. reflexivity.
  apply compute_converges with 1. reflexivity.
  destruct IHeval1 as [n1 A1].
  destruct IHeval2 as [n2 A2].
  destruct IHeval3 as [n3 A3].
  apply compute_converges with (S (max n1 (max n2 n3))). simpl. 
  rewrite A1; eauto. rewrite A2; eauto. 
Qed.

Lemma diverges_evalinf:
  forall a, evaluates a Bottom -> evalinf a.
Proof.
  cofix COINDHYP; intros. generalize (compute_diverges a H); intro.
  destruct a; try (generalize (H0 1); simpl; congruence).
  destruct (evaluates_total a1) as [r1 EVAL1].
  elim EVAL1; intros n1 COMP1.
  destruct r1. 
  apply evalinf_app_l. auto.
  generalize (H0 (S n1)); simpl. rewrite COMP1. congruence. auto.
  destruct (evaluates_total a2) as [r2 EVAL2].
  elim EVAL2; intros n2 COMP2.
  destruct r2. 
  apply evalinf_app_r with t. apply converges_eval; auto. auto.
  generalize (H0 (S (max n1 n2))); simpl. 
  rewrite COMP1. rewrite COMP2. congruence. eauto. eauto.
  assert (exists x, exists b, t = Fun x b).
    generalize (H0 (S (max n1 n2))); simpl.
    rewrite COMP1; eauto. rewrite COMP2; eauto.
    destruct t; intros; try congruence. 
    exists v; exists t; auto.
  destruct H1 as [x [b EQ]]. subst t.
  apply evalinf_app_f with x b t0. 
  apply converges_eval; auto.
  apply converges_eval; auto.
  apply COINDHYP. exists (max n1 n2); intros.
  generalize (H0 (S m)). simpl. 
  rewrite COMP1; eauto. rewrite COMP2; eauto.
Qed.

Lemma evalinf_diverges:
  forall a, evalinf a -> evaluates a Bottom.
Proof.
  assert (forall n a, evalinf a -> compute n a = Bottom).
  induction n; intros.
  reflexivity. 
  inversion H; simpl. 
  (* function part diverges *)
  rewrite IHn; auto.
  (* argument part diverges *)
  elim (evaluates_compute_either _ _ n (eval_converges _ _ H0));
  intro EQ1; rewrite EQ1.
  auto. rewrite (IHn b); auto.
  (* body diverges *)
  elim (evaluates_compute_either _ _ n (eval_converges _ _ H0));
  intro EQ1; rewrite EQ1.
  auto.
  elim (evaluates_compute_either _ _ n (eval_converges _ _ H1));
  intro EQ2; rewrite EQ2.
  auto.
  apply IHn. auto.

  intros. exists 0; auto.
Qed.
