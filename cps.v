(* Coq development underlying the paper
   "Coinductive big-step operational semantics", 
   Xavier Leroy and Hervé Grall, 2007.

   Copyright 2005, 2006, 2007 Institut National de la Recherche en
   Informatique et Automatique.

   This file is distributed under the terms of the GNU Public License
   version 2, http://www.gnu.org/licenses/gpl.html *)

Require Import semantics.

(** Coevaluation for terms in CPS form **)

Inductive isatom: term -> Prop :=
  | isatom_var: forall x,
      isatom (Var x)
  | isatom_const: forall c,
      isatom (Const c)
  | isatom_fun: forall x b,
      isbody b ->
      isatom (Fun x b)

with isbody: term -> Prop :=
  | isbody_atom: forall a,
      isatom a ->
      isbody a
  | isbody_app: forall b a,
      isbody b -> isatom a ->
      isbody (App b a).

Scheme isatom_ind2 := Minimality for isatom Sort Prop
  with isbody_ind2 := Minimality for isbody Sort Prop.

Lemma isbody_subst:
  forall x a b, isatom a -> isbody b -> isbody (subst x a b).
Proof.
  assert (forall b, isbody b -> forall x a, isatom a -> isbody (subst x a b)).
  apply (isbody_ind2
    (fun a' => forall x a, isatom a -> isatom (subst x a a'))
    (fun b => forall x a, isatom a -> isbody (subst x a b))); intros; simpl.
  case (var_eq x0 x); intro. auto. constructor.
  constructor.
  case (var_eq x0 x); intro; constructor. auto. 
  apply H0. auto. apply isbody_atom. auto.
  apply isbody_app; auto.
  auto.
Qed.

Lemma eval_body_atom:
  forall b v, eval b v -> isbody b -> isatom v.
Proof.
  induction 1; intros.
  constructor.
  inversion H. auto.
  inversion H2; subst. inversion H3.
  apply IHeval3. apply isbody_subst. 
  apply IHeval2. apply isbody_atom. auto.
  generalize (IHeval1 H5); intro. inversion H3; auto.
Qed.

Lemma eval_body_fun:
  forall b x c, eval b (Fun x c) -> isbody b -> isbody c.
Proof.
  intros. generalize (eval_body_atom _ _ H H0); intro. inversion H1; auto.
Qed.

(* Closed terms *)

Fixpoint isfree (x: var) (a: term) {struct a} : Prop :=
  match a with
  | Var y => y = x
  | Const c => False
  | Fun y b => isfree x b /\ y <> x
  | App b c => isfree x b \/ isfree x c
  end.

Definition closed (a: term) : Prop := forall x, ~isfree x a.

Lemma isfree_subst:
  forall x a, closed a ->
  forall b y, isfree y (subst x a b) -> isfree y b /\ y <> x.
Proof.
  induction b; simpl; intros.
  destruct (var_eq x v). elim (H _ H0). 
  simpl in H0. split; congruence.
  tauto.
  destruct (var_eq x v). intuition congruence.  firstorder.
  firstorder.
Qed.

Lemma closed_subst:
  forall x a b, closed (Fun x a) -> closed b -> closed (subst x b a).
Proof.
  intros; red; intro y; red; intro. 
  elim (isfree_subst _ _ H0 _ _ H1); intros.
  elim (H y). simpl. split; auto.
Qed.

Lemma closed_App_inv:
  forall a b, closed (App a b) -> closed a /\ closed b.
Proof.
  unfold closed; firstorder.
Qed.

Lemma closed_eval:
  forall a v, eval a v -> closed a -> closed v.
Proof.
  induction 1; intros.
  auto.
  auto.
  elim (closed_App_inv _ _ H2); intros.
  apply IHeval3. apply closed_subst. auto. auto.
Qed.

(* Evaluation of closed atoms *)

Lemma not_evalinf_atom:
  forall a, evalinf a -> isatom a -> False.
Proof.
  intros. inversion H0; subst; inversion H. 
Qed.

Lemma eval_atom:
  forall a, isatom a -> closed a -> eval a a.
Proof.
  induction 1; intros.
  elim (H x). simpl. auto.
  constructor.
  constructor.
Qed.

Lemma eval_atom_inv:
  forall a v, eval a v -> isatom a -> v = a.
Proof.
  intros. inversion H0; subst; inversion H; auto.
Qed.
  
(* The absorbing term *)

Remark subst_omega:
  forall b, subst vx b omega = omega.
Proof.
  intros. reflexivity. 
Qed.

Definition Omega := Fun vx omega.

(* Divergence implies coevaluation to Omega for closed CPS bodies *)

Lemma evalinf_coeval_cps:
  forall b, evalinf b -> isbody b -> closed b -> coeval b Omega.
Proof.
  cofix COINDHYP; intros.
  inversion H0; subst; clear H0. elim (not_evalinf_atom _ H H2).
  assert (closed b0).
    red; intros. generalize (H1 x). simpl. tauto.
  assert (closed a).
    red; intros. generalize (H1 x). simpl. tauto.
  inversion H; subst.
  (* case 1: function part diverges *)
  apply coeval_app with vx omega a. apply COINDHYP; assumption.
  apply eval_coeval. apply eval_atom; auto. 
  rewrite subst_omega. apply coeval_omega.
  (* case 2: argument part diverges *)
  elim (not_evalinf_atom _ H8 H3).
  (* case 3: substituted body diverges *)
  apply coeval_app with x c vb.
  apply eval_coeval; assumption.
  apply eval_coeval; assumption.
  apply COINDHYP. assumption.
  apply isbody_subst. 
  generalize (eval_atom_inv _ _ H8 H3); intro. subst vb. assumption.
  eapply eval_body_fun; eauto.
  eapply closed_subst; eauto; eapply closed_eval; eauto. 
Qed.

Lemma coeval_cps_characterization:
  forall b, isbody b -> closed b ->
  ((exists v, coeval b v) <-> evalinf b \/ (exists v, eval b v)).
Proof.
  intros. split.
  intros [v COEVAL]. 
  elim (coeval_eval_or_evalinf _ _ COEVAL); intro; firstorder.
  intros [EVALINF | [v EVAL]].
  exists Omega; apply evalinf_coeval_cps; auto.
  exists v; apply eval_coeval; auto.
Qed.
