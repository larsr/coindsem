(* Coq development underlying the paper
   "Coinductive big-step operational semantics", 
   Xavier Leroy and Hervé Grall, 2007.

   Copyright 2005, 2006, 2007 Institut National de la Recherche en
   Informatique et Automatique.

   This file is distributed under the terms of the GNU Public License
   version 2, http://www.gnu.org/licenses/gpl.html *)

Require Import Setoid.
Require Import Classical.
Require Import List.
Require Import semantics.

(** Traces **)

Definition trace: Set := list term.

Definition cons_right (t: trace) (a: term) := t ++ (a :: nil).

Notation "a @@ b" := (cons_right a b) (at level 55, right associativity).

Lemma cons_right_app:
  forall a b c, (a ++ b) @@ c = a ++ (b @@ c).
Proof.
  intros. unfold cons_right. rewrite app_ass. auto.
Qed.

Definition trace_app_l (t: trace) (b: term) : trace :=
  List.map (fun a => App a b) t.

Definition trace_app_r (a: term) (t: trace) : trace :=
  List.map (fun b => App a b) t.

CoInductive traceinf: Set :=
  | Tcons: term -> traceinf -> traceinf.

Infix ":::" := Tcons (at level 60, right associativity).

Fixpoint append_trace_traceinf (t1: trace) (t2: traceinf) {struct t1}: traceinf :=
  match t1 with
  | nil => t2
  | ev :: t => ev ::: append_trace_traceinf t t2
  end.

Notation "a +++ b" := (append_trace_traceinf a b) (at level 55, right associativity).

Lemma append_assoc: forall t1 t2 t3, (t1 ++ t2) +++ t3 = t1 +++ (t2 +++ t3).
Proof.
  induction t1; simpl; intros. auto. rewrite IHt1. auto.
Qed.

Lemma decompose_traceinf:
  forall t, t = match t with Tcons e t' => Tcons e t' end.
Proof.
  intro. destruct t; auto.
Qed.

Ltac dec x := rewrite (decompose_traceinf x); simpl.

CoFixpoint traceinf_app_l (t: traceinf) (b: term) : traceinf :=
  match t with
  | a ::: t' => App a b ::: traceinf_app_l t' b
  end.
CoFixpoint traceinf_app_r (a: term) (t: traceinf) : traceinf :=
  match t with
  | b ::: t' => App a b ::: traceinf_app_r a t'
  end.

CoInductive traceinf_sim: traceinf -> traceinf -> Prop :=
  | traceinf_sim_intro: forall a t1 t2,
      traceinf_sim t1 t2 -> traceinf_sim (a ::: t1) (a ::: t2).

Notation "x == y" := (traceinf_sim x y) (at level 70, no associativity).

Lemma traceinf_sim_refl: forall x, x == x.
Proof.
  cofix COINDHYP; intro. destruct x. constructor. apply COINDHYP.
Qed.

Lemma traceinf_sim_sym: forall x y, x == y -> y == x.
Proof.
  cofix COINDHYP; intros. inversion H. constructor. apply COINDHYP; auto.
Qed.

Lemma traceinf_sim_trans: forall x y z, x == y -> y == z -> x == z.
Proof.
  cofix COINDHYP; intros. inversion H; subst. inversion H0; subst. constructor. apply COINDHYP with t2; auto.
Qed.

Add Relation traceinf traceinf_sim
  reflexivity proved by traceinf_sim_refl
  symmetry proved by traceinf_sim_sym
  transitivity proved by traceinf_sim_trans
  as traceinf_sim_Rel.

Add Morphism Tcons
  with signature eq ==> traceinf_sim ==> traceinf_sim
  as Tcons_M.
Proof.
 intros. constructor; auto.
Qed.

Add Morphism append_trace_traceinf
  with signature eq ==> traceinf_sim ==> traceinf_sim
  as append_trace_traceinf_M.
Proof.
  induction y; intros; simpl. auto. constructor; auto.
Qed.

Add Morphism traceinf_app_l
  with signature traceinf_sim ==> eq ==> traceinf_sim
  as traceinf_app_l_M.
Proof.
  cofix COINDHYP; intros. 
  inversion H. dec (traceinf_app_l (a ::: t1) y0). dec (traceinf_app_l (a ::: t2) y0).
  constructor. apply COINDHYP; assumption.
Qed.

Add Morphism traceinf_app_r
  with signature eq ==> traceinf_sim ==> traceinf_sim
  as traceinf_app_r_M.
Proof.
  cofix COINDHYP; intros. 
  inversion H. dec (traceinf_app_r y (a ::: t1)). dec (traceinf_app_r y (a ::: t2)).
  constructor. apply COINDHYP; assumption.
Qed.

(** Big-step semantics with traces **)

Inductive teval: term -> trace -> term -> Prop :=
  | teval_const: forall c,
      teval (Const c) nil (Const c)
  | teval_fun: forall x a,
      teval (Fun x a) nil (Fun x a)
  | teval_app: forall a b x c vb v t1 t2 t3,
      teval a t1 (Fun x c) ->
      teval b t2 vb ->
      teval (subst x vb c) t3 v ->
      teval (App a b) (trace_app_l t1 b ++
                       trace_app_r (Fun x c) t2 ++
                       App (Fun x c) vb :: t3) v.

Lemma teval_isvalue:
  forall a t b, teval a t b -> isvalue b.
Proof.
  induction 1; intros.
  constructor.
  constructor.
  auto.
Qed.

Lemma teval_deterministic:
  forall a t v, teval a t v -> forall t' v', teval a t' v' -> v' = v /\ t' = t.
Proof.
  induction 1; intros.
    inversion H; auto.
    inversion H; auto.
    inversion H2. subst.
      destruct (IHteval1 _ _ H5) as [EQ1 EQ2].
      subst t1. inversion EQ1; subst.
      destruct (IHteval2 _ _ H6) as [EQ3 EQ4]. subst.
      destruct (IHteval3 _ _ H9) as [EQ5 EQ6]. subst.
      auto.
Qed.

Definition vx: var := 0.
Definition delta := Fun vx (App (Var vx) (Var vx)).
Definition omega := App delta delta.

Lemma not_eval_omega:
  forall t v, ~(teval omega t v).
Proof.
  assert (forall a t v, teval a t v -> a <> omega).
    induction 1; unfold omega.
    congruence.
    congruence.
    red; intro. injection H2; intros; subst a; subst b. clear H2.
    unfold delta in H. inversion H. subst x; subst c. clear H.
    unfold delta in H0. inversion H0. subst vb; clear H0.
    simpl in IHteval3. fold delta in IHteval3. fold omega in IHteval3. congruence.
  intros; red; intros. 
  elim (H _ _ _ H0). auto.
Qed.

CoInductive tevalinf: term -> traceinf -> Prop :=
  | tevalinf_app_l: forall a b t1 t,
      tevalinf a t1 ->
      t == traceinf_app_l t1 b ->
      tevalinf (App a b) t
  | tevalinf_app_r: forall a b va t1 t2 t,
      teval a t1 va ->
      tevalinf b t2 ->
      t == trace_app_l t1 b +++ traceinf_app_r va t2 ->
      tevalinf (App a b) t
  | tevalinf_app_f: forall a b x c vb t1 t2 t3 t,
      teval a t1 (Fun x c) ->
      teval b t2 vb ->
      tevalinf (subst x vb c) t3 ->
      t == trace_app_l t1 b +++
           trace_app_r (Fun x c) t2 +++
           (App (Fun x c) vb ::: t3) ->
      tevalinf (App a b) t.

CoFixpoint omegatrace : traceinf :=
  omega ::: omegatrace.

Lemma tevalinf_omega: tevalinf omega omegatrace.
Proof.
  unfold omega. cofix COINDHYP. dec omegatrace.
  change (omega ::: omegatrace)
    with (trace_app_l nil delta +++
          trace_app_r delta nil +++ (omega ::: omegatrace)).  
  unfold omega, delta. 
  eapply tevalinf_app_f. 
  constructor.
  constructor.
  simpl. fold delta. apply COINDHYP.
  reflexivity.
Qed.

(** Small-step semantics **)

Inductive tred: term -> trace -> term -> Prop :=
  | tred_refl: forall a,
      tred a nil a
  | tred_step: forall a b c t,
      red1 a b -> tred b t c -> tred a (a :: t) c.

Lemma tred_one: forall a b, red1 a b -> tred a (a :: nil) b.
Proof.
  intros. apply tred_step with b. auto. apply tred_refl.
Qed.

Lemma tred_trans: forall a t1 b t2 c, tred a t1 b -> tred b t2 c -> tred a (t1 ++ t2) c.
Proof.
  induction 1; intros. simpl. auto. 
  simpl. apply tred_step with b; auto. 
Qed.

CoInductive tredinf: term -> traceinf ->Prop :=
  | tredinf_intro: forall a b t,
      red1 a b -> tredinf b t -> tredinf a (a ::: t).

Lemma tredinf_deterministic:
  forall a t1 t2, tredinf a t1 -> tredinf a t2 -> t1 == t2.
Proof.
  cofix COINDHYP; intros.
  inversion H; subst. inversion H0; subst.
  assert (b = b0). eapply red1_deterministic; eauto.
  subst b0. constructor. apply COINDHYP with b; assumption.
Qed.

CoInductive tredinf': term -> traceinf ->Prop :=
  | tredinf'_intro: forall a b t1 t,
      red1 a b -> tredinf' b t1 -> t == a ::: t1 -> tredinf' a t.

Lemma tredinf'_tredinf:
  forall a t, tredinf' a t -> tredinf a t.
Proof.
  cofix COINDHYP; intros. inversion H; subst.
  inversion H2; subst. apply tredinf_intro with b. 
  assumption. apply COINDHYP. 
  inversion H1; subst. apply tredinf'_intro with b0 t2; auto.
  transitivity t1. auto. auto.
Qed.

Lemma tredinf_decompose:
  forall a b t, tred a t b ->
  forall T, tredinf a T -> exists T', tredinf b T' /\ T = t +++ T'.
Proof.
  induction 1; intros.
  exists T; split; auto.
  inversion H1. subst. 
  assert (b = b0). eapply red1_deterministic; eauto. subst b0.
  destruct (IHtred t0 H3) as [T' [A B]].
  exists T'; split; auto. simpl. rewrite B; auto.
Qed.

(** Connections between the reduction semantics with and without traces *)

Lemma tred_red:
  forall a t b, tred a t b -> red a b.
Proof.
  induction 1; econstructor; eauto. 
Qed.

Lemma red_tred:
  forall a b, red a b -> exists t, tred a t b.
Proof.
  induction 1. 
  exists (@nil term); constructor.
  destruct IHred as [t R2].
  exists (a :: t); econstructor; eauto.
Qed.

Lemma tred_or_redinf:
  forall a,
  (exists b, exists t, tred a t b /\ notred b) \/ redinf a.
Proof.
  intro. elim (red_or_redinf a).
  intros [b [R NR]]. destruct (red_tred _ _ R) as [t TR]. 
  left; exists b; exists t; split. auto. auto.
  intro RI. right; auto.
Qed.

Lemma isvalue_dec: forall a, {isvalue a} + {~isvalue a}.
Proof.
  destruct a. 
  right; red; intro; inversion H.
  left; constructor.
  left; constructor.
  right; red; intro; inversion H.
Qed.

Fixpoint reduce1 (a: term): option term :=
  match a with
  | Var _ => None
  | Const c => None
  | Fun x b => None
  | App (Fun x b) c =>
      if isvalue_dec c
      then Some (subst x c b)
      else match reduce1 c with
           | Some c' => Some (App (Fun x b) c')
           | None => None
           end
  | App b c =>
      match reduce1 b with
      | Some b' => Some(App b' c)
      | None =>
          if isvalue_dec b then
            match reduce1 c with
            | Some c' => Some(App b c')
            | None => None
            end
          else None
      end
  end.

Lemma isvalue_reduce1:
  forall v, isvalue v -> reduce1 v = None.
Proof.
  intros. inversion H; reflexivity.
Qed.

Lemma red1_reduce1:
  forall a b, red1 a b -> reduce1 a = Some b.
Proof.
  induction 1; simpl.
  destruct (isvalue_dec v). auto. contradiction.
  rewrite IHred1. destruct a1; auto. inversion H.
  repeat rewrite (isvalue_reduce1 _ H). 
  destruct (isvalue_dec v); [idtac | contradiction].
  rewrite IHred1. destruct v; auto. 
  destruct (isvalue_dec b1). 
  generalize (isvalue_reduce1 _ i0). congruence.
  auto.
Qed.

CoFixpoint traceinf_for (a: term) : traceinf :=
  match reduce1 a with
  | Some b => a ::: traceinf_for b
  | None => a ::: traceinf_for a
  end.

Lemma redinf_tredinf_aux:
  forall a, redinf a -> tredinf a (traceinf_for a).
Proof.
  cofix COINDHYP; intros. inversion H. 
  dec (traceinf_for a). rewrite (red1_reduce1 _ _ H0). 
  apply tredinf_intro with b. assumption. apply COINDHYP. assumption.
Qed.

Lemma tred_or_tredinf:
  forall a,
  (exists b, exists t, tred a t b /\ notred b) \/ 
  (exists t, tredinf a t).
Proof.
  intro. elim (red_or_redinf a).
  intros [b [R NR]]. destruct (red_tred _ _ R) as [t TR]. 
  left; exists b; exists t; split. auto. auto.
  intro RI. right. exists (traceinf_for a). apply redinf_tredinf_aux; auto.
Qed.

(** Connections between big-step and small-step semantics *)

(* eval -> red *)

Lemma tred_app_l:
   forall a1 t a2 b, tred a1 t a2 -> tred (App a1 b) (trace_app_l t b) (App a2 b).
Proof.
  induction 1; intros; simpl.
  apply tred_refl.
  apply tred_step with (App b0 b). apply red1_app_l; auto. auto.
Qed.

Lemma tred_app_r:
   forall v a1 t a2 , isvalue v -> tred a1 t a2 -> tred (App v a1) (trace_app_r v t) (App v a2).
Proof.
  induction 2; intros; simpl.
  apply tred_refl.
  apply tred_step with (App v b). apply red1_app_r; auto. auto.
Qed.

Lemma teval_tred:
  forall a t v, teval a t v -> tred a t v.
Proof.
  induction 1.
  apply tred_refl.
  apply tred_refl.
  apply tred_trans with (App (Fun x c) b).
    apply tred_app_l. assumption.
  apply tred_trans with (App (Fun x c) vb).
    apply tred_app_r. constructor. assumption.
  apply tred_step with (subst x vb c). 
  apply red1_beta. eapply teval_isvalue; eauto. 
  assumption.
Qed.

(* red -> eval *)

Lemma teval_value:
  forall v, isvalue v -> teval v nil v.
Proof.
  induction 1; intros. apply teval_const. apply teval_fun.
Qed.

Lemma tred1_teval:
  forall a b, red1 a b -> forall t v, teval b t v -> teval a (a :: t) v.
Proof.
  induction 1; intros.
  change (App (Fun x a) v :: t)
    with (trace_app_l nil v ++ trace_app_r (Fun x a) nil ++ App (Fun x a) v :: t).
  eapply teval_app. apply teval_fun. apply teval_value; auto. assumption.
  inversion H0; subst. 
  change (App a1 b :: trace_app_l t1 b ++ trace_app_r (Fun x c) t2 ++ App (Fun x c) vb :: t3)
    with (trace_app_l (a1 :: t1) b ++ trace_app_r (Fun x c) t2 ++ App (Fun x c) vb :: t3).
  eapply teval_app; eauto.
  inversion H1; subst; clear H1.
  assert (v = Fun x c /\ nil = t1). 
    apply teval_deterministic with v. auto. apply teval_value; auto.
  destruct H1 as [A B]; subst v t1. simpl.
  change (App (Fun x c) b1 :: trace_app_r (Fun x c) t2 ++ App (Fun x c) vb :: t3)
    with (trace_app_l nil b1 ++ trace_app_r (Fun x c) (b1 :: t2) ++ App (Fun x c) vb :: t3).
  eapply teval_app; eauto.
Qed.

Lemma tred_teval:
  forall a t v, tred a t v -> isvalue v -> teval a t v.
Proof.
  induction 1; intros.
  apply teval_value. assumption.
  eapply tred1_teval; eauto.
Qed.

(* evalinf -> redinf *)

Lemma tevalinf_tred1:
  forall a t, tevalinf a t -> 
  exists b, exists t', red1 a b /\ tevalinf b t' /\ t == a ::: t'.
Proof.
  induction a; intros; inversion H; clear H; subst.
  (* function part evaluates infinitely *)
  destruct (IHa1 _ H2) as [b [t1' [R1 [RI EQ]]]].
  exists (App b a2); exists (traceinf_app_l t1' a2); intuition.
  constructor; auto.
  eapply tevalinf_app_l; eauto. reflexivity.
  rewrite H4. rewrite EQ. dec (traceinf_app_l (a1 ::: t1') a2). reflexivity.
  (* function part evaluates finitely,
     argument evaluates infinitely *)
  destruct (IHa2 _ H3) as [b [t3 [R1 [RI EQ]]]].
  generalize (teval_tred _ _ _ H2). intro. inversion H; clear H; subst.
    (* function part was already a value *)
    exists (App va b); exists (traceinf_app_r va t3); intuition.
    constructor.  eapply teval_isvalue; eauto. auto.
    eapply tevalinf_app_r. eassumption. eassumption. reflexivity. 
    rewrite H5; simpl. rewrite EQ. dec (traceinf_app_r va (a2 ::: t3)).
    reflexivity.
    (* function part evaluates *)
    exists (App b0 a2); exists (trace_app_l t0 a2 +++ traceinf_app_r va (a2 ::: t3)); intuition.
    constructor. auto.
    eapply tevalinf_app_r. apply tred_teval; eauto. eapply teval_isvalue; eauto.
    eassumption. 
    rewrite EQ. reflexivity.
    rewrite H5. simpl. rewrite EQ. reflexivity.
  (* function and argument parts evaluate finitely,
     beta-redex evaluates infinitely *)
  generalize (teval_tred _ _ _ H2). intro. inversion H; clear H; subst.
    (* function part was already a value *)
    generalize (teval_tred _ _ _ H3). intro. inversion H; clear H; subst.
      (* argument part was already a value *)
      exists (subst x vb c); exists t3; intuition.
      constructor. eapply teval_isvalue; eauto.
      (* argument part reduces *)
      exists (App (Fun x c) b); exists (trace_app_r (Fun x c) t0 +++ (App (Fun x c) vb ::: t3)); intuition.
      constructor. constructor. auto.
      eapply tevalinf_app_f. 
      constructor. 
      apply tred_teval; eauto. eapply teval_isvalue; eauto.
      eauto. 
      simpl. reflexivity.
    (* function part reduces *)
    exists (App b a2); exists(trace_app_l t0 a2 +++ trace_app_r (Fun x c) t2 +++ (App (Fun x c) vb ::: t3)); intuition.
    constructor. auto.
    eapply tevalinf_app_f.
    apply tred_teval; eauto. constructor.
    eauto. eauto.
    reflexivity.
Qed.

Lemma tevalinf_tredinf':
  forall a t, tevalinf a t -> tredinf' a t.
Proof.
  cofix COINDHYP. intros. 
  destruct (tevalinf_tred1 _ _ H) as [b [t1 [R1 [RI EQ]]]].
  apply tredinf'_intro with b t1. auto. apply COINDHYP. auto. auto.
Qed.  

Lemma tevalinf_tredinf:
  forall a t, tevalinf a t -> tredinf a t.
Proof.
  intros. apply tredinf'_tredinf. apply tevalinf_tredinf'. auto.
Qed.

(* redinf -> evalinf *)

Lemma tredinf_app_l_1:
  forall a t a' b t',
  tred a t a' -> tredinf (App a b) t' ->
  exists t'', tredinf (App a' b) t'' /\ t' = trace_app_l t b +++ t''.
Proof.
  intros. apply tredinf_decompose with (App a b). 
  apply tred_app_l. auto. auto.
Qed.

Lemma tredinf_app_r_1:
  forall b t b' a t',
  tred b t b' -> isvalue a -> tredinf (App a b) t' ->
  exists t'', tredinf (App a b') t'' /\ t' = trace_app_r a t +++ t''.
Proof.
  intros. apply tredinf_decompose with (App a b).
  apply tred_app_r; auto. auto.
Qed.

Lemma tredinf_app_l:
  forall a b t, tredinf a t -> tredinf (App a b) (traceinf_app_l t b).
Proof.
  cofix COINDHYP; intros.
  inversion H. subst. dec (traceinf_app_l (a ::: t0) b). 
  apply tredinf_intro with (App b0 b). constructor. auto.
  apply COINDHYP. assumption.
Qed.

Lemma tredinf_app_r:
  forall a b t, isvalue a -> tredinf b t -> tredinf (App a b) (traceinf_app_r a t).
Proof.
  cofix COINDHYP; intros.
  inversion H0. subst. dec (traceinf_app_r a (b ::: t0)). 
  apply tredinf_intro with (App a b0). 
  constructor. auto. auto.
  apply COINDHYP. assumption. assumption.
Qed.

Lemma tredinf_app_l_2:
  forall a b t ta,
  tredinf (App a b) t -> tredinf a ta -> 
  t == traceinf_app_l ta b.
Proof.
  intros. apply tredinf_deterministic with (App a b).
  assumption. apply tredinf_app_l. auto.
Qed.

Lemma tredinf_app_r_2:
  forall a b t tb,
  tredinf (App a b) t -> isvalue a -> tredinf b tb ->
  t == traceinf_app_r a tb.
Proof.
  intros. apply tredinf_deterministic with (App a b).
  assumption. apply tredinf_app_r; auto.
Qed.

Lemma redinf_evalinf:
  forall a t, tredinf a t -> tevalinf a t.
Proof.
  cofix COINDHYP.
  intros. 
  destruct a; try (inversion H; inversion H0; fail).
  elim (tred_or_tredinf a1). 
  (* a1 evaluates finitely *)
  intros [n1 [t1 [REDM1 NOTRED1]]]. 
  destruct (tredinf_app_l_1 _ _ _ _ _ REDM1 H) as [t1' [REDINF1 EQ1]]. 
  assert (ISVAL1: isvalue n1). 
    inversion REDINF1. inversion H0.
    constructor.
    elim (NOTRED1 _ H7).
    assumption.
  elim (tred_or_tredinf a2).
  (* a2 evaluates finitely as well *)
  intros [n2 [t2 [REDM2 NOTRED2]]].
  destruct (tredinf_app_r_1 _ _ _ _ _ REDM2 ISVAL1 REDINF1) as [t2' [REDINF2 EQ2]].
  assert (exists x, exists c, exists t3,
            n1 = Fun x c /\ isvalue n2 /\ 
            tredinf (subst x n2 c) t3 /\
            t2' = App n1 n2 ::: t3).
    inversion REDINF2; subst. inversion H0; subst.
    exists x; exists a; exists t0. tauto.
    elim (NOTRED1 _ H5).
    elim (NOTRED2 _ H6).
  destruct H0 as [x [c [t3 [A [B [C D]]]]]]. subst n1.
  rewrite EQ1; rewrite EQ2; rewrite D.  
  eapply tevalinf_app_f.
    apply tred_teval; eassumption.
    apply tred_teval; eassumption.
    apply COINDHYP. eassumption.
    reflexivity.
  (* a2 evaluates infinitely *)
  intros [t2' TREDINF2]. 
  assert (t1' == traceinf_app_r n1 t2').
    apply tredinf_app_r_2 with a2; auto. 
  eapply tevalinf_app_r.  
  apply tred_teval; eassumption.
  apply COINDHYP. eassumption.
  rewrite EQ1. rewrite H0. reflexivity.  
  (* a1 evaluates infinitely *)
  intros [t1' REDINF1]. 
  assert (t == traceinf_app_l t1' a2). 
    apply tredinf_app_l_2 with a1; auto.
  apply tevalinf_app_l with t1'. apply COINDHYP. assumption. assumption.
Qed.

(* Corollary: determinism of tevalinf *)

Lemma tevalinf_deterministic:
  forall a t1 t2, tevalinf a t1 -> tevalinf a t2 -> t1 == t2.
Proof.
  intros. apply tredinf_deterministic with a.
  apply tevalinf_tredinf; auto. 
  apply tevalinf_tredinf; auto.
Qed.
