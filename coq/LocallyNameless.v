
From Coq Require Import Arith.
From Coq Require Import Relations.
From Eln Require Import Tactics.
From Eln Require Import Relations.

(** Definition of the locally nameless terms *)
Inductive tm : Set :=
  | C : nat -> tm (* Constants *)
  | V : nat -> tm (* Named variables *)
  | I : nat -> tm (* de Bruijn indices *)
  | Abs : tm -> tm
  | App : tm -> tm -> tm.

(** Shifting de Bruijn indices in terms *)

(* The function shift adds n to all indices greater or equal to k in the term t.
The index k takes into account the number of lambda abstraction *)
Fixpoint shift (t : tm) (n k : nat) : tm :=
  match t with
  | C c => C c
  | V v => V v
  | I i => if lt_dec i k then I i else I (i + n)
  | Abs t => Abs (shift t n (k + 1))
  | App t1 t2 => App (shift t1 n k) (shift t2 n k)
  end.

(* Let us prove some usefull theorems about shift. *)

Theorem shift_0 : forall t k,
  shift t 0 k = t.
Proof.
  induction t; crush; autodestruct; crush.
Qed.
#[export] Hint Resolve shift_0 : elnHints.
#[export] Hint Rewrite shift_0 : elnHints.

Theorem shift_merge : forall t n1 k1 n2 k2,
  k1 <= k2 ->
  k2 <= k1 + n1 ->
  shift (shift t n1 k1) n2 k2 = shift t (n1 + n2) k1.
Proof.
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Resolve shift_merge : elnHints.
#[export] Hint Rewrite shift_merge : elnHints.

Theorem shift_swap_le : forall t n1 k1 n2 k2,
  k2 <= k1 ->
  shift (shift t n1 k1) n2 k2 = shift (shift t n2 k2) n1 (k1 + n2).
Proof.
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Rewrite shift_swap_le : elnHints.

(* This theorem is the reverse of the preceding one *)
Theorem shift_swap_ge : forall t n1 k1 n2 k2,
  k2 >= k1 + n1 ->
  shift (shift t n1 k1) n2 k2 = shift (shift t n2 (k2 - n1)) n1 k1.
Proof.
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Rewrite shift_swap_ge : elnHints.

(** Let us now define the substitution *)
Fixpoint subst (t u : tm) (k : nat) : tm :=
  match t with
  | C c => C c
  | V v => V v
  | I i => match lt_eq_lt_dec i k with
            | inleft (left _) => I i
            | inleft (right _) => shift u k 0
            | inright _ => I (i - 1)
           end
  | Abs t => Abs (subst t u (k + 1))
  | App t1 t2 => App (subst t1 u k) (subst t2 u k)
  end.

(** Theorems about the substitution function *)
Theorem subst_shift_swap : forall t u k1 n2 k2,
  k2 <= k1 ->
  shift (subst t u k1) n2 k2 = subst (shift t n2 k2) u (k1 + n2).
Proof.
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Resolve subst_shift_swap : elnHints.

Theorem subst_shift_merge : forall t u k1 n2 k2,
  k2 <= k1 ->
  k1 < k2 + n2 ->
  subst (shift t n2 k2) u k1 = shift t (n2 - 1) k2.
Proof.
  induction t; crush; repeat (autodestruct; crush).
Qed.
#[export] Hint Resolve subst_shift_merge : elnHints.

Theorem subst_shift_shift : forall t u k1 n2 k2 n3 k3,
  k1 + k3 < k2 ->
  k2 <= k1 + k3 + 1 + (n3 - n2) ->
  n2 <= n3 ->
  subst (shift t n2 k2) (shift u n3 k3) k1 = 
  shift (subst t (shift u (n3 - n2) k3) k1) n2 (k2 - 1).
Proof.
  induction t; crush; repeat (autodestruct; crush).
  repeat match goal with
  | [ |- context [shift (shift ?x ?n1 ?k1) ?k2 0]] => 
      rewrite (shift_swap_le x n1 k1 k2 0) by crush
  | [ |- shift ?x ?n1 ?k1 = shift (shift ?x (?n1 - ?n2) ?k1) ?n2 ?k2 ] => 
      rewrite (shift_merge x (n1 - n2) k1 n2 k2) by crush
  | [ |- context [?x - ?y + ?y]] => assert (x - y + y = x) by crush; auto
  end.
Qed.
#[export] Hint Resolve subst_shift_shift : elnHints.
#[export] Hint Rewrite subst_shift_shift : elnHints.


(** Also known as the substitution lemma *)
Theorem subst_swap : forall t u1 k1 u2 k2,
  k1 <= k2 ->
  subst (subst t u1 k1) u2 k2 = subst (subst t u2 (S k2)) (subst u1 u2 (k2 - k1)) k1.
Proof.
  induction t; crush; repeat (autodestruct; crush);
  (* We are left with to cases where we need to massage the hypothesis
     a little bit to apply subst_shift_swap and subst_shift_merge *)
  match goal with
  | [ |- subst (shift ?u1 ?k1 0) ?u2 ?k2 = shift (subst ?u1 ?u2 (?k2 - ?k1)) ?k1 0] =>
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        assert (H1 : 0 <= k2 - k1) by lia';
        pose proof (subst_shift_swap u1 u2 (k2 - k1) k1 0 H1) as H2;
        assert (H3 : k2 - k1 + k1 = k2) by lia';
        rewrite H3 in H2;
        auto
  | [ |- shift ?u2 ?n2 0 = subst (shift ?u (S ?n2) 0) ?u1 ?k1] =>
      let H1 := fresh "H1" in
      let H2 := fresh "H2" in
      assert (H1 : 0 <= k1) by lia';
      assert (H2 : k1 < S n2) by lia';
      pose proof (subst_shift_merge u2 u1 k1 (S n2) 0 H1 H2);
      crush
  end.
Qed.
#[export] Hint Resolve subst_swap : elnHints.
#[export] Hint Rewrite <- subst_swap : elnHints.

(** Small steps *)
Inductive ss : tm -> tm -> Prop :=
  | ss_left : forall t1 t1' t2, ss t1 t1' -> ss (App t1 t2) (App t1' t2)
  | ss_right : forall t1 t2 t2', ss t2 t2' -> ss (App t1 t2) (App t1 t2')
  | ss_abs : forall t t', ss t t' -> ss (Abs t) (Abs t') 
  | ss_beta : forall t u, ss (App (Abs t) u) (subst t u 0).

#[export] Hint Constructors ss : elnHints.

Notation "ss*" := (clos_refl_trans_1n tm ss).

Lemma pss_shift : forall t t' n k,
  pss t t' ->
  pss (shift t n k) (shift t' n k).
Proof.
  intros t t' n k t_t';
  generalize dependent k; 
  induction t_t'; crush.
  - specialize (IHt_t'1 (k + 1)).
    specialize (IHt_t'2 k).
    pose proof (pss_beta _ _ _ _ IHt_t'1  IHt_t'2) as H.
    rewrite (subst_shift_shift t' u' 0 n (k + 1) n k) in H by crush.
    assert (H2 : k + 1 - 1 = k) by crush.
    rewrite H2 in H.
    assert (H3 : n - n = 0) by crush.
    rewrite H3 in H.
    rewrite (shift_0 u' k) in H. 
    auto.
Qed.
#[local] Hint Resolve pss_shift : elnHints.

Lemma pss_subst : forall t t' u u' k,
  pss t t' ->
  pss u u' ->
  pss (subst t u k) (subst t' u' k).
Proof.
  intros t t' u u' k t_t';
  generalize dependent k;
  induction t_t'; crush; repeat (autodestruct; crush).
  - specialize (IHt_t'1 (k + 1) H).
    specialize (IHt_t'2 k H).
    pose proof (pss_beta _ _ _ _ IHt_t'1  IHt_t'2) as H2.
    assert (H3 : 0 <= k) by crush.
    pose proof (subst_swap t' u'0 0 u' k H3) as H4.
    assert (S k = k + 1) by crush.
    assert (k - 0 = k) by crush.
    crush.
Qed.
#[local] Hint Resolve pss_subst : elnHints.

(** We want to prove the confluence of the small steps relation. We will first
        show that ss and pss defined below have the same reflexive transitive
        closure. Then prove that pss is confluent, thus proving ss confluent.*)

(** Parallel small steps *)
Inductive pss : tm -> tm -> Prop :=
| pss_c : forall i, pss (C i) (C i)
| pss_v : forall i, pss (V i) (V i)
| pss_i : forall i, pss (I i) (I i)
| pss_para : forall t1 t1' t2 t2', 
    pss t1 t1' -> 
    pss t2 t2' -> 
    pss (App t1 t2) (App t1' t2')
| pss_abs : forall t t', 
    pss t t' -> 
    pss (Abs t) (Abs t') 
| pss_beta : forall t t' u u', 
    pss t t' -> 
    pss u u' -> 
  pss (App (Abs t) u) (subst t' u' 0).

#[local] Hint Constructors pss : elnHints.

Notation "pss*" := (clos_refl_trans_1n tm pss).

Lemma pss_refl : reflexive tm pss.
Proof.
  intro t1;
  induction t1; crush.
Qed.
#[local] Hint Resolve pss_refl : elnHints.



Lemma inclusion_ss_pss : inclusion tm ss pss.
Proof.
  intros x y x_y; induction x_y; crush.
Qed.
#[local] Hint Resolve inclusion_ss_pss : elnHints.

Lemma inclusion_pss_ss_rt : inclusion tm pss ss*.
Proof.
  intros x y x_y; induction x_y; crush.
  - 
  Admitted.

Lemma diamond_pss : diamond pss.
Proof.
  (* By induction on x and then we inspect what step is used in both direction.
     Only the case of App where one side use para and the other use subst is
     interesting. We need to use pss_para_beta when this happens. *)
  intros x yl yr x_yl; generalize dependent yr; 
  induction x_yl as [il | il | il 
    | lt1 lt1' lt2 lt2' lt1_t1' lt1_t1'_H lt2_t2' lt2_t2'_H 
    | lt lt' lt_t' lt_t'_H 
    | lt lt' lu lu' lt_t' lt_t'_H lu_u' lu_u'_H ]; 
  intros yr x_yr;
  inversion x_yr as [ir | ir | ir 
  | rt1 rt1' rt2 rt2' rt1_t1' rt1_t1'_H rt2_t2' rt2_t2'_H 
  | rt rt' rt_t' rt_t'_H 
  | rt rt' ru ru' rt_t' rt_t'_H ru_u' ru_u'_H ]; 
  ecrush.
  - repeat autoSpecialize; simplHyp; ecrush.
  - inversion lt1_t1'; subst.
    destruct (lt2_t2'_H ru' rt_t'_H).
    assert (H1: pss (Abs rt) (Abs rt')) by crush.
    destruct (lt1_t1'_H (Abs rt') H1).
    simplHyp. inversion H2; subst.
    inversion H3; subst.
    exists (subst t'0 x 0); crush.
  - autoSpecialize; simplHyp.
    exists (Abs x); crush.
  - inversion rt1_t1'; subst.
    destruct (lt_t2'_H ru' rt_t'_H).
    assert (H1: pss (Abs rt) (Abs rt')) by crush.
    destruct (lt1_t1'_H (Abs rt') H1).
    simplHyp. inversion H2; subst.
    inversion H3; subst.
    exists (subst t'0 x 0); crush.
  
  subst; repeat autoSpecialize; simplHyp.
    specialize
  
  repeat autoSpecialize; simplHyp; ecrush.
    
  repeat autoSpecialize; simplHyp; ecrush.
    exists (subst rt' ru' 0); crush.
  
  
  
  
  
  induction x as [ | | | x IHx | x1 IHx1 x2 IHx2 ]; intros y1 y2 x_y1 x_y2;
  match goal with
   | [ |- _ ] => solve [inversion x_y1; inversion x_y2; subst; eauto with elnHints]
   | [x_y1 : pss (Abs x) y1, x_y2 : pss (Abs x) y2 |- _ ] => 
      inversion x_y1 as [ | | t1 t2 x_t2 | ]; subst; eauto with elnHints;
      inversion x_y2 as [ | | t3 t4 x_t4 | ]; subst; eauto with elnHints;
      destruct (IHx t2 t4 x_t2 x_t4) as [z [H1z H2z]];
      eauto with elnHints
   | _ => idtac
   end.
  - inversion x_y1 as [ | a t1 b t2 x1_t1 x2_t2 | | a b c d ]; subst; eauto with elnHints;
    inversion x_y2 as [ | a1 t3 b t4 x1_t3 x2_t4 | | e f g h ]; subst; eauto with elnHints.
    * destruct (IHx1 t1 t3 x1_t1 x1_t3) as [z [H1z H2z]].
      destruct (IHx2 t2 t4 x2_t2 x2_t4) as [z2 [H1z2 H2z2]].
      eauto with elnHints.
    * inversion x1_t1; subst.
      + pose proof (pss_para_beta e e x2 t2 0 (pss_refl e) x2_t2).
      eauto with elnHints.
      + pose proof (pss_para_beta e t' x2 t2 0 H0 x2_t2).
      eauto with elnHints. 
    * inversion x1_t3; subst.
      + pose proof (pss_para_beta a a x2 t4 0 (pss_refl a) x2_t4).
        eauto with elnHints.
      + pose proof (pss_para_beta a t' x2 t4 0 H0 x2_t4).
      eauto with elnHints.
Qed.  