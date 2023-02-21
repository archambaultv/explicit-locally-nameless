From Coq Require Import Relations.
From Eln Require Import Tactics.

Section Definitions.

Context {A : Type}.

(* From Wadler https://plfa.github.io/Confluence/, who I think got it from
   Takahashi’s complete development (1995).*)
Definition triangle (R : relation A) (f : A -> A) : Prop :=
  forall x y, R x y -> R x (f x) /\ R y (f x).

Definition diamond (R : relation A) : Prop :=
  forall x y1 y2, R x y1 -> R x y2 -> exists z,  R y1 z /\ R y2 z.

Definition local_triangle (R : relation A) (f : A -> A) : Prop :=
  forall x y, R x y -> 
  clos_refl_trans A R x (f x) /\ clos_refl_trans A R y (f x).

Definition local_confluence (R : relation A) : Prop :=
  forall x y1 y2, 
    R x y1 -> 
    R x y2 -> 
    exists z, clos_refl_trans A R y1 z /\ clos_refl_trans A R y2 z.

Definition confluence (R : relation A) : Prop :=
  forall x y1 y2, 
    clos_refl_trans A R x y1 -> 
    clos_refl_trans A R x y2 -> 
    exists z, clos_refl_trans A R y1 z /\ clos_refl_trans A R y2 z.

Definition normal_form (R : relation A) (x : A): Prop :=
    forall y, ~ R x y.

Inductive weakly_normalize (R : relation A) : A -> Prop :=
    | wn_normal_from : forall x, normal_form R x -> weakly_normalize R x
    | wn_intro : forall x, (exists y, R x y -> weakly_normalize R y) -> weakly_normalize R x.

Inductive strongly_normalize (R : relation A) : A -> Prop :=
    | sn_normal_from : forall x, normal_form R x -> strongly_normalize R x
    | sn_intro : forall x y, R x y -> strongly_normalize R y -> strongly_normalize R x.

Definition weakly_normalizing (R : relation A) : Prop :=
    forall x, weakly_normalize R x.

Definition strongly_normalizing (R : relation A) : Prop :=
    forall x, strongly_normalize R x.

End Definitions.

Section Properties.
  Context {A : Type}.
  Variable R : relation A.

  Lemma triangle_diamond : forall f, 
    triangle R f -> diamond R.
  Proof.
    intros f tri x y1 y2 x_y1 x_y2;
    exists (f x); unfold triangle in tri;
    pose proof (tri x y1 x_y1);
    pose proof (tri x y2 x_y2);
    crush.
  Qed.

  Lemma local_triangle_local_confluent : forall f,
    local_triangle R f -> local_confluence R.
  Proof.
    intros f tri x y1 y2 x_y1 x_y2;
    exists (f x); unfold triangle in tri;
    pose proof (tri x y1 x_y1);
    pose proof (tri x y2 x_y2);
    crush.
  Qed.   

  Lemma diamond_strip : diamond R ->
    forall x y1 y2, 
    R x y1 -> 
    clos_refl_trans A R x y2 -> 
    exists z, clos_refl_trans A R y1 z /\ R y2 z.
  Proof.
    intros D x y1 y2 x_y1 rt_x_y2; generalize dependent y1;
     induction rt_x_y2 as [x y2 x_y2| | x y2 z2 x_y2 x_y2_H y2_z2 y2_z2_H]; intros y1 x_y1.
    - destruct (D x y1 y2 x_y1 x_y2) as [z [y1_z y2_z]];
      eauto with sets.
    - eauto with sets.
    - destruct (x_y2_H y1 x_y1) as [z3 [y1_z3_H y2_z3_H]].
      destruct (y2_z2_H z3 y2_z3_H) as [z4 [H_z3_z4 H_z2_z4]].
      eauto using rt_trans with sets.
  Qed.

  Theorem diamond_confluence : diamond R -> confluence R.
  Proof.
    intros D x y1 y2 y1H; generalize dependent y2; 
    induction y1H as [x y1 x_y1 | |x y1 z1 x_y1 x_y1_H y1_z1 y1_z1_H]; intros y2 y2H.
    - destruct (diamond_strip D x y1 y2 x_y1 y2H) as [z [zH1 zH2]].
      eauto with sets.
    - eauto using rt_refl.
    - destruct (x_y1_H y2 y2H) as [z2 [Hyz2 Hy2z2]];
      destruct (y1_z1_H z2 Hyz2) as [z3 [Hyz3 Hy2z3]];
      eauto using rt_trans. 
  Qed. 
  Hint Resolve diamond_confluence : elnHints.

  Theorem same_clos_refl_trans_confluence : forall (R2 : relation A),
    same_relation A (clos_refl_trans A R) (clos_refl_trans A R2) ->
    confluence R -> confluence R2.
  Proof.
    intros R2 same confluentR.
    destruct same as [H1 H2]. unfold inclusion in *. unfold confluence in *.
    intros x y1 y2 x_y1 x_y2.
    destruct (confluentR x y1 y2 (H2 x y1 x_y1) (H2 x y2 x_y2)) as [z [H1z H2z]].
    eauto.
  Qed.

  Theorem diamond_terminating_confluent :
    diamond R -> strongly_normalizing R -> confluence R.
  Admitted.

End Properties.