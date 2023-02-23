From Coq Require Import Relations.
From Eln Require Import Tactics.

Section Definitions.

Context {A : Type}.

(* The idea for triangle I got from Wadler https://plfa.github.io/Confluence/,
   who I think got it from Takahashi’s complete development (1995).*)

Definition triangle (R : relation A) (f : A -> A) : Prop :=
  forall x, R x (f x) 
    /\ forall y, R x y -> R y (f x).

Definition local_triangle (R : relation A) (f : A -> A) : Prop :=
  forall x, clos_refl_trans A R x (f x) 
    /\ forall y, R x y -> clos_refl_trans A R y (f x).

Definition confluent_triangle (R : relation A) (f : A -> A) : Prop :=
  forall x, clos_refl_trans A R x (f x)
   /\ forall y, clos_refl_trans A R x y -> clos_refl_trans A R y (f x).

Definition diamond (R : relation A) : Prop :=
  forall x y1 y2, R x y1 -> R x y2 -> exists z,  R y1 z /\ R y2 z.

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

Definition semi_diamond (R : relation A) : Prop :=
  forall x y1 y2, 
  R x y1 -> 
  clos_refl_trans A R x y2 -> 
  exists z, clos_refl_trans A R y1 z /\ R y2 z.

Definition semi_confluence (R : relation A) : Prop :=
  forall x y1 y2, 
  R x y1 -> 
  clos_refl_trans A R x y2 -> 
  exists z, clos_refl_trans A R y1 z /\ clos_refl_trans A R y2 z.

Definition convergence (R : relation A) (f : A -> A) : Prop :=
  forall x y, R x y -> clos_refl_trans A R (f y) (f x).

Definition respects_rt (R : relation A) (f : A -> A) : Prop :=
  forall x y, R x y -> clos_refl_trans A R (f x) (f y).

Definition normal_form (R : relation A) (x : A) : Prop :=
  forall y, ~ R x y.

Definition terminal (R : relation A) (x y : A) : Prop :=
  normal_form R y /\ clos_refl_trans A R x y.

  (* Weak normalization *)
Definition WN (R : relation A) (x : A) : Prop :=
  exists z, terminal R x z.

  (* Strong normalization *)
Inductive SN (R : relation A) (x : A) : Prop :=
  | sn_intro : (forall y, R x y -> SN R y) -> SN R x.

Print SN_ind.

Definition terminating (R : relation A) : Prop :=
    forall x, SN R x.

End Definitions.

Section Properties.
  Context {A : Type}.
  Variable R : relation A. 

  Lemma triangle_diamond : forall f, 
    triangle R f -> diamond R.
  Proof.
    intros f tri x y1 y2 x_y1 x_y2;
    destruct (tri x);
    autoSpecialize; ecrush.
  Qed.

  Lemma diamond_semi_diamond : 
    diamond R ->
    semi_diamond R.
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

  Theorem semi_diamond_confluence : semi_diamond R -> confluence R.
  Proof.
    intros D x y1 y2 y1H; generalize dependent y2; 
    induction y1H as [x y1 x_y1 | |x y1 z1 x_y1 x_y1_H y1_z1 y1_z1_H]; intros y2 y2H.
    - destruct (D x y1 y2 x_y1 y2H) as [z [zH1 zH2]].
      eauto with sets.
    - eauto using rt_refl.
    - destruct (x_y1_H y2 y2H) as [z2 [Hyz2 Hy2z2]];
      destruct (y1_z1_H z2 Hyz2) as [z3 [Hyz3 Hy2z3]];
      eauto using rt_trans. 
  Qed. 
  Hint Resolve semi_diamond_confluence : elnHints.

  Theorem confluence_semi_confluence :
    confluence R -> semi_confluence R.
  Proof.
    intros C x y1 y2 x_y1 x_y2;
    destruct (C x y1 y2 (rt_step _ _ _ _ x_y1) x_y2);
    ecrush.
  Qed.

  Theorem semi_confluence_confluence :
  semi_confluence R -> confluence R.
  Proof.
    intros D x y1 y2 y1H; generalize dependent y2; 
    induction y1H as [x y1 x_y1 | |x y1 z1 x_y1 x_y1_H y1_z1 y1_z1_H]; intros y2 y2H.
    - destruct (D x y1 y2 x_y1 y2H) as [z [zH1 zH2]].
      eauto with sets.
    - eauto using rt_refl.
    - destruct (x_y1_H y2 y2H) as [z2 [Hyz2 Hy2z2]];
      destruct (y1_z1_H z2 Hyz2) as [z3 [Hyz3 Hy2z3]];
      eauto using rt_trans.
  Qed. 

  Theorem confluence_local_confluence :
  confluence R -> local_confluence R.
  Proof.
    intros C x y1 y2 x_y1 x_y2;
    destruct (C x y1 y2 (rt_step _ _ _ _ x_y1) (rt_step _ _ _ _ x_y2));
    ecrush.
  Qed.

  Theorem triangle_local_triangle :
    forall f, triangle R f -> local_triangle R f.
  Proof.
    intros f T x.
    destruct (T x);
    autoSpecialize; ecrush.
  Qed.

  Theorem local_triangle_local_confluence :
    forall f, local_triangle R f -> local_confluence R.
  Proof.
    intros f T x y1 y2 x_y1 x_y2;
    destruct (T x);
    autoSpecialize; ecrush.
  Qed.

  Theorem confluent_triangle_confluence :
  forall f, confluent_triangle R f -> confluence R.
  Proof.
    intros f T x y1 y2 x_y1 x_y2;
    destruct (T x);
    autoSpecialize; ecrush.
  Qed.

  Theorem confluent_triangle_local_triangle :
  forall f, confluent_triangle R f -> local_triangle R f.
  Proof.
    intros f T x;
    destruct (T x);
    autoSpecialize; ecrush.
  Qed.

  Lemma confluent_triangle_respects_rt :
  forall f, confluent_triangle R f -> respects_rt R f.
  Proof.
    intros f T x y x_y.
    destruct (T x) as [x_fx Hx].
    destruct (T y) as [y_fy Hy].
    autoSpecialize; crush.
  Qed.

  Lemma convergence_rt :forall f, 
    convergence R f ->
      forall x y, clos_refl_trans A R x y -> 
                  clos_refl_trans A R (f y) (f x).
  Proof.
    unfold convergence;
    intros f Cf x y x_y;
    induction x_y; crush; eauto using rt_trans.
  Qed.

    (* This means that if we can prove local_triangle and convergence, 
     we also know that f respects_rt, so basically the terms reduce to 
     a cycle. *)
  Theorem local_triangle_confluent_triangle : forall f, 
    convergence R f ->
    local_triangle R f ->
    confluent_triangle R f.
  Proof.
    intros f convergencef T x;
    destruct (T x) as [x_fx y_fx]; split ; [auto | intros y H];
    induction H; auto.
    - pose proof (convergence_rt f convergencef x y H).
      destruct (T y);
      intuition (eauto using rt_trans).
  Qed.

  Theorem nf_terminal : forall x,
    normal_form R x -> terminal R x x.
  Proof.
    unfold terminal; crush.
  Qed.
  Hint Resolve nf_terminal : elnHints.

  Theorem nf_rt_equal : forall x,
  normal_form R x -> 
  forall y, clos_refl_trans A R x y -> x = y.
  Proof.
    unfold normal_form; 
    intros x H y x_y; induction x_y; crush;
    exfalso; repeat (autoSpecialize; crush).
  Qed.
  Hint Resolve nf_rt_equal : elnHints.

  Theorem nf_terminal_equal : forall x,
  normal_form R x -> 
  forall y, terminal R x y -> x = y.
  Proof.
    unfold terminal; crush.
  Qed. 
  Hint Resolve nf_terminal_equal : elnHints.

  Theorem terminal_step : forall x y z,
    R x y -> terminal R y z -> terminal R x z.
  Proof.
    unfold terminal; crush; eauto using rt_trans with sets.
  Qed.
  Hint Resolve terminal_step : elnHints.

  (* Lemma sn_rt_terminal : forall x y z,
    strongly_normalize R x -> 
    clos_refl_trans A R x y ->
    terminal R x z ->
    terminal R y z.
  Proof.
    Admitted.
  Hint Resolve sn_rt_terminal : elnHints. *)

  Lemma normal_form_step_false : forall x y,
    normal_form R x -> R x y -> False.
  Proof.
    unfold normal_form; intros; ecrush.
  Qed.
  Hint Resolve normal_form_step_false : elnHints.

  (* Lemma local_confluence_unique_terminal : forall x y z,
    local_confluence R -> 
    strongly_normalizing R ->
    R x y ->
    unique (fun z => terminal R y z) z ->
    unique (fun z => terminal R x z) z.
  Proof.
    intros x y z C SN x_y unique_y_z;
    destruct unique_y_z as [terminal_y_z H];
    assert (Hterminal_y_z := terminal_y_z);
    destruct terminal_y_z as [nf_z y_z];
    split; [ecrush | intros z2 terminal_x_z2];
    induction y_z as [y1 y2 | | ].
    -   


    split; [ecrush | intros z2 terminal_x_z2];
    destruct terminal_x_z2 as [nf_z2 x_z2];

    
    induction x_z2 as [x y2 x_y2 | | ].
    - destruct (C x y y2 x_y x_y2) as [u [Hy Hy2]].
      pose proof (nf_rt_equal y2 nf_z2 u Hy2) as H1.
      rewrite H1 in *.
      destruct (sn_rt_terminal y u z (SN y) Hy Hterminal_y_z).
      specialize (H u).
      assert (terminal R y u) by ecrush.
      crush.
    - exfalso. ecrush.
    - specialize (H z0).
      destruct (sn_rt_terminal z y z0 (SN z)).
      
      


    Admitted.
  Hint Resolve local_confluence_unique_terminal : elnHints. *)
  Print strongly_normalize_ind.
  Lemma local_confluence_and_strongly_normalizing : 
    local_confluence R -> 
    strongly_normalizing R ->
    forall x, exists! z, 
      terminal R x z /\ 
      forall y1 y2, clos_refl_trans A R x y1 -> 
                    clos_refl_trans A R x y2 -> 
                    unique (fun u => terminal R y1 u) z ->
                    unique (fun u => terminal R y2 u) z.
  Proof.
    intros C SN x;
    induction (SN x) as [| x y x_y SNy HSNy ].
    - exists x; unfold unique; split.
      * split.
       + ecrush.
       + intros y1 y2 x_y1 x_y2;
          pose proof (nf_rt_equal x H y1 x_y1) as H2;
          pose proof (nf_rt_equal x H y2 x_y2) as H3;
          rewrite H2 in *; rewrite H3 in *; ecrush.
      * ecrush. 
    - destruct HSNy as [z [[terminal_y_z H1] H2]].
      exists z.
      split; [split | intro x2].
      * ecrush.
      * intros y2 x_y2.
           induction x_y2.
           + admit.
           + split. ecrush. intros u Hu.
             destruct terminal_y_z.
             specialize (H1 z H0). 
           *** intros z2 terminal_y2_z2.
               specialize (H2 z2). 




      * unfold unique; ecrush.  unfold unique. ecrush split.
      pose proof (nf_rt_equal x H y1 x_y1) as H1.
      rewrite <- H1 in *. clear H1.
      pose proof (nf_rt_equal x H y2 x_y2) as H2.
      rewrite <- H2 in *. clear H2.
      unfold unique; crush.
    - pose proof (C x y )
    
    destruct HSNy as [z Hz].
      destruct Hz as [H1 H0].
      exists z. split.
      ecrush.
      intros x2 H2.
      destruct H2.
      induction H2.
      * admit.
      * exfalso. ecrush.
      *     
      ecrush.
  Qed.

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