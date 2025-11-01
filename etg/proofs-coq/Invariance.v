From Coq Require Import Reals Psatz.
Require Import Base DETG Frames.
Set Implicit Arguments.
Local Open Scope R_scope.

Section Invariance.
  Context (M:DETG).

  Definition s2_num (dt dx:R) : R := (c M)*(c M)*dt^2 - dx^2.

  Theorem s2_boost_invariant_numbers
          (v dt dx:R)
          (Vb: Rabs v < c M) :
    s2_num (boost_dt (c M) v dt dx) (boost_dx (c M) v dt dx)
    = s2_num dt dx.
  Proof.
    unfold s2_num.
    eapply boost_invariance_1d; [apply c_pos | exact Vb].
  Qed.

  (* Lift to events under any frame that supplies signed differences. *)
  Theorem s2_boost_invariant_events (F:Frame M) (v:R)
          (Vb: Rabs v < c M) (e1 e2:E M) :
    let '(dt,dx) := @dtx M F e1 e2 in
    s2_num (boost_dt (c M) v dt dx) (boost_dx (c M) v dt dx)
    = s2_num dt dx.
  Proof.
    intros; apply s2_boost_invariant_numbers; assumption.
  Qed.

  (* Consequence: causal class (sign) invariances without Rcompare. *)
  Corollary s2_class_pos_invariant (F:Frame M) (v:R)
            (Vb: Rabs v < c M) (e1 e2:E M) :
    let '(dt,dx) := @dtx M F e1 e2 in
    (0 < s2_num (boost_dt (c M) v dt dx) (boost_dx (c M) v dt dx)) <->
    (0 < s2_num dt dx).
  Proof.
    remember (@dtx M F e1 e2) as Hpair eqn:Hp; destruct Hpair as [dt dx]; simpl.
    split; intro H.
    - rewrite (s2_boost_invariant_numbers v dt dx Vb) in H; exact H.
    - rewrite <- (s2_boost_invariant_numbers v dt dx Vb) in H; exact H.
  Qed.

  Corollary s2_class_zero_invariant (F:Frame M) (v:R)
            (Vb: Rabs v < c M) (e1 e2:E M) :
    let '(dt,dx) := @dtx M F e1 e2 in
    (s2_num (boost_dt (c M) v dt dx) (boost_dx (c M) v dt dx) = 0) <->
    (s2_num dt dx = 0).
  Proof.
    remember (@dtx M F e1 e2) as Hpair eqn:Hp; destruct Hpair as [dt dx]; simpl.
    split; intro H.
    - rewrite (s2_boost_invariant_numbers v dt dx Vb) in H; exact H.
    - rewrite <- (s2_boost_invariant_numbers v dt dx Vb) in H; exact H.
  Qed.

  Corollary s2_class_neg_invariant (F:Frame M) (v:R)
            (Vb: Rabs v < c M) (e1 e2:E M) :
    let '(dt,dx) := @dtx M F e1 e2 in
    (s2_num (boost_dt (c M) v dt dx) (boost_dx (c M) v dt dx) < 0) <->
    (s2_num dt dx < 0).
  Proof.
    remember (@dtx M F e1 e2) as Hpair eqn:Hp; destruct Hpair as [dt dx]; simpl.
    split; intro H.
    - rewrite (s2_boost_invariant_numbers v dt dx Vb) in H; exact H.
    - rewrite <- (s2_boost_invariant_numbers v dt dx Vb) in H; exact H.
  Qed.

End Invariance.
