From Coq Require Import Reals Psatz.
Require Import Base DETG Frames Invariance Metric.
Set Implicit Arguments.
Local Open Scope R_scope.

Module Example1.
  (* Deterministic ETG with L = R and dist = |x-y| *)
  Program Instance Euclid1D : MetricSpace R := {
    dist x y := Rabs (x - y)
  }.
  (* 0 <= |x - y| *)
  Next Obligation.
    unfold dist; simpl. apply Rabs_pos.
  Qed.
  (* |x - y| = 0 <-> x = y, proved via squaring (no Rabs_eq_0) *)
  Next Obligation.
    unfold dist; simpl.
    split; intro H.
    - (* -> *)
      assert (Hsq: sq (x - y) = 0)
        by (unfold sq; rewrite <- (abs_sq_eq (x - y)); rewrite H; nra).
      apply sq_eq0 in Hsq. nra.
    - (* <- *)
      subst. unfold dist; simpl.
      rewrite Rminus_diag_eq by reflexivity.
      now rewrite Rabs_R0.
  Qed.
  (* |x - y| = |y - x| *)
  Next Obligation.
    unfold dist; simpl. rewrite Rabs_minus_sym. reflexivity.
  Qed.
  (* Triangle inequality: |x - z| <= |x - y| + |y - z| *)
  Next Obligation.
    unfold dist; simpl.
    replace (x - z) with ((x - y) + (y - z)) by nra.
    apply Rabs_triang.
  Qed.

  (* A concrete DETG instance *)
  Definition M : DETG := {| L := R; E := (R*R)%type;
     T_of := fun e => snd e; L_of := fun e => fst e;
     MS := Euclid1D; c := 1; c_pos := Rlt_0_1 |}.

  (* A trivial frame using the identity embedding x_of = id *)
  Definition F : Frame M := {| x_of := fun _ => 0%R |}.

  (* Sanity: invariance for a specific numeric case *)
  Example invariance_demo :
    let e1 := (0%R, 0%R) in let e2 := (2%R, 3%R) in
    let '(dt,dx) := @dtx M F e1 e2 in
    s2_num M (boost_dt (c M) 0.6 dt dx) (boost_dx (c M) 0.6 dt dx)
    = s2_num M dt dx.
  Proof.
    cbv zeta.
    remember (@dtx M F (0%R, 0%R) (2%R, 3%R)) as p eqn:Hp.
    destruct p as [dt dx].
    apply (@s2_boost_invariant_numbers M 0.6 dt dx).
    assert (Rabs 0.6 = 0.6) by (apply Rabs_right; lra).
    rewrite H; replace (c M) with 1 by (cbv [M]; reflexivity); lra.
  Qed.

End Example1.
