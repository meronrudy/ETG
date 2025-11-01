From Coq Require Import Reals Psatz Field.
Set Implicit Arguments.
Set Asymmetric Patterns.
Local Open Scope R_scope.

Module Base.
  (* Basic helpers *)
  Definition sq (x:R) : R := x*x.
  Lemma sq_nonneg x : 0 <= sq x. Proof. unfold sq; nra. Qed.
  Lemma sq_eq0 x : sq x = 0 -> x = 0. Proof. unfold sq; nra. Qed.

  (* Absolute value square identity *)
  Lemma abs_sq_eq (x:R) : (Rabs x) * (Rabs x) = x * x.
  Proof. unfold Rabs; destruct (Rcase_abs x); nra. Qed.

  (* Gamma and 1D Lorentz boost w.r.t. invariant speed c>0. *)
  Definition gamma (c v:R) : R := / sqrt (1 - (v*v)/(c*c)).

  Lemma gamma_real (c v:R) : 0 < c -> Rabs v < c -> 0 < gamma c v.
  Proof.
    intros Cpos Vlt.
    unfold gamma.
    set (a := Rabs v).
    (* Show (1 - (v^2)/(c^2)) > 0 via (c-a)(c+a) = c^2 - a^2 > 0 *)
    assert (H1: 0 < c - a) by (unfold a in *; nra).
    assert (Ha_nonneg: 0 <= a) by (unfold a; apply Rabs_pos).
    assert (H2: 0 < c + a) by (unfold a in *; nra).
    assert (Hnum_a: 0 < c*c - a*a).
    { replace (c*c - a*a) with ((c - a)*(c + a)) by nra.
      apply Rmult_lt_0_compat; assumption. }
    assert (Hnum: 0 < c*c - v*v).
    { unfold a in Hnum_a. rewrite abs_sq_eq in Hnum_a. exact Hnum_a. }
    assert (Cpos2: 0 < c*c) by nra.
    assert (Hdenpos: 0 < (c*c - v*v)/(c*c))
      by (apply Rdiv_lt_0_compat; [exact Hnum | exact Cpos2]).
    assert (Cneq0: c <> 0) by (apply Rgt_not_eq; exact Cpos).
    assert (HdenposD: 0 < 1 - (v*v)/(c*c)).
    { replace (1 - (v*v)/(c*c)) with ((c*c - v*v)/(c*c)) by (field; auto).
      exact Hdenpos. }
    apply Rinv_0_lt_compat, sqrt_lt_R0; exact HdenposD.
  Qed.

  (* 1D Lorentz transform on differences (Δx, Δt) → (Δx', Δt'). *)
  Definition boost_dt (c v dt dx:R) : R :=
    let g := gamma c v in g*(dt - (v*dx)/(c*c)).
  Definition boost_dx (c v dt dx:R) : R :=
    let g := gamma c v in g*(dx - v*dt).

  (* Invariance of the quadratic form c^2 dt^2 - dx^2 under the 1D boost. *)
  Lemma boost_invariance_1d (c v dt dx:R)
        (Cpos: 0 < c) (Vb: Rabs v < c) :
    c*c*(boost_dt c v dt dx)^2 - (boost_dx c v dt dx)^2
    = c*c*dt^2 - dx^2.
  Proof.
    unfold boost_dt, boost_dx, gamma.
    set (g := / sqrt (1 - (v*v)/(c*c))).
    (* Factor (g*g) cleanly *)
    assert (Hfactor:
      c*c* (g*(dt - (v*dx)/(c*c)))^2 - (g*(dx - v*dt))^2
      = (g*g) * (c*c*(dt - (v*dx)/(c*c))^2 - (dx - v*dt)^2)) by nra.
    rewrite Hfactor; clear Hfactor.
    (* Denominator positivity: D > 0 *)
    set (D := 1 - (v*v)/(c*c)).
    assert (Hpos: 0 < D).
    { subst D.
      set (a := Rabs v).
      assert (H1: 0 < c - a) by (unfold a in *; nra).
      assert (Ha_nonneg: 0 <= a) by (unfold a; apply Rabs_pos).
      assert (H2: 0 < c + a) by (unfold a in *; nra).
      assert (Hnum_a: 0 < c*c - a*a).
      { replace (c*c - a*a) with ((c - a)*(c + a)) by nra.
        apply Rmult_lt_0_compat; assumption. }
      assert (Hnum: 0 < c*c - v*v)
        by (unfold a in Hnum_a; rewrite abs_sq_eq in Hnum_a; exact Hnum_a).
      assert (Cpos2: 0 < c*c) by nra.
      assert (Hdenpos: 0 < (c*c - v*v)/(c*c))
        by (apply Rdiv_lt_0_compat; [exact Hnum | exact Cpos2]).
      assert (Cneq0: c <> 0) by (apply Rgt_not_eq; exact Cpos).
      assert (HdenposD: 0 < 1 - (v*v)/(c*c)).
      { replace (1 - (v*v)/(c*c)) with ((c*c - v*v)/(c*c)) by (field; auto).
        exact Hdenpos. }
      exact HdenposD. }
    (* Derive g*g = /D *)
    assert (Eg2: g*g = / D).
    { unfold g. change (1 - (v*v)/(c*c)) with D.
      assert (Spos: 0 < sqrt D) by (apply sqrt_lt_R0; exact Hpos).
      assert (Sneq: sqrt D <> 0) by (apply Rgt_not_eq; exact Spos).
      rewrite <- (Rinv_mult_distr (sqrt D) (sqrt D) Sneq Sneq).
      now rewrite (sqrt_def D (Rlt_le _ _ Hpos)). }
    (* Algebraic identity inside the brackets: avoid fragile field-side conditions. *)
    assert (Hinner: c*c*(dt - (v*dx)/(c*c))^2 - (dx - v*dt)^2
                    = D*(c*c*dt^2 - dx^2)).
    { subst D.
      assert (Cneq0: c <> 0) by (apply Rgt_not_eq; exact Cpos).
      field; auto. }
    rewrite Hinner, Eg2.
    (* g*g * (D * X) = (g*g*D) * X = 1 * X via Eg2 *)
    rewrite <- Rmult_assoc.
    assert (Dnz: D <> 0) by (apply Rgt_not_eq; exact Hpos).
    replace (/ D * D) with 1 by (field; exact Dnz).
    rewrite Rmult_1_l; reflexivity.
  Qed.
End Base.

Export Base.
