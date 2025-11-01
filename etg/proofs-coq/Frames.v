From Coq Require Import Reals Psatz.
Require Import DETG Base.
Set Implicit Arguments.
Local Open Scope R_scope.

Module Frames.
  (* We model frames by giving a signed spatial coordinate x: L -> R.
     This is only used to form signed differences Δx.  In higher-dim, replace by R^n. *)
  Record Frame (M:DETG) := {
    x_of : L M -> R;
    (* Optional axiom if you want |Δx|=dist; not required for invariance over numbers. *)
  }.

  (* Differences induced by a frame *)
  Definition dtx (M:DETG) (F:Frame M) (e1 e2: E M) : R*R :=
    let dx := x_of F (L_of M e2) - x_of F (L_of M e1) in
    let dt := T_of M e2 - T_of M e1 in (dt, dx).

  (* Apply a 1D boost with velocity v to differences. *)
  Definition boost_diff (M:DETG) (v:R) (dt_dx:R*R) : R*R :=
    let '(dt,dx) := dt_dx in
    let dt' := boost_dt (c M) v dt dx in
    let dx' := boost_dx (c M) v dt dx in (dt',dx').

End Frames.

Export Frames.
