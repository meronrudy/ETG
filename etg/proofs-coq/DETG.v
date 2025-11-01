From Coq Require Import Reals Psatz.
Require Import Metric Base.
Set Implicit Arguments.
Local Open Scope R_scope.

Record DETG := {
  L : Type;
  E : Type;
  T_of : E -> R;          (* timestamps *)
  L_of : E -> L;          (* locations  *)
  MS : MetricSpace L;     (* spatial metric *)
  c : R;                  (* invariant speed *)
  c_pos : 0 < c
}.

Arguments dist {L} {_} _ _.

Section Deterministic.
  Context (M: DETG).
  Let c := c M.
  Let cpos := c_pos M.

  Definition dt (e1 e2: E M) : R := T_of M e2 - T_of M e1.
  Definition dx (e1 e2: E M) : R :=
    @dist (L M) (MS M) (L_of M e1) (L_of M e2).

  Definition s2 (e1 e2: E M) : R := c*c*(dt e1 e2)^2 - (dx e1 e2)^2.

  (* Causality as a definitional inequality *)
  Definition caus (e1 e2: E M) : Prop := dt e1 e2 >= (dx e1 e2) / c.

End Deterministic.
