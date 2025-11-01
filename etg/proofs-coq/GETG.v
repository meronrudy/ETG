From Coq Require Import Reals Psatz.
Require Import Metric DETG.
Set Implicit Arguments.
Local Open Scope R_scope.

Module GETG.
  (* Time-varying metric field — minimal interface for later proofs. *)
  Record Geometry (L:Type) := {
    g_t : R -> (L -> L -> R);  (* a family of distances; you can require MetricSpace per t *)
  }.

  (* Evolution rule placeholder *)
  Parameter evolve : forall {L}, Geometry L -> R -> Geometry L.

End GETG.
