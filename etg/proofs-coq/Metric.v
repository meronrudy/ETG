From Coq Require Import Reals.
Set Implicit Arguments.
Local Open Scope R_scope.

Class MetricSpace (L:Type) := {
  dist : L -> L -> R;
  dist_nonneg : forall x y, 0 <= dist x y;
  dist_id : forall x y, dist x y = 0 <-> x = y;
  dist_sym : forall x y, dist x y = dist y x;
  dist_tri : forall x y z, dist x z <= dist x y + dist y z
}.
