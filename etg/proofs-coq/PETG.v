From Coq Require Import Reals Psatz.
Require Import DETG Base.
Set Implicit Arguments.
Local Open Scope R_scope.

Module PETG.
  (* Skeleton interface that keeps P-ETG separate from core. *)
  Record RV (A:Type) := { sample : nat -> A }.

  Record EventRV (M:DETG) := {
    Lrv : RV (L M);
    Trv : RV R
  }.

  Definition dt_rv (M:DETG) (E1 E2:EventRV M) : RV R :=
    {| sample := fun n =>
         sample (A:=R) (Trv E2) n - sample (A:=R) (Trv E1) n |}.

  (* Placeholder: in a real dev, you would bring in mathcomp-analysis/Coquelicot/Iris-prob *)
End PETG.
