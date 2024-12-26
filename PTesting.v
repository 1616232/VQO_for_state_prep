Require Import PQASM.
Require Import Testing.

Inductive basis_val := Nval (b:bool) | Rval (n:rz_val). (*same as PQASM, overrides Testing definition*)
