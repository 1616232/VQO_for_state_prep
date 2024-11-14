Require Import OQASM.
Require Import PQASM.
Require Import BasicUtility.


(*repeat until success: Inductive success or fail
if fail -> repeat until success*)

(*uniform superposition*)
(*Ry Had (posi)*)
Definition a: var :=3.
Definition test: iota:= Ry (a,3).

(*permutations*)
(*Fredkin gates; can be built with  *)

(*Hamming weight*)

(*Permutation*)