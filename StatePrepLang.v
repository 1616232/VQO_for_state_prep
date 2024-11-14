Require Import OQASM.
Require Import PQASM.
Require Import BasicUtility.
Require Import Coq.QArith.QArith.
(* Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat.  *)



(*repeat until success: Inductive success or fail
if fail -> repeat until success*)

(*uniform superposition*)
(*Ry Had (posi)*)
Definition a: nat :=3.
Definition b: var := a.
Definition c: nat :=4.
Definition d: var := c.
Definition test: iota:= Ry (b,d) (5 / 4).


(*permutations*)
(*Fredkin gates; can be built with  *)

(*Hamming weight*)

(*Permutation*)