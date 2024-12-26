Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
Require Import Classical_Prop.
Require Import RZArith.
Require Import PQASM.

(*Require Import OQASM.
Require Import Coq.QArith.QArith.*)
Import Nat (eqb).
(*Import Coq.FSets.FMapList.*)
From Coq Require Import BinaryString.
From Coq Require Import Lists.ListSet.
(**********************)
(** Unitary Programs **)
(**********************)

Declare Scope exp_scope.
Delimit Scope exp_scope with expScope.
Local Open Scope exp_scope.
Local Open Scope nat_scope.

(* The type progress theorem. It says that given a aenv being empty, and the program type checked, 
      a program is either SKIP or can always be evaluated. *)
Lemma type_progress : 
    forall rmax T T' phi e , etype nil T e T' 
          -> exists r phi' e', @prog_sem rmax (phi,e) r (phi',e').
Proof.
  intros rmax T T' phi e Htype.
  induction Htype.
  - (* Case: Next *)
    exists R1, (app_inst rmax phi p), ESKIP.
    apply iota_sem.

  -  (* Case: Had *)
    exists R1, (apply_hads phi qs), ESKIP.
    apply had_sem.
  - (* Case: New *)
    exists R1, (add_new phi qs), ESKIP.
    apply new_sem.
     - (* Case: ESeq *)
    destruct IHHtype1 as [r1 [phi1 [e1' Hprog1]]].
    destruct IHHtype2 as [r2 [phi2 [e2' Hprog2]]].
    exists r1, phi1, (e1' [;] qb).
    apply seq_sem_2. 
    assumption.
 - (* Case: IFa *)
    destruct (simp_bexp b) eqn:Hb.
    + (* Simplifiable boolean expression *)
       destruct b0.
      * (* Case: b evaluates to true *)
        exists R1, phi, e1.
        apply if_sem_1.
        assumption.
      * (* Case: b evaluates to false *)
        exists R1, phi, e2.
        apply if_sem_2. 
        assumption.
    + (* Case: b evaluates to None *)
      exists R1, phi, (IFa b e1 e2).
      apply if_sem_3.
      assumption.
 - (* Case:  Meas *)
  remember (apply_mea rmax phi qs (fun _ => false)) as mea_res.
  destruct mea_res as [phi' rv].
  exists rv, phi', (exp_subst_c e x (a_nat2fb (fun _ => false) (length qs))).
  apply mea_sem.
 auto.
Qed.

(* type preservation. *)
Definition aenv_consist (aenv aenv': list var) := forall x, In x aenv -> In x aenv'.

Definition nor_consist (s: list posi) (phi: state) :=
  forall i, i < (fst phi) -> forall p, In p s -> exists v, (snd ((snd phi) i)) p = Nval v.

Definition rot_consist (s: list posi) (phi: state) :=
  forall i, i < (fst phi) -> forall p, In p s -> exists v, (snd ((snd phi) i)) p = Rval v.

Definition type_consist (T:list qrecord) (phi:state) :=
  forall s, In s T -> nor_consist (had s) phi /\ nor_consist (nor s) phi /\ rot_consist (rot s) phi.

Lemma type_preservation : 
    forall rmax aenv T T' phi phi' e e' r, etype aenv T e T' -> @prog_sem rmax (phi,e) r (phi',e') -> type_consist T phi
            -> exists aenv' T1 T2, etype aenv' T1 e' T2 /\ rec_eq T' T2 /\ type_consist T2 phi'.
Proof.
  intros rmax aenv T T' phi phi' e  e'  r Htype.
  -(* Case: Next *)
    exists aenv, T', T'.
    split.
    

      

Admitted.

