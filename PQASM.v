Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
Require Import Classical_Prop.
Require Import OQASM.
Require Import Coq.QArith.QArith.
Import Nat (eqb).
From Coq Require Import BinaryString.
(**********************)
(** Unitary Programs **)
(**********************)

Declare Scope exp_scope.
Delimit Scope exp_scope with expScope.
Local Open Scope exp_scope.
Local Open Scope nat_scope.

Inductive pexp := Oexp (e:exp) | H (p:posi) | PSeq (s1:pexp) (s2:pexp).

Notation "p1 [;] p2" := (PSeq p1 p2) (at level 50) : exp_scope.

Fixpoint inv_pexp p :=
  match p with
  | Oexp a => Oexp (inv_exp a)
  | H p => H p
  | PSeq p1 p2 => inv_pexp p2 [;] inv_pexp p1
   end.

Definition rand:= bool.
Inductive mu := Add (ps: list posi) (n:(nat-> bool)) (* we add nat to the bitstring represenation of ps *)
              | Less (ps : list posi) (n:(nat-> bool)) (p:posi) (* we compare ps with n (|ps| < n) store the boolean result in p. *)
              | Equal (ps : list posi) (n:(nat-> bool)) (p:posi) (* we compare ps with n (|ps| = n) store the boolean result in p. *).
Check mu.

Inductive iota:= SeqInst (k: iota) (m: iota) | ICU (x:posi) (y:iota)| Ora (e:mu) | Ry (p: posi) (r: rz_val).

Inductive e := Next (p: pexp) | Had (b:list posi) | New (b:list posi) 
| AddProg (k: iota) (m: iota)| Meas (x:list posi) | IFa (k: rand) (op1: e) (op2: e).

(*true -> 1, false -> 0, rz_val : nat -> bool, a bitstring represented as booleans *)
Inductive basis_val := Hval (b1: bool) (b2:bool) | Nval (b:bool) | Rval (n:rz_val).

Definition eta_state : Type := posi -> basis_val.
Fixpoint list_of_states (ps: list posi) (st: eta_state) : list basis_val :=
  match ps with 
  | [] => []
  | h::t => (st h)::(list_of_states t st)
  end.

Definition mu_sem (add_n :(nat->bool)->nat->bool) (n:(nat-> bool)): (nat-> bool) := add_n n.

Fixpoint position (p: posi) (l : list posi) : nat := 
  match l with 
  | [] => (0)
  | h::t => match (posi_eq h p) with 
            | true =>  1
            | false =>  1 + (position p t)
            end
  end.

Fixpoint swap (h: posi) (a: list posi) (b: list posi)

Definition permu (l : list posi) (f:nat -> bool) (G: list posi): nat->bool :=
  match G with 
  | [] => []
  | h::t => swap h position h l position 
  end.

Fixpoint push_to_st (G: list posi) (f' : nat -> bool) (st: eta_state) :=
  
Definition pi32 := update (update allfalse 0 true) 1 true.

Definition angle_sum (f g:rz_val) (rmax:nat) := cut_n (sumfb false f g) rmax.

Definition angle_sub (f g: rz_val) (rmax:nat) := cut_n (sumfb false f (negatem rmax g)) rmax.

Definition ry_rotate (st:eta_state) (p:posi) (r:rz_val) (rmax:nat): eta_state :=
   match st p with Hval b1 b2 => if b2 then st[ p |-> Rval (angle_sub pi32 r rmax) ] else st[ p |-> Rval r]
                  | Nval b2 => if b2 then st[ p |-> Rval (angle_sub pi32 r rmax) ] else st[ p |-> Rval r]
                  |  Rval r1 => st[ p |-> Rval (angle_sum r1 r rmax)]
   end.
   Check eta_state.

Fixpoint sumOfBits (st:eta_state) (str: list posi) (n:(nat-> bool)): eta_state :=
  match str with 
  | [] => st
  | h::t => match st h with 
      | Hval b1 b2 => if b2 then st[p |-> ]
      | Nval b2
      | Rval r1 
Fixpoint instr_sem (rmax:nat) (e:iota) (st: eta_state) (env: list (list posi * list posi * list posi)): eta_state :=
   match e with 
   | Ry p r => ry_rotate st p r rmax 
   | SeqInst a b => instr_sem rmax b (instr_sem rmax a st)
   | Ora m => match m with 
   | Add ps n => sumOfBits st ps n
   | Less ps n p =>
   | Equal ps n p =>
   end
 | ICU x y => match x with 
   | 0 -> 
   | 1 -> instr_sem rmax y st
   end.

Definition match_posi (a: posi) (b:posi): bool :=
  match a with
  | (w,x) => match b with 
      |(y,z) => match (eqb w y) with
          |false => false
          |true => match (eqb x z) with 
                |true => true
                |false => false
                end
          end
      end
    end.

Fixpoint disjoint_match (target: posi) (str: list posi): bool :=
  match str with 
  |[] => true
  | h::t => match match_posi h target with
      |true => disjoint_match target t 
      | false => false 
      end
    end.

Fixpoint disjoint_list (str: list posi): bool :=
    match str with
    | [] => true
    | h::t => match disjoint_match h t with
        | false => false
        | true => disjoint_list t
        end
     end.   

(*
Add [q1,q2] 1

take q1 and q2 value in st, and then compose them to be a bitstring, and then add 1, 
,after adding one, then you resolve them into two bits.

nat -> anything, use update

posi -> anything, use st[p |-> up_h (st p)]

1 / 2^rmax

rz_val : nat -> bool, a bitstring, 0 is the max number, and rz_val (rmax - 1) is the least significant bit,

0_position: 1/2. 
1_position: 1/4.
2_position: 1/8.

i * 2 pi  3/2 pi == rz_val , 0 -> True, 1 -> true ,, (1/2 + 1/4) * 2 pi 

*)

(* This is the semantics for basic gate set of the language. 
Fixpoint pexp_sem (env:var -> nat) (e:pexp) (st: posi -> val) : (posi -> val) :=
   match e with (Oexp e') => (exp_sem env e' st)
               | H p => st[p |-> up_h (st p)]
              | e1 [;] e2 => pexp_sem env e2 (pexp_sem env e1 st)
    end.

 (env:var -> nat) (i:iota) (st: posi -> val) : (posi -> val) :=

*)

(* Fixpoint instruction_sem (env:var -> nat) (i:iota) (st: posi -> val) : (posi -> val) :=
match i with
| Ry (p: posi) (r: Q) => match (st p) with
    | =>
    | => 
    | _ =>
| ICU (p: posi) (k: iota) => (instruction_sem env k st).
| AddInst (k: iota) (m: iota) => (instruction_sem env k st)
| mu (e:exp) (x:list posi) => (exp_sem exp). *)


(* Inductive well_typed_pexp (aenv: var -> nat) : env -> pexp -> env -> Prop :=
    | oexp_type : forall env e env', well_typed_oexp aenv env e env' -> well_typed_pexp aenv env (Oexp e) env'
    | rz_had : forall env b p q, Env.MapsTo (fst p) (Had b) env -> well_typed_pexp aenv env (Oexp (RZ q p)) env
    | rrz_had : forall env b p q, Env.MapsTo (fst p) (Had b) env -> well_typed_pexp aenv env (Oexp (RRZ q p)) env
    | h_nor : forall env env' p, Env.MapsTo (fst p) Nor env -> snd p = 0 ->
                  Env.Equal env' (Env.add (fst p) (Had 0) env) ->  
                  well_typed_pexp aenv env (H p) env'
    | h_had : forall env env' p b, Env.MapsTo (fst p) (Had b) env -> snd p = S b ->
              Env.Equal env' (Env.add (fst p) (Had (S b)) env) ->  
                  well_typed_pexp aenv env (H p) env'
    | pe_seq : forall env env' env'' e1 e2, well_typed_pexp aenv env e1 env' -> 
                 well_typed_pexp aenv env' e2 env'' -> well_typed_pexp aenv env (e1 [;] e2) env''. *)

Inductive pexp_WF (aenv:var -> nat): pexp -> Prop :=
     | oexp_WF : forall e, exp_WF aenv e -> pexp_WF aenv (Oexp e)
     | h_wf : forall p, snd p < aenv (fst p) -> pexp_WF aenv (H p)
      | pseq_wf : forall e1 e2, pexp_WF aenv e1 -> pexp_WF aenv  e2 -> pexp_WF aenv  (PSeq e1 e2).

(*
               | H p => st[p |-> up_h (st p)]

      | h_fresh : forall p p1 , p <> p1 -> exp_fresh aenv p (H p1)

      | h_neul : forall l y, exp_neu_l x l (H y) l

    | rz_had : forall env b p q, Env.MapsTo (fst p) (Had b) env -> well_typed_exp AE env (RZ q p)
    | rrz_had : forall env b p q, Env.MapsTo (fst p) (Had b) env -> well_typed_exp AE env (RRZ q p)

              | H p => ((fst p)::[])

    | h_nor : forall env env' p, Env.MapsTo (fst p) Nor env -> snd p = 0 ->
                  Env.Equal env' (Env.add (fst p) (Had 0) env) ->  
                  well_typed_pexp aenv env (H p) env'
    | h_had : forall env env' p b, Env.MapsTo (fst p) (Had b) env -> snd p = S b ->
              Env.Equal env' (Env.add (fst p) (Had (S b)) env) ->  
                  well_typed_pexp aenv env (H p) env'

      | h_wf : forall p, snd p < aenv (fst p) -> exp_WF aenv (H p).

*)

(*  Define approximate QFT in the Had basis by the extended type system. In this type system, 
    once a value is in Had basis,
     it will never be applied back to Nor domain, so that we can define more SR gates. *)
Fixpoint many_CR (x:var) (b:nat) (n : nat) (i:nat) :=
  match n with
  | 0 | 1 => SKIP (x,n)
  | S m  => if b <=? m then (many_CR x b m i ; (CU (x,m+i) (RZ n (x,i)))) else SKIP (x,m)
  end.

(* approximate QFT for reducing b ending qubits. *)
Fixpoint appx_QFT (x:var) (b:nat) (n : nat) (size:nat) :=
  match n with
  | 0    => Oexp (SKIP (x,n))
  | S m => if b <=? m then ((appx_QFT x b m size)) [;] (H (x,m))
                    [;] (Oexp (many_CR x b (size-m) m)) else Oexp (SKIP (x,m))
  end.

(* Match the K graph by LV decomposition, the following define the L part.  (H ; R(alpha)); H  |x> -> Sigma|y>. *)
Fixpoint half_k_graph (x:var) (r:nat) (size:nat) :=
   match size with 0 => (Oexp (SKIP (x,0)))
          | S m => (H (x,m)) [;] (Oexp (RZ r (x,m))) [;] half_k_graph x r m
   end.
