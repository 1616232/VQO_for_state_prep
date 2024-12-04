Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
Require Import Classical_Prop.
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

Inductive aexp := BA (x:var) | Num (n:nat) | APlus (e1:aexp) (e2:aexp) | AMult (e1:aexp) (e2:aexp).

(* Coercion means that in a function or an inductive relation, var can be viewed as aexp. *)
Coercion BA : var >-> aexp.

(* Turnning prefix notation to mixfix notation. *)
Notation "e0 [+] e1" := (APlus e0 e1) (at level 50) : exp_scope.
Notation "e0 [*] e1" := (AMult e0 e1) (at level 50) : exp_scope.

Inductive cbexp := CEq (x:aexp) (y:aexp) | CLt (x:aexp) (y:aexp).

Inductive mu := Add (ps: list posi) (n:(nat-> bool)) (* we add nat to the bitstring represenation of ps *)
              | Less (ps : list posi) (n:(nat-> bool)) (p:posi) (* we compare ps with n (|ps| < n) store the boolean result in p. *)
              | Equal (ps : list posi) (n:(nat-> bool)) (p:posi) (* we compare ps with n (|ps| = n) store the boolean result in p. *).

Inductive iota:= ISeq (k: iota) (m: iota) | ICU (x:posi) (y:iota)| Ora (e:mu) | Ry (p: posi) (r: rz_val).

Notation "e0 ; e1" := (ISeq e0 e1) (at level 50) : exp_scope.

Inductive exp := ESKIP | Next (p: iota) | Had (b:list posi) | New (b:list posi) 
| ESeq (k: exp) (m: exp) | Meas (x:var) (qs:list posi) (e1:exp) | IFa (k: cbexp) (op1: exp) (op2: exp).

Coercion Next : iota >-> exp.
Notation "e0 [;] e1" := (ESeq e0 e1) (at level 50) : exp_scope.

(*true -> 1, false -> 0, rz_val : nat -> bool, a bitstring represented as booleans *)
Inductive basis_val := Nval (b:bool) | Rval (n:rz_val).

Definition eta_state : Type := posi -> basis_val.
Fixpoint list_of_states (ps: list posi) (st: eta_state) : list basis_val :=
  match ps with 
  | [] => []
  | h::t => (st h)::(list_of_states t st)
  end.

Fixpoint position (p: posi) (l : list posi) : nat := 
  match l with 
  | [] => (0)
  | h::t => match (posi_eq h p) with 
            | true =>  1
            | false =>  1 + (position p t)
            end
  end.

Definition swap (f:nat -> bool) (x: nat) (y: nat): nat->bool :=
  fun k => if eqb k x then f y else if eqb k y then f x else f k.

Fixpoint permu (l : list posi) (f:nat -> bool) (G: list posi): nat->bool :=
  match G with 
  | [] => f
  | h::t => permu l (swap f (position h l) (position h G)) t
  end.

  Fixpoint push_to_st_helper (n: nat ) (G: list posi) (f' : nat -> bool) (st: eta_state): eta_state :=
    match G with 
    | [] => st
    | h::t => push_to_st_helper (n + 1) t f' (eupdate st h (Nval (f' n)))
    end.

Definition push_to_st (G: list posi) (f' : nat -> bool) (st: eta_state): eta_state :=
  match G with 
  | [] => st
  | h::t => push_to_st_helper 2 t f' (eupdate st h (Nval (f' 1)))
  end.

Definition pi32 := update (update allfalse 0 true) 1 true.

Definition angle_sum (f g:rz_val) (rmax:nat) := cut_n (sumfb false f g) rmax.

Definition angle_sub (f g: rz_val) (rmax:nat) := cut_n (sumfb false f (negatem rmax g)) rmax.

Definition ry_rotate (st:eta_state) (p:posi) (r:rz_val) (rmax:nat): eta_state :=
   match st p with  Nval b2 => if b2 then st[ p |-> Rval (angle_sub pi32 r rmax) ] else st[ p |-> Rval r]
                  |  Rval r1 => st[ p |-> Rval (angle_sum r1 r rmax)]
   end.

(*The following contains helper functions for records. *)
Definition qrecord : Type := (list posi * list posi * list posi).

Definition had (q:qrecord) := fst (fst q).

Definition nor (q:qrecord) := snd (fst q).

Definition rot (q:qrecord) := snd q.

Definition nor_sub (q:qrecord) (l:list posi) := (had q, l, rot q).

Definition had_sub (q:qrecord) (l:list posi) := (l, nor q, rot q).

Definition rec_union (q:qrecord) := (had q) ++ (nor q) ++ (rot q).

Definition flat_union (q:list qrecord) := fold_left (fun a b => a++rec_union b) q nil.

Definition set_inter_posi := set_inter posi_eq_dec.

Definition set_diff_posi := set_diff posi_eq_dec.

Definition qrecord_diff (q:qrecord) (l:list posi) := (set_diff_posi (had q) l, set_diff_posi (nor q) l, set_diff_posi (rot q) l).

(* Defining typing rules here. *)

(* Defining the inductive relation for disjoint. *)
Inductive disjoint : list posi -> Prop :=
   dis_empty : disjoint nil
  | dis_many : forall q qs, ~ In q qs -> disjoint qs -> disjoint (q::qs). 

(* subset definition. May turn it into bool type function. *)
Inductive sublist : list posi -> list posi -> Prop :=
   sublist_empty : forall qs, sublist nil qs
 | sublist_many : forall q qs1 qs2, In q qs2 -> sublist qs1 qs2 -> sublist (q::qs1) qs2.


Inductive type_aexp : list var -> aexp -> Prop :=
   | ba_type : forall env x, In x env -> type_aexp env x
   | num_type : forall env n, type_aexp env (Num n)
   | plus_type : forall env e1 e2, type_aexp env e1 -> type_aexp env e2 -> type_aexp env (APlus e1 e2)
   | mult_type : forall env e1 e2, type_aexp env e1 -> type_aexp env e2 -> type_aexp env (AMult e1 e2).

Inductive type_cbexp : list var -> cbexp -> Prop :=
  | ceq_type : forall env a b, type_aexp env a -> type_aexp env b -> type_cbexp env (CEq a b)
  | clt_type : forall env a b, type_aexp env a -> type_aexp env b -> type_cbexp env (CLt a b).

Inductive type_mu : list posi -> mu -> Prop :=
   type_add : forall qs v, disjoint qs -> type_mu qs (Add qs v)
 | type_less: forall qs q v, disjoint (q::qs) -> type_mu (q::qs) (Less qs v q)
 | type_eq:   forall qs q v, disjoint (q::qs) -> type_mu (q::qs) (Equal qs v q). 


(* Equivalence Relations among records *)
Inductive rec_eq : list qrecord -> list qrecord -> Prop :=
   join_eq : forall q1 q2 q3 q4 q5 q6 qs, rec_eq ((q1,q2,q3)::(q4,q5,q6)::qs) ((q1++q4,q2++q5,q3++q6)::qs)
 | nor_split_eq : forall q1 q2 qs, rec_eq ((nil,q1++q2,nil)::qs) ((nil,q1,nil)::(nil,q2,nil)::qs)
 | had_split_eq : forall q1 q2 qs, rec_eq ((q1++q2,nil,nil)::qs) ((q1,nil,nil)::(q2,nil,nil)::qs)
 | swap_eq : forall qs1 qs2, rec_eq (qs1++qs2) (qs2++qs1).


(* Type Rules. *)

Inductive ityping : list qrecord -> iota -> list qrecord -> Prop :=
   rec_eq_ty : forall ia T1 T2 T3, rec_eq T1 T2 -> ityping T2 ia T3 -> ityping T1 ia T3
 | ry_nor : forall p r T, ityping ((nil,([p]),nil)::T) (Ry p r) ((nil,nil,([p]))::T)
 | ry_rot : forall th T p r ps, rot th = (p::ps) -> ityping (th::T) (Ry p r) (th::T)
 | mu_nor : forall qs mu th T, type_mu qs mu -> sublist qs (nor th) -> ityping (th::T) (Ora mu) (th::T)
 | cu_nor : forall q qs ia th T, nor th = (q::qs) -> ityping ((nor_sub th qs)::T) ia ((nor_sub th qs)::T) -> ityping (th::T) (ICU q ia) (th::T)
 | cu_had : forall q qs ia th T, nor th = (q::qs) -> ityping ((had_sub th qs)::T) ia ((had_sub th qs)::T) -> ityping (th::T) (ICU q ia) (th::T)
 | iseq_ty : forall qa qb T1 T2 T3, ityping T1 qa T2 -> ityping T2 qb T3 -> ityping T1 (ISeq qa qb) T2.


Inductive etype : list var -> list qrecord -> exp -> list qrecord -> Prop :=
   next_ty : forall s p T, ityping T p T -> etype s T (Next p) T
 | had_ty : forall qs s T, etype s ((nil,qs,nil)::T) (Had qs) ((qs,nil,nil)::T)
 | new_ty : forall qs s T, disjoint qs -> set_inter_posi qs (flat_union T) = nil -> etype s T (New qs) ((nil,qs,nil)::T)
 | eseq_ty : forall s qa qb T1 T2 T3, etype s T1 qa T2 -> etype s T2 qb T3 -> etype s T1 (ESeq qa qb) T2
 | eif_ty : forall b e1 e2 s T T1, type_cbexp s b -> etype s T e1 T1 -> etype s T e2 T1 -> etype s T (IFa b e1 e2) T
 | mea_ty : forall x qs e s th T T1, sublist qs (rec_union th) -> etype (x::s) ((qrecord_diff th qs)::T) e T1 -> etype s (th::T) (Meas x  qs e) T1.

(* Semantic Functions. *)
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

Fixpoint posi_list_to_bitstring_helper (ps: list posi) (st: eta_state) (n: nat): (nat-> bool) :=
    fun k=>  match ps with 
      |[] => false
      |a::b => match eqb k n with
          |true => match (st a) with 
              | Rval r =>  false 
              | Nval b =>  b 
              end
          | false => posi_list_to_bitstring_helper b st n k
          end
          end.
Definition posi_list_to_bitstring (ps: list posi) (st: eta_state): (nat-> bool) :=
    posi_list_to_bitstring_helper ps st 0.
    
Definition mu_addition (ps: list posi) (n:(nat-> bool)) (st: eta_state): (nat-> bool) :=
  sumfb false (posi_list_to_bitstring ps st) n.

Fixpoint mu_less_helper (ps: list posi) (bitstring:(nat-> bool)) (st: eta_state) (n: nat) : bool :=
  match n with 
    | 0 => false
    | S k => match ps with 
          | [] => false
          |a::b => match (st a) with 
          | Rval r =>  false 
          | Nval j => if ((bitstring n) && j)
          then (mu_less_helper b bitstring st k)
          else (bitstring n)
            end
          end
      end.    
Definition mu_less (ps: list posi) (n:(nat-> bool)) (st: eta_state): bool := 
  mu_less_helper (rev ps) n st (length ps).

Fixpoint mu_eq_helper (ps: list posi) (bitstring:(nat-> bool)) (st: eta_state) (n: nat) : bool :=
  match n with 
    | 0 => false
    | S k => match ps with 
      | [] => true
      |a::b => match (st a) with 
        | Rval r =>  false 
        | Nval j => if ((bitstring n) && j) 
        then mu_eq_helper b bitstring st k
        else false  
        end
    end
  end.    
  Definition mu_eq (ps: list posi) (n:(nat-> bool)) (st: eta_state): bool := 
    mu_eq_helper (rev ps) n st (length ps).

Fixpoint bitstring_to_eta (f:nat -> bool) (l:list posi) (size:nat): eta_state :=
  match l with nil => (fun posi => Nval false)
             | x::xs => (fun y => if (posi_eq x y) then Nval (f (size - length (x::xs))) else (bitstring_to_eta f xs size) y)
  end.
Definition mu_handling (m: mu) (st: eta_state) : eta_state :=
  match m with 
  | Add ps n => bitstring_to_eta (mu_addition ps n st) ps (length ps)
  | Less ps n p => st[ p|-> Nval (mu_less ps n st)]
  | Equal ps n p => st[ p|-> Nval (mu_eq ps n st)]
  end.
Fixpoint instr_sem (rmax:nat) (e:iota) (st: eta_state): eta_state :=
   match e with 
   | Ry p r => ry_rotate st p r rmax 
   | ISeq a b => instr_sem rmax b (instr_sem rmax a st)
   | Ora m => mu_handling m st
  | ICU x y => match st x with 
      | Rval r =>  st 
      | Nval j => if j then instr_sem rmax y st else st
        end  
   end.

(* Program Semantics. *)
Definition state : Type := nat * (nat -> R * eta_state).
Definition config : Type := state * exp.
Definition bottom_state : nat -> R * eta_state := fun i => (R0, fun q => Nval false).

(* simp boolean expressions. *)
Fixpoint simp_aexp (e:aexp) :=
 match e with Num n => Some n
            | e1 [+] e2 => match simp_aexp e1
                                    with None => None
                                       | Some v1 => match simp_aexp e2 
                                               with None => None
                                                  | Some v2 => Some (v1 + v2)
                                                    end
                           end
            | e1 [*] e2 => match simp_aexp e1
                                    with None => None
                                       | Some v1 => match simp_aexp e2 
                                               with None => None
                                                  | Some v2 => Some (v1 * v2)
                                                    end
                           end
           | _ => None
 end.

Definition simp_bexp (e:cbexp) :=
  match e with CEq a b => match simp_aexp a with Some v1 =>
                                     match simp_aexp b with Some v2 => Some (v1 =? v2) | _ => None end 
                                                 | _ => None end
             | CLt a b => match simp_aexp a with Some v1 =>
                                     match simp_aexp b with Some v2 => Some (v1 <? v2) | _ => None end 
                                                 | _ => None end
  end.

(* add new qubits. *)
Definition add_new_eta (s:eta_state) (q:posi) := s[q |-> Nval false].

Fixpoint add_new_elem (n:nat) (s:nat -> R * eta_state) (q:posi) :=
   match n with 0 => s
              | S m => update (add_new_elem m s q) m (fst (s m), add_new_eta (snd (s m)) q)
   end.

Fixpoint add_new_list (n:nat) (s:nat -> R * eta_state) (q:list posi) :=
  match q with nil => s
             | x::xs => add_new_elem n (add_new_list n s xs) x
  end.
Definition add_new (s:state) (q:list posi) := (fst s, add_new_list (fst s) (snd s) q).

Fixpoint app_inst' (rmax:nat) (n:nat) (s:nat -> R * eta_state) (e:iota) :=
   match n with 0 => s
             | S m => update (app_inst' rmax m s e) m (fst (s m), instr_sem rmax e (snd (s m)))
   end.
Definition app_inst (rmax:nat) (s:state) (e:iota) := (fst s, app_inst' rmax (fst s) (snd s) e).


(* apply had operations. *)

Definition single_had (s:R * eta_state) (q:posi) (b:bool) :=
  match s with (phase,base) => 
    match (base q) with Rval v => (phase, base)
                      | Nval v =>
                if b then 
                  (if v then ((Rmult (Rdiv (Ropp 1) (sqrt(2))) phase):R, base[q |-> Nval b]) 
                        else ((Rmult (Rdiv 1 (sqrt(2))) phase):R, base[q |-> Nval b]))
                     else ((Rmult (Rdiv 1 (sqrt(2))) phase):R, base[q |-> Nval b])
    end
  end.

Fixpoint add_had' (n size:nat) (s:nat -> R * eta_state) (q:posi) :=
   match n with 0 => s
              | S m => update (update (add_had' m size s q) m (single_had (s m) q false)) (size + m) (single_had (s m) q true)
   end.
Definition add_had (s:state) (q:posi) := (2 * fst s, add_had' (fst s) (fst s) (snd s) q).

Fixpoint apply_hads (s:state) (qs : list posi) :=
  match qs with nil => s
              | x::xs => add_had (apply_hads s xs) x
  end.

Fixpoint turn_angle_r (rval :nat -> bool) (n:nat) (size:nat) : R :=
   match n with 0 => (0:R)
             | S m => (if (rval m) then (1/ (2^ (size - m))) else (0:R)) + turn_angle_r rval m size
   end.
Definition turn_angle (rval:nat -> bool) (n:nat) : R :=
      turn_angle_r (fbrev n rval) n n.

(* apply computational basis measurement operations. *)
Fixpoint single_mea (rmax n:nat) (s:nat -> R * eta_state) (q:posi) (b:bool) :=
  match n with 0 => (0, R0, bottom_state)
             | S m => 
    match single_mea rmax m s q b with (num, prob, new_s) =>
       match (snd (s m)) q with Rval r => 
         if b then (S num,Rplus prob (Rmult (sin (turn_angle r rmax)) ((fst (s m))^2)), update new_s m (s m))
              else (S num,Rplus prob (Rmult (cos (turn_angle r rmax)) ((fst (s m))^2)), update new_s m (s m))
                            | Nval b1 => 
         if Bool.eqb b b1 then (S num, Rplus prob ((fst (s m))^2), update new_s m (s m))
                    else (num, prob, new_s)
       end
    end
  end.

Fixpoint amp_reduce (n:nat) (s: nat -> R * eta_state) (r:R) :=
   match n with 0 => s
             | S m => update (amp_reduce m s r) m (Rdiv (fst (s m)) (sqrt r), snd (s m))
   end.

Definition move_1 (f : nat -> bool) := fun i => f (i + 1).

Fixpoint apply_mea' (rmax:nat) (n:nat) (s:nat -> R * eta_state) (qs:list (posi * bool)) :=
   match qs with nil => ((n,s),R1)
               | (x,b)::xs => match apply_mea' rmax n s xs with ((new_n,new_s),re) =>
                             match single_mea rmax new_n new_s x b with (na,ra,sa) =>
                              ((na,amp_reduce na sa ra), Rmult re ra)
                             end
                          end
    end.

Fixpoint zip_b (qs:list posi) (bl: nat -> bool) :=
    match qs with nil => nil
                | x::xs => (x,bl 0)::(zip_b xs (move_1 bl))
    end.

Definition apply_mea (rmax:nat) (s:state) (qs:list posi) (bl:nat -> bool) : state * R :=
   apply_mea' rmax (fst s) (snd s) (zip_b qs bl).

Fixpoint aexp_subst_c (a:aexp) (x:var) (n:nat) :=
  match a with BA y => if x =? y then Num n else BA y
             | Num m => Num m
             | APlus e1 e2 => APlus (aexp_subst_c e1 x n) (aexp_subst_c e2 x n)
             | AMult e1 e2 => AMult (aexp_subst_c e1 x n) (aexp_subst_c e2 x n)
  end.


Definition bexp_subst_c (a:cbexp) (x:var) (n:nat) :=
  match a with CEq e1 e2 => CEq (aexp_subst_c e1 x n) (aexp_subst_c e2 x n)
             | CLt e1 e2 => CLt (aexp_subst_c e1 x n) (aexp_subst_c e2 x n)
  end.

Fixpoint exp_subst_c (a:exp) (x:var) (n:nat) :=
  match a with ESKIP => ESKIP
             | Next p => Next p
             | Had b => Had b
             | New b => New b
             | ESeq e1 e2 => ESeq (exp_subst_c e1 x n) (exp_subst_c e2 x n)
             | Meas y qs e => if x =? y then Meas y qs e else Meas y qs (exp_subst_c e x n)
             | IFa b e1 e2 => IFa (bexp_subst_c b x n) (exp_subst_c e1 x n) (exp_subst_c e2 x n)
  end.


Inductive prog_sem {rmax:nat}: config -> R -> config -> Prop :=
   seq_sem_1 : forall phi e,  prog_sem (phi, ESKIP [;] e) (1:R) (phi,e)
 | seq_sem_2: forall phi phi' r e1 e1' e2, prog_sem (phi,e1) r (phi',e1') -> prog_sem (phi, e1 [;] e2) r (phi', e1' [;] e2)
 | if_sem_1 : forall phi b e1 e2, simp_bexp b = Some true -> prog_sem (phi, IFa b e1 e2) 1 (phi, e1)
 | if_sem_2 : forall phi b e1 e2, simp_bexp b = Some false -> prog_sem (phi, IFa b e1 e2) 1 (phi, e2)
 | new_sem : forall phi bl, prog_sem (phi, New bl) 1 (add_new phi bl, ESKIP)
 | iota_sem : forall phi e, prog_sem (phi, Next e) 1 (app_inst rmax phi e, ESKIP)
 | had_sem : forall phi bl, prog_sem (phi, Had bl) 1 (apply_hads phi bl, ESKIP)
 | mea_sem : forall phi x qs e bl phi' rv, apply_mea rmax phi qs bl = (phi',rv) 
           -> prog_sem (phi, Meas x qs e) rv (phi', exp_subst_c e x (a_nat2fb bl (length qs))).
   

(* progress theorem *)
Lemma type_progress : 
    forall rmax aenv T T' phi e, etype aenv T e T' 
          -> exists r phi' e', @prog_sem rmax (phi,e) r (phi',e').
Proof.
Admitted.


(* type preservation. *)
(* We might need to have some theorem to show the relationship between phi and phi'. *)
Definition aenv_consist (aenv aenv': list var) := forall x, In x aenv -> In x aenv'.


Lemma type_preservation : 
    forall rmax aenv T T' phi phi' e e' r, etype aenv T e T' -> @prog_sem rmax (phi,e) r (phi',e')
            -> exists aenv' T1 T2, etype aenv' T1 e' T2 /\ rec_eq T' T2.
Proof.
Admitted.


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

(* Inductive pexp_WF (aenv:var -> nat): pexp -> Prop :=
     | oexp_WF : forall e, exp_WF aenv e -> pexp_WF aenv (Oexp e)
     | h_wf : forall p, snd p < aenv (fst p) -> pexp_WF aenv (H p)
      | pseq_wf : forall e1 e2, pexp_WF aenv e1 -> pexp_WF aenv  e2 -> pexp_WF aenv  (PSeq e1 e2). *)

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
(* Fixpoint many_CR (x:var) (b:nat) (n : nat) (i:nat) :=
  match n with
  | 0 | 1 => SKIP (x,n)
  | S m  => if b <=? m then (many_CR x b m i ; (CU (x,m+i) (RZ n (x,i)))) else SKIP (x,m)
  end. *)

(* approximate QFT for reducing b ending qubits. *)
(* Fixpoint appx_QFT (x:var) (b:nat) (n : nat) (size:nat) :=
  match n with
  | 0    => Oexp (SKIP (x,n))
  | S m => if b <=? m then ((appx_QFT x b m size)) [;] (H (x,m))
                    [;] (Oexp (many_CR x b (size-m) m)) else Oexp (SKIP (x,m))
  end. *)

(* Match the K graph by LV decomposition, the following define the L part.  (H ; R(alpha)); H  |x> -> Sigma|y>. *)
(* Fixpoint half_k_graph (x:var) (r:nat) (size:nat) :=
   match size with 0 => (Oexp (SKIP (x,0)))
          | S m => (H (x,m)) [;] (Oexp (RZ r (x,m))) [;] half_k_graph x r m
   end. *)
