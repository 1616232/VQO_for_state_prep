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

(*add mod multiplication here, compilation to OQASM*)
Inductive mu := Add (ps: list posi) (n:(nat-> bool)) (* we add nat to the bitstring represenation of ps *)
              | Less (ps : list posi) (n:(nat-> bool)) (p:posi) (* we compare ps with n (|ps| < n) store the boolean result in p. *)
              | Equal (ps : list posi) (n:(nat-> bool)) (p:posi) (* we compare ps with n (|ps| = n) store the boolean result in p. *)
              | ModMult (ps : list posi) (n:(nat-> bool)) (m: (nat-> bool)).

Inductive iota:= ISeq (k: iota) (m: iota) | ICU (x:posi) (y:iota)| Ora (e:mu) | Ry (p: posi) (r: rz_val).

Coercion Ora : mu >-> iota.
Notation "e0 ; e1" := (ISeq e0 e1) (at level 50) : exp_scope.

Inductive exp := ESKIP | Next (p: iota) | Had (b:list posi) | New (b:list posi) 
| ESeq (k: exp) (m: exp) | Meas (x:var) (qs:list posi) (e1:exp) | IFa (k: cbexp) (op1: exp) (op2: exp).

Coercion Next : iota >-> exp.
Notation "e0 [;] e1" := (ESeq e0 e1) (at level 50) : exp_scope.

(* Examples. We use the constant hard-code variable names below. *)
Definition x_var : var := 0.
Definition y_var : var := 1.
Definition z_var : var := 2.

Fixpoint lst_posi (n:nat) (x:var) :=
   match n with 0 => nil | S m => (x,m)::(lst_posi m x) end.
(* Check lst_posi.  *)
(* we prepare a superposition of m different basis-states, where n is the length of qubits in x_var. 
  nat2fb turns a nat number to a bitstring. 
  we define a function P for a one step process of the repeat-until-success.
  In Ocaml, you can input a variable name for P, 
 *)
Definition uniform_state (n:nat) (m:nat) := 
          fun P => New (lst_posi n x_var) [;] New ([(y_var,0)]) [;] Had (lst_posi n x_var)
                             [;] Less (lst_posi n x_var) (nat2fb m) (y_var,0) [;] Meas z_var (lst_posi n x_var) (IFa (CEq z_var (Num 1)) ESKIP P).

(* Check uniform_state. *)
Fixpoint repeat_operator_ICU_Add (a b: list posi):= 
  match a with 
| nil => ESKIP 
| h::t => (repeat_operator_ICU_Add t b) [;] (ICU h (Ora (Add b (nat2fb 1))))
end.

Definition hamming_weight_superposition (n m:nat) := 
  fun P =>  New (lst_posi n x_var) [;] New (lst_posi n y_var) [;] Had (lst_posi n x_var)
                             [;] repeat_operator_ICU_Add (lst_posi n x_var) (lst_posi n y_var)
                               [;] Meas z_var (lst_posi n x_var) (IFa (CEq z_var (Num 1)) ESKIP P).

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

  Fixpoint mu_addition_reps (ps: list posi) (n:(nat-> bool)) (st: eta_state) (reps: nat): (nat-> bool):=
    match reps with 
    |0 => n
    | S m => mu_addition_reps ps (mu_addition ps n st) st m 
    end.

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

(*add case here for modulo multiplication*)
Definition mu_handling (rmax:nat) (m: mu) (st: eta_state) : eta_state :=
  match m with 
  | Add ps n => bitstring_to_eta (mu_addition ps n st) ps (length ps)
  | Less ps n p => st[ p|-> Nval (mu_less ps n st)]
  | Equal ps n p => st[ p|-> Nval (mu_eq ps n st)]
  | ModMult ps n m =>  bitstring_to_eta (nat2fb 
  ((a_nat2fb (posi_list_to_bitstring ps st) rmax) * (a_nat2fb n rmax) mod (a_nat2fb m rmax))) ps (length ps)
  end.
Fixpoint instr_sem (rmax:nat) (e:iota) (st: eta_state): eta_state :=
   match e with 
   | Ry p r => ry_rotate st p r rmax 
   | ISeq a b => instr_sem rmax b (instr_sem rmax a st)
   | Ora m => mu_handling rmax m st
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
(* Check simp_bexp. *)
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
  (* Check apply_hads. *)

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
(* Check exp_subst_c. *)
Inductive prog_sem {rmax:nat}: config -> R -> config -> Prop :=
   seq_sem_1 : forall phi e,  prog_sem (phi, ESKIP [;] e) (1:R) (phi,e)
 | seq_sem_2: forall phi phi' r e1 e1' e2, prog_sem (phi,e1) r (phi',e1') -> prog_sem (phi, e1 [;] e2) r (phi', e1' [;] e2)
 | if_sem_3: forall phi b e1 e2, simp_bexp b = None -> prog_sem (phi, IFa b e1 e2) 1 (phi, IFa b e1 e2)
 | if_sem_1 : forall phi b e1 e2, simp_bexp b = Some true -> prog_sem (phi, IFa b e1 e2) 1 (phi, e1)
 | if_sem_2 : forall phi b e1 e2, simp_bexp b = Some false -> prog_sem (phi, IFa b e1 e2) 1 (phi, e2)
 | new_sem : forall phi bl, prog_sem (phi, New bl) 1 (add_new phi bl, ESKIP)
 | iota_sem : forall phi e, prog_sem (phi, Next e) 1 (app_inst rmax phi e, ESKIP)
 | had_sem : forall phi bl, prog_sem (phi, Had bl) 1 (apply_hads phi bl, ESKIP)
 | mea_sem : forall phi x qs e bl phi' rv, apply_mea rmax phi qs bl = (phi',rv) 
           -> prog_sem (phi, Meas x qs e) rv (phi', exp_subst_c e x (a_nat2fb bl (length qs))).
  
(* progress theorem *)
Lemma type_progress : 
    forall rmax aenv T T' phi e , etype aenv T e T' 
          -> exists r phi' e', @prog_sem rmax (phi,e) r (phi',e').
Proof.
  intros rmax aenv T T' phi e Htype.
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

(* Testing Semantics. *)


Fixpoint eval_aexp (env: (var -> nat)) (e:aexp) :=
 match e with BA x => env x
            | Num n => n
            | e1 [+] e2 => (eval_aexp env e1) + (eval_aexp env e2)
            | e1 [*] e2 => (eval_aexp env e1) * (eval_aexp env e2)
 end.

Definition eval_bexp (env: (var -> nat)) (e:cbexp) :=
  match e with CEq a b => (eval_aexp env a) =? (eval_aexp env b)
             | CLt a b => (eval_aexp env a) <? (eval_aexp env b)
  end.

Definition tstate : Type := list posi * eta_state.

Definition fstate : Type := (var -> nat) * tstate.

Definition new_env (x:var) (qs:list posi) (st:fstate) :=
  (fun b => if (b =? x) then (a_nat2fb (posi_list_to_bitstring qs (snd (snd st))) (length qs)) else (fst st) b).
   

Fixpoint prog_sem_fix (rmax: nat) (e: exp)(st: fstate) : fstate := match e with 
| Next p => (fst st, (fst (snd st),instr_sem rmax p (snd (snd st))))
| ESeq k m => prog_sem_fix rmax k (prog_sem_fix rmax m st)
| IFa k op1 op2=> if (eval_bexp (fst st) k) then (prog_sem_fix rmax op1 st) else (prog_sem_fix rmax op2 st)
| ESKIP => st
| Had b => st
| New b => st
| Meas x qs e1 => prog_sem_fix rmax e1 ((new_env x qs st),(set_diff_posi (fst (snd st)) qs, snd (snd st)))
end.

Definition env_equivb vars (st st' : var -> nat) :=
  forallb (fun x =>  st x =? st' x) vars.


Fixpoint rz_val_eq (n:nat) (x y : rz_val) :=
    match n with 0 => true
               | S m => Bool.eqb (x m) (y m) && rz_val_eq m x y
    end.

Definition basis_val_eq (rmax:nat) (x y : basis_val) :=
   match (x,y) with (Nval b, Nval b') => Bool.eqb b b'
                | (Rval bl1, Rval bl2) => rz_val_eq rmax bl1 bl2
                | _ => false
   end.

Definition st_equivb (rmax:nat) (vars: list posi) (st st': eta_state) :=
  forallb (fun x => basis_val_eq rmax (st x) (st' x)) vars.

From Coq Require Import Arith NArith.
From QuickChick Require Import QuickChick.
Require Import Testing.

Definition bv2Eta (n:nat) (x:var) (l: N) : eta_state :=
   fun p => if (snd p <? n) && (fst p =? x) then Nval (N.testbit_nat l (snd p)) else Nval false.

Module Simple.
(* 
  Definition rmax := 16.

  Definition m := 1000. *)

  (* Definition cvars := [z_var]. *)

  Definition qvars (n: nat) : list posi := (y_var,0)::(lst_posi n x_var).

  Definition init_env : var -> nat := fun _ => 0.

  (* Definition init_st : eta_state := fun _ => (Rval (fun (n:nat) => true)). *)

  (* n= number of qubits to put in this state, m is their maximum value. Here, both lead to skips, but one sets z_var equal to 1, which affects how simple_eq tests it.*)
  Definition uniform_s (n:nat) (m:nat) := 
       Less (lst_posi n x_var) (nat2fb m) (y_var,0) [;] Meas z_var ([(y_var,0)]) (IFa (CEq z_var (Num 1)) ESKIP ESKIP).
Check uniform_s.
  Definition simple_eq (e:exp) (v:N) (k n m: nat) := 
     let (env,qstate) := prog_sem_fix n e (init_env,(qvars k,bv2Eta n x_var v)) in
        if env z_var =? 1 then a_nat2fb (posi_list_to_bitstring (fst qstate) (snd qstate)) n <? m  else true.
Check simple_eq.
  Conjecture uniform_correct :
    forall (vx : N) (a b c j k: nat), simple_eq (uniform_s j k) vx a b c = true.

End Simple.

QuickChick (Simple.uniform_correct 100).

Definition exp_comparison (e1 e2: exp): bool :=
  match e1 with 
  | Next p => match e2 with 
        | Next q => true
        | _ => false
        end
  | ESKIP => match e2 with 
      | ESKIP => true
      | _ => false
      end
  | ESeq k m => match e2 with 
      | ESeq o p => true
      | _ => false
      end 
  | Had b=> match e2 with 
      | Had c => true
      | _ => false
      end  
| New b=> match e2 with 
      | New c => true
      | _ => false
      end 
  | Meas x qs e1 => match e2 with 
      | Meas y qs2 e2 => true
      | _ => false
      end 
  | IFa k op1 op2=> match e2 with 
      | IFa l op3 op4 => true
      | _ => false
      end              
  end.

(*
Definition exp_map_comparison (e1: (exp->exp)) (e2: (exp->exp)): bool:=
(exp_comparison (e1 ESKIP) (e2 ESKIP))
&& (exp_comparison (e1 IFa _ _ _) (e2 IFa)). 
Lemma exp_of_uniform_state: forall (m n: nat) (e1 e2 e3: exp), (exp_comparison (uniform_state m n e3) (ESeq e1 e2))=true.
Proof. intros. unfold uniform_state. unfold exp_comparison.  reflexivity. Qed. 
*)
From QuickChick Require Import QuickChick.


Module Test_prop. 
Conjecture uniform_state_eskip_behavior: forall (m: nat) (n: nat),
exp_comparison ((uniform_state m n) ESKIP) ((uniform_state n m) ESKIP) = true.
(* Check uniform_state_eskip_behavior. *)
Conjecture uniform_state_new_behavior: forall (m n o: nat) (x: var),
exp_comparison ((uniform_state m n) (New (lst_posi o x))) ((uniform_state n m) (New (lst_posi o x))) = true.
(* Check uniform_state_new_behavior. *)
Conjecture uniform_state_new_eskip_behavior: forall (m n o: nat) (x: var),
exp_comparison ((uniform_state m n) (New (lst_posi o x))) ((uniform_state n m) ESKIP) = true.

End Test_prop.

(* Takes a boolean and returns 1 if it's true and 0 if it's false *)
Definition bool_to_nat (b: bool) :=
  match b with
  | true => 1
  | false => 0
  end.

Module Hamming.

  Definition state_qubits := 20.
  Definition hamming_qubits := 6.
  (* Definition target_hamming_w := 17. *)

  (* classical variables *)
  Definition cvars := [z_var].

  (* Fixpoint concat (l1 l2: list (var * nat)) :=
    match l1 with
    | nil => l2
    | _ => (fst l1)::(concat (snd l1) l2)
    end. *)

  (* Quantum registers, accessible with x_var and y_var *)
  Definition qvars : list posi := (lst_posi state_qubits x_var).

  (* Environment to start with; all variables set to 0 *)
  Definition init_env : var -> nat := fun _ => 0.

  (* not sure if this is actually needed *)
  Definition init_st : eta_state := fun _ => Nval false.

  (* Returns an expression to run P on each qubit position in reg*)
  Fixpoint repeat (reg: list posi) (P: (posi -> exp)) :=
    match reg with
    | nil => ESKIP
    | p::r => (P p) [;] (repeat r P)
    end.

  (* For the hamming_test_eq, gets the hamming weight of a bitstring
    bs is the bitstring, n is the length of the bitstring *)
  Fixpoint hamming_weight_of_bitstring (n: nat) (bs: (nat -> bool)) :=
    match n with
    | 0 => 0
    | S m => (bool_to_nat (bs n)) + (hamming_weight_of_bitstring m bs)
    end.

  (* Prepare a uniform superposition across all states that have a hamming weight equal to w.
    n is the number of qubits in the register being preapred; 
    h_n is the number of qubits to use when measuring the hamming weight
  *)
  Definition hamming_state (n:nat) (h_n:nat) (w:nat) :=
    New (lst_posi n x_var) [;] New (lst_posi h_n y_var) [;] Had (lst_posi n x_var) [;]
      (repeat (lst_posi n x_var) (fun (p:posi) => (ICU p (Ora (Add (lst_posi h_n y_var) (nat2fb 1)))))) [;] 
      Meas z_var (lst_posi h_n y_var) (IFa (CEq z_var (Num w)) ESKIP ESKIP).

  Definition hamming_test_eq (e:exp) (v:N) := 
     let (env,qstate) := prog_sem_fix state_qubits e (init_env,(qvars,bv2Eta state_qubits x_var v)) in
        if env z_var =?  (hamming_weight_of_bitstring state_qubits 
           (posi_list_to_bitstring (fst qstate) (snd qstate))) then true else false.

  Conjecture hamming_state_correct:
    forall (vx : N) (n: nat), hamming_test_eq (hamming_state state_qubits hamming_qubits n) vx = true.

End Hamming.
(* Check @choose. *)
(* Check returnGen. *)
(* Sample (choose (0,10)). *)
QuickChick (Hamming.hamming_state_correct 100).

Module AmplitudeAmplification.

  (* Returns an expression to run P on each qubit position in reg*)
  Fixpoint repeat (reg: list posi) (P: (posi -> exp)) :=
    match reg with
    | nil => ESKIP
    | p::r => (P p) [;] (repeat r P) 
    end.
(* Like repeat, but also gives the function an index to work with*)
Fixpoint repeat_ind (reg: list posi) (index: nat) (P: (posi -> nat -> exp)) :=
  match reg with
  | nil => ESKIP
  | p::r => (P p index) [;] (repeat_ind r (index-1) P)
  end.
  Fixpoint pow_2 (n: nat) :=
    match n with
    | 0 => 1
    | S m => 2*(pow_2 (m))
    end.
Check nat2fb.
    Definition amplitude_amplification_state (n r:nat) (h_n:nat) (w:nat) :=
    New (lst_posi n x_var) [;] New (lst_posi h_n y_var) [;] Had (lst_posi n x_var) [;]
      repeat (lst_posi h_n y_var)  (fun (p:posi) => Next (Ry p (fun (a:nat)=> nat2fb a (r/pow_2 n)))) [;]
      repeat (lst_posi h_n y_var) (fun (p:posi) => repeat_ind (lst_posi n x_var) n (fun (k: posi) (j: nat) => (ICU p (Ry p (fun (a:nat)=> nat2fb a (r/pow_2 (n-j))))))).
      
End AmplitudeAmplification.

Module SumState.

  (* Number of quantum registers *)
  Definition num_reg_test := 3.

  (* Size of each register *)
  Definition reg_size_test := 4.

  (* Target Sum *)
  Definition k_test := 20.

  (* classical variables *)
  Definition cvars := [z_var].

  (* Quantum registers; x_var stores all of the state qbits*)
  Definition qvars : list posi := (lst_posi (num_reg_test*reg_size_test) x_var).

  (* Environment to start with; all variables set to 0 *)
  Definition init_env : var -> nat := fun _ => 0.

  (* Returns an expression to run P on each qubit position in reg*)
  Fixpoint repeat (reg: list posi) (P: (posi -> exp)) :=
    match reg with
    | nil => ESKIP
    | p::r => (P p) [;] (repeat r P)
    end.

  (* Like repeat, but also gives the function an index to work with*)
  Fixpoint repeat_ind (reg: list posi) (index: nat) (P: (posi -> nat -> exp)) :=
    match reg with
    | nil => ESKIP
    | p::r => (P p index) [;] (repeat_ind r (index-1) P)
    end.

  (* Returns a list of variables that start at start_var *)
  Fixpoint lst_var (len: nat) (start_var: var) :=
    match len with
    | 0 => nil
    | S len_m => ((len_m+(start_var:nat)):var)::(lst_var len_m start_var)
    end.

  (* Repeats an operation on a list of quantum registers *)
  Fixpoint repeat_reg (P: (list posi -> exp)) (regs: list var) (reg_size: nat):=
    match regs with
    | nil => ESKIP
    | r::rs => (P (lst_posi reg_size r)) [;] (repeat_reg P rs reg_size)
    end.

  Fixpoint pow_2 (n: nat) :=
    match n with
    | 0 => 1
    | S m => 2*(pow_2 (m))
    end.

  Definition sum_state (num_reg:nat) (reg_size:nat) (target_sum:nat) :=
    let prep_list := (lst_var num_reg x_var) in 
      let sum_var := ((x_var:nat)+num_reg):var in
        (repeat_reg New prep_list reg_size) [;] (New (lst_posi (reg_size+num_reg) sum_var)) [;]
        (
          repeat_reg (
            fun (lp: list posi) => (
              repeat_ind lp reg_size (fun (p: posi) (index: nat) => (
                ICU p (Ora (Add (lst_posi (reg_size + num_reg) sum_var) (nat2fb (pow_2 index))))
              ))
            )
          )
          prep_list
          reg_size
        ) [;]
        Meas z_var (lst_posi (reg_size+num_reg) sum_var) (IFa (CEq z_var (Num target_sum)) ESKIP ESKIP).

  (* Gets a register from a bitstring as a natural number *)
  Fixpoint bitstring_slice (reg: nat) (reg_size: nat) (ind: nat) (bs: (nat -> bool)) :=
    match ind with
    | 0 => 0
    | S m => (bitstring_slice reg reg_size m bs) * 2 + (bool_to_nat (bs ((reg - 1) * reg_size + (ind-1))))
    end.

  (* Sum of the integer values in a bitstring in big endian (MSB first) order. reg_size is the number of bits in each integer and n is the number of integers to add up*)
  Fixpoint sum_of_bitstring (n: nat) (reg_size: nat) (bs: (nat -> bool)) :=
    match n with
    | 0 => 0
    | S m => (bitstring_slice n reg_size reg_size bs) + (sum_of_bitstring m reg_size bs)
    end.

  (* Just need to get this to work *)
  Definition sum_test_eq (e:exp) (v:N) :=
    let state_qubits := num_reg_test * reg_size_test in
      let (env,qstate) := prog_sem_fix state_qubits e (init_env,(qvars,bv2Eta state_qubits x_var v)) in
        if env z_var =? k_test then (sum_of_bitstring num_reg_test reg_size_test (posi_list_to_bitstring (fst qstate) (snd qstate))) =? k_test else true.

  Conjecture sum_state_correct:
    forall (vx : N), sum_test_eq (sum_state num_reg_test reg_size_test k_test) vx = true.

End SumState.

QuickChick (SumState.sum_state_correct).

Module ModExpState.

  Definition c_test := 3.
  Definition N_test := 34.

  Definition num_qubits_test := 8.
  Definition num_exp_qubits_test := 7.

  (* Environment to start with; all variables set to 0 *)
  Definition init_env : var -> nat := fun _ => 0.

  (* Quantum registers; x_var stores all of the state qubits*)
  Definition qvars : list posi := (lst_posi (num_qubits_test) x_var).
  
  (* Returns c^n mod m. c is the base number, n is the exponent, m is the mod factor, 
  and max_iter is the maximum number of iterations this function should have. 
  It's needed to placate Coq. This function requires about log_2 n recursive steps. *)
  Fixpoint mod_pow (c n m max_iter: nat) :=
    match max_iter with
    | 0 => 1 mod m
    | S l => 
      if n =? 0 then 1 
      else 
        let u := (mod_pow c (n/2) m l) in
          if (n mod 2 =? 0) then 
            ((u*u) mod m) 
          else 
            ((((u*u) mod m)*c) mod m)
    end.

  (* Returns c^n *)
  Fixpoint pow(c n: nat) :=
    match n with 
    | 0 => 1
    | S m => c * (pow c m)
    end.

  Fixpoint repeat (reg: list posi) (P: (posi -> exp)) :=
    match reg with
    | nil => ESKIP
    | p::r => (P p) [;] (repeat r P)
    end.

  (* Like repeat, but also gives the function an index to work with*)
  Fixpoint repeat_ind (reg: list posi) (index: nat) (P: (posi -> nat -> exp)) :=
    match reg with
    | nil => ESKIP
    | p::r => (repeat_ind r (index-1) P) [;] (P p index)
    end.

  Fixpoint fst_reg (reg_1_size: nat) (bs: (nat -> bool)) :=
    match reg_1_size with
    | 0 => 0
    | S m => (fst_reg m bs) * 2 + (bool_to_nat (bs (reg_1_size-1)))
    end.

  Fixpoint snd_reg (reg_1_size reg_2_size: nat) (bs: (nat -> bool)) :=
    match reg_2_size with
    | 0 => 0
    | S m => (snd_reg reg_1_size m bs) * 2 + (bool_to_nat (bs (reg_1_size + reg_2_size-1)))
    end.

  Definition mod_exp_state (num_qubits c num_exp_qubits N: nat) :=
    New (lst_posi num_qubits x_var) [;] New (lst_posi num_exp_qubits y_var) [;]
    Had (lst_posi num_qubits x_var) [;]
    (repeat_ind
      (lst_posi num_qubits x_var)
      num_qubits
      (fun (p: posi) (i: nat) => (
        let A := (mod_pow c (pow 2 (i-1)) N (i)) in
          (ICU p (Ora (ModMult (lst_posi num_exp_qubits y_var) (nat2fb A) (nat2fb N))))
      )
      )
    ).

  Definition mod_exp_test_eq (e:exp) (v:N) := 
    let state_qubits := num_qubits_test in
      let (env,qstate) := prog_sem_fix state_qubits e (init_env,(qvars,bv2Eta state_qubits x_var v)) in
        (snd_reg num_qubits_test num_exp_qubits_test (posi_list_to_bitstring (fst qstate) (snd qstate))) =? 
          ((mod_pow c_test (fst_reg num_qubits_test (posi_list_to_bitstring (fst qstate) (snd qstate)))) N_test num_qubits_test + 2).
          
  Conjecture mod_exp_state_correct:
    forall (vx : N), mod_exp_test_eq (mod_exp_state num_qubits_test c_test num_exp_qubits_test N_test) vx = true.

End ModExpState.

QuickChick (ModExpState.mod_exp_state_correct).
