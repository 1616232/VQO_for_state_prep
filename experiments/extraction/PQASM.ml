open BasicUtility
open Datatypes
open ListSet
open MathSpec
open PeanoNat
open VectorStates

type aexp =
| BA of var
| Num of int
| APlus of aexp * aexp
| AMult of aexp * aexp

type cbexp =
| CEq of aexp * aexp
| CLt of aexp * aexp

type mu =
| Add of posi list * (int -> bool)
| Less of posi list * (int -> bool) * posi
| Equal of posi list * (int -> bool) * posi

type iota =
| ISeq of iota * iota
| ICU of posi * iota
| Ora of mu
| Ry of posi * rz_val

type exp =
| ESKIP
| Next of iota
| Had of posi list
| New of posi list
| ESeq of exp * exp
| Meas of var * posi list * exp
| IFa of cbexp * exp * exp

(** val x_var : var **)

let x_var =
  0

(** val y_var : var **)

let y_var =
  succ 0

(** val z_var : var **)

let z_var =
  succ (succ 0)

(** val lst_posi : int -> var -> (var * int) list **)

let rec lst_posi n x =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> [])
    (fun m -> (x, m) :: (lst_posi m x))
    n

(** val uniform_state : int -> int -> exp -> exp **)

let uniform_state n m p =
  ESeq ((ESeq ((ESeq ((ESeq ((New (lst_posi n x_var)), (New ((y_var,
    0) :: [])))), (Had (lst_posi n x_var)))), (Next (Ora (Less
    ((lst_posi n x_var), (nat2fb m), (y_var, 0))))))), (Meas (z_var,
    (lst_posi n x_var), (IFa ((CEq ((BA z_var), (Num (succ 0)))), ESKIP,
    p)))))

type basis_val =
| Nval of bool
| Rval of rz_val

type eta_state = posi -> basis_val

(** val pi32 : int -> bool **)

let pi32 =
  update (update allfalse 0 true) (succ 0) true

(** val angle_sum : rz_val -> rz_val -> int -> int -> bool **)

let angle_sum f g rmax =
  cut_n (sumfb false f g) rmax

(** val angle_sub : rz_val -> rz_val -> int -> int -> bool **)

let angle_sub f g rmax =
  cut_n (sumfb false f (negatem rmax g)) rmax

(** val ry_rotate : eta_state -> posi -> rz_val -> int -> eta_state **)

let ry_rotate st p r rmax =
  match st p with
  | Nval b2 ->
    if b2
    then eupdate st p (Rval (angle_sub pi32 r rmax))
    else eupdate st p (Rval r)
  | Rval r1 -> eupdate st p (Rval (angle_sum r1 r rmax))

(** val set_diff_posi : posi set -> posi set -> posi set **)

let set_diff_posi =
  set_diff posi_eq_dec

(** val posi_list_to_bitstring_helper :
    posi list -> eta_state -> int -> int -> bool **)

let rec posi_list_to_bitstring_helper ps st n k =
  match ps with
  | [] -> false
  | a :: b ->
    if Nat.eqb k n
    then (match st a with
          | Nval b0 -> b0
          | Rval _ -> false)
    else posi_list_to_bitstring_helper b st n k

(** val posi_list_to_bitstring : posi list -> eta_state -> int -> bool **)

let posi_list_to_bitstring ps st =
  posi_list_to_bitstring_helper ps st 0

(** val mu_addition :
    posi list -> (int -> bool) -> eta_state -> int -> bool **)

let mu_addition ps n st =
  sumfb false (posi_list_to_bitstring ps st) n

(** val mu_less_helper :
    posi list -> (int -> bool) -> eta_state -> int -> bool **)

let rec mu_less_helper ps bitstring st n =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> false)
    (fun k ->
    match ps with
    | [] -> false
    | a :: b ->
      (match st a with
       | Nval j ->
         if (&&) (bitstring n) j
         then mu_less_helper b bitstring st k
         else bitstring n
       | Rval _ -> false))
    n

(** val mu_less : posi list -> (int -> bool) -> eta_state -> bool **)

let mu_less ps n st =
  mu_less_helper (List.rev ps) n st (length ps)

(** val mu_eq_helper :
    posi list -> (int -> bool) -> eta_state -> int -> bool **)

let rec mu_eq_helper ps bitstring st n =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> false)
    (fun k ->
    match ps with
    | [] -> true
    | a :: b ->
      (match st a with
       | Nval j ->
         if (&&) (bitstring n) j then mu_eq_helper b bitstring st k else false
       | Rval _ -> false))
    n

(** val mu_eq : posi list -> (int -> bool) -> eta_state -> bool **)

let mu_eq ps n st =
  mu_eq_helper (List.rev ps) n st (length ps)

(** val bitstring_to_eta : (int -> bool) -> posi list -> int -> eta_state **)

let rec bitstring_to_eta f l size posi0 =
  match l with
  | [] -> Nval false
  | x :: xs ->
    if posi_eq x posi0
    then Nval (f ((fun x y -> max 0 (x-y)) size (length (x :: xs))))
    else bitstring_to_eta f xs size posi0

(** val mu_handling : mu -> eta_state -> eta_state **)

let mu_handling m st =
  match m with
  | Add (ps, n) -> bitstring_to_eta (mu_addition ps n st) ps (length ps)
  | Less (ps, n, p) -> eupdate st p (Nval (mu_less ps n st))
  | Equal (ps, n, p) -> eupdate st p (Nval (mu_eq ps n st))

(** val instr_sem : int -> iota -> eta_state -> eta_state **)

let rec instr_sem rmax e st =
  match e with
  | ISeq (a, b) -> instr_sem rmax b (instr_sem rmax a st)
  | ICU (x, y) ->
    (match st x with
     | Nval j -> if j then instr_sem rmax y st else st
     | Rval _ -> st)
  | Ora m -> mu_handling m st
  | Ry (p, r) -> ry_rotate st p r rmax

(** val eval_aexp : (var -> int) -> aexp -> int **)

let rec eval_aexp env = function
| BA x -> env x
| Num n -> n
| APlus (e1, e2) -> (+) (eval_aexp env e1) (eval_aexp env e2)
| AMult (e1, e2) -> ( * ) (eval_aexp env e1) (eval_aexp env e2)

(** val eval_bexp : (var -> int) -> cbexp -> bool **)

let eval_bexp env = function
| CEq (a, b) -> Nat.eqb (eval_aexp env a) (eval_aexp env b)
| CLt (a, b) -> Nat.ltb (eval_aexp env a) (eval_aexp env b)

type tstate = posi list * eta_state

type fstate = (var -> int) * tstate

(** val new_env : var -> posi list -> fstate -> int -> int **)

let new_env x qs st b =
  if Nat.eqb b x
  then a_nat2fb (posi_list_to_bitstring qs (snd (snd st))) (length qs)
  else fst st b

(** val prog_sem_fix : int -> exp -> fstate -> fstate **)

let rec prog_sem_fix rmax e st =
  match e with
  | Next p -> ((fst st), ((fst (snd st)), (instr_sem rmax p (snd (snd st)))))
  | ESeq (k, m) -> prog_sem_fix rmax k (prog_sem_fix rmax m st)
  | Meas (x, qs, e1) ->
    prog_sem_fix rmax e1 ((new_env x qs st),
      ((set_diff_posi (fst (snd st)) qs), (snd (snd st))))
  | IFa (k, op1, op2) ->
    if eval_bexp (fst st) k
    then prog_sem_fix rmax op1 st
    else prog_sem_fix rmax op2 st
  | _ -> st
