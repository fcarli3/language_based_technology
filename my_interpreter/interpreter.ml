 (* TYPES *)
 type value = 
  | Int of int
  | Bool of bool
  | String of string;;

(*  ENVIRONMENT *)
type env = (string*value) list;;

(* EXPRESSIONS *)
type expr =
  | EInt of int
  | Ebool of bool
  | Estring of string
  | Evar of string
  | Let of string * expr
  | LetIn of string * expr * expr 
  | Plus of expr * expr
  | Minus of expr * expr
  | Mul of expr * expr
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Equal of expr * expr
  | Major of expr * expr
  | IfThenElse of expr * expr * expr;;

(* LOOKUP FUNCTION, SEARCH THE VALUE FOR THE GIVEN STRING IN THE ENVIRONMENT *)
let rec lookup (env : env) (s : string) : value =
  match env with
  | [] -> failwith("ERROR: Var not found!")
  | (i,v)::r -> if i=s then v else lookup r s;;

(* INTERPRETER *)
let rec eval (e : expr) (env : env) : (value*env) =
  match e with
  | EInt i -> (Int i, env)
  | Ebool b -> (Bool b, env)
  | Estring s -> (String s, env)
  | Evar v -> (lookup env v, env)
  | Let(s,e) -> let (_value, _) = eval e env in
                  let new_env = (s,_value)::env in
                    (Bool true,new_env) (* in this case return a pair where the first elem says that the environment has been modified  *)
  | LetIn(s,v,body) -> let (_value,_) = eval v env in
                        let new_env = (s,_value)::env in (* It is something like a push on the stack *)
                          eval body new_env
  | Plus(op1,op2) -> let (x1,_) = eval op1 env in
                      let (x2,_) = eval op2 env in
                        begin match (x1,x2) with 
                          | (Int e1, Int e2) -> (Int(e1 + e2),env)
                          | (_,_) -> failwith("ERROR: Operands are not integer!")
                        end
  | Minus(op1,op2) -> let (x1,_) = eval op1 env in
                        let (x2,_) = eval op2 env in
                          begin match (x1,x2) with 
                            | (Int e1, Int e2) -> (Int(e1 - e2),env)
                            | (_,_) -> failwith("ERROR: Operands are not integer!")
                          end
  | Mul(op1,op2) -> let (x1,_) = eval op1 env in
                      let (x2,_) = eval op2 env in
                        begin match (x1,x2) with 
                          | (Int e1, Int e2) -> (Int(e1 * e2),env)
                          | (_,_) -> failwith("ERROR: Operands are not integer!")
                        end
  | And(op1,op2) -> let (x1,_) = eval op1 env in
                      let (x2,_) = eval op2 env in
                        begin match (x1,x2) with 
                          | (Bool e1, Bool e2) -> (Bool(e1 && e2),env)
                          | (_,_) -> failwith("ERROR: Operands are not boolean!")
                        end
  | Or(op1,op2) -> let (x1,_) = eval op1 env in
                    let (x2,_) = eval op2 env in
                      begin match (x1,x2) with 
                        | (Bool e1, Bool e2) -> (Bool(e1 || e2),env)
                        | (_,_) -> failwith("ERROR: Operands are not boolean!")
                      end
  | Not(op) -> let (x1,_) = eval op env in
                begin match x1 with 
                  | Bool e1 -> (Bool(not(e1)),env)
                  | _ -> failwith("ERROR: Operand is not boolean!")
                end
  | Equal(op1,op2) -> let (x1,_) = eval op1 env in
                        let (x2,_) = eval op2 env in
                          begin match (x1,x2) with 
                            | (Bool e1, Bool e2) -> (Bool(e1 = e2),env)
                            | (Int e1, Int e2) -> (Bool(e1 = e2),env)
                            | (String e1, String e2) -> (Bool(e1 = e2),env)
                            | (_,_) -> failwith("ERROR: Unknown Type!")
                          end
  | Major(op1,op2) -> let (x1,_) = eval op1 env in
                        let (x2,_) = eval op2 env in
                          begin match (x1,x2) with 
                            | (Int e1, Int e2) -> (Bool(e1 > e2),env)
                            | (_,_) -> failwith("ERROR: Operands are not integer!")
                          end
  | IfThenElse(cond,e1,e2) -> let (c,_) = eval cond env in
                              begin match c with
                                | Bool b -> if b = true then eval e1 env else eval e2 env
                                | _ -> failwith("ERROR: Not bool!")
                              end;;

(* MAIN *)
let myEnv : env = [];;
let (_, new_env) = eval (Let("x", EInt 10)) myEnv;;
eval (Let("y", EInt 10)) new_env;;
