
 (* PERMISSIONS *)
 type permission =
 | Read
 | Write
 | Exec

(* LANGUAGE CONSTRUCTS *)
type expr =
  | ENone
  | EInt of int
  | EBool of bool
  | EString of string
  | EVar of string
  | LetIn of string * expr * expr (* string, value to associate to string, body of let. i.e x (ide) = 5 (exp) in x + 10 (exp)  *)
  | Plus of expr * expr (* + of Int * Int *)
  | Minus of expr * expr (* - of Int * Int *)
  | Mul of expr * expr (* * of Int * Int *)
  | And of expr * expr (* && of Bool * Bool *)
  | Or of expr * expr (* || of Bool * Bool *)
  | Not of expr (* ! of Bool *)
  | Equal of expr * expr (* e1 == e2 *)
  | Greater of expr * expr (* e1 > e2 *)
  | Minor of expr * expr (* e1 < e2 *)
  | IfThenElse of expr * expr * expr (* check, then, else *)
  | Fun of string * expr * permission list (* Fun is anonymous, 'ide' is the formal parameter, 'expr' is the body *)
  | Call of expr * expr (* 'expr' is the function, 'expr' is the actual parameter *)
  | EnableP of expr * permission (* 'expr' is a function, 'permission' is the permission to enable *)
  | DisableP of expr * permission (* 'expr' is a function, 'permission' is the permission to disable *)
;; 

type iexpr = 
  | StackInsp of expr (* 'expr' is a function of which permissions should be checked *)
;;

(* POLYMORPHIC ENVIRONMENT: LIST OF PAIRS (STRING, VALUE) *)
type 'v env = (string * 'v) list;;

(* LANGUAGE TYPES *)
 type value = 
 | None
 | Int of int
 | Bool of bool
 | String of string
 | Closure of string * expr * (value) env
;;

(* --- DECLARATION OF FUNCTIONS --- *)

(* CHECK IF STRING s HAS AN ASSOCIATED VALUE IN THE ENVIRONMENT env *)
let rec lookup (env : 'v env) (s : string) : value =
  match env with
  | [] -> failwith("ERROR: Var not found!")
  | (i,v)::r -> if (i=s) then 
                  v 
                else 
                  lookup r s
;;

(* CHECK IF A CERTAIN PERMISSION p IS PART OF A LIST OF PERMISSION p_list *)
let rec isIn (p : permission) (p_list : permission list) : bool = 
  match p_list with
  | [] -> false
  | perm::l -> if (p=perm) then 
                true 
              else 
                isIn perm l
;;

(* CHECK IF A LIST OF PERMISSIONS OF A FUNCTION fList MATCHES THE LIST OF GLOBAL PERMISSIONS permList *)
let rec checkPermissions (fList : permission list) (permList : permission list) : bool = 
  match fList with
  | [] -> true
  | p1::l1 -> if (isIn p1 permList) = true then 
                checkPermissions l1 permList 
              else 
                false
;;

(* REMOVE A PERMISSION perm FROM A LIST OF PERMISSIONS pList AND RETRIEVES THE MODIFIED LIST *)
let rec removePermission (perm : permission) (pList : permission list) : permission list =
  match pList with
  | [] -> []
  | p::l -> if (p=perm) then 
              l
            else 
              p :: removePermission perm l
;;

(* --- INTERPRETER --- *)

(* BACK-END INTERPRETER (TRANSPARENT TO THE PROGRAMMER) USED ONLY TO IMPLEMENT THE STACK INSPECTION MECHANISM *)
let rec ieval (ie : iexpr) (perm_list : permission list) (env : 'v env) : value =
  match ie with
  | StackInsp(func) -> begin match func with
                        | Fun(p, fbody, flist) -> if (checkPermissions flist perm_list) = true then 
                                                    Closure(p, fbody, env) 
                                                  else 
                                                    failwith("ERROR: Forbidden operation!")
                        | _ -> failwith("ERROR: Not a function!")
                      end
;; 

(* EXTENDED INTERPRETER WITH A LIST OF ENABLED PERMISSION AT RUNTIME *)
let rec eval (e : expr) (perm_list: permission list) (env : 'v env) : value =
  match e with
  | ENone -> None
  | EInt i -> Int i
  | EBool b -> Bool b
  | EString s -> String s
  | EVar v -> lookup env v
  | LetIn(s, v, body) -> let _value = eval v perm_list env in
                          let new_env = (s, _value)::env in 
                            eval body perm_list new_env
  | Plus(op1, op2) -> let x1 = eval op1 perm_list env in
                        let x2 = eval op2 perm_list env in
                          begin match (x1, x2) with 
                            | (Int e1, Int e2) -> Int(e1 + e2)
                            | (_, _) -> failwith("ERROR: Operands are not integer!")
                          end
  | Minus(op1, op2) -> let x1 = eval op1 perm_list env in
                        let x2 = eval op2 perm_list env in
                          begin match (x1, x2) with 
                            | (Int e1, Int e2) -> Int(e1 - e2)
                            | (_, _) -> failwith("ERROR: Operands are not integer!")
                          end
  | Mul(op1, op2) -> let x1 = eval op1 perm_list env in
                      let x2 = eval op2 perm_list env in
                        begin match (x1, x2) with 
                          | (Int e1, Int e2) -> Int(e1 * e2)
                          | (_, _) -> failwith("ERROR: Operands are not integer!")
                        end
  | And(op1, op2) -> let x1 = eval op1 perm_list env in
                      let x2 = eval op2 perm_list env in
                        begin match (x1, x2) with 
                          | (Bool e1, Bool e2) -> Bool(e1 && e2)
                          | (_, _) -> failwith("ERROR: Operands are not boolean!")
                        end
  | Or(op1, op2) -> let x1 = eval op1 perm_list env in
                    let x2 = eval op2 perm_list env in
                      begin match (x1, x2) with 
                        | (Bool e1, Bool e2) -> Bool(e1 || e2)
                        | (_, _) -> failwith("ERROR: Operands are not boolean!")
                      end
  | Not(op) -> let x1 = eval op perm_list env in
                begin match x1 with 
                  | Bool e1 -> Bool(not(e1))
                  | _ -> failwith("ERROR: Operand is not boolean!")
                end
  | Equal(op1, op2) -> let x1 = eval op1 perm_list env in
                        let x2 = eval op2 perm_list env in
                          begin match (x1, x2) with 
                            | (Bool e1, Bool e2) -> Bool(e1 = e2)
                            | (Int e1, Int e2) -> Bool(e1 = e2)
                            | (String e1, String e2) -> Bool(e1 = e2)
                            | (_, _) -> failwith("ERROR: Unknown type of operands!")
                          end
  | Greater(op1, op2) -> let x1 = eval op1 perm_list env in
                        let x2 = eval op2 perm_list env in
                          begin match (x1, x2) with 
                            | (Int e1, Int e2) -> Bool(e1 > e2)
                            | (_, _) -> failwith("ERROR: Operands are not integer!")
                          end
  | Minor(op1, op2) -> let x1 = eval op1 perm_list env in
                          let x2 = eval op2 perm_list env in
                            begin match (x1, x2) with
                              | (Int e1, Int e2) -> Bool(e1 < e2)                 
                              | (_, _) -> failwith("ERROR: Operands are not integer!")
                            end
  | IfThenElse(cond, e1, e2) -> let c = eval cond perm_list env in
                              begin match c with
                                | Bool b -> if b = true then 
                                              eval e1 perm_list env 
                                            else 
                                              eval e2 perm_list env
                                | _ -> failwith("ERROR: the condition of the 'if-then-else' is not boolean!")
                              end
  | Fun(p, body, plist) -> ieval (StackInsp(e)) perm_list env 
  | Call(func, param) -> let closure = eval func perm_list env in 
                          begin match closure with
                            | Closure(par, fbody, fenv) ->  let p = eval param perm_list env in 
                                                              let new_env = (par, p)::fenv in 
                                                                eval fbody perm_list new_env 
                            | _ -> failwith("ERROR: Not a closure!")
                          end
  | EnableP(func, p) -> begin match func with
                            | Fun(_, _, _) ->  let newPermissions = p::perm_list in eval func newPermissions env
                            | _ -> failwith("ERROR: Not a function!")
                        end
  | DisableP(func, p) -> begin match func with
                          | Fun(_, _, _) ->  let newPermissions = removePermission p perm_list in eval func newPermissions env
                          | _ -> failwith("ERROR: Not a function!")
                        end
;;



(* --- TESTS --- *)

let myEnv : (value) env = []  ;;
let pList : (permission list) = [Read] ;; (* global permissions *)

(* --- Example of a function which has all the permissions to be executed --- *)
  
let f1 = Fun("x", Plus(EVar("x"), EInt(1)), [Read]) ;;
eval f1 pList myEnv;; (* output --> - : value = Closure ("x", Plus (EVar "x", EInt 1), []) *)
let call1 = Call(f1, EInt(1)) ;;
eval call1 pList myEnv;; (* output -->  - : value = Int 2 *)



(* --- Example of a function which has not permissions to be executed --- *)

let f2 = Fun("y", Mul(EVar("y"), EInt(2)), [Write]) ;;
eval f2 pList myEnv;;  (* output --> Exception: Failure "ERROR: Forbidden operation!" *)
let call2 = Call(f2, EInt(3)) ;;
eval call2 pList myEnv ;; (* output --> Exception: Failure "ERROR: Forbidden operation!" *)


(* --- Example of enabling a permission for a function that it hadn't it before --- *) 

let fEnabled = EnableP(Fun("x", Mul(EVar("x"), EInt(2)), [Write]), Write) ;;
eval fEnabled pList myEnv;; (* output --> - : value = Closure ("y", Mul (EVar "y", EInt 2), []) *)
eval (Call((EnableP(fEnabled, Write)), EInt(4))) pList myEnv ;;  (* output --> - : value = Int 8 *)


(* --- Example of disabling a permission for a function that it had it before --- *)

let fDisabled = DisableP(Fun("x", Plus(EVar("x"), EInt(1)), [Read]), Read) ;;
eval fDisabled pList myEnv ;;  (* output --> Exception: Failure "ERROR: Forbidden operation!" *)
eval (Call((DisableP(fDisabled, Read)), EInt(4))) pList myEnv ;; (* output --> Exception: Failure "ERROR: Forbidden operation!" *)










