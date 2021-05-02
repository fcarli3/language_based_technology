
(*
DFA
• A deterministic ﬁnite automaton M is a 5tuple, (Q, Σ, δ, q0, F), consisting of
– a ﬁnite set of states (Q)
– a ﬁnite set of input symbols called the alphabet (Σ)
– a transition function (δ : Q × Σ → Q)
– a start state (q0 ∈ Q)
– a set of accepting states (F ⊆ Q)
*)

(* Represents states of dfa as int *)
type state = int;;

(* Represents symbols (alphabet) as a char *)
type symbol = char;;

(* transaction function delta *)
type transition = state * symbol * state;;

(* description of dfa *)
type dfa = {
  states : state list;
  sigma : symbol list;
  start : state;
  transitions : transition list;
  accepting : state list;
  error : string
};;

(* Auxiliary Functions *)
(* To dereference a record, use the dot notation, like a class *)
let states (dfa : dfa) = dfa.states;;
let alphabet (dfa : dfa) = dfa.sigma;;
let start (dfa : dfa) = dfa.start;;
let transitions (dfa : dfa) = dfa.transitions;;
let acceptings (dfa : dfa) = dfa.accepting;;

(* This is a function that takes in a DFA as input, and adds a transition.
*)

(* "with" evaluates to a new record of the same type as X, and whose 
fields are initialized to the same as those in X, except the ones
which are listed after the "with", which are initialized to those
given values.
*)
let addTransition t dfa = { 
  dfa with transitions = t::dfa.transitions 
};;

(*
explode takes a string `s`, and turns it into its individual
characters. This way we can run the DFA on the string "101"
without explicitly writing ['1';'0';'1']
*)
let explode s =
  let rec expl i l =
    if i < 0 
      then l 
      (* s.[i] returns the ith element of s as a char *)
    else expl (i - 1) (s.[i] :: l) in 
   (* String.length s returns the length of s *)
      expl (String.length s - 1) [];;

(* 
another helper function that checks whether a list contains an
element *)
let rec contains e l =
  match l with
  | [] -> false
  | hd::tl -> if hd = e then true else contains e tl;;


(*
Checking DFA Acceptance
• Attempt 1: we might keep a (mutable) 
variable that keeps track of what state the
DFA is currently at, and then updates the state depending on that.
*)
let check_accepts str dfa =
  (* Get the list of symbols. *)
  let symbols = explode str in
    (* If I'm at state {state}, where do I go on {symbol}? *)
    let transition state symbol =
      let rec find_state l =
        match l with
        | (s1, sym, s2)::tl ->
          if (s1 = state && symbol = sym) then s2 else find_state tl
        | _ -> failwith "no next state" 
      in find_state dfa.transitions      
    in let final_state = 
      let rec h symbol_list =
        match symbol_list with
        | [hd] -> (transition dfa.start hd)
        | hd::tl -> (transition (h tl) hd)
        | _ -> failwith "empty list of symbols"
      in h (List.rev symbols) in
        if (contains final_state dfa.accepting) then 
          true 
        else false;;


(* LANGUAGE CONSTRUCTS *)
type expr =
  | EInt of int
  | EBool of bool
  | EString of string
  | EVar of string
  | LetIn of string * expr * expr (* 'string' value to associate to string, 'expr' value to associate to string, 'expr' body of let. (i.e x (ide) = 5 (exp) in x + 10 (exp))  *)
  | Plus of expr * expr (* + of Int * Int *)
  | Minus of expr * expr (* - of Int * Int *)
  | Mul of expr * expr (* * of Int * Int *)
  | And of expr * expr (* && of Bool * Bool *)
  | Or of expr * expr (* || of Bool * Bool *)
  | Not of expr (* ! of Bool *)
  | Equal of expr * expr (* e1 == e2 *)
  | Greater of expr * expr (* e1 > e2 *)
  | Minor of expr * expr (* e1 < e2 *)
  | IfThenElse of expr * expr * expr (* 'expr' check, 'expr' then branch, 'expr' else branch *)
  | Read of string (* Security event, 'string' is the argument of the read (es. file, db, socket, etc...) *)
  | Write of string (* Security event, 'string' is the argument of the write (es. file, db, socket, etc...) *)
  | Lambda of string * expr (* Lambda is an anonymous function, 'string' is the formal parameter, 'expr' is the body *)
  | RecLambda of string * expr (* Recursive function, 'string' is the name of the function, 'expr' is lambda *)
  | Apply of expr * expr (* Function call, 'expr' is the function, 'expr' is the actual parameter *)
  | SecurityFrame of expr * expr (* 'expr' represents the local policy, 'expr' is an operation or a list of nested operations *)
  | UserPolicy of dfa list (* user-defined policies, 'dfa list' is a list of automata that represent security policies *)
;; 

(* POLYMORPHIC ENVIRONMENT: LIST OF PAIRS (STRING, VALUE) *)
type 'v env = (string * 'v) list;;

(* LANGUAGE TYPES *)
 type value = 
 | Int of int
 | Bool of bool
 | String of string
 | Closure of string * expr * (value) env
 | RecClosure of string * string * expr * (value) env (* 'string': name of the fun, 'string': formal parameter, 'expr': fun body, 'env': declaration environment *)
 | Policy of dfa list (* value for a security policy *)
;;

(* --- DECLARATION OF FUNCTIONS --- *)

(* CHECK IF STRING s HAS AN ASSOCIATED VALUE IN THE ENVIRONMENT env *)
let rec lookup (env : 'v env) (s : string) : value =
  match env with
  | [] -> failwith("ERROR: Var not found in lookup function!")
  | (i,v)::r -> if (i=s) then 
                  v 
                else 
                  lookup r s
;;

(* CHECK IF A SECURITY OPERATION, REPRESENTED BY THE STRING c, RESPECTS THE CURRENT POLICY automa (THE FIRST OF THE LIST OF POLICIES) AND THE PREVIOUS IN CASE OF NESTED POLICIES *)
let rec check_op (c : string) (automa : dfa list) (history : string ): (value * expr * string) =
  match automa with
    | [] -> (Int(1), UserPolicy(automa), (history ^ c)) (* there are no policies or all the policies of the list hold *)
    | x :: xs -> 
                if (check_accepts (history ^ c) x) then (* check on the first policy of the list, if it holds check the rest of the list *)
                  check_op c xs history
                else 
                  failwith(x.error)
;;


(* --- INTERPRETER --- *)

(* EXTENDED INTERPRETER *)
let rec eval (e : expr) (env : 'v env) (automa: expr) (history : string) : (value * expr * string) =
  match e with
  | EInt i -> (Int i, automa, history)

  | EBool b -> (Bool b, automa, history)

  | EString s -> (String s, automa, history)

  | EVar v -> ((lookup env v), automa, history)

  | LetIn(s, v, body) -> let (_value, _, new_history) = eval v env automa history in
                          let new_env = (s, _value)::env in 
                            eval body new_env automa new_history

  | Plus(op1, op2) -> let (x1, _, _) = eval op1 env automa history in
                        let (x2, _, _) = eval op2 env automa history in
                          begin match (x1, x2) with 
                            | (Int e1, Int e2) -> (Int(e1 + e2), automa, history)
                            | (_, _) -> failwith("ERROR: Operands are not integer in Plus operation!")
                          end

  | Minus(op1, op2) -> let (x1, _, _) = eval op1 env automa history in
                        let (x2, _, _) = eval op2 env automa history in
                          begin match (x1, x2) with 
                            | (Int e1, Int e2) -> (Int(e1 - e2), automa, history)
                            | (_, _) -> failwith("ERROR: Operands are not integer in Minus operation!")
                          end

  | Mul(op1, op2) -> let (x1, _, _) = eval op1 env automa history in
                      let (x2, _, _) = eval op2 env automa history in
                        begin match (x1, x2) with 
                          | (Int e1, Int e2) -> (Int(e1 * e2), automa, history)
                          | (_, _) -> failwith("ERROR: Operands are not integer in Mul operation!")
                        end

  | And(op1, op2) -> let (x1, _, _) = eval op1 env automa history in
                      let (x2, _, _) = eval op2 env automa history in
                        begin match (x1, x2) with 
                          | (Bool e1, Bool e2) -> (Bool(e1 && e2), automa, history)
                          | (_, _) -> failwith("ERROR: Operands are not boolean in And operation!")
                        end

  | Or(op1, op2) -> let (x1, _, _) = eval op1 env automa history in
                    let (x2, _, _) = eval op2 env automa history in
                      begin match (x1, x2) with 
                        | (Bool e1, Bool e2) -> (Bool(e1 || e2), automa, history)
                        | (_, _) -> failwith("ERROR: Operands are not boolean in Or operation!")
                      end

  | Not(op) -> let (x1, _, _) = eval op env automa history in
                begin match x1 with 
                  | Bool e1 -> (Bool(not(e1)), automa, history)
                  | _ -> failwith("ERROR: Operand is not boolean in Not operation!")
                end

  | Equal(op1, op2) -> let (x1, _, _) = eval op1 env automa history in
                        let (x2, _, _) = eval op2 env automa history in
                          begin match (x1, x2) with 
                            | (Bool e1, Bool e2) -> (Bool(e1 = e2), automa, history)
                            | (Int e1, Int e2) -> (Bool(e1 = e2), automa, history)
                            | (String e1, String e2) -> (Bool(e1 = e2), automa, history)
                            | (_, _) -> failwith("ERROR: Unknown type of operands in Equal operation!")
                          end

  | Greater(op1, op2) -> let (x1, _, _) = eval op1 env automa history in
                          let (x2, _, _) = eval op2 env automa history in
                          begin match (x1, x2) with 
                            | (Int e1, Int e2) -> (Bool(e1 > e2), automa, history)
                            | (_, _) -> failwith("ERROR: Operands are not integer in Greater operation!")
                          end

  | Minor(op1, op2) -> let (x1, _, _) = eval op1 env automa history in
                          let (x2, _, _) = eval op2 env automa history in
                            begin match (x1, x2) with
                              | (Int e1, Int e2) -> (Bool(e1 < e2), automa, history)                
                              | (_, _) -> failwith("ERROR: Operands are not integer in Minor operation!")
                            end

  | IfThenElse(cond, e1, e2) -> let (c, _, _) = eval cond env automa history in
                              begin match c with
                                | Bool b -> if b = true then 
                                              eval e1 env automa history
                                            else 
                                              eval e2 env automa history
                                | _ -> failwith("ERROR: the condition of the 'if-then-else' is not boolean!")
                              end

  | Read(s) -> let (a, _, _) = eval automa env automa history in
                begin match a with
                  | Policy p ->  check_op "R" p history
                  | _ -> failwith("ERROR: Invalid policy format in 'Read' operation!")
                end

  | Write(s) -> let (a, _, _) = eval automa env automa history in 
                  begin match a with
                    | Policy p ->  check_op "W" p history
                    | _ -> failwith("ERROR: Invalid policy format in 'Write' operation !")
              end

  | Lambda(p, body) -> (Closure(p, body, env), automa, history)

  | RecLambda(fname, func) -> begin match func with
                                | Lambda(p, body) -> (RecClosure(fname, p, body, env), automa, history)
                                | _ -> failwith("ERROR: Second parameter is not a function in RecLambda operation!")
                              end

  | Apply(func, param) -> let (closure, _, _) = eval func env automa history in 
                          begin match closure with (* check if the first parameter of Apply is a closure or a rec closure *)
                            | Closure(par, fbody, fenv) ->  let (p, _, new_history) = eval param env automa history in (* evaluate the actual param of Apply *)
                                                              let new_env = (par, p)::fenv in (* add the pair (formal param , value) to the environment *)
                                                                eval fbody new_env automa new_history (* evaluate the body of the function in the new env *)
                            | RecClosure(fname, par, fbody, fenv) -> let (p, _, new_history) = eval param env automa history in (* evaluate the actual param of Apply *)
                                                                      let new_env = (fname, closure)::fenv in (* add the pair (fun name, function) to the environment *)
                                                                        let new_env_2 = (par, p)::new_env in (* add the pair (formal param , value) to the environment *)
                                                                          eval fbody new_env_2 automa new_history (* evaluate the body of the function in the new env *)                          
                            | _ -> failwith("ERROR: First parameter is not a closure in Apply operation!")
                          end

  | SecurityFrame(a, op) -> begin match (automa, a) with (* check if both automata represent security policies *)
                              | (UserPolicy prev, UserPolicy curr) -> eval op env (UserPolicy(curr@prev)) history (* evaluate the security event concatenating the policies. That way I'll be able to evaluate if the security event respects nested policies *)
                              | (_, _) -> failwith("ERROR: Unknown types of local policies in SecurityFrame operation!")
                            end

  | UserPolicy(list) -> (Policy(list), automa, history)
;;


(* ****************************************************************************************** *)


(*** MAIN ***)

(* Policy: "NO WRITE AFTER READ" *)
let noRW : dfa = {
  states = [0; 1; 2]; 
  sigma = ['R'; 'W'];
  start = 0;
  transitions = [(0, 'R', 1);
                 (0, 'W', 0);
                 (1, 'R', 1);
                 (1, 'W', 2);
                 (2, 'R', 2);
                 (2, 'W', 2)];
  accepting = [0; 1];
  error = "ERROR: NO WRITE AFTER READ !"
};; 

(* Policy: "NO READ AFTER WRITE " *)
let noWR : dfa = {
  states = [0; 1; 2]; 
  sigma = ['R'; 'W'];
  start = 0;
  transitions = [(0, 'R', 0);
                 (0, 'W', 1);
                 (1, 'R', 2);
                 (1, 'W', 1);
                 (2, 'R', 2);
                 (2, 'W', 2)];
  accepting = [0; 1];
  error = "ERROR: NO READ AFTER WRITE !"
};; 

(* Policy: "NO WRITE" *)
let noWrite : dfa = {
  states = [0; 1]; 
  sigma = ['R'; 'W'];
  start = 0;
  transitions = [(0, 'R', 0);
                 (0, 'W', 1);
                 (1, 'R', 1);
                 (1, 'W', 1)];
  accepting = [0];
  error = "ERROR: NO WRITE !"
};; 

(* Policy: "NO READ" *)
let noRead : dfa = {
  states = [0; 1]; 
  sigma = ['R'; 'W'];
  start = 0;
  transitions = [(0, 'R', 1);
                 (0, 'W', 0);
                 (1, 'R', 1);
                 (1, 'W', 1)];
  accepting = [0];
  error = "ERROR: NO READ !"
};; 

let myHistory : string = "";;

let myEnv : (value) env = [];;


(* Operation: ϕ[Read, Write] | ϕ = "NO WRITE AFTER READ"

   expected output --> Exception: Failure "ERROR: NO WRITE AFTER READ !"

*)
let (v, _, _) = eval (SecurityFrame(UserPolicy[noRW], Apply(Lambda("x", Write("file")), Read("file")))) myEnv (UserPolicy([])) myHistory;;


(* Operation: ϕ[Write, Read] | ϕ = "NO WRITE AFTER READ"

   expected output --> val v : value = Int 1

*)
let (v1, _, _) = eval (SecurityFrame(UserPolicy[noRW], Apply(Lambda("x", Read("file")), Write("file")))) myEnv (UserPolicy([])) myHistory;;


(* Operation -> Read, ϕ[Write] | ϕ = "NO WRITE AFTER READ"

   expected output --> Exception: Failure "ERROR: NO WRITE AFTER READ !"

*)
let (v2, _, _) = eval (Apply(Lambda("x", SecurityFrame(UserPolicy[noRW], Write("file"))), Read("file"))) myEnv (UserPolicy([])) myHistory;;


(* Operation: ϕ[Read, ϕ'[Write]] | ϕ = "NO READ" | ϕ' = "NO WRITE"

   expected output --> Exception: Failure "ERROR: NO READ !"

*)
let (v3, _, _) = eval (SecurityFrame(UserPolicy[noRead], Apply(Lambda("x", SecurityFrame(UserPolicy[noWrite], Write("file"))), Read("file")))) myEnv (UserPolicy([])) myHistory;;


(* Operation: ϕ[Write, ϕ'[Read]] | ϕ = "NO READ" | ϕ' = "NO WRITE"

   expected output --> Exception: Failure "ERROR: NO WRITE !"

*)
let (v4, _, _) = eval (SecurityFrame(UserPolicy[noRead], Apply(Lambda("x", SecurityFrame(UserPolicy[noWrite], Read("file"))), Write("file")))) myEnv (UserPolicy([])) myHistory;;


(* Operation: fact(5) = 5 * 4 * 3 * 2 * 1 = 120

  let rec fact x = if x < 1 then 1 else x * fact(x - 1)

   expected output --> val v5 : value = Int 120

*)
let rec fact = RecLambda("fact", Lambda("x", IfThenElse(Minor(EVar "x", EInt 1), EInt 1, Mul(EVar "x", (Apply(EVar "fact", Minus((EVar "x", EInt 1))))))));;
let (v5, _, _) = eval(Apply(fact, EInt 5)) myEnv (UserPolicy([])) myHistory ;;


(* Operation: func(5) = Write, Write, Write, Write, Write, ϕ[Read] | ϕ = "NO READ AFTER WRITE"

  let rec func x = if x < 1 then ϕ[Read] else Write; func(x - 1)

   expected output --> Exception: Failure "ERROR: NO READ AFTER WRITE !"

*)
let rec func = RecLambda("func", Lambda("x", IfThenElse(Minor(EVar "x", EInt 1), SecurityFrame(UserPolicy[noWR], Read("file")), Apply(EVar "func", Apply(Lambda("x", Minus(EVar "x", EInt 1)), Write("file"))))));;
let (v6, _, _) = eval(Apply(func, EInt 5)) myEnv (UserPolicy([])) myHistory ;;


