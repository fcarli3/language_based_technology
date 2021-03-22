## In-lined Reference Monitor
This code contains the implementation of a functional programming language equipped with a simple IRM using inlining in OCaml.

# Inlining
The idea is to implement an EM by in-lining its logic into an untrusted code instead of see the EM as an extension of an OS. 

# Inlining Algorithm
1. *Insert Security Automata*
    Inserts a copy of the security automata before each target instruction. 
2. *Evaluate Transitions*
    Evaluates any transition predicates that can be given the target instruction. 
3. *Simplify Automata*
    Deletes transitions labelled by transition predicates that evaluated to false. 
4. *Compile Automata*
    Translates the remaining security automata into code. FAIL invoked by the added code if the automata reject its input. 
