# Interpreter with History Dependent Access Control mechanism

## Objectives
Goals of the homework:
* Understanding the capabilities and the limitations of History Dependent Access Control
* Understanding the tradeoffs in the design and implementation of History Dependent Access Control

## Implementation
The aim of this homework is to extend an interpreter of a simple functional language with local security policies. Local security policies are characterized by a scope and are defined over a set of security relevant actions. The interpreter checks the policy within its scope and continues execution if the policy is satisfied; otherwise, execution fails.
