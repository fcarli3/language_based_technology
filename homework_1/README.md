#Interpreter with stack inspection mechanism

##Objectives
Goals of the homework:
* Understanding the capabilities and the limitations of stack inspection
* Understanding the tradeoffs in the design and implementation of stack inspection

##Implementation
The aim of this homework is to extend the interpreter of a simple functional language equipped with security permissions. 
Each function definition is equipped with a set of permissions (e.g. {read, write, execute, ...}) over a set of security relevant actions. 
The language should have a primitive construct to check a permission: if the permission is enabled, the interpreter executes the requested function, else it rejects the request and throws an exception.
