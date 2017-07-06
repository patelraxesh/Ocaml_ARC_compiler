README.text

AUTOMATIC REFERENCE COUNTING
---------------------------------------------------------------------------------
T A B L E   O F   C O N T E N T S
0. Table of contents
1. What has changed?
2. Key locations in the code
2. What was up with that cyclic tuple?
3. Known issues

---------------------------------------------------------------------------------
W H A T   H A S   C H A N G E D ?
Optimization has been disabled. Garbage collection has been removed and replaced
by an Auto-Reference Counting system. Changes made to implement this are as below:
- All of the C changes are in main.c, which include functions for
    > allocation of memory to Tuples and Lambdas
    > deallocation of memory when ref_count drops to 0
    > checking for Tuples or Lambdas and  then incrementing/decrementing the ref_counts
All this functions are being called from compile.ml whenever required.

- In compile.ml file we made changes for getting the anfed expression in a
form that it always ends with an immediate. Also additional helpers and support
code is added to implement the system. Where and Why changes are made for it is
shown in below section.

Lambda Representation
  (* |  arity | ref_count | code ptr | var1 | var2 | ... | varn | (maybe padding) | *)
Tuple Representation
  (* | length | ref_count | ele1 | ele2 | ... | elen | (maybe padding) | *)

---------------------------------------------------------------------------------
K E Y   L O C A T I O N S   I N   T H E   C O D E
Makefile | run tests with 'make testrun'
main.c | 35 | set debug to 0/1 to disable/enable debug statements.
main.c | 124 - 236 | functions handling memory and ref_count
compile.ml | 253 | imposing the invariant that let bindings will end with an immediate
compile.ml | 258 | reserve—used to reserve a block of memory
compile.ml | 412 | let_helper makes use of the let-invariant to place increment
and decrements instructions in the code.
compile.ml | 626; 644 | initializing the reference count in tuples and closures

---------------------------------------------------------------------------------
W H A T   W A S   U P   W I T H   T H A T   C Y C L I C   T U P L E ?
- It was not actually creating a cyclic tuple; it was actually caused by a set
of bugs in the code for printing our tuples, which I find hard to justify or
explain. These appear to be responsible for several segfaults when putting our
code in other situations. We have left this code intact instead of fixing it in
order to preserve it for your curiosity—see main.c, line 59.
- There were certain changes that were missing on the laptop that the code was
demoed on, which explains why the decrements were not visible. Unfortunately,
adding those changes in causes the program you provided to segfault. The reason
for this failure is unclear.

---------------------------------------------------------------------------------
K N O W N   I S S U E S
- There is a longstanding issue involving stack alignment that still eludes us. It
causes segfaults when closing over too many items, or calling functions
recursively.
- LetRec has not been adapted to the new invariants, and is therefore disabled.
