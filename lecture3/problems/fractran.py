"""
FRACTRAN program optimizer

FRACTRAN is an esoteric programming language invented by John Conway.
A "program" is given as a list of fractions, like this:

455/33, 11/13, 1/11, 3/7, 11/2, 1/3

The input to the program is an integer. The execution of the program
keeps a single integer in memory, and at each step, it multiplies the
integer by the first fraction in the list that results in an integer.

Example:
- Start with 22
    - We can't mutiply by 455/33
    - We can't multiply by 11/13
    - We can multiply by 1/11, resulting in 2
- Go back to the start and repeat with 2

The program above is actually a multiplication program:
it takes as input 2^a * 3^b and returns 5^(a * b).

It turns out this language is Turing complete, meaning we can
simulate any program (in Python, Java, etc.) just using FRACTRAN.

=== Task 1 (warm up) ===

Take as an input a program
and a possible *output*, and try to decide if there
is an input that will produce the given output.

=== Example input ===

55/1
Target: 55
Answer: Possible (1 --> 55)

=== Task 2 (optimizer) ===

Build a simple program optimizer:
Determine if any of the fractions in the list are redundant,
and can be removed.

(There is a similar task on the homework extra credit, part 4).

"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN
