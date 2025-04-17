"""
Traveling Salesperson Problem

We are given a list of cities and the distances between them.
What is the fastest way to visit all the cities and return to the starting point?

=== Example input ===

Cities: 3
Distances:
 [ [0, 1, 2],
   [1, 0, 3],
   [2, 3, 0] ]

"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN
