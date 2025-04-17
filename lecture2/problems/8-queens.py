"""
N Queens Problem

The 8 queens problem is a classic chess puzzle.
A chess board is an 8x8 grid. The goal is to place 8 queens on the board such that no two queens can "attack" each other using the rules of chess.

- "Attack" means that two queens are in the same row, column, or diagonal.


   | x |   |   | y |
   |   | z |   |   |

x can attack y and vice versa
x can attack z and vice veras
but y and z cannot attack each other

=== Input ===

n: the size of the n x n board
    (default: n = 8)

=== Output ===

Output a solution for the n queens in the form of
an n x n grid where each cell is either " " or "Q".
"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

"""
How to approach solving a problem in Z3?

1. Pick your variables

2. Encode the constraints of your problem

3. Call solve() or prove() to automatically determine an answer.

(For more on this: see methodology.md)
"""

def get_input():
    # Placeholder
    return 8

"""
Starting with step 1:
what should our variables be?

- 2D Boolean array of the chessboard: True = queen is present, False = queen is not present?

- Encode how many queens there are in one row?

- Keep an array of positions of the queens on the board? (x, y) coordinates
  (Let's use this encoding)
"""

n = get_input()

# positions = [(z3.Int(f"x{i}"), z3.Int(f"y{i}")) for i in range(n)]
# Can't we just make one?
# Position in the list tells us the x-value

# Let: q_i be the column of the queen in row i
queens = [z3.Int(f"q{i}") for i in range(n)]

"""
2. Encode constraints

What constraints do we need to encode?

- column of queen i should be between 0 and (n-1)
- queen i and queen j are not in the same row
- queen i and queen j are not in the same column (given)
- queen i and queen j are not in off diagonals
"""

col_constraints = [z3.And(queens[i] >= 0, queens[i] < n) for i in range(n)]

not_in_same_col = [
    queens[i] != queens[j]
    for i in range(n)
    for j in range(i, n)
]

def same_diag(i, j, queeni, queenj):
    # could also use the z3 abs function that we defined in lecture.py and hw
    return z3.Or(j - i == queeni - queenj, j - i == queenj - queeni)

not_in_same_diag = [
    z3.Not(same_diag(i, j, queens[i], queens[j]))
    for i in range(n)
    for j in range(i, n)
]

constraints = col_constraints + not_in_same_col + not_in_same_diag

solve(constraints)
