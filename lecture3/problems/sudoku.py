"""
Sudoku solver

=== Sudoku ===

A Sudoku puzzle is a 9x9 grid of numbers, where each row, column, and 3x3 box contains all of the numbers from 1 to 9.

+-------+-------+-------+
| 5 3   |   7   |       |
| 6     | 1 9 5 |       |
|   9 8 |       |   6   |
+-------+-------+-------+
|  ...  |  ...  |  ...  |
|       |       |       |
|       |       |       |
+-------+-------+-------+
|       |       |       |
|       |       |       |
|       |       |       |
+-------+-------+-------+

We are given as input a partially filled grid, where some of the cells
are empty (indicated by 0). Our goal is to fill in the empty cells
with the numbers from 1 to 9 to solve the puzzle.

=== Example input ===

[[5, 3, 0, 0, 7, 0, 0, 0, 0],
 [6, 0, 0, 1, 9, 5, 0, 0, 0],
 [0, 9, 8, 0, 0, 0, 0, 6, 0],
 [8, 0, 0, 0, 6, 0, 0, 0, 3],
 [4, 0, 0, 8, 0, 3, 0, 0, 1],
 [7, 0, 0, 0, 2, 0, 0, 0, 6],
 [0, 6, 0, 0, 0, 0, 2, 8, 0],
 [0, 0, 0, 4, 1, 9, 0, 0, 5],
 [0, 0, 0, 0, 8, 0, 0, 7, 9]]

=== Example output ===

[[5, 3, 4, 6, 7, 8, 9, 1, 2],
 [6, 7, 2, 1, 9, 5, 3, 4, 8],
 [1, 9, 8, 3, 4, 2, 5, 6, 7],
 [8, 5, 9, 7, 6, 1, 4, 2, 3],
 [4, 2, 6, 8, 5, 3, 7, 9, 1],
 [7, 1, 3, 9, 2, 4, 8, 5, 6],
 [9, 6, 1, 5, 3, 7, 2, 8, 4],
 [2, 8, 7, 4, 1, 9, 6, 3, 5],
 [3, 4, 5, 2, 8, 6, 1, 7, 9]]
"""

"""
Step 0: let's import z3 and our helper functions.
"""
import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

"""
Step 1

(*) Define a function that checks if a fully filled out Sudoku
board is valid

- Get input
- Solve function which actually solves the sudoku grid
    (*) used here?
- Print output

How to go about encoding a problem in Z3:
  1. What are the variables?
  2. What are the constraints?
  3. What are the properties we want to check?

1. Variables
Empty cells in the grid?
Column or row of each empty cell?
Boolean that says whether it's a valid solution

The
-> The 81 numbers in the grid
-> I have 81 integers in the grid.

2. What are the constraints?
1-9 in each column
1-9 in each row
1-9 in each box

(redundant)
The numbers themselves have to be between 1 and 9.

The integers that are given as part of the input
should stay the same.

(redundant)
No repeats within each row/column/box

* (This is more about the input -- let's start with the output)
Should the numbers also include 0?
-> We probably could do it that way
-> To simplify things let's start out by describing
what it means to be "valid Sudoku grid"
We'll see that the answer should sort of fall out of that.

Number of rows and columns should stay the same frmo input
to output.

Grid has to be 9 x 9

Notice that some of our constraints are redundant!
- we probably don't need all constraints at once.

3. What are the properties we want to check?

Yes/no answer
Is it a valid sudoku board?

Is the input grid solveable?
"""

def get_input():
    # Placeholder
    grid = [[5, 3, 0, 0, 7, 0, 0, 0, 0],
            [6, 0, 0, 1, 9, 5, 0, 0, 0],
            [0, 9, 8, 0, 0, 0, 0, 6, 0],
            [8, 0, 0, 0, 6, 0, 0, 0, 3],
            [4, 0, 0, 8, 0, 3, 0, 0, 1],
            [7, 0, 0, 0, 2, 0, 0, 0, 6],
            [0, 6, 0, 0, 0, 0, 2, 8, 0],
            [0, 0, 0, 4, 1, 9, 0, 0, 5],
            [0, 0, 0, 0, 8, 0, 0, 7, 9]]

    return grid

input_grid = get_input()

# 1. What are the variables?

grid = [[z3.Int(f"row{i}col{j}") for j in range(9)] for i in range(9)]

# e.g.: Row 3, column 4 is the variable z3.Int("row3col4")
# and I can get it with grid[3][4]

# 2. What are the constraints?

# 1-9 in each row
row_constraints = []
for i in range(9):
    for d in range(1, 10):
        row_constraints.append(z3.Or([grid[i][j] == d for j in range(9)]))

# 1-9 in each column
col_constraints = []
for j in range(9):
    for d in range(1, 10):

        # col_possibilities = []
        # for i in range(9):
        #     col_possibilities.append(grid[i][j] == d)
        # col_constraints.append(z3.Or(col_possibilities))

        col_constraints.append(z3.Or([
            grid[i][j] == d
            for i in range(9)
        ]))

# 1-9 in each box
# 3x3 grid of windows or boxes to go over
box_constraints = []
for box_i in range(3):
    for box_j in range(3):
        # This is one of our windows or boxes
        for d in range(1, 10):
            box_possibilities = []
            for i in range(3 * box_i, 3 * box_i + 3):
                for j in range(3 * box_j, 3 * box_j + 3):
                    box_possibilities.append(grid[i][j] == d)
            box_constraints.append(
                z3.Or(box_possibilities)
            )

# Input constraints

input_grid = get_input()
input_constraints = []
for i in range(9):
    for j in range(9):
        if input_grid[i][j] != 0:
            input_constraints.append(grid[i][j] == input_grid[i][j])

# 3. What are the properties we want to check?

# collect all of our constraints together:
constraints = row_constraints + col_constraints + box_constraints + input_constraints

# solve(z3.And(constraints))

# Make this a bit more readable?

solution = get_solution(z3.And(constraints))

output_grid = [[solution[grid[i][j]] for j in range(9)] for i in range(9)]

# Pretty print the grid
for i in range(9):
    print(" ".join([str(output_grid[i][j]) for j in range(9)]))

# Is the answer correct?
assert output_grid == [
 [5, 3, 4, 6, 7, 8, 9, 1, 2],
 [6, 7, 2, 1, 9, 5, 3, 4, 8],
 [1, 9, 8, 3, 4, 2, 5, 6, 7],
 [8, 5, 9, 7, 6, 1, 4, 2, 3],
 [4, 2, 6, 8, 5, 3, 7, 9, 1],
 [7, 1, 3, 9, 2, 4, 8, 5, 6],
 [9, 6, 1, 5, 3, 7, 2, 8, 4],
 [2, 8, 7, 4, 1, 9, 6, 3, 5],
 [3, 4, 5, 2, 8, 6, 1, 7, 9]]

"""
=== Discussion questions ===

How would we do this without Z3?

What are the advantages of using Z3?

How is Z3 different from Hypothesis?

What are the drawbacks of using Z3?

=== Follow up ===

- Can we reorganize our code to be better?

- Can we check that there is only one solution?

- Can we generate valid Sudoku puzzles?

- Generalize to an arbitrary N x N board.
(This only works for certain board sizes: 4x4, 9x9, 16x16, etc.)
"""
