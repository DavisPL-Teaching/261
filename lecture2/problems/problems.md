# Z3 Programming Challenges

Some hands-on Z3 programming challenges.

## Problems

- Sudoku solver
  Given a 9x9 Sudoku board, find a solution to the Sudoku puzzle

- 8 queens problem
  Famous chess puzzle (not really about chess)
  Place 8 queens on an 8x8 chessboard so that no two queens attack each other
  "Attack" means moving diagonally, horizontally, or vertically

- Seating arrangement generator
  Imagine you're inviting a bunch of people over for dinner
  You want to seat them all around a round table
  but certain pairs of them don't get along and might generate
  heated arguments, which you want to avoid.
  Can we automatically generate a seating arrangement?

- Task scheduler
  We have a bunch of tasks, including
  + duration of the task
  + deadline of the task
  Can we schedule all the tasks so that they all get done?

- FRACTRAN program optimizer
  FRACTRAN is an "esoteric programming language"
  Esoteric programming languages are typically minimal
  syntax languages that make it easy to write a program
  interpreter or compiler, and which are expressive enough
  for arbitrary programs (Turing complete), but probably
  don't have many practical and convenient features.
  Designed to be extremely minimal.
  FRACTRAN is one particular such minimal language.
  We can use Z3 to answer questions about a program,
  and even to optimize a program.

  Two classical program optimizations:
  + Dead code elimination
    If there's a piece of your program that isn't needed,
    delete it.
  + Constant propagation
    If you know the value of a variable at a certain point,
    replace all uses of that variable with the constant value.

- Travelling salesperson problem
  Given a list of cities and the distances between each pair of cities,
  what is the shortest possible route that visits each city exactly once
  and returns to the origin city?
