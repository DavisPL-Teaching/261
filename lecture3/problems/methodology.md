# Z3 methodology

Solving problems with Z3 takes some getting used to.
It is very different from the programming you are used to.

## Solving problems without Z3

Normal process: think about the input and output of the problem,
divide the problem into smaller parts, and solve each part.

How would we solve the Sudoku problem *without* Z3?

- Maintain the squares that are unknown (0s) and the squares
are known?

- Maintain a set of possible numbers for each square?

- If there's only one number possible, we could fill in
  that number.

- What if there are >= 2 numbers possible at every square?

  + If we don't care about doing it quickly, pick one?
    and then check if it works out!

  + If it doesn't work out, rollback the whole thing
    and pick the other.

Essentially: "try every combination"
Naive / "brute force" solution.

That doesn't sound very good!
- If we pick the wrong number, we could go down a long
path of trying things that don't work out.
- We have to think a lot about implementation details (searching for solutions)

## Solving problems with Z3

Z3 requires thinking about problems in a very different way!

Z3 process: think about "what" instead of "how":
    - we define the *output* as a set of abstract variables
    - we think about what constraints the output must satisfy
    - (Magic part)
      we pass the constraints to Z3 to solve the problem for us.

Z3 integers: not the same as Python integers!

(aside: quick terminal demo)

- In Z3, everything is an abstract expression
  Integer values are not known, they're abstract variables
  "x" and "y", not specific integers
- Z3 integers support +, *, ==, and some other operations,
  but don't assume that every Python operator is automatically
  going to work on Z3 integers.
- In Z3, everything proceeds in two stages: first, we create
  a Z3 expression or formula for what we want, and then
  we pass it to z3.solve or z3.prove to actually solve the
  problem.

Steps:
    1. What are the variables?
    2. What are the constraints?
    3. What are the properties we want to check?

(1) is talking about Z3 variables, not Python variables!
How are they different?

## Hypothesis vs Z3

Similarly: Hypothesis and Z3 are very different.
They work differently and they are used differently.

Hypothesis methodology:
- Write a program
- I want to make sure it's correct -- write a test with
  a spec for that program
- Then run hypothesis to find out if the program passes the spec

Z3 methodology:
- Think about what problem I'm using Z3 to solve, and what
  is the *output* to the problem
- What Z3 variables I can use to describe the output and
  constraints on the output (3 steps that we've been using)
- Then encode the problem and pass it to Z3 to solve
