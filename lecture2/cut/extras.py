"""
Some additional Z3 examples and syntax

Additional help:

- Useful guide:
  [Z3 py guide](https://ericpony.github.io/z3py-tutorial/guide-examples.htm)

- Documentation:
  [Z3 py docs](https://z3prover.github.io/api/html/namespacez3py.html)

- The Z3 solver API
"""

"""
Solve and prove

Two main functions of Z3:
z3.solve (or our helper solve) --> ask if formula is satisfiable
z3.prove (or our helper prove) --> ask if formula is valid

Possible answers:
    SAT
    UNSAT
    COUNTEREXAMPLE

Validity and satisfiability are reducible to each other
Specifically: validity of "P" and satisfiability of "Not P" are solving
the same problem.

Thus, how z3.prove works:
- If I run z3.prove(formula) it calls z3.solve(z3.Not(formula))
- If satisfiable: that means there is an input where "NOT formula" is true
    Therefore, "formula" must be false (on that input)
    Therefore, "formula" is not necessarily true for all inputs, i.e. it's not
    provable -- there is a counterexample.
- If unsatisfiable: that means there are no inputs where "NOT formula" is true
    Therefore, "NOT formula" is false for all inputs
    Therefore, "formula" is true for all inputs
    Therefore, formula is provable.
- If unknown: we return unknown.

Q: When does z3.solve (or z3.prove) return unknown?
Intuitively, if the formula is really mathematically complex, involves a lot
of difficult operations and it's too hard to figure out whether it's satisfiable
or not.
--> Booleans are quite easy, so this will rarely happen with booleans.

Q: When should you use z3.prove vs z3.solve?

- z3.prove is useful for proving specifications, and also when
    you want to show that some assertion or some property always holds

- z3.solve is useful for solving equations, solving puzzles, and
    similar tasks where you have some set of constraints, and
    you want to find a solution to those constraints.
    E.g.: you want to solve x^2 - 3x + 2 = 0
    or you want to solve a Sudoku puzzle
"""

# z3.solve(form1)
# z3.solve(form2)
# z3.solve(form3)
# z3.solve(form4)
# =====> Satisfiable, Z3 gives an example

# For all four examples, the formula is satisfiable -- Z3 returns an example
# where the formula is true.
# What about something that's NOT satisfiable?

# form5 = z3.And(a, z3.Not(a))
# # A and Not A --> always false, should be never true, i.e. not satisfiable

# z3.solve(form5)
# # =====> Unsatisfiable, Z3 says "no solution"

"""
Boolean syntax

What boolean operations can we use?

- z3.And
- z3.Or
- z3.Not
- z3.Implies
- z3.If
- z3.Xor

These are all standard functions on boolean numbers, but instead of evaluating
the operation, they create a formula.

The reason they have to create a formula is because Z3 wants to determine
if the formula is true for ANY input (satisfiability) or for ALL inputs (provability)
not necessarily just evaluate it on a single input.

Examples:

"""

# print("More examples:")
# x = z3.Bool('x')
# y = z3.Bool('y')
# What does implies do?
# z3.solve(z3.Implies(x, y))
# Implies is basically the "if then" function and it has the following meaning:
# if x is true then y, otherwise true.
# arrow (-->)
# If you like you can write z3.If(x, y, True) instead of z3.Implies(...)
# It's reducible to if then.

# XOR implies or?
# XOR is exclusive or (exactly one, but not both of x and y are true)
# x_xor_y = z3.Xor(x, y)
# x_or_y = z3.Or(x, y)
# z3.prove(z3.Implies(x_xor_y, x_or_y))

"""
Convenient shortcuts:

- Equality (==)
- z3.And([...])
- z3.Or([...])

You can directly write x == y
for booleans, and Z3 knows what that means
You can also write
z3.And([formula1, formula2, formula3, ...])
for a list of formulas and it will create an "and" expression of all of them.
Similarly for Or.

These are just shortcuts, and can be implemented using the above operations already.
"""


"""
=== Integers ===

z3.Int
z3.Ints -- creates multiple integers

Examples
"""
# x, y = z3.Ints("x y")
# spec = z3.And(x > y, y > 5)
# z3.solve(spec)

"""
What operations are supported here?
You can use most built-in integer operations in Python
on Z3 integers. BUT keep in mind it's not the same as Python
integer arithmetic.
"""

# x + y # <- Z3 expression, NOT a Python integer
# print(x + y) # Prints as "x + y", not as some specific integer

# Problem: find two integers whose sum and product is the same.
# print("Find two integers whose sum and product is equal:")
# z3.solve(x + y == x * y)

# Operations we've seen so far: +, *, ==, <, all of these
# work on Z3 integers.

"""
We can use functions to wrap up useful functionality.

For example:
Define a Pythagorean triple as three positive integers a, b, c
such that a^2 + b^2 = c^2.

Q1: Find a pythagorean triple.
Q2: Find a pythagorean triple with a = 5.

It's often useful to define a function which abstracts the
behavior you're interested in.
"""

def pythagorean_triple(a, b, c):
    # We can just return the expression a^2 + b^2 = c^2
    # return (a * a + b * b == c * c)
    # Debugging: we can add the additional constraints
    # that we forgot here
    pythag_constraint = a * a + b * b == c * c
    a_is_positive = a > 0
    b_is_postive = b > 0
    c_is_positive = c > 0
    return z3.And([
        pythag_constraint,
        a_is_positive,
        b_is_postive,
        c_is_positive,
    ])
    # Here: the other constraints are silently ignored :(
    # What's happening here?
    # Python boolean operators (and/or) are defined for arbitrary
    # data types. And "falsey" datatypes are treated as false
    # and "truthy" datatypes are treated as true
    # and/or are both short circuiting so they'll return
    # the first value that is either false/true, respectively.
    # Bottom line here: this doesn't work because "and" already
    # has a definition in Python.
    # This is not what we want.
    # return (pythag_constraint and a_is_positive and b_is_postive and c_is_positive)
    # TL;DR Python boolean operators are weird, so be careful with them.

# If we want an example:
# a, b, c = z3.Ints("a b c")
# print("Example pythagorean triple:")
# z3.solve(pythagorean_triple(a, b, c))

"""
Q: what if we want more than one answer?

We can try rerunning...

The easiest way is a common technique where
each time we get an answer, we add an assertion that
that answer is excluded.
"""

# First answer: a = 6, b = 8, c = 10
# Second answer
# new_constraint = z3.Or(
#     z3.Not(a == 6),
#     z3.Not(b == 8),
#     z3.Not(c == 10),
# )
# ^ Force the solver to give us a new answer.
# z3.solve(z3.And([
#     pythagorean_triple(a, b, c),
#     new_constraint,
# ]))

# We can keep adding constraints for each new answer,
# there is also a way to do this programmatically
# (This will use the Solver API that we will shortly see.)
# We will see how to write a wrapper around Solver to do this.

"""
SKIP
Q: Write a function to determine whether a number
is a perfect square.
"""

"""
Q: write a function to solve the formula
x^2 + 5x + 6 = 0
"""

# x = z3.Int('x')
# print("Solution:")
# z3.solve(x * x + 5 * x + 6 == 0)
# # If we want the other answer?
# y = z3.Int('y')
# z3.solve(z3.And([
#     x * x + 5 * x + 6 == 0,
#     y * y + 5 * y + 6 == 0,
#     x != y,
# ]))

# Another poll
# What would you guess is the output of the following Z3 code?

@pytest.mark.skip
def test_poll_output_2():
    x = z3.Int('x')
    y = z3.Int('y')
    spec = z3.Implies(z3.And(x >= 10, y == x * x), y >= 100)
    prove(spec)

# print("Output:")
# test_poll_output_2()


"""
=== True Real Numbers ===

We've seen so far how Z3 can work with standard Python datatypes.

Because Z3 is a theorem prover, and not just a testing framework,
it can also work with data types that are not available in Python:
for example, real numbers.

In Python, there's no such thing as a "true" real number,
there are only floating point values (floats)
But in Z3 there is.

z3.Real
z3.Reals
"""

# x = z3.Real('x')
# # what happens?
# print("Square root of two:")
# z3.solve(x * x == 2)

# Note: there is no floating point value x with x^2 = 2
# It only exists as a true real number.

# How does Z3 represent real numbers, when computers can't
# represent real numbers?

# Answer: they're treated as abstract symbols, not as concrete
# values.
# In fact, everything in Z3 is treated as abstract symbols!
# z3.If, z3.Int, z3.Or, the reason there's a Z3 version is that
# it treats it as an abstract formula, not a concrete value.
# Just like when I write x = sqrt(2) on the board, I'm not actually
# computing the exact value of x, that's the same thing that Z3
# does.

"""
More advanced data types:
(later)
- Functions
- Arrays and sequences
- Strings and regular expressions
"""
