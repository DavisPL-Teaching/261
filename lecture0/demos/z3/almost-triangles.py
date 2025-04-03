"""
Demo example using Z3

(Question earlier mentioned:
    interactive verification tools like Dafny, Coq/Rocq, etc.
    vs automated verification tools like Z3
)

Problem statement:

A triangle is an "almost right triangle" if one of its angles differs from
90 degrees by at most 15 degrees. A triangle is an "almost isosceles
triangle" if two of its angles differ from each other by at most 15
degrees. Prove that all acute triangles are either almost right or almost
isosceles.

How should we prove this?

- We could go through the hard work of writing a formal mathematical proof,
  but then we have to think about the problem! :(

- Alternative approach: give the problem to the computer and have it prove
  it for us.
"""

import z3

# x, y, z: the angles of the triangle
# This is not a normal Python program!
# Returns: a logical/mathematical formula that describes whether or not x, y, z form a triangle
def triangle(x, y, z):
    return z3.And(x > 0, y > 0, z > 0, x + y + z == 180)

def acute(x, y, z):
    return z3.And(x < 90, y < 90, z < 90)

# |x|
def abs(x):
    return z3.If(x > 0, x, -x)

def almost_right(x, y, z):
    return z3.Or(abs(x - 90) <= 15, abs(y - 90) <= 15, abs(z - 90) <= 15)

def almost_isosceles(x, y, z):
    return z3.Or(abs(x - y) <= 15, abs(x - z) <= 15, abs(y - z) <= 15)

x = z3.Real("x")
y = z3.Real("y")
z = z3.Real("z")

# Call to z3.solve
# Try commenting out one of the lines - what happens?
z3.solve(
    triangle(x, y, z),
    acute(x, y, z),
    z3.Not(almost_right(x, y, z)),
    z3.Not(almost_isosceles(x, y, z)),
)

"""
Note: if "at most 15" is replaced by "less than 15" in the problem statement
(change "<= 15" to "< 15" everywhere below), the formula becomes satisfiable
and we get the following counterexample: a triangle with angles 45, 60, and 75.
"""
