"""
Lecture 1, Part 2:
Methodology of writing specs

=== Intro ===

Recap from last time:

- Spec = true or false property of a program

- ways / tiers of writing and validating specs:

    + Documentation (not executable)
    + Unit tests (executable but not exhaustive)
    + Random testing (executable, but not fully exhaustive)

- Difference between testing & verification.

Today:

- Practice with writing specs

- Stronger and weaker specs

=== Methodology ===

Methodology of program specification:

1. We write a program
    (i.e.: what the program does)

2. We write a specification (or spec)
    (i.e.: what the program *should* do)

3. We check whether the program satisfies the spec

    Different methods:
    a. Testing (unit tests) - try a few examples
    b. Testing (random testing, fuzzing) - try random examples
    c. Automated Verification (Z3) - automatically search for a mathematical proof
    d. Interactive Verification (Dafny) - write the proof yourself

    (Other methods?
     I note that many other methods can be thought of as special cases of the above.
     E.g.: fuzzing = (b), static analysis = (c), typechecking = (c) and (d), etc.)

=== "Test harness" approach ===

For steps 2 and 3:

    To specify the behavior on multiple inputs, we saw that we could write specs
    using a "test harness" approach:
    like this:

    def spec_foo(arg1, arg2, ...):
        # do some checks, make some python assertions

    followed by a test like

    def test_foo():
        for arg1, arg2, in ...
            spec_foo(arg1, arg2)
"""

# Imports
import pytest

"""
Let's practice this.
(This time with a simpler example)

Exercise:

    Write a function that calculates the "integer square root" --
    that is, takes an integer and calculates the square root of it,
    rounded down to the nearest integer.

    int_sqrt(4) = 2
    int_sqrt(6) = 2
    int_sqrt(9) = 3
"""

# We might need this
from math import sqrt

# 1. Write the program
def integer_sqrt(n):
    # Simple implementation: let's just call sqrt from Python's math library,
    # and round down to an integer
    return int(sqrt(n))
    # (other methods? e.g. binary search)

# 2. Write the specification - first in English
# What does it mean for this program to be correct?

# Ideas?
# TODO

def spec_integer_sqrt(n):
    # TODO
    raise NotImplementedError

# For now: test the behavior on inputs 0 to 1000
# Comment out to run
@pytest.mark.skip
def test_integer_sqrt():
    for n in range(1000):
        spec_integer_sqrt(n)

# Some examples to try running the program
# print(integer_sqrt(3))
# print(integer_sqrt(4))
# print(integer_sqrt(6))
# print(integer_sqrt(-3))

"""
=== Checking our understanding ===

https://forms.gle/GziWYHdtx4Y9HJAE9

True/False
- The function integer_sqrt satisfies the specification we wrote in test_integer_sqrt.
- All functions that satisfy the specification in test_integer_sqrt are necessarily exactly equivalent to integer_sqrt.

Which of the following additional specifications does integer_sqrt satisfy?
1. The output of integer_sqrt is always an integer.
2. If the input to integer_sqrt is an integer, then the output is an integer.
3. True (true of all programs)
4. False (false of all programs)
5. The input arguments are not modified by the program.
6. If the input is greater than 100, then the output is greater than 10.
7. If the input is greater than or equal to 100, then the output is greater than or equal to 10.

Answers:

.
.
.
.
.
.
.
.
.

(Let's run the code)
"""

"""
.
.
.
.
.
(if it works)

spec works!
Program satisfies the spec!

We are happy! --> we think we've implemented the program correctly
    (AND, we've specified it correctly)

=== Q+A ===

Q: How valuable is this spec?
Have we tested EVERYTHING about the program?
No, for example, we didn't test it on negative inputs.

For now: no spec is perfect! Writing and defining precise & helpful specs
is an art and it's something that we will continue to get more practice with.

Q: are properties about the syntax or lines of code considered specifications?
    E.g.: the function must have at least 10 Lines of code
    A: Yes, that's a valid spec but probably not one we're interested in.

=== The verification approach ===

Verification instead of testing:

Because Z3 lives in a separate world from Python,
we have to "translate" the Python program into Z3 formulas.

If this seems tedious, we will get to better ways later!
"""

import z3

# Program
def abs(x):
    if x > 0:
        return x
    else:
        return -x

# Translate to Z3
def abs_z3(x):
    return z3.If(x > 0, x, -x)

# Normal spec:
def spec_abs(x):
    y = abs(x)
    assert x >= 0
    assert x == y or x == -y

# Z3 spec:
def spec_abs_z3(x):
    y = abs_z3(x)
    return z3.And(y >= 0, z3.Or(y == x, y == -x))

    # Note: Try replacing with

# ignore this line - helper file, will also be used on the HW!
from helper import prove, PROVED

# Comment out to run
@pytest.mark.skip
def test_prove_z3():
    # prove the spec on all inputs!
    x = z3.Int("x")
    spec = spec_abs_z3(x)

    assert prove(spec) == PROVED

    # Note: Try replacing Int with Real!

"""
For lecture 1, we will go back and forth between writing executable
specs in Python, vs. verifiable specs in Z3.

Later we will move to pure verification using Z3 and Dafny.
"""
