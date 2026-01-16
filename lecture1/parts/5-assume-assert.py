"""
Lecture 1, Part 5:
Assume and Assert

We can write specs using pre/postconditions

This part is about a generalization of this

Provocative statement:
All verification of programs can be boiled down to two simple commands:

    assume

and

    assert

===== Assume and assert =====

Going back to our divide by zero example.
This time using floating point arithmetic.

Here, we want to exclude 0.
We saw multiple ways to do this. Another way would be using
an "assume" keyword.
"""

import pytest

def divides_2(x, y):
    return x / y

ERROR = .00001

import sys

def my_assert(b):
    if not b:
        # halt the program with an error :-(
        sys.exit(1)
        # alternative:
        # raise AssertionError("assertion failed")

def assume(b):
    if not b:
        # halt the program -- no error :-)
        sys.exit(0)

def spec_divide_2(x, y):
    # Assume statement!
    # Adds some constraint to the precondition.
    assume(y > 0) # If this isn't true, throw away this particular test run.

    # Equivalent to:
    # if y == 0:
    #     return

    # assert type(divide(x, y)) is float
    my_assert(abs(divides_2(x, y) * y - x) < ERROR)

"""
... if I had a bunch of tests going on, and one of them failed,
would that kill the whole testing process?

Yes. This doesn't work for multiple tests.

I'm using sys.exit(0) and sys.exit(1) here as shorthand for...

    "accept" and "reject", respectively

    i.e.

    "the spec should pass" and "the spec should fail".
"""

"""
These two little functions, assume and assert, turn out to be
fundamentally important to testing & verification.

- Assert: This property should hold, if it doesn't, that's an
    error. I want to report a test failure.
- Assume: This property should hold, if it doesn't, I want to
    ignore this test.

Assert and assume interact in interesting ways...

Poll:
(we will do this start of next time)

Which of the following has no effect? (Select all that apply)
- assert True
- assert False
- assume True
- assume False
- assert P if it occurs immediately following assume P
- assume P if it occurs immediately following assert P

Some of you may have picked up on the facts that:

- preconditions are just assume() statements
- postconditions are just assert() statements.

precond P, program f, postcondition Q
    == equivalent to ==
    assume(P(x))
    y = f(x)
    assert(Q(y))

We have to be careful with assume!
It's very dangerous.
"""

# Another example
# Is this program for sorting a list correct? :)

def sort_list(l):
    l = l.copy()
    return l

# The spec:
def spec_sort_list(l):
    assume(l == sorted(l))
    assert sort_list(l) == sorted(l)

"""
.
.
.
.
.
.
.
.
.
.

Multiverse view
- Quantum bogosort:
    https://wiki.c2.com/?QuantumBogoSort
- (Based on: bogosort
    https://en.wikipedia.org/wiki/Bogosort)

assume(P) is kind of like this!

    assume(P) means:

        if P does not hold, destroy the universe.

Another way of thinking about this is, whose responsibility is
it to ensure the list is sorted?
- If I use assume, I'm saying it's the caller's responsibility.
- If I use assert, in a specification to say that some property
  is true, then I'm saying it's the function's responsibility
  to guarantee that property.
"""

"""
Now that we know about assume and assert,
a more complete claim about what testing can express:

Testing can express exactly those specifications that are
expressible using assume() and assert().

- On all input executions such that all assume() statements
  hold up to a given point,
  all assert() statements hold after that point.
"""
