"""
=== More on Hypothesis ===

Some additional notes on
Hypothesis syntax and useful features.

https://hypothesis.readthedocs.io/en/latest/data.html
"""

from hypothesis import given
from hypothesis import strategies as st
# from hypothesis import settings
import pytest

##### Exercise #####
# (We covered this in class in lecture.py)

from math import sqrt

def square_root(x):
    return int(sqrt(x))

# POLL: Come up with a specification for the program.
# Also, come up with a specification that does NOT hold of the program.
# You can write either as a Python function or in words.

# Examples
# >>> int(sqrt(4))
# 2
# >>> int(sqrt(5))
# 2
# >>> int(sqrt(10))
# 3

# @given(st.integers(min_value = 0, max_value = 1000000))
# def test_square_root(x):
#     # what should go here?
#     # Try to make it more interesting that just a specific example
#     # Ex.: Square_root(x) is a function where it returns a number, when multiplied by itself, equals x.
#     y = square_root(x)
#     assert y * y <= x and (y + 1) * (y + 1) > x

# Some additional useful features

# - Other @given strategies

# - the @example syntax

from hypothesis import example

# @given(st.integers(min_value = 0, max_value = 100))
# @example(x=10000)
# def test_square_root_2(x):
#     y = square_root(x)
#     assert y * y <= x and (y + 1) * (y + 1) > x

# Writing specifications: additional notes

# Important note: the same function can have multiple specifications!
# Examples:

def list_interleave(l1, l2):
    # Return a list with the elements of l1 and l2 interleaved
    result = []
    n = min(len(l1), len(l2))
    for i in range(n):
        result.append(l1[i])
        result.append(l2[i])
    return result

# ex.: interleave([1, 4, 5], [2, 3, 6] --> [1, 2, 4, 3, 5, 6])

# @given(st.lists(st.integers()),st.lists(st.integers()))
# def test_list_interleave(l1, l2):
#     l = list_interleave(l1, l2)
#     # Weak spec
#     assert len(l) == min(2 * len(l1), 2 * len(l2))
#     # Stronger spec: check that the elements are as we expect
#     # for i in range(..):
#     # check that l[2 * i] = l1[i]
#     # check that l[2 * i + 1] = l2[i]

# Skip
def ncr(n, k):
    # Return the number of ways to choose k items from n items
    result = 1
    for i in range(k):
        result *= n - i
        result //= i + 1
    return result

# What can we check about this function?

# A more interesting one:

def functional_map(f, l):
    return [f(x) for x in l]

# how to generate f?
# Let's check the documentation
@pytest.mark.skip
@given(st.functions(like=lambda x: x,returns=st.integers()),st.lists(st.integers(), max_size=5))
def test_functional_map(f, l):
    result = functional_map(f, l)
    assert len(result) == len(l)

# Another function example

@pytest.mark.xfail
@given(st.functions(
    like=lambda state, move1, move2, result: (state, result),
    returns=st.tuples(st.integers(), st.integers()),
    pure=True,
))
def test_fn(f):
    assert f(1, 2, 3, 4) == (5, 6)

"""
===== More about strategies =====

NOT part of the spec:
- the program
- the strategy (generator)

We've seen some strategies already:
- st.integers()
- st.lists() -- given as a parameter a base strategy
    for generating elements of theh list.

What is the difference between a strategy and a precondition?
    st.lists(st.integers(), min_length = 1)
The strategy is an st.lists object, the precondition is just
the statement "l is a list of integers of length at least 1."

Example strategies:
(written as Python generators)
"""

def gen_simple():
    # generate sequential inputs
    for i in range(0, 1000):
        yield i

from random import randint

def gen_smarter():
    # generate completely random inputs
    # import a random number generator
    while True:
        yield randint(-10000, 10000)
    # Also not perfect and you can do better.

def gen_simpler():
    while True:
        yield 7
    # Probably not a good strategy
    # https://imgur.com/uR4WuQ0

"""
Some other useful strategies:
- st.text() -- for generating (valid) strings
- st.one_of() -- generates one thing or the other
    st.one_of(st.integers(), st.floats())
- st.functions() -- generates functions with a given signature

Hypothesis generators are much smarter than just generating
random values.

Minimizing examples:
    https://hypothesis.readthedocs.io/en/latest/data.html
    Once Hypothesis finds a failing example, it doesn't give up,
    it will continue searching to find a "minimal" example
    to show to the user

Custom formats: (emails, dates, etc.)
    st.text() -- UTF8 by default
    st.datetimes()
    st.emails()
    (you can also write your own)

Guiding the search:
    assumptions: https://hypothesis.readthedocs.io/en/latest/details.html#making-assumptions
    target: https://hypothesis.readthedocs.io/en/latest/details.html#hypothesis.target
"""

@given(st.floats(0, 1e100), st.floats(0, 1e100), st.floats(0, 1e100))
@pytest.mark.skip
def test_associativity_with_target(a, b, c):
    ab_c = (a + b) + c
    a_bc = a + (b + c)
    difference = abs(ab_c - a_bc)
    target(difference)  # Without this, the test almost always passes
    assert difference < 2.0

"""
Summary:
How hypothesis works, roughly:

1. Generate a random example

2. Run the example

    a. If it encounters a precondition/assume:
        does it satisfy the precondition?
        - If YES, continue
        - If NO, move on to the next test
            + on the next run, try to guide the search towards a passing example

    b. If it encounters an assertion:
        does it satisfy the assertion?
        - If YES, continue
            + on the next run, try to guide the search towards a failing example
        - If NO, report a failure -- go to step 4

4. Once a failing assertion is found:
    try to simplify the example ("shrink") it to something understandable.
"""
