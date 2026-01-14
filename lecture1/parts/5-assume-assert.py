"""
Lecture 1, Part 4:
Assume and Assert

**Please note: These notes have not yet been updated for winter quarter 2026.**

===== Assume and assert =====

Going back to our divide by zero example.

This time we will use Hypothesis again for random testing.

pip3 install hypothesis

What if we want to write it to include positive and negative integers,
not only positive integers?
"""

import pytest
import hypothesis
from hypothesis import assume, strategies as st, settings, given

def divides_2(x, y):
    return x / y

ERROR = .00001

@given(
    st.integers(min_value = -1000, max_value = 1000),
    st.integers(min_value = -1000, max_value = 1000),
)
@settings(max_examples=1000)
@pytest.mark.skip
def test_divide_2(x, y):
    # Assume statement!
    # Adds some constraint to the precondition.
    assume(y != 0) # If this isn't true, throw away this particular test run.
    # assert type(divide(x, y)) is float
    assert abs(divides_2(x, y) * y - x) < ERROR

"""
These two little functions, assume and assert, turn out to be
fundamentally important to testing & verification.

- Assert: This property should hold, if it doesn't, that's an
    error. I want to report a test failure.
- Assume: This property should hold, if it doesn't, I want to
    ignore this test.

Assert and assume interact in interesting ways...

Poll:

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
@given(st.lists(st.integers()))
def test_sort_list(l):
    assume(l == sorted(l))
    assert sort_list(l) == sorted(l)

"""
Multiverse view
- Quantum bogosort:
    https://wiki.c2.com/?QuantumBogoSort
- (Based on: bogosort
    https://en.wikipedia.org/wiki/Bogosort)

Another way of thinking about this is, whose responsibility is
it to ensure the list is sorted?
- If I use assume, I'm saying it's the caller's responsibility.
- If I use assert, in a specification to say that some property
  is true, then I'm saying it's the function's responsibility
  to guarantee that property.
"""

"""
Now that we know about assume and assert,
A more complete definition of specifications in Hypothesis:

Hypothesis can express exactly those specifications that are
expressible using assume() and assert().

- On all input executions such that all assume() statements
  hold up to a given point,
  all assert() statements hold after that point.
"""
