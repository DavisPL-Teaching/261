"""
Lecture 1: Program Specifications
ECS 261 - Spring 2025

Part 1: Writing Specifications

=== Program specifications ===

A specification (or a "spec") is any true or false property about a program.

- By "program", at this stage, just think of this as any function in Python

    (or your favorite programming language)

Any given program
- "satisfies" the specification if the property is true for that program
- "does not satisfy" the specification, i.e. the property is false

Some programs satisfy the property (spec), others don't.
Like an answer key for a test question.

Recall the is_even function from Lecture 0:
"""

def is_even(x):
    if x == 1:
        return False
    elif x == 2:
        return True
    elif x == 3:
        return False
    elif x == 4:
        return True
    else:
        return False

"""
=== Poll ===

Which of the following is NOT a specification for the is_even function, according to the above definition?
Select all that apply.

https://forms.gle/Xwj61QidouEYaERC6

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
.
.
.
.
.

Recap:

A specification is a true or false property of a program.

    --> I give you a program, you decide if it's correct or not
        (yes or no answer).

===== Where to we get specifications from? =====

Specifications can come from:

I) Natural language
II) Unit tests
III) More general ways?

Let's compare each of these ways...
we will then see that there is a need to "generalize" these to get something
that is more robust for the purposes of true program verification.

(I) From natural language:
"""

# Specifications in natural language
# SPECIFICATION:
# On all inputs x, is_even(x) should return whether or not x is even.
# On inputs x that are ...,
def is_even_2(x):
    """
    (Docstring)

    @x: x is an integer
    Returns: true if x is even, false otherwise.

    ^^ This docstring is a specification!

    That's the same as:
    "On all inputs x such that x is an integer, is_even(x) returns true
     iff x is even."

    It's written in English, not in a formal langauge that we can
    apply automated tools to.
    """
    # <Body omitted>
    pass

"""
Problem:
You've written your program and your docstring,
but later on, the program gets edited!

Developer forgets to update the docstring

Docstring is now out of date! But nothing failed - the program still runs,
we didn't realize that anything went wrong.

(II) From unit tests

So: second step is to write unit tests.

Unit tests are an example of specifications!

Example:
"""

import pytest

# Unit test
# Comment out to run
# @pytest.mark.skip
# @pytest.mark.skip
@pytest.mark.xfail
def test_is_even():
    # This is a specification!!
    assert is_even(4)
    assert not is_even(3)
    # This is also a specification!
    # Fails because is_even(6) returns False
    assert is_even(6)

# run: pytest 1-specifications.py

"""
The unit test corresponds to a specification:

    "is_even(4) return true; is_even(3) should return false; and is_even(6) should return true)."

You may not know it, but you write specifications every day while programming!
Every time you write an "assert" statement or a unit test, you are writing a specification.

Unit testing is helpful!
Unit testing can be considered a form of writing specifications.
(Why?)

However, what is the problem with unit tests?

- Unit test could be wrong!

  It could pass the unit test, but I failed to check what we actually
  wanted to be true about the program

- Humans write them - so they miss edge cases

- You can only ever check finitely many cases!

.
.
.
"""

def average(xs):
    return sum(xs) / len(xs)

# Common experience unit testing:
@pytest.mark.skip
def test_average_function():
    assert average([1, 2, 3]) == 2
    assert average([1, 2, 3, 4]) == 2.5
    assert average([1, 2, 3, 4, 5]) == 3
    assert average([2.0]) == 2.0
    # ^^ long list of cases that may or may not be exhaustive!

# test_average_function()

"""
(III) More general ways?

Can we test the program on ALL inputs, rather than just some?

example sketch:


"""

def average(xs):
    return sum(xs) / len(xs)

# known "correct" average function
def average_gold(xs):
    # eg. a builtin:
    # return math.avg(xs)
    raise NotImplementedError

# Write a little contract:
# "On all inputs (of type ...), the output does (...)"

# We could even a little test harness to test this!

def my_test_harness(xs):
    avg1 = average(xs)
    avg2 = average_gold(xs)
    assert avg1 == avg2

"""
One idea: random testing/fuzzing.

Def. Random testing:
    Given a program and a spec that is executable (say,
    written as a test harness as above),
    automatically generate many inputs and try them.

Def. Fuzzing:
    Random testing against the spec "program does not crash"

This works pretty well!

Does this solve our problem?

===== A tangent: random testing =====

The following is an example using Hypothesis - a random testing tool -
to automatically test specifications.

To install:

    pip3 install hypothesis

    (requires pytest)

To run:

    pytest lecture1.py

"""

from hypothesis import given
from hypothesis import strategies as st
from hypothesis import settings

# First, we need a program to test
def average(l):
    return sum(l) / len(l)

# Next, we need to write down a specification

# Using Hypothesis to test specifications
# This causes Hypothesis to automatically generate a unit test
# The unit test will: run a bunch of random inputs, try running the program,
# and raise an error if any assertions are violated.
# ===== Version 1 =====
# @given(st.lists(st.floats(allow_nan=False, allow_infinity=False), min_size=1))
# ===== Version 2 =====
@given(st.lists(st.floats(allow_nan=False, min_value=0, max_value=100, allow_infinity=False), min_size=1))
# @pytest.mark.skip
# @settings(verbosity=3)
def test_average(xs):
    # ===== Version 1 =====
    # assert min(xs) <= average(xs) <= max(xs)
    # ===== Version 2 =====
    EPSILON = .00000001
    assert min(xs) - EPSILON <= average(xs) <= max(xs) + EPSILON

"""
This is better! Why?

- The spec is better:

- The checking is better:

- The checking is still limited!

Problem is, even if I generate 100s of examples, I'm still only testing
the function on finitely many inputs.

--> not truly proving -- or *verifying* the spec.

(more on this shortly)
"""

"""
===== The problem with testing =====

Consider the following program

(This is derived from a program we came up with last year in ECS 261):
"""

def prog_ex(x):
    # Program returning 9 if the input is 100, otherwise returning 11
    if x == 1000:
        return 9
    else:
        return 11

"""
Here is an example:
Write a test which states that:
For all integer inputs x, if x > 100, the output is 11.
"""

@given(st.integers(min_value=0, max_value=10_000))
# Comment out to run
# @pytest.mark.skip
def test_prog_ex_spec_6(x):
    y = prog_ex(x)
    if x > 100:
        assert y == 11

"""
The program passes!

This reveals a problem with testing!
Our testing tool (Hypothesis)
tries random inputs, but in this case, it failed to try
the input 1000, so it failed to find the input which falsifies specification 7.

There are ways to fix this by:

- generating more inputs

- specifying the input manually

But it isn't very satisfying.
"""

"""
=== Testing vs. verification ===

The above illustrates a fundamental problem.

Testing is the gold standard in industry!

BUT:

    Q: If we can't find a counterexample to the specification for a program,
    does that mean the program satisfies the specification?

    A:
        If we test **all possible inputs**, then yes!
        If we only test **some** possible inputs, then no.

    This is what makes Hypothesis a **testing** tool, rather than **verification.**

***** where we ended for today *****
"""

"""
Clarifying from last time:

- Specification vs. verification

- Verification vs. testing

=== Formal Definition of Specifications ===

The above motivates that we want specifications which:

- Specify the behavior precisely ("clear and ambiguous" from lecture 1)

- Specify the behavior on ALL inputs.

Also:

- We want to check or validate the spec on ALL inputs, not just some inputs.

In this class, we're generally interested in writing specifications that can be automatically
tested - or at least validated, whether or not the specification is true for that program.
This is what we call "formal specifications".

We will use mathematical logic to express formal specifications.

=== A formal definition of formal specifications ===

What is an appropriate definition of a formal spec?

We've been thinking of specs informally as "any true or false property of a program"

Assume we have some set of programs in mind (e.g., all programs that could be written in Python or C++)

Definition.
- A *specification* S is a statement, written in some grammar (in our case, the grammar for writing Python Hypothesis tests), which denotes true or false for any individual program.
  Equivalently, a specification denotes a *set of programs*

    (I can look at the set of programs for which the property is true.)

    Mathematically:
    If we write ⟦ S ⟧ for the denotation of S:

    Prog := set of all programs (defined by a syntax or grammar)

    ⟦ Spec ⟧ ∈ 2^Prog

    ⟦ Spec ⟧ ⊆ Prog

Q: are properties about the syntax or lines of code considered specifications?
    E.g.: the function must have at least 10 Lines of code

A: Yes, that's a valid spec but probably not one we're interested in.

Thinking about a spec as its "set of possible programs" is often useful!
(More on this in the next lecture part.)
"""

"""
=== Recap, philosophical discussion, and end notes ===

1. We defined a "program specification" as any true or false property of a program

To determine if our code is correct, we need a specification!

    remember the car example and chess program (Stockfish) examples!
    What does it mean for a program to be "correct"?
    Our answer is that it *can't* mean anything, unless there is some
    definition of what it *means* to be correct.
    That definition is the specification.

After all, when your boss/teacher/colleague/friend asks you to
write a program, they probably have some particular expectation
in mind of what that program should do.
If we write the expectation down in a precise way, then we get
a specification.

2. Specifications need to be clear & ambiguous - formally understandable

    We are agnostic to how specifications are written, but in this class we are generally
    interested in "formal specifications" - we can run/test them, they are formally
    defined in logic.

   Each formal specification S corresponds to a set of programs

    ⟦ S ⟧

3. You write specifications every day!

    Every time you write a Python unit test or assertion, that's a spec!

4. Testing can be used to, given input a program and a specification, determine whether the spec seems to hold on some specific inputs

    Random testing: try many inputs!

5. Difference between testing & verification: Testing = try some inputs, verification (where we're eventually going) = actually determine whether the spec holds on **all** inputs, not just some inputs.

Edsger Dijkstra:

    "Program testing can be a very effective way to show the presence of bugs, but it is hopelessly inadequate for showing their absence."

It is for this reason that we prefer to turn to more rigorous verification next,
in the coming lectures.
"""
