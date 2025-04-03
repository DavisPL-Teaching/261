"""
Lecture 1: Program Specifications
ECS 261 - Spring 2025
"""

"""
=== Program specifications ===

A specification is:


(Tying this back to lecture 0)

Some programs satisfy the property (spec), others don't.
Like a blueprint for a house, or an answer key for a test question.

Some philosophy here:
remember the car example from lecture 0?
What does it mean for a program to be "correct"?
Our answer is that it *can't* mean anything, unless there is some
definition of what it *means* to be correct.
That definition is the specification.

After all, when your boss/teacher/colleague/friend asks you to
write a program, they probably have some particular expectation
in mind of what that program should do.
If we write the expectation down in a precise way, then we get
a specification.

Examples on today's poll:
https://forms.gle/AG5XoCkBiiGKK7WZA

We can also come up with more interesting specifications:

    The program is_even(x) always terminates for all x.

Is it always possible to easily check whether a specification holds?

Answer (guesses):
    Yes?
    No?

Let's go through the examples from the poll...
"""

"""
Other examples:

    For all sufficiently large x, ...

    The source code of is_even contains...

    If is_even(x) is run on an arbitrary Python object x...

"""

"""
=== Hypothesis ===

*hypothesis* is...

To install:

    - Check your python version: python3 --version
    - Check your pytest version: pytest --version
    - Install Hypothesis:

        pip3 install

    (Note: I know this is not the right way to actually install Python packages,
    but I'm lazy)

Hypothesis is a nice tool we can use to explore specifications,
before diving into the deeper formal logic parts of the course.

It helps transition if you are used to program testing in a more
pragmatic engineering context, and helps explore the transition to formal
specs.
"""

from hypothesis import given
from hypothesis import strategies as st

import pytest

def average(l):
    return sum(l) / len(l)

# Using Hypothesis to test specifications
@given(st.lists(st.floats(allow_nan=False, allow_infinity=False), min_size=1))
def test_average(xs):
    assert min(xs) <= average(xs) <= max(xs)


"""
Note the argument xs -- this is called random testing!
Usually contrasted with unit testing.

Some additional motivation:
Here's a common experience when doing unit testing:
"""

# Common experience unit testing:
def ignore_test_average_function():
    assert average([1, 2, 3]) == 2
    assert average([1, 2, 3, 4]) == 2.5
    assert average([1, 2, 3, 4, 5]) == 3
    assert average([2.0]) == 2.0

# ignore_test_average_function()


# Another example

def list_product(l):
    result = 1
    for x in l:
        result *= x
    return result

# (Of course we could just use built-in from functools
# or implement this with reduce or whatever.)

from functools import reduce

# @given(st.lists(st.integers()))
# def test_list_product(xs):
#     # Unit examples
#     # assert list_product([]) == 1
#     # Not very interesting!
#     # More interesting: check that our implementation
#     # matches the standard/expected implementation.
#     assert list_product(xs) == reduce(lambda x, y: x * y, xs, 1)

"""
This is really tedious!
Hypothesis makes it easier by generating all of these tests (and more)
automatically.

It's also unclear if my tests are really thorough.
I haven't included:
- any lists with negative numbers
- any lists with both floats and integers
- any lists with repeated elements
"""

"""
=== Types of Specifications ===

I've been using the word "specification" in a very abstract sense.


without any real guidelines about what it is/is not allowed to say.

In practice, we write specifications in some dedicated tool for the task...

- A **logical specification** is:

What is the specification in the case of a Hypothesis test?



A **safety property** is...


A common way to define logical specifications?
Preconditions and postconditions.

Task:
Rewrite the examples above using preconditions/postconditions
"""

# Review: writing specifications
# list product example:
# Spec:
# - we test whether our impl matches the intended behavior.

# average of a list example:
# Spec:
# - we test whether our impl satisfies a property of interest.

#  Another example:
def double_list(l):
    # Program or implementation
    result = []
    for x in l:
        result.append(2 * x)
    return result

# Specification
# @given(st.lists(st.integers()))
# def test_double_list(l):
#     new_list = double_list(l)
#     # range(5) = numbers between 0 and 4
#     for i in range(len(l)):
#         assert new_list[i] == 2 * l[i]

"""
Components of correctness

Review: correctness requires:
- Model of what the program does (in our case, a Python program)
- Model of what the program *should* do (in Hypothesis, we do this through the @given and assertion statements)

Model?
One thing we have swept under the rug:
- what is the program anyway? What program behaviors are in scope?
  (Generally speaking this is something we can leave up to the PL and compiler
   people)

Comments

"All models are wrong, some are useful."
- attributed to George E. P. Box

"The best model of a cat is a cat, especially the same cat."
- Unknown
"""

########## Poll ##########

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

"""
=== More on Hypothesis ===

Hypothesis syntax
and useful features

https://hypothesis.readthedocs.io/en/latest/data.html

"""

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
# @given(st.functions(like=lambda x: x,returns=st.integers()),st.lists(st.integers(), max_size=5))
# def test_functional_map(f, l):
#     result = functional_map(f, l)
#     assert len(result) == len(l)

# Review:
# - We talked more about writing specs
# - The same function can have multiple specs, and it can have
#   incorrect specs
# - The process of writing a spec can be a good tool for debugging
#   BOTH problems with the function, and problems with the spec.

# Also, a *different* function can satisfy the same specification

def list_product_2(l):
    result = 1
    l.reverse()
    for x in l:
        result *= x
    return result

# Fixing the average function

def fixed_average(l):
    l_modified = [x / len(l) for x in l]
    return sum(l_modified)
    # (could also use a built-in)
    # e.g. there's a statistics.mean function

ERROR = .000001

# @given(st.lists(st.floats(allow_nan=False, allow_infinity=False), min_size=1))
# @pytest.mark.xfail
# def test_fixed_average(xs):
#     assert min(xs) - ERROR <= fixed_average(xs) <= max(xs) + ERROR

"""
=== Specifications, more formally? ===

How do we model the program?

We will get to this later in more dedicated verification frameworks.

However, often we are interested most in specifications which actually
relate to the program behavior
- (not, e.g., the function contains a comma inside its implementation)

Definition of correctness, slightly more formally:

1. What is a program? For our purposes, a program is something
that you can run and stuff will happen.
It has:
- An input (some keys/words/etc. the user types)
- An output (something that happens or gets returned at the end)
May also have:
- Various other behaviors as the function is executed (e.g.,
prints stuff to stdout, opens up Google.com on your browser,
deletes your home directory, reads from id_rsa and sends it
to an unknown email address, etc.)
To summarize the output and behaviors part:
Basically, a sequence of events/behaviors happen when its executed.
^^ i.e. a program execution

2. What is a specification (or spec, for short)
WORKING DEFINITION: let's say that a
spec
- TAKES AS INPUT: a possible input to the program
- DESCRIBES AS OUTPUT: a logical constraint on the behaviors that should occur
when the program is executed.
Well I mean:
a) Some sequences of behaviors are OK
b) Some sequences of behaviors are not OK.
In other words, it's a boolean property on program executions.

Relating this to preconditions/postconditions

Relating this to another concept: *assumptions* and *assertions*

(Note: assume statement in Hypothesis if we haven't covered it already)

def divide(x, y):
    return x / y

Notice I haven't asserted that y != 0
Therefore y != 0 is a precondition of this program.

Another example, in lots of C code you'll see things like

void buffer_write(x: *char, idx: i32, val: char):
    x[idx] = char

This is an important example of preconditions because if idx
is outside of the bounds of the array, there's really nothing
that the program can guarantee

A program is **correct** if
for all inputs x satisfying the preconditions,
and if I execute the program on x,
the program execution satisfies the spec.
"""
