"""
Lecture 1, part 3:
Stronger and weaker specifications

=== Segue ===

The previous exercise from part 2 is a good segue into two topics we want to cover next:

1. An appropriate formal def of specs?

2. Stronger and weaker specifications

=== Formal Definition of Specifications ===

What is an appropriate formal definition of a spec?

We've been thinking of specs informally as "any true or false property of a program"

    ---> we can think of a spec as its set of satisfying
         programs

Mathematically, if I have a spec S:

    If we write ⟦ S ⟧ for the denotation of S:

    Prog := set of all programs (defined by a syntax or grammar)

    ⟦ S ⟧ ⊆ Prog

    ex.:

        ⟦ True ⟧ = Prog
        ⟦ False ⟧ = ∅ <-- emptyset

Assume we have some set of programs in mind (e.g., all programs that could be written in Python or C++)

Definition.
- A *specification* S is a statement, written in some grammar
  (in our case, the grammar for some subset of Python or Z3),
  which denotes true or false for any individual program.

A specification **denotes a set of programs**
because I can look at the set of programs for which the property is true.

Thinking about a spec as its "set of possible programs" is often useful!

=== Stronger and Weaker Specifications ===

Definition.

Let S1 and S2 be specifications

- S1 is *stronger* than S2
    if every program satisfying S1 satisfies S2.

    i.e.

        if the set of programs satisfying S1 is a subset (or equal) to the set of programs satisfying S2

    i.e.

        ⟦ S1 ⟧ ⊆ ⟦ S2 ⟧

    Think of an example:
    "S1 = the output is 1"
    "S2 = the output is odd"

    the set of programs outputting 1 is a subset of the set of programs whose output is odd.
    S1 is constraining the program more (giving more information about the program,
    so S1 is stronger).

    btw:
        S1 is stronger than S1
        S2 is stronger than S2.

- S1 is *weaker* than S2
    means the same thing as S2 is stronger than S1.

        ⟦ S2 ⟧ ⊆ ⟦ S1 ⟧

Special cases:

    False (the specification true of no programs)
        = the empty set of programs, which makes it the strongest possible spec

    If you give me any spec (your definition of correctness) S

        False is stronger than S

    True (the specification true of all programs)
        = the set of all programs, which makes it the weakest possible spec.

    If you give me any spec (your definition of correctness S),

        True is weaker than S.

Think of it this way: if I write a Python test, and I put

    assert True

that's equivalent to saying nothing. (will pass for all programs) If I put

    assert False

that will always fail! that fails for all programs.

And all of our other examples so far (e.g., the spec is_even, test_integer_srt, etc.
are somewhere in between the two extremes.)

=== Exercise ===

Let's sort the previous specifications by which is stronger/weaker than the others.

Let's do this exercise together as a class --

1. If the input to integer_sqrt is a nonnegative integer, then the output is an integer.
2. If the input to integer_sqrt is a positive integer, then the output is an integer.
3. True (true of all programs)
4. False (false of all programs)
5. The input arguments are not modified by the program.
6. If the input is greater than 100, then the output is greater than 10.
7. If the input is greater than or equal to 100, then the output is greater than or equal to 10.

Let's try to sort all of these by which are stronger and weaker.

between 2 and 1:
    2 is stronger? xxx
    1 is stronger? x

In fact, 1 is stronger.

TODO: place in the following picture:
Start: put False and True down

    Strongest
    4
    |  \
    |  1
    |  |
    5  2
    |  |
    |  |
    3  |
    Weakest

"""

"""
Exercises:

1. If the input to integer_sqrt is a nonnegative integer, then the output is an integer.
2. If the input to integer_sqrt is a positive integer, then the output is an integer.

If we want to decide if 2 is stronger than 1,

    every program satisfying 2 satisfies 1

which means, to find a counterexample to this, we should find
a particular program such that

    our program satisfies 2 and NOT 1.

similarly, if we want to decide if 1 is stronger than 2,
we want to decide whether there is any program such that

    our program satisfies 1 and NOT 2.
"""

"""
- For specifications 1 and 2, write an example program
  which satisfies one spec and not the other.

1. If the input to integer_sqrt is a nonnegative integer, then the output is an integer.
2. If the input to integer_sqrt is a positive integer, then the output is an integer.

program satisfying
2 and not 1:
"""

def prog_ex(n):
    if n == 0:
        return None
    else:
        return 1000

"""
This satisfies 2 but not 1

showing that 2 is NOT stronger than 1

what about the other way around:
program satisfying 1 but not 2:

impossible.

Any program satisfying 1 does satisfy 2.
So
1 is stronger than 2
"""

# def prog_ex_2(n):
#     # 1. If the input to integer_sqrt is a nonnegative integer, then the output is an integer.
#     if n >= 0:
#         return 1000
#     else:
#         #

"""
what about 6 and 7?
- For specifications 6 and 7, write an example program
  which satisfies one spec and not the other.

6. If the input is greater than 100, then the output is greater than 10.
7. If the input is greater than or equal to 100, then the output is greater than or equal to 10.

6 is talking about a smaller set of inputs (integers > 100 instead of integers >= 100)
6 is making a stronger statement on the output (output > 10 instead of output >= 10)

This makes 6 and 7 incomparable

Once again, we can give specific examples:

prog satisfying 6 but not 7:
"""

def my_prog(n):
    if n > 100:
        return 11
    elif n == 100:
        return 5
# ^^^ satisfies 6 but not 7

def my_prog(n):
    return 10

# ^^^ satisfies 7 but not 6

"""
The homework has a similar exercise related to stronger/weaker specs.
(exercise 2)
"""

# Import
import pytest

def prog_ex(x):
    # TODO
    raise NotImplementedError

def spec_prog_ex_1(x):
    # TODO
    raise NotImplementedError

def spec_prog_ex_2(x):
    # TODO
    raise NotImplementedError

# Test that prog satisfies one spec but not the other
@pytest.mark.skip
def test_prog_ex():
    # TODO
    raise NotImplementedError

"""
This can be confusing!

    Even though spec 1 tests a *wider range* of inputs --
    in other words, has a *weaker* requirement on the input --
    spec 1 is not weaker than spec 2,
    and in fact, spec 2 is weaker than spec 1.

Recap:

- Formal def of a spec *denoting* a "set of programs"

    ⟦ S ⟧ = set of programs satisying S

- We talked about stronger/weakers specs

    spec S1 is stronger than S2 (i.e. S2 weaker than S1)
    if every prog satisfying S1 satisfies S2

        ---> I.E.: there is no program satisfying S1 and not S2.

- We did some exercises practicing the methodology of working with specs,
  in particular using the "test harness" approach.

- We did an example of coming up with a specific program satisfying
  spec S1 but not S2.
"""
