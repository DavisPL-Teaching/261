"""
Lecture 1, part 3:
Stronger and weaker specifications

=== Segue ===

The previous exercise from part 2 is a good segue into two topics we want to cover next:

1. An appropriate formal def of specs?

2. Stronger and weaker specifications

3. Types of specifications / ways of writing specifications.

=== Formal Definition of Specifications ===

What is an appropriate formal definition of a spec?

We've been thinking of specs informally as "any true or false property of a program"

Assume we have some set of programs in mind (e.g., all programs that could be written in Python or C++)

Definition.
- A *specification* S is a statement, written in some grammar
  (in our case, the grammar for some subset of Python),
  which denotes true or false for any individual program.

A specification **denotes a set of programs**
because I can look at the set of programs for which the property is true.

    Mathematically:
    If we write ⟦ S ⟧ for the denotation of S:

    Prog := set of all programs (defined by a syntax or grammar)

    ⟦ Spec ⟧ ⊆ Prog

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

    assert false

that will always fail! that fails for all programs.

And all of our other examples so far (e.g., the spec is_even, test_integer_srt, etc.
are somewhere in between the two extremes.)

=== Exercise ===

Let's sort the above specifications by which is stronger/weaker than the others.

Let's do this exercise together as a class --
if we don't finish it, we will do it as next time's poll.

1. If the input to integer_sqrt is a nonnegative integer, then the output is an integer.
2. If the input to integer_sqrt is a positive integer, then the output is an integer.
3. True (true of all programs)
4. False (false of all programs)
5. The input arguments are not modified by the program.
6. If the input is greater than 100, then the output is greater than 10.
7. If the input is greater than or equal to 100, then the output is greater than or equal to 10.

Let's try to sort all of these by which are stronger and weaker.

TODO: place in the following picture:

    Strongest


    Weakest

"""

"""
Exercises:

- For specifications 1 and 2, write an example program
  which satisfies one spec and not the other.

- For specifications 6 and 7, write an example program
  which satisfies one spec and not the other.

(Some people thought that 6 was stronger than 7!
Let's disprove that and find an example that satisfies 6 but not 7.)

The homework has a similar exercise related to stronger/weaker specs.
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

- We talked about stronger/weakers specs
- We did some exercises practicing the methodology of working with specs,
  in particular using the "test harness" approach.
- Formal def of a spec as a "set of programs"
- We did an example of coming up with a specific program satisfying
  spec S1 but not S2.
"""
