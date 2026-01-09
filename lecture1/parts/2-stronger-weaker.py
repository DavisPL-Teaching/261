"""
Lecture 1, Part 2:
Stronger and weaker specifications

**Please note: These notes have not yet been updated for winter quarter 2026.**

=== Intro and poll ===

Recap on methodology so far:

1. We write a program
    (i.e.: what the program does)

2. We write a specification (or spec)
    (i.e.: what the program *should* do)

3. We check whether the program satisfies the spec

    3 Methods:
    a. Testing (Hypothesis) - try random examples
    b. Automated Verification (Z3) - automatically search for a mathematical proof
    c. Interactive Verification (Dafny) - write the proof yourself

    (And other methods we won't cover in this class!
     Though I note that many other methods can be thought of as special cases of the above.
     E.g.: fuzzing = (a), static analysis = (b), typechecking = (b) and (c), etc.)
"""

"""
Let's practice this.
(This time with a simpler example)

Exercise:

    Write a function that calculates
    the "integer square root" -- that is, takes an integer
    and calculates the square root of it, rounded down to the nearest
    integer.
"""

# We might need this
from math import sqrt

# 1. Write the program
def integer_sqrt(n):
    # Ideas: binary search and check the square to see if it's greater than the target integer - keep narrowing search window until we hit the point
    # where the current integer is the int square root
    # Another idea: just call the sqrt function and round it down.
    return int(sqrt(n))

# 2. Write the specification
# In plain English:
# Suggestion: whatever the function returns, if we square it, we get n
# This is the right idea but might not always work...
# Input: 10, int(sqrt(10)) = 3, 3*3 = 9, not quite 10
# Suggestion:
# - if our answer is ans, we could look at ans^2 and (ans+1)^2
# - The original integer n should be between ans^2 and (ans+1)^2
# - In our example: 3^2 = 9 < 10 < 4^2 = 16

# As a logical assertion:
# assert ans * ans <= n and (ans + 1) * (ans + 1) > n

# 3. Check the specification
# This step will depend on the tool.
# As a Hypothesis test: - @given annotation and a unit test.
@pytest.mark.skip # comment out to run
@given(st.integers(min_value=0, max_value=10_000))
def test_integer_sqrt(n):
    ans = integer_sqrt(n)
    assert (ans * ans <= n and (ans + 1) * (ans + 1) > n)

# Some examples to try running the program
# print(integer_sqrt(3))
# print(integer_sqrt(-3))

"""
=== Checking our understanding ===

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

(Let's run the code)

=== Question ===

Q: are properties about the syntax or lines of code considered specifications?
    E.g.: the function must have at least 10 Lines of code
    A: Yes, that's a valid spec but probably not one we're interested in.

=== Segue ===

The above exercise is a good segue into two topics we want to cover next:

1. Stronger and weaker specifications

2. Types of specifications / ways of writing specifications.

=== Stronger and Weaker Specifications ===

Definition.

Let S1 and S2 be specifications

- S1 is *stronger* than S2
    if the set of programs satisfying S1 is a subset (or equal) to the set of programs satisfying S2

    ⟦ S1 ⟧ ⊆ ⟦ S2 ⟧

    Think of an example:
    "S1 = the output is 1"
    "S2 = the output is odd"
    the set of programs outputting 1 is a subset of the set of programs whose output is odd.
    S1 is constraining the program more (giving more information about the program,
    so S1 is stronger).

- S1 is *weaker* than S2
    if the set of programs satisfying S2 is a subset of the set of programs satisfying S1.

    ⟦ S2 ⟧ ⊆ ⟦ S1 ⟧

A set is a subset of itself (⊆, not ⊂).
We could speak of "strictly stronger" or "strictly weaker" specs if desired.

Special cases:

    False (the specification true of no programs)
        = the empty set of programs, which makes it the strongest possible spec

    True (the specification true of all programs)
        = the set of all programs, which makes it the weakest possible spec.

And all of our other examples so far (e.g., the spec is_even, test_integer_srt, etc.
are somewhere in between the two extremes.)

Observation:

-  "Stronger than" is a mathematical partial order on specifications.
    (Actually a preorder)
    (This means... it's transitive and reflexive)

    1. For all S1, S2, S3, if ⟦ S1 ⟧ ⊆ ⟦ S2 ⟧ and ⟦ S2 ⟧ ⊆ ⟦ S3 ⟧ then ⟦ S1 ⟧ ⊆ ⟦ S3 ⟧.

    2. For all S, ⟦ S ⟧ ⊆ ⟦ S ⟧

Fun exercise:

- Show that the partial order is countable, has infinite width, and has infinite height.

Another exercise:

- Define a similar partial order on programs: P1 *refines* P2 if all specs true of P1 are true of P2.

  Is this partial order interesting or is it trivial?

=== Exercise ===

Let's sort the above specifications by which is stronger/weaker than the others.

Let's do this poll together as a class.

1. If the input to integer_sqrt is a nonnegative integer, then the output is an integer.
2. If the input to integer_sqrt is a positive integer, then the output is an integer.
3. True (true of all programs)
4. False (false of all programs)
5. The input arguments are not modified by the program.
6. If the input is greater than 100, then the output is greater than 10.
7. If the input is greater than or equal to 100, then the output is greater than or equal to 10.
"""

"""
Additional Exercise:

- Pick one of the rows/columns in the above poll
(an example pair where one program is stronger than the other),
and write an example
which satisfies one spec and not the other.

- Pick one of the rows/columns in the above poll
(an example pair where one program is NOT stronger than the other),
and write an example
which satisfies one spec and not the other.

(The homework may have some similar exercises!)
"""
