"""
Lecture 1: Program Specifications
ECS 261 - Spring 2025
"""

"""
=== Program specifications ===

A specification is any true or false property about a program.

- By "program", at this stage, just think of this as any function in Python.

Any given program either "satisfies" the specification (i.e., the property is true for that program, or does not satisfy the specification, i.e. the property is false for that program.

Some programs satisfy the property (spec), others don't.
Like a blueprint for a house, or an answer key for a test question.

We saw examples on today's poll:
https://forms.gle/AG5XoCkBiiGKK7WZA
"""

# Specifications in natural language
# SPECIFICATION:
# On all inputs x, is_even(x) should return whether or not x is even.
# On inputs x that are ...,
def is_even(x):
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
Tying this back to lecture 0?

Some philosophy here:
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
"""

"""
=== Exploring specifications ===

Hypothesis is a nice tool we can use to explore specifications,
before diving into the deeper formal logic parts of the course.

It helps transition if you are used to program testing in a more
pragmatic engineering context, and helps explore the transition to formal
specs.

=== Hypothesis ===

*hypothesis* is...

To install:

    - Check your python version: python3 --version
    - Check your pytest version: pytest --version
    - Install Hypothesis:

        pip3 install hypothesis

    (Note: I know this is not the right way to actually install Python packages,
    but I'm lazy)
"""

# Starting with imports...
from hypothesis import given
from hypothesis import strategies as st
from hypothesis import settings

# We don't need this yet, but will need it later
import pytest

"""
To run:

    pytest lecture1.py

"""

# First, we need a program to test
def average(l):
    return sum(l) / len(l)

# Next, we need to write down a specification

# Using Hypothesis to test specifications
# This causes Hypothesis to automatically generate a unit test
# The unit test will: run a bunch of random inputs, try running the program,
# and raise an error if any assertions are violated.
@given(st.lists(st.floats(allow_nan=False, allow_infinity=False), min_size=1))
@pytest.mark.skip
# Try this to show how many examples were tried - thanks to Hassnain for finding!
# https://piazza.com/class/m8t4cwl1qsm6yw/post/13
# @settings(verbosity=3)
def test_average(xs):
    assert min(xs) <= average(xs) <= max(xs)

"""
Note the argument xs -- this is called random testing!
Usually contrasted with unit testing.

Some additional motivation:
Here's a common experience when doing unit testing:
"""

# Common experience unit testing:
@pytest.mark.skip
def test_average_function():
    assert average([1, 2, 3]) == 2
    assert average([1, 2, 3, 4]) == 2.5
    assert average([1, 2, 3, 4, 5]) == 3
    assert average([2.0]) == 2.0
    # ^^ long list of cases that may or may not be exhaustive!

# ignore_test_average_function()

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
The idea of Hypothesis: instead of running a long list of specific
examples, randomly generate thousands or tens or hundreds of thousands
of examples.

This is called "random testing".

Advantages:
- More likely to find a bug (assertion violation) if one exists
- Allows to test more general specifications, not just specific input
  and output examples.
"""

# Another example

def list_product(l):
    result = 1
    for x in l:
        result *= x
    return result

# (Of course we could just use built-in from functools
# or implement this with reduce or whatever.)

from functools import reduce

# This example generates input lists of integers
@pytest.mark.skip
@given(st.lists(st.integers()))
def test_list_product(xs):
    # Unit examples
    # assert list_product([]) == 1
    # Not very interesting!
    # More interesting: check that our implementation
    # matches the standard/expected implementation.
    assert list_product(xs) == reduce(lambda x, y: x * y, xs, 1)

# Internally: will generate like
# def __hypothesis_wrapper_test_list_product():
#     # generate a bunch of random inputs
#     for xs in input_examples:
#         run test_list_product(xs)
#         if error: return error
#     return Ok

"""
One important point for now:
Ties back to the question earlier:

    Q: If we can't find a counterexample to the specification for a program,
    does that mean the program satisfies the specification?

    A:
        If we test **all possible inputs**, then yes!
        If we only test **some** possible inputs, then no.

    Important point: Hypothesis only tests some inputs, not all!
    (We will see that the tools we cover later actually cover all inputs:
     Z3 and Dafny will be able to check whether the specification holds on
     all inputs.)

    This is what makes Hypothesis a **testing** tool, rather than **verification.**

=== Recap ===

1. We defined a "program specification" as any true or false property of a program

2. We are agnostic to how specifications are written, so **any** true or false statement about the program is a valid specification

3. Hypothesis can be used to, given input a program and a specification, determine whether the spec seems to hold on a bunch of random inputs
(useful for software testing)

4. Difference between testing & verification: Testing = try some inputs, verification (where we're eventually going) = actually determine whether the spec holds on **all** inputs, not just some inputs.

********** Where we ended for today **********

=== Tuesday April 8 ===

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
@pytest.mark.skip
@given(st.integers(min_value=0, max_value=10_000))
def test_integer_sqrt(n):
    ans = integer_sqrt(n)
    assert (ans * ans <= n and (ans + 1) * (ans + 1) > n)

# Some examples to try running the program
# print(integer_sqrt(3))
# print(integer_sqrt(-3))

"""
=== Checking our understanding ===

Before we run the code, let's do a poll.

https://forms.gle/eGnEDsmnmjEVH8ZB9

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

=== Segue ===

The above exercise is a good segue into two topics we want to cover next:

1. Formal definition of a specification

2. Stronger and weaker specifications

3. Types of specifications / ways of writing specifications.

=== Formal Definition of Specifications ===

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

=== Second poll ===

Let's sort the above specifications by which is stronger/weaker than the others.

Let's do this poll together as a class.
(But still submit it on your own machines)

https://forms.gle/F4mfmfGvJC1FVVu89

Exercise:

- Pick one of the rows/columns in the above poll
(an example pair where one program is stronger than the other),
and write an example
which satisfies one spec and not the other.

- Pick one of the rows/columns in the above poll
(an example pair where one program is NOT stronger than the other),
and write an example
which satisfies one spec and not the other.

(The homework has some similar exercises!)
"""

# 6. For all integer inputs x, If the input is greater than 100, then the output is greater than 10.
# 7. For all integer inputs x, If the input is greater than or equal to 100, then the output is greater than or equal to 10.

# Between 6 and 7, is either one stronger?
# - 6 is stronger than 7 iff all programs satisfying 6 also satisfy 7
# Is there a program satisfying 6 but not 7?

def prog_ex(x):
    # Program returning 9 if the input is 100, otherwise returning 11
    if x == 100:
        return 9
    else:
        return 11

@given(st.integers(min_value=0, max_value=10_000))
def test_prog_ex_spec_6(x):
    y = prog_ex(x)
    if x > 100:
        assert y > 10

@given(st.integers(min_value=100, max_value=100))
# Mark as expected failure -
@pytest.mark.xfail
def test_prog_ex_spec_7(x):
    y = prog_ex(x)
    if x >= 100:
        assert y >= 10

# - 7 is stronger than 6 iff all programs satisfying 7 also satisfy 6
# (Exercise)

# @pytest.mark.skip
# # @given(st.integers(min_value = , max_value = ))
# def test_prog_ex_stronger():
#     # TODO
#     raise NotImplementedError

"""
The program we wrote satisfies spec 6 but not spec 7.

This reveals a problem with Hypothesis!
Hypothesis tries random inputs, but in this case, it failed to try
the input 100, so it failed to find the input which falsifies specification 7.

One way to fix is (as we do above) by reducing the range of inputs we consider
(perhaps not very satisfying)

Another way to fix is by increasing the number of inputs we try (better - the
homework shows how to do this, @settings(...))

But, this is a fundamental limitation of testing specifications,
and is why we will turn to verifying them (i.e., actually proving
whether the spec holds or not) in the coming lectures.
This is what we will do in Z3 in Dafny.

*************** Where we ended for today ***************

===== Thursday, April 10 =====

From last time, a specification denotes a set of programs:

    ⟦ Spec ⟧ ∈ 2^Prog

    ^ read: denotation of a spec is a subset of all programs.

    Spec is written in some grammar
    Prog is the set of all programs written in some grammar

S1 is stronger than S2 if:

    ⟦ S1 ⟧ ⊆ ⟦ S2 ⟧

Observation:

-  "Stronger than" is a mathematical partial order on specifications.
    (This means...)

Fun exercise (thanks to a student after class last time!)

- Show that the partial order is countable, has infinite width, and has infinite height.

Another exercise:

- Define a similar partial order on programs: P1 *refines* P2 if all specs true of P1 are true of P2.

  Is this partial order interesting or is it trivial?

"""

"""
=== Types of Specifications ===

Remember that second step...

Our definition of "specification" is very broad:

    ⟦ Spec ⟧ ∈ 2^Prog

this is very useful! But it is also not very specific.

In practice, we need our specification to be understandable to the tool we are using...
    i.e.: written in a more specific grammar:

- Hypothesis only understands specs using @given annotations on pytests (+ assert and assume)

- Verification tools like Z3 and Dafny only understand specs written in formal logic
  (typically, first-order logic)

Here are some examples (some previous and some new ones) on integer_sqrt:

1. If the input is an integer, then the output is an integer.
2. False (false of all programs)
3. The input arguments are not modified by the program.
4. If the input is greater than or equal to 100, then the output is greater than or equal to 10.
5. The program does not read any files from the filesystem
6. The program executes in constant time
7. The program always terminates

Types of specs above?
Try translating them to logical statements about a program f.

Some questions:

- Which of these specifications expressible as Hypothesis tests?

- Which of these specifications easily checkable?

Other examples?
    (see cut/other-specs.md)

We can try writing some of these in Hypothesis:
"""

@pytest.mark.skip
def test_int_sqrt_always_terminates(x):
    # TODO
    raise NotImplementedError

@pytest.mark.skip
def test_int_sqrt_never_opens_a_file(x):
    # TODO
    raise NotImplementedError

"""
=== Classes of specifications ===

The discsussion about which are testable using Hypothesis should reveal an important distinction:

- A **functional correctness** property is...

Two other special cases of specifications that turn out to be particularly useful:

- A **full functional correctness** spec is...

- A **safety property** is...

- A **liveness property** is...

Are the above all possible specifications?
No! We can imagine much more interesting cases...
    (More examples, again, in cut/other-specs.md)

Review:

Can we test safety properties in Hypothesis?

Can we test liveness properties in Hypothesis?

What are all possible specifications expressible in Hypothesis?
(pin in this question - more on this soon)
"""

"""
=== Functional correctness ===

Functional correctness is the focus of many program verification efforts in practice.
It's not perfect, but it is often a good starting point!
And we have good tools for reasoning about it (compared to some of the others
which require deep and difficult encodings, more on this later.)

We typically express functional correctness using...

=== Preconditions and postconditions ===

Let's start with an example:
"""

# Classic example: Division by zero

# input two integers
def divide(x, y):
    return x / y

@pytest.mark.skip
# @pytest.mark.xfail
@given(
    st.integers(min_value = -100, max_value = 100),
    st.integers(min_value = -100, max_value = 100),
)
@settings(max_examples=10_000)
def test_divide(x, y):
    # what to test here?
    z = divide(x, y)
    # Write the spec here:
    assert type(divide(x, y)) is float
    # (or another property)
    raise NotImplementedError

# We couldn't even test our statement, because our program
# crashed :(
# Exception handling?
# this is exactly what preconditions are for.
# Let's directly make sure the thing we are dividing by (y)
# is > 0.

"""
Exercise (skip for time):
Rewrite the examples 1-7 using preconditions/postconditions

Even if you have not heard of the word "precondition",
you are probably intuitively familiar with the concept of preconditions
if you have some experience programing and working with libraries...

Examples:
- list pop: https://docs.python.org/3/tutorial/datastructures.html

    "It raises an IndexError if the list is empty or the index is outside the list range."

    This is another way of saying that the precondition of
    list.pop() is that the list should be nonempty.

- file open: https://docs.python.org/3/library/functions.html#open

    Has a number of preconditions:
    - The file should be able to be opened (OSError otherwise)

    - "If closefd is False and a file descriptor rather than a filename was given, the underlying file descriptor will be kept open when the file is closed. If a filename is given closefd must be True (the default); otherwise, an error will be raised."

Point:
You can often read off preconditions from the documentation!

Point:
In practice, exceptions are often used to enforce preconditions --
if we don't know what to do on a particular input, we crash the program

Note that we can model exceptions in our specification in two
ways:
- If the exception is expected behavior, we can test that
  when the function is run on the bad input, the exception is raised.
  This does NOT involve excluding the input via the precondition,
  instead we write an assertion to expect the correct behavior.

- If the exception is not expected behavior, or if we don't
  want to consider inputs for which the exception is raised
  as valid, we can exclude them via a precondition.

Another example:
"""

def divides_2(x, y):
    return x / y

ERROR = .000001

@given(
    st.integers(min_value = -100, max_value = 100),
    st.integers(min_value = -100, max_value = 100),
)
def test_divides_2(x, y):
    # could do e.g.:
    # assume -100 <= y <= 100
    assume(y != 0)
    result = divides_2(x, y)
    assert (result * y - x < ERROR)

"""
With the precondition included, the spec says:
On all inputs x, y such that
        -100 <= x <= 100 and
        -100 <= y <= 100 and
        y is not zero,
    divides_2(x, y) * y is approximately x.

More generally, the spec has the following form:

    "On all inputs x such that P(x) holds, Q(function(x)) holds."

Are pre and postconditions sufficient?

- Can we now express all properties we are interested in?

- Can Hypothesis express anything that pre/postconditions can't?

More general:

===== Assume and assert =====

Going back to our divide by zero example.

What if we want to write it to include positive and negative integers,
not only positive integers?
"""

from hypothesis import assume

@pytest.mark.skip
@given(
    st.integers(min_value = -1000, max_value = 1000),
    st.integers(min_value = -1000, max_value = 1000),
)
@settings(max_examples=1000)
def test_divide_2(x, y):
    # Assume statement!
    # Adds some constraint to the precondition.
    assume(y != 0)
    # assert type(divide(x, y)) is float
    # assert abs(divide(x, y) * y - x) < ERROR

"""
Why is it called "assume"?

- Assert: This property should hold, if it doesn't, that's an
    error. I want to report a test failure.
- Assume: This property should hold, if it doesn't, I want to
    ignore this test.

Assert and assume interact in interesting ways...

Poll:
https://forms.gle/cr5DYBDo3nTbB2oK6

Which of the following has no effect? (Select all that apply)
- assert True
- assert False
- assume True
- assume False
- assert P if it occurs immediately following assume P
- assume P if it occurs immediately following assert P
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

- On all input executions such that all assume() statements
  hold up to a given point,
  all assert() statements hold after that point.
"""

"""
===== Discussion and limitations =====

Hypothesis

# Advantages

Some more about advantages:
https://news.ycombinator.com/item?id=34450736

"I've never introduced property tests [Hypothesis specs] without finding a bug in either the specification or implementation. I have repeatedly spent time figuring out where the bug was in my property testing library before realising that it was correct and the obviously correct code I was testing was actually wrong."

# Disadvantages

Most important limitation:

- Testing might not find the bug!

Edsger Dijkstra:

    "Program testing can be a very effective way to show the presence of bugs, but it is hopelessly inadequate for showing their absence."

This is not a problem with the spec itself, but with using random testing
as a method of validating the spec.

Limitations related to writing specs -- these are not specific to Hypothesis (!)

- Specification could be wrong

- Specification could be incomplete

Other limitations of Hypothesis specifically?

- Customization

- Testing can be redundant.

Quick recap:
- we talked more about assert/assume
- why is assume useful? why are invariants useful?
- we talked about postconditions:
    most of the specs so far have been postconditions
    on the output.
    A pre/post condition based spec is called
    functional correctness
- we talked about limitations of Hypothesis: it can't
    prove there are no bugs.
    That is what the remaining tools in this class
    will be about.

"""
