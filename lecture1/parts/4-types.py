"""
Lecture 1, Part 4:
Types of Specifications

=== Intro ===

From last time: S1 is stronger than S2 if
all programs satisfying S1 also satisfy S2.

"stronger than" works how you would expect! for example:

- If S1 is stronger than S2 and S2 is stronger than S3, then S1 is stronger than S3.

Exercise:

    - show that "stronger than" forms a pre-order on all specifications

        also, each S is stronger than S

        if S1 is stronger than S2 and S2 is stronger than S1, we don't
        necessarily say that S1 and S2 are equal, but we can call them
        *equivalent.*

Thinking about how strong you want your specification to be is an important part of testing
and verifying software correctness in practice!

    ==> Weaker specs are often easier to test and verify, but they leave room for mistakes!

    ==> Stronger specs are often harder to write, but
        can be more likely to find bugs --
        however, it can be difficult to ensure that the
        spec covers all cases (more about this in today's lecture).

An extra practice question on stronger/weaker specs can be found in extras/stronger-weaker-practice.py

Note: from last time:

    A criteria that can be used:

        If spec S1 makes a **stronger** requirement on a
        **larger** set of inputs, compared to S2, then
        S1 is stronger than S2.
"""

import pytest

"""
=== Types of Specifications ===

Our definition of "specification" is very broad:

    "any true or false property"

this is very useful! But it is also not very specific.

In practice, we need our specification to be understandable to the tool we are using...
    i.e.: written in a more specific grammar

Ex:

- Python unit tests can only write assertions that are expressible in Python syntax

- We may be testing a function that we didn't implement! (or a foreign API, such
  as a network API)
  If so, we can only test statements that are true *before* and *after* the program executes

    These are called preconditions and postconditions

We can express these "statements that are true" using formal logic syntax.

- for all, there exists, if-then, and, or, not, ...

Not all specs can be easily written into Python tests!

    Even using the test harness approach

Here are some examples (some previous and some new ones) on integer_sqrt:

1. If the input is an integer, then the output is an integer.

    assert typeof(output) is int

    Let's think of our program integer_sqrt, as just a function f

    For all x, if typeof(x) is int then typeof(f(x)) is int.

    + this test can be expressed using Python syntax
      (as a Python test using the test harness approach)
    + It can also be written using formal logic

2. False (false of all programs) (empty set of programs)

    assert false

3. If the input is greater than or equal to 100, then the output is greater than or equal to 10.

    For all x, if x ≥ 100 then f(x) ≥ 10

4. The program terminates on all inputs.

    For all x, f(x) exists?
    ^^ maybe expressible using logic?

5. The program does not read any files from the filesystem

    ???
    Check the journal log of the computer?
    We would need some way to log all of the function calls
    (in this case system calls) that are made by f when it executes.
    This would be somewhat difficult to do in testing alone.

^^ More on these soon!
"""

from math import sqrt
def integer_sqrt(n):
    return int(sqrt(n))

# Spec 3:
def spec_3(n):
    if n >= 100:
        assert integer_sqrt(n) >= 10

# Spec 4:
def spec_4(n):
    # ensure that program terminates for n...
    # I can run the program...
    ans = integer_sqrt(n)
    # ^^^ if the program terminates, great!
    # ^^^ if the program doesn't terminate... we have a problem
    # our test also just won't terminate.
    # TODO ...
    # assert ???
    raise NotImplementedError

"""
What properties exactly *can* be tested using testing?

===== Functional correctness =====

An important pattern:

    For some of the specs above, we were able to write the spec
    just thinking about what's true
    before/after the program executes.

        --> solely about the input/output behavior of the function

    Like testing a foreign function!
        e.g. connecting to Google, GitHub, or chatGPT network
        API

- A **functional correctness** property is a spec which only depends
  on the set of all ordered pairs (x, y) such that f(x) = y.

    in other words:
    I have a program f

    I can run it on different inputs x and get different outputs y

    For any (x, y), it is either possible to get f(x) = y or it
    is not possible

    Functional correctness means: we only care about the set of
    possible (x, y).

Functional correctness is the focus of many program verification efforts in practice.
It's not perfect, but it is often a good starting point!
And we have good tools for reasoning about it (compared to some of the others
which require deep and difficult encodings, more on this later.)

- Often other properties can be encoded as functional correctness
  by maintaining some additional "state".

Informally:
    functional correctness = property of a program that only
    depends on its input-output behavior.

But even "True" and "False" are examples of this which aren't very useful.
Also "if the input is an integer, then the output is an integer"
isn't very useful.

Problem:

    if my spec is too weak (e.g. True), I may say "I wrote a formally verified system!"
    but I really didn't verify anything nontrivial or interesting about it.

    if my spec is too strong (e.g. False), I may say, "I wrote a formally verified system!"
    but in fact, I secretly assumed a false assumption, and proved false.

More useful:

our spec should be fully precise about what our system should do -- omitting
no unchecked data or edge cases.

- A **full functional correctness** spec is one which exactly specifies
    what f should do on every input.

    That means: for all x, f(x) is exactly the value y

    **Pragmatically/informally:** it means...

        if you write a spec, you should go
        through every piece of data in your output, and
        verify that every piece of data was computed
        correctly.

    Example: if we say "whenever x is an integer, f(x) is an integer", this doesn't define which integer it is!
    but in our example:

        "for all integers x, y = int_sqrt(x) is an integer such that y * y <= x < (y + 1) * (y + 1)"

    can actually show that there is only one such y.
    So this is a full functional correctness spec.

    **More formally:**
    A spec S is a full functional correctness spec if:

        For any f1, f2 satisfying the spec S, and for any input x,
        if f1(x) = y1 and f2(x) = y2 then y1 == y2.

=== Poll ===

For each of the following, is it a functional correctness spec? Is it a full functional correctness spec?

1. "int_sqrt(x) is always odd"
    is this functional correctness?
    is this full functional correctness?

2. "int_sqrt(x) is odd on at least two inputs"
    is this functional correctness?
    is this full functional correctness?

3. "int_sqrt(x) takes less than 5 minutes to run"
    is this functional correctness?
    is this full functional correctness?

4. "int_sqrt(x) does not read your password from memory"
    is this functional correctness?
    is this full functional correctness?

https://forms.gle/4ynHVtSqd4BftFtw9

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
.
.
.
.
.

Observation:

    A full functional correctness spec for a program
    is stronger than any functional correctness spec for that program.
"""

"""
A common way to express (full) functional correctness
is using...

===== Preconditions and postconditions =====

    (A.k.a.: "Programming by Contract")
    (A.k.a.: "Hoare triples")

    "An Axiomatic Basis for Computer Programming"
    Tony C.A.R. Hoare, 1969

A pre/postcondition spec has the following form:

    P and Q: Boolean properties

    - if P is true before executing the program,
        and we execute f,
      Q is true after.

In other words:

    - for ALL inputs satisfying P, after executing program
      f, the output satisfies Q.

We often use preconditions and postconditions to express functional correctness specs.
"""

# Spec 3:
def spec_3(n):
    #  vvvvvvvv  precondition
    if n >= 100:
        assert integer_sqrt(n) >= 10
        #      ^^^^^^^^^^^^^^^^^^^^^ postcondition

# Another classic example: Division by zero

# input two integers
def divide(x, y):
    # (integer division)
    return x // y

def spec_divides(x, y):
    # what to test here?
    # Write the spec here:
    # (you could write any spec here, but let's use:)
    z = divide(x, y)
    assert z * y <= x < (z + 1) * y

    # Fixed version with added precondition
    # if y > 0:
    #     z = divide(x, y)
    #     assert z * y <= x < (z + 1) * y

@pytest.mark.xfail
def test_spec_divides():
    for x in range(-100, 100):
        for y in range(0, 100):
            spec_divides(x, y)

# problems:
#    - spec didn't work for negative input
#    - spec didn't work for y == 0 because the program crashed

"""
We got an unexpected input! What do we do?
We have a decision to make here!

    1. specify the behavior on the unexpected input

        ===> if y > 0, then divides(x, y) satisfies ....
             AND if y == 0, then divides(x, y) throws an error.

             (e.g. use try - catch Python exception handling)

    2. say "I don't care about this input, whether the program
           crashes or not on a division by zero is not my problem."

Choice (2) is preconditions.

    Preconditions are dangerous! You might think you verified the software,
    but in fact you accidentally added inconsistent preconditions
    (equivalent to False)

    If this happens, you've verified the software ... on no inputs.

"""

def precond(x):
    # returns precond as a Boolean
    raise NotImplementedError

def postcond(y):
    # returns postcond as a Boolean
    raise NotImplementedError

def f(x):
    # return y
    raise NotImplementedError

def precond_postcond_spec(x):
    if precond(x):
        y = f(x)
        assert postcond(y)

    # If precond(n) never returns True ... then the above never actually
    # runs the postcondition and doesn't make any assertions.

"""
Difference between preconditions and regular assertions -

    Preconditions exclude some inputs from consideration

    Even if the program crashes or misbehaves wildly on
    other inputs, I won't catch it.

Exercise (skip for time)
Rewrite the examples 1-7 using preconditions/postconditions

Even if you have not heard of the word "precondition",
you are probably intuitively familiar with the concept of preconditions
if you have some experience programming and working with libraries...

Examples:
- list pop: https://docs.python.org/3/tutorial/datastructures.html

    "It raises an IndexError if the list is empty or the index is outside the list range."

    This is another way of saying that the precondition of
    list.pop() is that the list should be nonempty.

    Implicit preconditions:
    - input is a list
    - input should be nonempty

    pre/post style spec:

    "for any          inputs that are lists and are nonempty,
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                      precondition
     and run the progam, then the output will satisfy ...."
                                                ^^^^^^^^^^
                                                postcondition

- file open: https://docs.python.org/3/library/functions.html#open

    Has a number of preconditions:
    - The file should be able to be opened (OSError otherwise)

    - "If closefd is False and a file descriptor rather than a filename was given, the underlying file descriptor will be kept open when the file is closed. If a filename is given closefd must be True (the default); otherwise, an error will be raised."

Point:
This is why pre/postconditions are sometimes called "design by contract"

You can often read off preconditions from the documentation!

There are always implicit assumptions in any API that you use.

Point:
Often a precondition that's useful is whatever is needed to not
have the program crash or otherwise misbehave.

In practice, exceptions are often used to enforce preconditions --
if we don't know what to do on a particular input, we crash the program

"Who is responsible" / "blame" viewpoint:

    precondition = the caller is responsible for ensuring this property

    postcondition = the implementer of this function is responsible for
       ensuring this property.
"""

"""
Question:
Are pre and postconditions sufficient?

- Can we now express all properties we are interested in?

    A: probably not

    - Runtime? we could write a test that times the program
      (using time.time or something)
    - What about running the program multiple times?
        e.g.: test that the program is deterministic
            y1 = f(x)
            y2 = f(x)
            assert y1 == y2

      This can't be expressed using a pre/post on f,
      but it CAN be expressed using a pre/post on a function
      calling into f

        def f(x):
            # ...
            return y

        def f_det(x):
            y1 = f(x)
            y2 = f(x)
            return (y1, y2)

    - What about asserting something inside the program?
        Put assertions inside your program
        and assertions before/after running different programs
        so, you don't only have to assert things at the end.
"""

"""
=== Other types of specifications? ===

Recall these examples from before:

4. The program terminates on all inputs.

5. The program does not read any files from the filesystem

and others...

6. The program executes in constant time
7. The input arguments are not modified by the program.

Again... many of these difficult to write using pre/postconditions,

for some of them: it's not even clear that they can be expressed
using executable Python tests.
"""

"""
Other examples?
    (see cut/other-specs.md)

===== Safety and Liveness =====

Two other special cases of specifications that turn out to be particularly useful
(these are not functional correctness):

These have to do with the behavior of the program when run
(properties of the program trace):

- A **safety property** states that "for all x, when f(x) is run,
  some bad event X does not happen."

    "the program doesn't read any files"
    "the program doesn't modify its input x"

- A **liveness property** states that "for all x, when f(x) is run,
  some good event X does happen."

    "f(x) does terminate"

Neither of these can be specified using functional correctness...

    but they *are* examples of specifications (since they
    are true or false properties)
    and they are often useful in practice.

Some systems can be used to verify safety and liveness properties...

    e.g. verification tools for distributed systems, we often
    verify safety and liveness rather than (only) functional
    correctness.

Are the above all possible specifications?
No! We can imagine much more interesting cases...
    (More examples, again, in cut/other-specs.md)

Questions:

Can we test safety properties using the test harness method?

Can we test liveness properties using the test harness method?

=== Conclusions ===

Some main points:

- Any testing or verification system is limited to a particular type of specs that it
  can express or support.

- Different ways of writing specs have different advantages and drawbacks!

- A common approach is to focus on properties about the input/output of a function:

    + functional correctness

    + full functional correctness

    + preconditions/postconditions

- Beyond functional correctness: safety and liveness are two other example classes of specs
  that are often useful.
"""
