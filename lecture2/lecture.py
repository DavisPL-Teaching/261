"""
Lecture 3: Z3 and Satisfiability
ECS 189C
April 15, 2025
"""

####################
###     Poll     ###
####################

"""
Which of the following is a limitation of testing with Hypothesis? (Select all that apply)

1. Testing can only demonstrate the presence of bugs, and can never prove their absence.
2. The specification written could be wrong (not what the user intended)
3. The specification written could be incomplete (underspecified)
4. It can only test preconditions and postconditions
5. It can only test assume and assert statements

Respond here:
https://forms.gle/wRkt67StL7eTmZn29
"""

#######################
###   Intro to Z3   ###
#######################

"""
You might be wondering:
In a verification class, why did we start by talking about Hypothesis?

Answers: I wanted to convince you that
- You're writing specifications all the time! Any time you put an assertion
  your code, or write a test or unit test, or document a precondition,
  you are writing specifications.
- I wanted to highlight the difference between testing and verification.

Limitations of Hypothesis? (See poll above)

Example:
"""

def absolute_value(x):
    # Def of absolute value?
    # (This is what the built-in abs function does)
    if x < 0:
        return -x
    else:
        return x

# In Hypothesis, we could write a specification for the function like this:

from hypothesis import given
import hypothesis.strategies as st
from hypothesis import settings
import pytest

@pytest.mark.skip
@given(st.integers())
# @settings(max_examples = 10_000)
def test_absolute_value(x):
    y = absolute_value(x)
    assert y == x or y == -x
    assert y >= 0
    # ^^ Convince yourself that this is a full functional correctness spec
    # for abs().

# What happens when we test it?

# It passes -- it seems to work for a bunch of random examples.

# What if we want to prove that the function is correct for all inputs?
# We could try increasing the number of test cases...

"""
Let's *prove* that the function is correct for all inputs using Z3.

=== How verification works ===

Insight: Programs can be encoded as logical formulas.
    Encode what used to be a function in Python as a logical formula.

Take abs() as an example above: it was written in Python but it's really just
a mathematical formula:

    output == if x > 0 then x else -x

Once we have written the program this way we can try to prove that

    for all input, output,
        if output = input(prog) and
        precond(input) then
        postcond(output).

    for all x, y:
        if (y == (if x > 0 then x else -x)) and
        True then
        (y == x or y == -x) and (y >= 0).

    for all x, y:
        if
            (
                x > 0 && y == x
                or
                !(x > 0) && y == -x
            )
        then
            (y == x or y == -x) and (y >= 0)
        .

(Recall: A proof is a rigorous mathematical argument that convinces the
reader (or a computer) that the conclusion must be true.)

=== Automated verification ===

What is Z3?

Z3 is an automated theorem prover (from Microsoft Research),
more specifically, it's a satisfiability modulo theories (SMT) solver.

Basically:
- You input a mathematical statement (mathematical formula)
- Z3 tries to prove it --> if so, returns a proof (formula is true)
- Simultaneously, Z3 tries to find a counterexample --> if so, returns a counterexample (formula is false)
- If it can't figure out if it's true or false, it may fail and return "Unknown"
    (more on this later).

It tries to do this fully automatically.

First step: we need to have Z3 installed

(You've done this on HW0 -- pip3 install z3-solver)

And, we need to import it
"""

import z3

"""
I've written a little z3 helper that is useful, also provided on the homework.
It provides z3.prove() and z3.solve().
"""

from helper import prove, solve, SAT, UNSAT, UNKNOWN, PROVED, COUNTEREXAMPLE

"""
Second step: we have to rewrite the function using Z3.

- [Z3 introduction](https://ericpony.github.io/z3py-tutorial/guide-examples.htm)
- [Z3 docs](https://ericpony.github.io/z3py-tutorial/guide-examples.html)
"""

def absolute_value_z3(x):
    # Read this as: if x < 0 then -x else x.
    # Cannot stress enough: this is NOT an executable program
    # It's an abstract if statement.
    return z3.If(x < 0, -x, x)

# Notice this is exactly the same function as before,
# but written in a different way, now with z3.If.

# To see output:
# run with pytest lecture.py -rP
def test_absolute_value_z3():
    # Declare our variables
    x = z3.Int('x')
    y = absolute_value_z3(x)
    # Spec:
    # y is either equal to x or -x, and y is nonnegative
    spec = z3.And(z3.Or(y == x, y == -x), y >= 0)
    # Ask Z3 to prove it:
    # This is our custom helper function
    # You can also just use z3.prove here
    # z3.prove will print stuff out to std output but won't
    # assert anything
    # but I wrote a version that works inside a unit test
    prove(spec)

# What happens if the spec does not hold?

@pytest.mark.skip
# @pytest.mark.xfail
def test_absolute_value_z3_2():
    x = z3.Int('x')
    y = absolute_value_z3(x)
    # This spec is wrong -- it says that abs(x) should
    # always be positive (not just nonnegative)
    spec = z3.And(z3.Or(y == x, y == -x), y > 0)
    # What happens when we try to prove it?
    prove(spec)

# Z3 tells us that it's not true -- and
# shows us a counterexample:
# counterexample
# [x = 0]

"""
What's happening here?

Z3 is interpreting the spec as a mathematical statement,
and trying to come up with either a proof that it's always true
or a counterexample.

"Mathematical statement" = statement is some logic.

In order to understand how Z3 works, we need to understand
logical formulas and satisfiability.
"""

##########################
###   Satisfiability   ###
##########################

"""
A *formula* is a logical or mathematical statement that is either true or false.
Formulas are the main subject of study in logic and they are also
the core objects that Z3 works with.
Examples:

    - "x > 100 and y < 100"
    - "x * x == 2"
    - "x is an integer"

Formulas can have variables (x and y above)

An *assignment* to the variables is a mapping from each variable to a value.

    Ex.: assigment: x ↦ 2, y ↦ 3
    Under this assignment the formulas above evaluate to:
    - "2 > 100 and 3 < 100"
    - "2 * 2 == 2"
    - "2 is an integer"

A formula is *satisfiable* if it is true for *at least one* assignment.

    i.e. an existential quantification:
    phi = spec

    "There exists an assignment v such that phi(v) is true".
                                            ^ not executable program,
                                            mathematical statement

Examples:

    - first one:
        true, for example, for x = 101 and y = 5
        =====> Satisfiable

    - second one:
        true for x = sqrt(2) (in the real numbers)
        never true in the integers
        =====> Satisfiable in real numbers
        =====> Unsatisfiable in integers

    - third one: true for any integer x, e.g. x = 5
        =====> Satisfiable in real numbers
        =====> Satisfiable in integers

Key point: Satisfiable == True for at least one input.

The satisfiability problem:

    INPUT: a mathematical formula φ

    OUTPUT: True if φ is satisfiable, false otherwise.

Question:

    -> Is satisfiability decidable?
    -> If so, what is the complexity?

It depends on the grammar of allowed formulas.

    What syntax do we allow for formulas?

Boolean logic:

    Infinite family of Boolean variables

        Var ::= b1, b2, b3, b4, ...

    Formula

        Formula φ ::= φ v φ  |  φ ^ φ  |  !φ  |  Var

            (add if you like -- expressible using above)
            | φ <-> φ
            | φ  -> φ
            | True
            | False
            | φ ⊕ φ (xor)

    Example:

        (b1 ^ !b2) v (b3 ^ !b1) v True

Is the satisfiability problem decidable?

    Idea:
    We can try brute forcing all variables!
    Only a finite number of vars occur in our formula -- let's n variables
    Try all 2^n variable assignments.
    (assignment = maps each var to True or False)
    Evaluate the formula

    Pseudocode:
    Enumerate n vars b1, b2, ..., b_n
    For all assignments v: Var -> Bool:
        evaluate φ(v)
        if φ(v) = true, return SAT
    Else (for loop terminates without finding a satisfying assignment):
        return UNSAT.

    Complexity: exponential.

    2^n (exponential in the length of the input formula).

(Review from ECS 120)
Because the input grammar is a Boolean formula, this is
called the Boolean satisfiability problem (or SAT or 3SAT for the 3-CNF version.)

What happens if we don't just have Booleans?

    Z3 = Satisfiability "Modulo Theories"
    This is the "Modulo Theories" part.

What's a mathematical theory?
We can do examples of data types like... integers, reals, lists, sets, ...

We want to replace our Boolean variables with constraints over the data type
we're interested in.

Theory of integers:

    Infinite family of Boolean variables

        IntVar ::= n1, n2, n3, ...

    Integer expressions
    (let's not include division)
    (other interesting operations -- % (modulo), ^ (exponentiation), ! (factorial))

        IntExpr ::=
            IntExpr + IntExpr
            | IntExpr - IntExpr
            | IntExpr * IntExpr
            | IntVar
            | 0
            | 1

    Formula
    We can compare two integers! (A relation)

        Formula φ ::= φ v φ  |  φ ^ φ  |  !φ
            | IntExpr == IntExpr
            | IntExpr < IntExpr

            (add if you like -- expressible using above)
            | φ <-> φ
            | φ  -> φ (if then)
            | True
            | False
            | φ ⊕ φ (xor)
            | IntExpr <= IntExpr
            | IntExpr >= IntExpr
            | IntExpr > IntExpr

    Example:

        (x > 0 ^ y > x) -> y > 0

        (x == y1 + y2 + y3 + y4)
            ^ (y1 == z1 * z1)
            ^ (y2 == z2 * z2)
            ^ (y3 == z3 * z3)
            ^ (y4 == z4 * z4)

            "x is expressible as the sum of four square numbers"

Question:
    Is the satisfiability problem for integers decidable?

    (Q: Is this just integer programming?)
    Claim: yes - can we just brute force and go through all the values and
        check whether it is true or not?
        That would work if the integers are in a bounded range.
        But what if the integers are unbounded integers
            (e.g., Python integers, not C integers)


    Famous open problem posed by Hilbert in 1900
    "Hilbert's 10th problem"
    Turned out to be undecidable, proof due to Julia Robinson and others.

--------------------

Recap:
we talked about the methodology of automated verification
- rewrite the program using mathematical formulas
- try an automated theorem prover (Z3) to check if the formula is true or not

we talked about satisfiability
- input a formula, determine if ∃ a assignment to the variables that renders the
  formula true
- decidable for Booleans (NP complete), undecidable already even for the simplest
    infinite datatype, integers.

where we are going next:
- what does satisfiability  have to do with provability?
- other theories (other than Booleans and integers)

***** where we ended for today *****

=== April 17 ===
.............................................

Recall:
- Boolean satisfiability problem: on input a Boolean formula, determine SAT or UNSAT
    + NP-complete
    + Strong Exponential-Time Hypothesis: Likely impossible to solve in less than exponential time
- Integer satisfiability problem: on input a formula involving integer arithmetic expressions (*, +, -), determine SAT or UNSAT (see grammar above)
    + Undecidable
    + Also NP-hard (why?)

Also:
- A formula is **valid** if...

Let's do a few examples in Z3.

Example from before:

    (b1 ^ !b2) v (b3 ^ !b1) v True

Syntax reference:

- z3.Bool("b1")
- z3.Bools("b1 b2 b3")
- z3.And(exprs or list of exprs)
- z3.Or(exprs or list of exprs)
- z3.Not(expr)
- z3.Implies(expr1, expr2)

Is it satisfiable?
- solve from helper
- z3.solve

Is it valid?
- prove from helper
- z3.prove
  (why prove? more on this soon)
"""

# TODO

"""
Common questions/notes:

- Why does the variable have to be named?
I.e., why did I write
    a = z3.Bool('a')
instead of just z = z3.Bool() ?

A: this is just how z3 works -- it uses the name, NOT the Python variable name,
to determine the identify of a variable.

x = z3.Bool('a')
y = z3.Bool('a')
^^ These are actually the same variable, in Z3

x = z3.Bool('y')
^^ the variable name here, in Z3, is 'y', not x.

(let's demonstrate this)
"""

"""

- What is the type of a and b?

A: It's a z3.Bool type, (not the same as a Python boolean)

Recall: Z3 manipulates formulas (a model of the program), not actual Python types (the program itself)

    + Python bool can be coerced to Z3.Bool
    + not the other way around
    + take special note of how equality works for Z3 datatypes

"""

"""
Integers

Similar to our grammar above, we have

- z3.Int("n")
- z3.Ints("n1 n2 n3")
- >, +, *, -, / work directly on integers

Our examples from before:

(x > 0 ^ y > x) -> y > 0

        (x == y1 + y2 + y3 + y4)
            ^ (y1 == z1 * z1)
            ^ (y2 == z2 * z2)
            ^ (y3 == z3 * z3)
            ^ (y4 == z4 * z4)
"""

"""
How does divide / work?
"""

####################
###     Poll     ###
####################

"""
Recall: prove function returns one of three results:
- proved (demonstrate that it's true for all inputs)
- failed to prove (this basically means "I don't know")
- counterexample (shows an input where the spec is not true)

What would you guess is the output of the following Z3 code?
"""

@pytest.mark.skip
def test_poll_output_1():
    x = z3.Int('x')
    y = z3.Int('y')
    spec = z3.And(x > 100, y < 100)
    prove(spec)

"""
A) "proved"
B) "failed to prove"
C) "counterexample" with no other text
D) "counterexample" together with an example of x and y

(Try running it)
"""

# print("Output:")
# test_poll_output_1()

"""
Basic data types: Bool, Int, Real

=== Real numbers ===

Grammar for reals:


Satisfiability problem?

=== Combining multiple theories ===

So far we have Booleans, Integers, and Reals.

(In fact we don't really need booleans -- we can represent them as integers.)

    ASIDE:
    How to define a boolean using integers
    b = z3.Int('b')
    boolean_spec = z3.And(b >= 0, b <= 1)
    z3.solve(boolean_spec)
    If you wanted to do boolean operations,
    and, or, implies, etc. you could define these on integers.

    Take-away point here: if you have a less restrictive data
    type than you want, you can add additional invariants
    into your formula to encode whatever additional properties you
    want.
    Here: we wanted b to be between 0 and 1, so we simply added
    0 <= b and b <= 1 into our spec.

But we really then just have "Satisfiability Modulo Theory"

What about combining multiple theories?

"""

"""
====== Some end notes ======

=== Complex data types ===

The power of Z3 is in its ability to work with more complex data types
(not just booleans).

Other types: lists, bitvectors, strings, floating point, etc.

=== Applications of Z3 ===

Z3 is not just useful for proving properties of "mathematical" functions.

- Recall slide from first lecture: all programs are secretly just
  math and logic

- Compilers also work with a model of the program!
    That is how they are able to optimize code prior to running it.

- Many applications to real-world software, like cloud services,
    distributed systems, compilers, system implementations, etc.
    (for example, teams at Amazon have spent millions of dollars on formal methods)

The key to applying Z3 in the real world is to define the right
mathematical domain to map your programs to.

=== Differences from Hypothesis? ===

1. Random test case vs. proof

Hypothesis just runs random examples, Z3 thinks about the program
mathematically and tries to analyze "all" examples.

2. We had to rewrite the function using Z3!

For absolute_value, it was just a standard Python function
For Z3, we had to rewrite it as absolute_value_z3, using Z3 abstractions.

- Other differences? (We will see later)

==> we are testing a *model* of the program, not the program itself!

Why are we testing a model?
Well, Z3 thinks about things formally and mathematically.
So it needs a description of the program that is fully mathematical.
- In principle, any program can be translated to the right model.
- In principle, this is often possible to do automatically.

Example: we have z3.If, so if your program has if statements,
we can encode it in Z3.
But the developers of Z3 may not have written equivalents for every
Python funciton. (Ex.: files, print(), ...)
And in those cases, you would need to write your own model.

Using a model is both a strength and a weakness.
"""
