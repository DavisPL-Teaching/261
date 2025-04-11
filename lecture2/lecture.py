"""
Lecture 3: Z3 and Satisfiability
ECS 189C
April 15, 2024
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
"""

#######################
###   Intro to Z3   ###
#######################

"""
Recap:
- We've learned about writing specifications
    + Ways to write specifications: precondtions, postconditions, assume, assert
- Hypothesis uses random testing (also known as property-based testing) to generate test cases
- Hypothesis is limited to finding bugs; it can't prove the specification holds for all inputs.

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
import pytest

@pytest.mark.skip
@given(st.integers())
def test_absolute_value(x):
    y = absolute_value(x)
    assert y == x or y == -x
    assert y >= 0

# What happens when we test it?

# It passes -- it seems to work for a bunch of random examples.

# What if we want to prove that the function is correct for all inputs?
# We could try increasing the number of test cases...

"""
=== Programs are logical formulas ===

Let's *prove* that the function is correct for all inputs using Z3.

Recall:
A proof is a rigorous mathematical argument that convinces the
reader (or a computer) that the conclusion must be true.

What is Z3?

Z3 is an automated theorem prover (from Microsoft Research),
more specifically, it's a satisfiability modulo thoeries (SMT) solver.

Basically:
- You input a mathematical statement (mathematical formula)
- If it's true, Z3 tries to prove it.
- If it's false, Z3 tries to find a counterexample.

It tries to do this fully automatically. (Not always successfully, as we will later see.)

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
    return z3.If(x < 0, -x, x)

# Notice this is exactly the same function as before,
# but written in a different way, now with z3.If.

# To see output:
# run with pytest lecture.py -rP
@pytest.mark.skip
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

Let's talk about logic & satisfiability.
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
    - "x * x = 2"
    - "x is an integer"

Essence of satisfiability:

A formula is *satisfiable* if it is true for *at least one* input.

Examples:

    - first one: true, for example, for x = 101 and y = 5
        =====> Satisfiable
    - second one: true for x = sqrt(2) (in the real numbers)
        never true in the integers
        =====> Satisfiable in real numbers, not satisfiable in integers
    - third one: true for any integer x, e.g. x = 5
        =====> Satisfiable both in real numbers or in integers
    - fourth one: satisfiable because we can take "Socrates" to be the actual
        Socrates and we can take "mortal" and "human" to be the usual meanings
        of those words, and then the statement is a true statement about
        Socrates, humans, and being mortal
        ^^ We're not going to encode this in Z3, but we could if we really wanted
        =====> Satisfiable because it's true for **some** examples of the terms
            or variables involved, i.e. true for some inputs.

Key point: Satisfiable == True for at least one input.

Side note:
If you've taken ECS 120, you may have seen the Boolean satisfiability problem,
or SAT or 3SAT, and this is an example of what I'm calling Satisfiability.

Let's start with boolean variables. Using Z3:

To make a Boolean variable, we use:
- z3.Bool
- z3.Bools
"""

a = z3.Bool('a')
b = z3.Bool('b')

# This defines two boolean variables, a and b.
# We'll see what the 'a' and 'b' mean in a moment

"""
Creating a formula

We can take our boolean variables and combine them
"""

form1 = z3.And(a, b)
form2 = z3.Or(a, b)
form3 = z3.Not(a)
form4 = z3.And(z3.Or(a, b), z3.Or(a, z3.Not(b)))

# We could run z3.prove() on these formulas or a new function called
# z3.solve() -- we will do this in a moment

"""
Questions:

- Why does the variable have to be named?
I.e., why did I write
    a = z3.Bool('a')
instead of just z = z3.Bool() ?

A: this is just how z3 works -- it uses the name, NOT the Python variable name,
to determine the identify of a variable.

x = z3.Bool('a')
y = z3.Bool('a')
# ^^ These are actually the same variable, in Z3

x = z3.Bool('y')
# ^^ the variable name here, in Z3, is 'y', not x.

- What is the type of a and b?

It's a z3.Bool type, (not the same as a Python boolean)

- Why aren't a and b just normal booleans?

This goes to the thing about Z3 working with a model of the program.
Z3 needs to know what are the symbols in a formula and what do they mean,
NOT just the true-or-false output.

a = True
b = False
a and b ====> False
But Z3 wouldn't be able to see what the formula is and what it means.

Z3 needs a formula object, not just a Python boolean.

- Why do we need to ues z3.And and z3.Or instead of just "and" and "or"?

Same reason: Z3 needs a formula in the end, not just the final result.
"""

"""
Checking satisfiability

We can use the z3.solve() function to check if a formula is satisfiable.
This is what all of Z3 is based on!

There are three possible outcomes:
- z3.sat =====> Yes the formula is satisfiable
- z3.unsat =====> No the formula is not satisfiable
- z3.unknown =====> I don't know

Note: If this seems similar to the "prove" function from earlier, it should!
We will discuss how prove is implemented shortly.

Recall:
form1 = z3.And(a, b)
form2 = z3.Or(a, b)
form3 = z3.Not(a)
form4 = z3.And(z3.Or(a, b), z3.Or(a, z3.Not(b)))
"""

z3.solve(form1)
z3.solve(form2)
z3.solve(form3)
z3.solve(form4)
# =====> Satisfiable, Z3 gives an example

# For all four examples, the formula is satisfiable -- Z3 returns an example
# where the formula is true.
# What about something that's NOT satisfiable?

form5 = z3.And(a, z3.Not(a))
# A and Not A --> always false, should be never true, i.e. not satisfiable

z3.solve(form5)
# =====> Unsatisfiable, Z3 says "no solution"

########################
###     Validity     ###
########################

"""
A formula is **valid** if...
"""


"""
=== Applications of Z3 ===

Z3 is not just useful for proving properties of "mathematical" functions.

- In fact, programs in any language are just mathematical functions!

- Compilers also work with a model of the program!
    That is how they are able to optimize code prior to running it.

- Many applications to real-world software, like cloud services,
    distributed systems, compilers, system implementations, etc.

The key to applying Z3 in the real world is to define the right
mathematical domain to map your programs to.
"""

####################
###     Poll     ###
####################

"""
The z3.prove function (or our custom prove function)
returns one of three results:
- proved (demonstrate that it's true for all inputs)
- failed to prove (this basically means "I don't know")
- counterexample (shows an input where the spec is not true)

What would you guess is the output of the following Z3 code?
"""

@pytest.mark.skip
# @pytest.mark.xfail
def test_poll_output():
    x = z3.Int('x')
    y = z3.Int('y')
    spec = z3.And(x > 100, y < 100)
    prove(spec)

"""
A) "proved"
B) "failed to prove"
C) "counterexample" with no other text
D) "counterexample" together with an example of x and y

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

(Try running it)

Key point: "proved" means it must be true for all inputs.
"""

"""
Two functions of Z3:
z3.prove --> ask if something can be proven
z3.solve --> ask if something is satisfiable

Actually, how does z3.prove work?
If I run z3.prove(formula)
it calls
z3.solve(z3.Not(formula))
- If satisfiable: that means there is an input where "NOT formula" is true
    Therefore, "formula" must be false (on that input)
    Therefore, "formula" is not necessarily true for all inputs, i.e. it's not
    provable -- there is a counterexample.
- If unsatisfiable: that means there are no inputs where "NOT formula" is true
    Therefore, "NOT formula" is false for all inputs
    Therefore, "formula" is true for all inputs
    Therefore, formula is provable.
- If unknown: we return unknown.

In essence: provability and satisfiability are reducible to each other
Specifically: provability of "P" and satisfiability of "Not P" are solving
the same problem.

When does z3.solve (or z3.prove) return unknown?
Intuitively, if the formula is really mathematically complex, involves a lot
of difficult operations and it's too hard to figure out whether it's satisfiable
or not.
--> Booleans are quite easy, so this will rarely happen with booleans.

What boolean operations can we use?

- z3.And
- z3.Or
- z3.Not
- z3.Implies
- z3.If
- z3.Xor

These are all standard functions on boolean numbers, but instead of evaluating
the operation, they create a formula.

The reason they have to create a formula is because Z3 wants to determine
if the formula is true for ANY input (satisfiability) or for ALL inputs (provability)
not necessarily just evaluate it on a single input.

Examples:

"""

print("More examples:")
x = z3.Bool('x')
y = z3.Bool('y')
# What does implies do?
z3.solve(z3.Implies(x, y))
# Implies is basically the "if then" function and it has the following meaning:
# if x is true then y, otherwise true.
# arrow (-->)
# If you like you can write z3.If(x, y, True) instead of z3.Implies(...)
# It's reducible to if then.

# XOR implies or?
# XOR is exclusive or (exactly one, but not both of x and y are true)
x_xor_y = z3.Xor(x, y)
x_or_y = z3.Or(x, y)
z3.prove(z3.Implies(x_xor_y, x_or_y))

"""
Convenient shortcuts:

- Equality (==)
- z3.And([...])
- z3.Or([...])

You can directly write x == y
for booleans, and Z3 knows what that means
You can also write
z3.And([formula1, formula2, formula3, ...])
for a list of formulas and it will create an "and" expression of all of them.
Similarly for Or.

These are just shortcuts, and can be implemented using the above operations already.
"""

"""
=== Recap ===

We know what a formula is.
- Mathematical statement that can be true or false

Satisfiability is the property of a formula being true for at least one input.
Provability is the property of a formula being true for all inputs

Z3 can try to automatically resolve satisfiability by running
z3.solve
or provability by running
z3.prove

A last question:
How does this help us prove specifications?

Remember that for a program my_prog, we defined preconditions and postconditions,
and the "spec" was the property that if the precondition holds, then the postcondition
must hold.

Roughly speaking, we can translate this to a Z3 spec by writing

x = Input(..)
y = my_prog(x)
Then we can write the formula:
    z3.Implies(precondition(x), postcondition(y))

If Z3 is able to prove this, then the spec holds -- the property is true for all inputs.
"""

########## Where we left off for Day 7 ##########

"""
Day 8

Announcements:
- HW1 due today

- For those added from the waitlist during weeks 2-3:
you can submit it by EOD Tuesday.
Please put a note at the top of the README with the
date you were added to the waitlist.
I will also announce this on Piazza

- If you're having trouble with Git, please see
[Git instructions](https://piazza.com/class/lt90i40zrot3ue/post/48)

- My office hours: today 330-430 in ASB

Questions about HW1?

Plan for today:
- Recap on provable vs. satisfiable
- Poll
- Additional data types
- Some tricks along the way

(Time permitting)
- Programming exercises

Recall:
- z3.prove
- z3.solve

z3.prove tries to figure out if the formula (or spec)
is true for ALL inputs.

z3.solve tries to figure out if the formula (or spec)
is true for SOME input.

What is an "input" here?
That's where this notion of variables comes up in Z3.
b = z3.Bool('b') <---- this is a variable, i.e. an input
x = z3.Int('x') <---- this is a variable, i.e. an input

In other words: z3.prove tries to show that the spec holds for all
values of the variables, while z3.solve tries to show that the
spec holds for one particular assignment of values to the variables.

Finally, we also saw that these are really the same thing under the
hood. In fact they use something called a Solver API
Under the hood:
z3.Solver
which you can create to solve arbitrary formulas.
We'll see this towards the end of today's lecture.

Q: x = z3.Int('x')
Does x have to match the string?
A: No. Z3 will use the string to determine the variable.
y = z3.Int('x') # This is also the same variable as x

When should you use z3.prove vs z3.solve?

- z3.prove is useful for proving specifications, and also when
    you want to show that some assertion or some property always holds

- z3.solve is useful for solving equations, solving puzzles, and
    similar tasks where you have some set of constraints, and
    you want to find a solution to those constraints.
    E.g.: you want to solve x^2 - 3x + 2 = 0
    or you want to solve a Sudoku puzzle

"""

####################
###     Poll     ###
####################

# What would you guess is the output of the following Z3 code?

@pytest.mark.skip
def test_poll_output_2():
    x = z3.Int('x')
    y = z3.Int('y')
    spec = z3.Implies(z3.And(x >= 10, y == x * x), y >= 100)
    prove(spec)

# print("Output:")
# test_poll_output_2()

# Let's try it out

########################
###    Data Types    ###
########################

"""
The power of Z3 is in its ability to work with more complex data types
(not just booleans).

Basic data types: Bool, Int, Real

(In fact we don't really need booleans -- we can represent them as integers.)
"""

# How to define a boolean using integers
b = z3.Int('b')
boolean_spec = z3.And(b >= 0, b <= 1)
z3.solve(boolean_spec)
# If you wanted to do boolean operations,
# and, or, implies, etc. you could define these on integers.

# Take-away point here: if you have a less restrictive data
# type than you want, you can add additional invariants
# into your formula to encode whatever additional properties you
# want.
# Here: we wanted b to be between 0 and 1, so we simply added
# 0 <= b and b <= 1 into our spec.

"""
=== Integers ===

z3.Int
z3.Ints -- creates multiple integers

Examples
"""
x, y = z3.Ints("x y")
spec = z3.And(x > y, y > 5)
z3.solve(spec)

"""
What operations are supported here?
You can use most built-in integer operations in Python
on Z3 integers. BUT keep in mind it's not the same as Python
integer arithmetic.
"""

x + y # <- Z3 expression, NOT a Python integer
print(x + y) # Prints as "x + y", not as some specific integer

# Problem: find two integers whose sum and product is the same.
print("Find two integers whose sum and product is equal:")
z3.solve(x + y == x * y)

# Operations we've seen so far: +, *, ==, <, all of these
# work on Z3 integers.

"""
We can use functions to wrap up useful functionality.

For example:
Define a Pythagorean triple as three positive integers a, b, c
such that a^2 + b^2 = c^2.

Q1: Find a pythagorean triple.
Q2: Find a pythagorean triple with a = 5.

It's often useful to define a function which abstracts the
behavior you're interested in.
"""

def pythagorean_triple(a, b, c):
    # We can just return the expression a^2 + b^2 = c^2
    # return (a * a + b * b == c * c)
    # Debugging: we can add the additional constraints
    # that we forgot here
    pythag_constraint = a * a + b * b == c * c
    a_is_positive = a > 0
    b_is_postive = b > 0
    c_is_positive = c > 0
    return z3.And([
        pythag_constraint,
        a_is_positive,
        b_is_postive,
        c_is_positive,
    ])
    # Here: the other constraints are silently ignored :(
    # What's happening here?
    # Python boolean operators (and/or) are defined for arbitrary
    # data types. And "falsey" datatypes are treated as false
    # and "truthy" datatypes are treated as true
    # and/or are both short circuiting so they'll return
    # the first value that is either false/true, respectively.
    # Bottom line here: this doesn't work because "and" already
    # has a definition in Python.
    # This is not what we want.
    # return (pythag_constraint and a_is_positive and b_is_postive and c_is_positive)
    # TL;DR Python boolean operators are weird, so be careful with them.

# If we want an example:
a, b, c = z3.Ints("a b c")
print("Example pythagorean triple:")
z3.solve(pythagorean_triple(a, b, c))

"""
Q: what if we want more than one answer?

We can try rerunning...

The easiest way is a common technique where
each time we get an answer, we add an assertion that
that answer is excluded.
"""

# First answer: a = 6, b = 8, c = 10
# Second answer
new_constraint = z3.Or(
    z3.Not(a == 6),
    z3.Not(b == 8),
    z3.Not(c == 10),
)
# ^ Force the solver to give us a new answer.
z3.solve(z3.And([
    pythagorean_triple(a, b, c),
    new_constraint,
]))

# We can keep adding constraints for each new answer,
# there is also a way to do this programmatically
# (This will use the Solver API that we will shortly see.)
# We will see how to write a wrapper around Solver to do this.

"""
SKIP
Q: Write a function to determine whether a number
is a perfect square.
"""

"""
Q: write a function to solve the formula
x^2 + 5x + 6 = 0
"""

x = z3.Int('x')
print("Solution:")
z3.solve(x * x + 5 * x + 6 == 0)
# If we want the other answer?
y = z3.Int('y')
z3.solve(z3.And([
    x * x + 5 * x + 6 == 0,
    y * y + 5 * y + 6 == 0,
    x != y,
]))

"""
=== True Real Numbers ===

We've seen so far how Z3 can work with standard Python datatypes.

Because Z3 is a theorem prover, and not just a testing framework,
it can also work with data types that are not available in Python:
for example, real numbers.

In Python, there's no such thing as a "true" real number,
there are only floating point values (floats)
But in Z3 there is.

z3.Real
z3.Reals
"""

x = z3.Real('x')
# what happens?
print("Square root of two:")
z3.solve(x * x == 2)

# Note: there is no floating point value x with x^2 = 2
# It only exists as a true real number.

# How does Z3 represent real numbers, when computers can't
# represent real numbers?

# Answer: they're treated as abstract symbols, not as concrete
# values.
# In fact, everything in Z3 is treated as abstract symbols!
# z3.If, z3.Int, z3.Or, the reason there's a Z3 version is that
# it treats it as an abstract formula, not a concrete value.
# Just like when I write x = sqrt(2) on the board, I'm not actually
# computing the exact value of x, that's the same thing that Z3
# does.

"""
More advanced data types:
(later)
- Functions
- Arrays and sequences
- Strings and regular expressions
"""

"""
Other tips

Useful guide:
[Z3 py guide](https://ericpony.github.io/z3py-tutorial/guide-examples.htm)

Documentation:
[Z3 py docs](https://z3prover.github.io/api/html/namespacez3py.html)

The Z3 solver API

(see helper_functions.py)
"""

"""
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
