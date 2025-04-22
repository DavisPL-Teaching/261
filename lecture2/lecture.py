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

Recall:
- Boolean satisfiability problem: on input a Boolean formula, determine SAT or UNSAT
    + Decidable
- Integer satisfiability problem: on input a formula involving integer arithmetic expressions (*, +, -), determine SAT or UNSAT (see grammar above)
    + Undecidable

Boolean Satisfiability is NP-complete
    + Strong Exponential-Time Hypothesis (SETH):
      Likely impossible to solve in less than exponential time in the worst case.

Integer satisfiability is also NP-hard
    + Reduce from Boolean sat
        * idea: can we think of positive integers true and negative as being false?

    + Q I am asking: how do we encode Boolean formulas as integer formulas?

        Idea: use the integer variables, and use comparison to compare to zero

        divide by the absolute value of integer?

        most common:
            True = 1
            False = 0

        Encode each boolean variable b as an integer variable that is between
        0 and 1

        add constraints that:
        (0 <= n1 <= 1) for all variables n1, n2, ...

        if I want to say a boolean variable is true I say
            n1 == 1
        and if I want to say it's false I say that
            n1 == 0

        Example:

            (b1 ^ !b2) v (b3 ^ !b1) v True

        Encoding returns:
            (n1 >= 0) and (n1 <= 1) and
            (n2 >= 0) and (n2 <= 1) and
            (n3 >= 0) and (n3 <= 1) and
            ((n1 == 1) and (n2 == 0))
                or (n3 == 1) and (n1 == 0)

        Would also work:
            ((n1 != 0) and (n2 == 0))
                or (n3 != 0) and (n1 == 0)

Point being:
    Integer satisfiability is also NP-hard (probably exp time)

Recall:
    φ is satisfiable if there exists an assignment to the variables
        v: Var -> Bool
        (or v: Var -> Integer)
    such that the formula φ(v) evaluates to true.
    "sometimes true"

Also:
- A formula φ is **valid** if for all assignments to the variables
        v: Var -> Bool
        (or v: Var -> Integer)
    the formula φ(v) evaluates to true.
    "always true"

Validity can be solved by reducing to satisfiability as follows:

    If I want to know if φ is valid, check if !φ is satisfiable.
"""

####################
###     Poll     ###
####################

"""
Is the following formula satisfiable, valid, neither, or both?

    (x > 100 and y <= 100)
    or
    (x <= 100 and y > 100)

True/False:
    All satisfiable formulas are valid
    All valid formulas are satisfiable
    All unsatisfiable formulas are valid
    All valid formulas are unsatisfiable

https://forms.gle/jPD3oRpGci3E4ikp9

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
"""

# In Z3:

@pytest.mark.skip
def test_poll_output_1():
    x = z3.Int('x')
    y = z3.Int('y')
    spec = z3.Or(
        z3.And(x > 100, y <= 100),
        z3.And(x <= 100, y > 100),
    )
    print("Is the formula satisfiable?")
    solve(spec)
    print("Is the formula valid?")
    prove(spec)

# Uncomment to run
# test_poll_output_1()

"""
Other examples in Z3:

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

Possible outputs of z3.solve:
    "unsatisfiable"
    "satisfiable" with a specific example (called a model)
    "unknown" -- unable to resolve

Possible outputs of z3.prove
    "proved"
    "counterexample" with a counterexample
    "failed to prove"
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

(Exercise - skip)

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

# x = z3.Int("x")
# y = z3.Int("y")
# z = z3.Int("z")

# Is the following satisfiable: x / y == z?
# spec = (x / y == z)
# solve(spec)

# Probably beter:
# spec = z3.And(x / y == z, y != 0)
# solve(spec)

# Instructive example:
# spec = z3.And(x / y == z, y == 0, x == 1, z == 3)
# solve(spec)

# What's going on: shows the power of satisfiability as a concept
# Z3 has a variable div0
# def of division: x / y == (standard result) if y is not zero, else div0
# Add a new variable to denote the undefined case.

# Is Z3 using integer division?
# spec = z3.And(x / y == z, y == 2, x == 3)
# spec = z3.And(x / y == z, y == 2, x == 3, z != 1)
# solve(spec1)
# solve(spec2)

"""
Basic data types: Bool, Int, Real

Before we continue...
let's reflect on where we're at here.

- The methodology of automated verification was that we wanted to
  encode our program and our spec as formulas, and then prove them by
  searching for a proof automatically (i.e., checking validity)

  Things look really grim at this point!
  We saw that SAT is already NP-hard
  We saw that even with the most simple data type, the problem is already
  impossible!
  AND we are only considering really simple formulas!
        -> we haven't included quantifiers: forall and there exists
        -> In order to encode all of mathematics and computer science
            (and many properties of real programs), we need quantifiers.

  But there is hope!
  1. Properties that come up in practice - in the real world - are often
     simple formulas, not complex formulas
  2. We don't need to solve the problem in the worst case, only in the
     case of real-world constraints
  3. (Foreshadowing to later) It turns out that people typically only write
     programs that they know are correct.

Z3 and other SMT solvers are built to solve practical constraints, and for
many practical applications they "just work" and come up with the right answer.

Programming exercises:
    In problems/problems.md
    We did the N queens puzzle (n-queens.py) in class.
    There is also a Sudoku solver (sudoku.py) and a task scheduler (task-scheduler.py)
    and a few other exercises to try out.

***** where we left off for today *****

=== April 22 ===

We have seen that even though satisfiability is hard or undecdidable in general,
Z3 can solve many practical problems.
- n-queens.py
- other examples in problems/ (sudoku.py, task-scheduler.py)

[N queens solution demonstration
How large can we take N up to before Z3 fails?]

Key points:
- We don't have to be good in the worst case - we can just be good on "average" cases!
- We don't have to be good for "sufficiently large" inputs - solving on small inputs is both useful and interesting!

How does Z3 do this? Important algorithms: DPLL, DPLL(T), CDCL, Nelson-Oppen.

- Still, some of you noticed that this fails sometimes. (More on this later)

First:
A tour of some of the remaining theories that Z3 supports
that you will most often encounter / will be most useful
(and corresponding Z3 syntax).

=== Real numbers ===

Grammar for reals:

Let's modify our grammar for integers below:

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

    Example?

        (x > 0 ^ y > x) -> y > 0

        (x == y1 + y2 + y3 + y4)
            ^ (y1 == z1 * z1)
            ^ (y2 == z2 * z2)
            ^ (y3 == z3 * z3)
            ^ (y4 == z4 * z4)

            "x is expressible as the sum of four square numbers"

POLL:

You can guess on these if you don't know!

Q: Is satisfiability for reals decidable?
Q: Is satisfiability for reals NP-hard?

https://forms.gle/WBbgUvvYuGEdPmgB9

=== More interesting data types ===

Besides reals, the most interesting and commonly useful datatype in practice
is strings.

What are string constraints?
This starts to look quite different:

        StringVar ::= n1, n2, n3, ...

    String expressions
    What do strings support?

        StrExpr ::= ...

    Formula
    Let's start with our previous grammar
    Do we want to add any other relations?

        Formula φ ::= φ v φ  |  φ ^ φ  |  !φ
            | StrExpr == StrExpr

            (add if you like -- expressible using above)
            | φ <-> φ
            | φ  -> φ (if then)
            | True
            | False
            | φ ⊕ φ (xor)

    Example:

Once again going back to our question:

Q: Is satisfiability for strings decidable?
Q: Is satisfiability for strings NP-hard?

Z3 syntax:

- z3.String(varname)
- + for concatenation
- z3.InRe(str, regex) for regular membership
    --> see extras/regex_help.md for regular expression help
- z3.IntToStr

=== Some words on applications ===

What are strings useful for?

String data is a HUGE source of security vulnerabilities.
Top 5 web application vulnerabilities:
- Cross-site scripting (XSS):
  https://owasp.org/www-community/attacks/xss/
- Injection attacks:
  https://owasp.org/www-community/Injection_Flaws

String length issues are also a common problem:
- Heartbleed: https://xkcd.com/1354/

=== XSS attack example ===

What is an XSS attack?
Basically, an XSS attack is where we insert a malicious script
to be executed on a page which was not intended to execute the
script.

A minimized model of XSS attacks:
"""

query = z3.String("query")
query_html = (
    z3.StringVal("<title>Search results for:") + query + z3.StringVal("</title>")
)

start = z3.String("start")
malicious_query = z3.StringVal("<script>alert('Evil XSS Script')</script>")
end = z3.String("end")

# Make a variable for the entire contents of the HTML page.
html = z3.String("html")

xss_attack = z3.And(
    html == query_html,
    html == start + malicious_query + end
)

# Uncomment to run
# z3.solve(xss_attack)

"""
Match a US phone number example:
"""

phone_number = z3.String("phone_number")
number = z3.Range("0","9")
hyphen = z3.Re("-")

length_constraint = z3.Length(phone_number) >= 12

# Start to concatenate them!
# Note: 2 ways to do this, concat regexes, or concat strings
# Leads to different encodings
regex_constraint = z3.Concat(
  number,
  number,
  number,
  hyphen,
  number,
  number,
  number,
  hyphen,
  number,
  number,
  number,
  number,
)

# Uncomment to run
# z3.solve(z3.InRe(phone_number, regex_constraint))

"""
=== Combining multiple theories ===

So far we have Booleans, Integers, and Reals.

(In fact we don't really need booleans -- we can represent them as integers.)

But we really then just have "Satisfiability Modulo Theory"

What about combining multiple theories?

It is easy to combine all the theories in a "trivial" way. How?

Combining them in more interesting ways?

=== Quantifiers ===

Finally the last part of Z3 syntax is the most insidious and the most
powerful - quantifiers.

- z3.ForAll(var_or_list_of_vars, formula)

- z3.Exists(var_or_list_of_vars, formula)

The following example also uses the Z3 theory of arrays
(very commonly combined with quantifiers)

Underlying theory: theory of finite collections
(basically, finite set theory)
"""

# Try to prove that if the sum of an array is positive, then an array has
# an element that is positive.

# Define the array variable
I = z3.IntSort()
array = z3.Array('array', I, I)

# First we have to express the sum of the array.
# How do we do that?
array_sum = z3.Function('array_sum', I, I)
# The value array_sum(i) will represent the sum of the values
# of the array up to index i.
constraints = []

# Base case
constraints.append(array_sum(-1) == 0)

# Inductive step -- using a ForAll constraint
# See: https://stackoverflow.com/a/31119239/2038713
i = z3.Int('i')
constraints.append(z3.ForAll(i, z3.Implies(
    z3.And(i >= 0),
    array_sum(i) == array_sum(i - 1) + array[i]
)))

# Uncomment to run
# solve(constraints)

# A simpler example
# A = z3.Array('A', I, I)
# solve(A[0] + A[1] + A[2] >=0)
# x = z3.Int('x')
# print(A[x])
# print(z3.Store(A, x, 10))

"""
Functions

Underlying theory: "Theory of uninterpreted functions"
"""

# Ignore this for now
I = z3.IntSort()

# Function example
x = z3.Int('x')
y = z3.Int('y')
f = z3.Function('f', I, I)
constraints = [f(f(x)) == x, f(x) == y, x != y]
# solve(z3.And(constraints))

"""
Custom datatypes

Underlying theory?
"""

# TreeList = Datatype('TreeList')
# Tree     = Datatype('Tree')
# Tree.declare('leaf', ('val', IntSort()))
# Tree.declare('node', ('left', TreeList), ('right', TreeList))
# TreeList.declare('nil')
# TreeList.declare('cons', ('car', Tree), ('cdr', TreeList))

# Tree, TreeList = CreateDatatypes(Tree, TreeList)


"""
===== Z3 internals =====

So how does Z3 work anyway?
Z3 is known as an "SMT solver": Satisfiability Modulo Theories.

- We know what "satisfiability" means

  We saw this in a previous lecture

Example:
Boolean satisfiability:

(p or q or r) and (~p or ~q or ~s) and (s)

We said it's "satisfiable" if there exists some values of the input
variables such that the formula is true.

The traditional problem of satisfiability, or SAT, is with boolean
variables -- if you've taken a CS theory class, you may have seen
that this is a famous example of an NP-hard problem. What that maens
is roughly that it's impossible to solve efficiently in general, in
general you would need exponential time to solve the problem.

A traditional Satisfiability solver (SAT solver) just deals with boolean
variables. So the second part is:

- The "theories" part is the fact that it can handle different data types:
  each data type, like integers, Reals, and Strings, comes with its own
  *theory* of how to process constraints on that data type.

Example:
  x = z3.Int("x")
  x < 2 and x > 2

We have the exact same thing as before, but we've replaced
p, q, r, and s with facts about our integer data type:
"x < 2" and "x > 2" are the new p, q, r, s:
Z3 will assign boolean variables:

  p = "x < 2"
  q = "x > 2"

Then it will apply a solver for boolean satisfiability.

How do we solve boolean satisfiability?

  (p or q or r) and (~p or ~q or ~s) and (s)

Simplest idea: try values of the variables.
First try p = True, then try p = False.

But that's not very clever.
Anything we could do better?
- Suggestion to: look at s!
- s has to be true! So let's just plug in s = True.

  (p or q or r) and (~p or ~q or False) and (True)

simplifies to:
  (p or q or r) and (~p or ~q)

What else should we look at?
- Suggestion 2: look at r!
- Just pick r = True, because if it's satisfiable, it might
  as well be satisfiable with r = True.

  (p or q or True) and (~p or ~q)
  True and (~p or ~q)
  ~p or ~q

Repeat.
--> set p to False
  True or ~q
  True
and we're done. Return satisfiable.

That's the rough idea behind basic satisfiability solving (SAT)

Remember that Z3 works with arbitrary data types.
There's one last step! Write out what we have:
  s = True
  r = True
  p = False
And we use a theory-specific solver to determine
whether these are a satisfiable set of formulas for the particular
data type we are using such as z3.Int.
E.g.: if
  s = x > 0
  r = x < 0
then we would find that this is not satisfiable, and we have to go
back and try again.

Discussion:
we just solved boolean satisfiability, suppoesdly an NP-complete
problem, extremely efficiently!
How is that possible?

The entire philosophy behind Z3: satisfiability is only NP complete
in the **worst case.**
In average cases, or practical examples that come up in the real world,
it's probably not too computationally difficult to solve them.

There are two algorithms,
- DPLL: Davis-Putnam-Logemann-Loveland
  https://en.wikipedia.org/wiki/DPLL_algorithm
  That's the one that we just showed above

- CDCL: Conflict-Driven Clause Learning
  https://en.wikipedia.org/wiki/Conflict-driven_clause_learning
  Optimized/better version
"""

"""
=== Generalizing theories ===

We have seen many specific theories that Z3 supports.

There are others, too: lists, bitvectors, strings, floating point, etc.

- What is the general form of a theory?
- How can we understand what theories Z3 is good at, vs. ones it is bad at?

====== Some end notes ======

=== Applications of Z3 ===

- Recall slide from first lecture: all programs are secretly just
  math and logic

- Compilers also work with a model of the program
    That is how they are able to optimize code prior to running it.

- Many applications to real-world software, like cloud services,
    distributed systems, compilers, system implementations, etc.
    (for example, millions of $ at Amazon invested in formal methods)

- You may choose to use Z3 for another domain-specific application for your final project

The key to applying Z3 in the real world is often to define the right
mathematical domain to map your programs to.

===== Z3 Review =====

Validity and satisfiability

We saw that:
Using the problem of satisfiability, we can:
- solve() constraints
- and we can prove() specifications.

We should now be comfortable with using Z3 to set up a problem:
1. Declare variables
2. Declare constraints
3. Ask Z3 to solve the constraints

Z3 has two "modes" that we have used: solve() and prove().
- solve() to determine satisfiability
- prove() to determine validity

How do program specifications relate to Z3?
(HW1 part2 has a question about this)

    inputs = ... # Z3 variables
    output = call_program(inputs)
    precondition = ...
    postcondition = ...
    spec = z3.Implies(precondition, postcondition)
    prove(spec)

We can also use Z3 more like Hypothesis to generate example inputs.
How?

    inputs = ... # Z3 variables
    precondition = ...
    example = get_solution(precondition)

^^ This is basically how Hypothesis works!

We saw that the main limitation of Hypothesis was?

- It can find a bug, but it can never prove that there are no bugs!

=== Main limitations of Z3 ===
(There are two)

1. We have to rewrite the program in Z3
2. Z3 might hang or return unknown

And that's where we are going next!

With general program verification frameworks!

The program and the proof will both be written in the same framework.

=== The "Big Question" ===

What is the boundary between problems that Z3 can solve and problems that it cannot?

-> I.e.: What is the boundary between logics that are tractable and those that are not?

-> One way to study this: which sub-logics are decidable or not?

This topic will lead us into the next lecture.

"""
