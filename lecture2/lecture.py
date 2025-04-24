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

We have seen that even though satisfiability is hard or undecidable in general,
Z3 can solve many practical problems.
- n-queens.py
- other examples in problems/ (sudoku.py, task-scheduler.py)

[N queens solution demonstration
How large can we take N up to before Z3 fails?]

- Around 30-40 it starts to get a bit slower.

Key points:
- We don't have to be good in the worst case - we can just be good on "average" cases!
- We don't have to be good for "sufficiently large" inputs - solving on small inputs is both useful and interesting!

How does Z3 do this? Important algorithms: DPLL, DPLL(T), CDCL, Nelson-Oppen.

- Still, some of you noticed that this fails sometimes. (More on this later)

=== Why can Z3 fail? ===

Z3 is a computer program. (It is equivalent to a Turing machine)

We give Z3 some input formula φ. It could fail for two reasons:
- Not computationally feasible?
- Times out or returns unknown?
- Solution space is too large -- too many inputs to consider

1. No matter how much time is given, the algorithm used by Z3 does not resolve whether φ is satisfiable
    --> there may be no such proof.
    --> Decidability boundary
    --> If a set of formulas L is undecidable, then Z3 is not special, for any TM M there exists
        a formula φ in L such that M doesn't output whether φ is satisfiable (SAT or UNSAT)

2. Z3 can decide that φ is satisfiable, but not in a "reasonable" amount of time.
    --> proof does exist and just takes too long to find
    --> Complexity boundary
    --> If a set of formulas L is decidable, then we can try to come up with algorithms or heuristics
        to return a result (SAT or UNSAT) more quickly on some inputs.

Both of these depend on the actual alg. that Z3 is using.

=== Z3 Tour ===

Keeping this mind...
A tour of some of the remaining theories that Z3 supports
that you will most often encounter / will be most useful
(and corresponding Z3 syntax).

=== Real numbers ===

Grammar for reals:

Let's modify our grammar for integers below:

        RealVar ::= n1, n2, n3, ...

    Integer expressions
    (let's not include division)
    (other interesting operations -- % (modulo), ^ (exponentiation), ! (factorial))

        IntExpr ::=
            RealExpr + RealExpr
            | RealExpr - RealExpr
            | RealExpr * RealExpr
            | RealVar
            | 0
            | 1

    Formula
    We can compare two integers! (A relation)

        Formula φ ::= φ v φ  |  φ ^ φ  |  !φ
            | RealExpr == RealExpr
            | RealExpr < RealExpr

            (add if you like -- expressible using above)
            | φ <-> φ
            | φ  -> φ (if then)
            | True
            | False
            | φ ⊕ φ (xor)
            | RealExpr <= RealExpr
            | RealExpr >= RealExpr
            | RealExpr > RealExpr

    This is exactly the same grammar as over the integers --
    the only thing different is the semantics, not the syntax.

    Q: Do we need to include additional constants? Right now we only have 0 and 1
    A: We could, but no matter what we include we won't get all real numbers
        We would have to allow only, e.g. rational numbers, algebraic numbers, or computable numbers,
        which get a bit more complicated to write down,
        so let's just assume 0 and 1 for now.

        We don't have 1/2, but we can say indirectly with 2 * x == 1
        We don't have sqrt(2), but we can say indirectly with x * x == 2
        ...

        (Recall that: syntax vs. semantics?
            Syntax == grammar above
            Semantics: for any variable assignment v: RealVar -> Real
                φ[v]
            evaluates to true or false.
        )

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
- Linear programming with real numbers is solvable in Ptime and linear programming with integers is NP-hard
- Integers are kind of like real numbers with extra constraints
-
            ax^2 + bx + c == 0
    has a solution over the reals iff
            b^2 - 4ac >= 0
            ^^^ discriminant

    And it turns out you can generalize this to any polynomial.

Q: Is satisfiability for reals NP-hard?

https://forms.gle/WBbgUvvYuGEdPmgB9

=== More interesting data types ===

Besides reals, the most interesting and commonly useful datatype in practice
is strings.

What are string constraints?
This starts to look quite different:

The theory of strings:
    (Recipe to define any logic: Variables, Exprs (operations supported), Formulas (relations supported))

        StringVar ::= s1, s2, s3, ...

    String expressions
    What do strings support?

        StrExpr ::= StringVar
                    | Concat(StrExpr, StrExpr)
                    | Character(sigma)       <--- sigma is from a finite alphabet Sigma
                    | EmptyString

                    Also could add:
                    | CharAt(StrExpr, IntExpr)
                    | Replace(...)
                    | Substring(...)

    Formula
    Let's start with our previous grammar
    Do we want to add any other relations?

        Formula φ ::= φ v φ  |  φ ^ φ  |  !φ
            | StrExpr == StrExpr
            | Len(StrExpr) <= IntExpr <--- combining theories!
                                        if you want, you can just add Len(StrExpr) to the IntExpr
                                        grammar. Then we would have two mutually recursive grammars.
            | StrInRegex(StrExpr, Regex)

            (add if you like -- expressible using above)
            | φ <-> φ
            | φ  -> φ (if then)
            | True
            | False
            | φ ⊕ φ (xor)

        Regex grammar:
            RegEx ::= Char(sigma) | Concat(Regex, Regex) | Union(Regex, Regex) | Star(Regex).
            Full grammar in: extras/regex_help.md

        Example:

        Every character in the string is either a or b?
        Withour regex - with CharAt?

            forall i: 0 <= i < Len(s) ==> CharAt(s, i) == Char(a) v CharAt(s, i) == Char(b)
            ^^^^^^ I used a quantifier
                    we aren't allowing quantifiers yet.

        With regex:

            StrInRegex(s, Star(Union(Char(a), Char(b)))).

Once again going back to our question:

Q: Is satisfiability for the theory of strings decidable?

    --> Decidable with just string concat and regex
    --> Open problem with including len()

Q: Is satisfiability for strings NP-hard?

    --> Yes again for the same reasons.

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

xss_attack = z3.And(
    query_html == start + malicious_query + end
)

# Uncomment to run
# z3.solve(xss_attack)

# (We could also generalize this to require that the </title> tag is closed before the query,
# or that the HTML matches a grammar, e.g. using regexes)

"""
Match a US phone number example:
"""

phone_number = z3.String("phone_number")
number = z3.Range("0","9") # Regex range -- matches a char from 0 to 9
hyphen = z3.Re("-") # Regex string constant - matches only the string "-"

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
z3.solve(z3.InRe(phone_number, regex_constraint))

"""
=== Quantifiers ===

Finally the last part of Z3 syntax is the most insidious and the most
powerful - quantifiers.

- z3.ForAll(var_or_list_of_vars, formula)

- z3.Exists(var_or_list_of_vars, formula)

Z3 supports quantifiers, but not very well.

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
solve(z3.And(constraints))

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

How SMT solvers work:

1. Algorithms for Boolean satisfiability
2. Decision procedure for specific theories.

Part 1: Boolean SAT:

Example:

    (p or q or r) and (~p or ~q or ~s) and (s)

What should I do to solve?

First, s is alone, so we know s has to be true!

    ===== DPLL Algorithm =====

    Key Idea #1: Unit Propagation.

    Assume the input is in conjuctive normal form: conjunction of disjuncts
        (... or ... or ...) and (... or ...) and ...
        ^^^^^^^^^^^^^^^^^^^ clause
                                ^^^^^^^^^^^^ clause
        where the ... can be literals or negated literals.

    Visit all clauses. If there are any clauses with only a single literal (or negated literal),
    mark that literal true (or false).

    (p or q or r) and (~p or ~q or ~true) and true
    (p or q or r) and (~p or ~q or false)
    (p or q or r) and (~p or ~q)

    Ideas:
    - Second clause into not (p and q) ?
    - Try all possibilities (yes - but here we can do something smarter)

    Set r to true!
    --> ~r never appears!
    --> WLOG just assume r is true. We get:
        (~p or ~q)
    --> Apply this again with ~p, we get True and the formula is SAT.

    Key Idea #2: Pure Literal Elimination

    Visit all clauses. If there are any variables which only ever appear in one polarity
    e.g., r only (respectively, ~r only), just assume that it is true (respectively, false)

    Key Idea #3: If both of the above fail, then pick a random variable, try setting it to true or false,
    and recurse.
        --> if we find SAT, great! we're done
        --> if we find UNSAT, backtrack and try the other way.

    That's it! That's the DPLL algorithm.

    Algorithm pseudocode
        1. Rewrite the formula in CNF
        2. While the formula is nonempty:
            2.0. If any clauses are empty, return UNSAT. If there are no clauses left, return SAT.
            2.1. Try unit propagation: look for any clauses with a single variable, mark them true.
            2.2. Try pure literal elimination: look for any variables in one polarity, mark them.
            2.3. If both of the above fail, guess a random variable and recurse.

    Theorem:
        1. DPLL is correct: if the formula is SAT, it will return SAT, if UNSAT, it will return UNSAT.
        2. DPLL is exponential time in the worst case.

Recap:
- We saw a tour of some of the remaining theories that Z3 has to offer
- We saw the DPLL algorithm
    Extensions of DPLL: DPLL(T) -- how to handle theories, CDCL.

******** Where we left off for today **********

=== April 24 ===

Last time: we saw the basic algorithm for SAT, DPLL.

=== Poll ===

Which of the following is a most likely reason that DPLL works well in practice?

https://forms.gle/QBp2N4E39BCQcU3f9

=====

Aside: SAT competition:
https://satcompetition.github.io/2024/

=====

Our roadmap to solve SMT (Satisfiability Modulo Theories):

1. Solve SAT - DPLL
2. Solve the theory part - DPLL(T)
3. Solve multilple theories - Nelson-Oppen

=== DPLL(T) ===

    (p or q or r) and (~p or ~q or ~s) and (s)

Example:
  x = z3.Int("x")
  p and s
  (x < 2) and (x > 2)

We have the exact same thing as before, but we've replaced
p, q, r, and s with facts about our integer data type:
"x < 2" and "x > 2" are the new p, q, r, s:
Z3 will assign boolean variables:

  p = "x >= 2"
  q = "x == 2"
  r = "x > 2"
  s = "x + y > 5"

Then it will apply a solver for boolean satisfiability.

What happens when we try the DPLL algorithm on the above?

    UP: s = True
    PLE: r = True
    PLE: ~p = True i.e. p = False

Remember that Z3 works with arbitrary data types.
There's one last step! Write out what we have:
  s = True
  r = True
  p = False

What happens? We add one step at the end:
check whether the theory constraints are satisfiable.
In this case, we have:

    x + y > 5 and x > 2 and ~(x >= 2)
    x + y > 5 and (x > 2) and (x < 2)

We query a theory-specific solver based on the form of the
constraints:
    -> in this case, we see that all the constraints are
    integer constraints
    -> and moreover they are all linear (never have two
       variables multiplied together)
    -> This is essentially Integer Linear Programming (ILP)
    -> Basically solve the linear equations the way you
       would have done in a linear algebra class

- If theory-specific solver says SAT, return SAT
- What happens if the theory-specific solver comes back and
  says UNSAT?
  (let's change our example so that p = "x >= 2")
    + Try another satisfying assignment?
    There's a problem with this, what is it?
    One of UP or PLE is suspect, which one?
    + Go back and backtrack on PLE constraints also?
    + This is very inefficient though...
        we just tried s = true, r = true, p = false
        we may end up trying the same assignment later with
        a different value for q.

Turns out to be a better idea:
    "learning" (in the traditional deductive sense)
    Add a constraint for what we learned.

    We learned: ~(s and r and ~p)

    This is a clause!

    ==> (~s or ~r or p)

Add it into the formula and continue with backtracking.

(We also have to backtrack through PLE)

When does this terminate?

Theorem: If all constraints are over a decidable theory
       or a decidable fragment (e.g. in our case, everything
       was linear constraints over the integers)
       then this procedure is guaranteed to terminate and returns
       SAT if the formula is SAT, UNSAT if the formula is UNSAT.

example: suppose our formula is
    (p or q or s or t)
and they all happen to be unsat theory-specific constraints
(e.g. p = "x == x + 1", q = "y == y + 1", etc.)

    try p?
    (p or q or s or t) and (~p)
    UP:
    (q or s or t)
    try q?
    (q or s or t) and (~q)
    UP:
    (s or t)
    try s?
    (s or t) and ~s
    UP:
    t
    try t?
    t and ~t
    DPLL returns UNSAT.

Note this could fail if the underlying theory is not decidable
or not decidable in a reasonable amount of time.

One takeaway from this is that adding clauses is often useful
to help the SAT solver -- this is the idea behind CDCL,
an extension of DPLL, which we will mention briefly below.
CDCL is actually how most modern SMT/SAT solvers work.

=== Nelson-Oppen ===

The above only works for a single decidable theory! (Why?)
So we really just have "Satisfiability Modulo Theory"

    Recall: some constraints combine multiple theories

        Len(StrExpr) <= IntExpr

Q: Is it always the case that if

    φ1 is satisfiable over theory T1 and
    φ2 is satisfiable over theory T2

then
    φ1 ^ φ2 is satisfiable?

A: No, let's try to construct a counterexample

    Satisfiable over strings:
    Let's have two string variables s1, s2
        len(s1) <= x and
        len(s2) > y and
        s1 == s2 and
        x <= y

    Purely looking at the string constraints:
    len(s1) <= x and len(s2) > y and s1 == s2
    SAT!
    Purely looking at the integer constraints:
    x <= y
    also SAT!

    But they are not jointly satisfiable.

How do we solve this?
(I will only cover at a high level)

    - Introduce new (fresh) variables for any expressions that
      occur in constraints of both theories

      ls1 <--- len(s1)
      ls2 <--- len(s2)

      Integer part:
      ls1 <= x
      ls2 > y
      x <= y
      String part:
      len(s1) == ls1
      len(s2) == ls2
      s1 == s2

      Idea: ask each solver to solve the constraints separately,
      then ask if they agree on which of the shared variables
      are equal to which others.

      Shared variables in this example: ls1, ls2

      String solver should come back with an assignment
      such that ls1 == ls2
        (e.g., ls1 == 5, ls2 == 5)
      Integer solver should come back with something where
        ls1 <= x <= y < ls2
      it should come back with a variable assignment that
      has ls1 < ls2
        (e.g., ls1 == 2, ls2 == 4)
      in particular ls1 != ls2,
      so the two variable assignments do not agree.
      If they don't agree, we add another constraint

      ((ls1 == ls2) or (ls1 != ls2))

      Isn't this a tautology so it's useless to add?

      p or ~p

It turns out for many (not all) theories we can prove
that if
    φ1 is satisfiable over theory T1
and
    φ2 is satisfiable over theory T2
and
    there exists a satisfying assignment v1 for T1
    and v2 for T2 such that the two agree on which shared
    variables are equal to one another
then
    φ1 ^ φ2 is satisfiable over the combined theory T1 U T2.

=== Another generalization of DPLL: CDCL ==

CDCL = Conflict-Driven Clause Learning

Modern SAT solvers are primarily based on a generalization of DPLL called CDCL.

Failure case of DPLL:

    Early on we make a decision for one or more variables
        say p,
        or say, (s and r)
    that turns out to be wrong.

CDCL basically adds just one additional core idea to DPLL, conflict resolution:

- We maintain an implication graph during unit propagation that indicates
  which choices have affected which other forced choices

- If we explore down a path that doesn't work, we learn a new clause:
  one of the choices we made must have been false!

In our example?

    Suppose I decide s, then r, then ~p then ~q
    Spupose we learn that s and ~p leads to a conflict
    Rather than just backtracking and trying p and continuing,
    add a clause that s and ~p is unsat

        ~s or p

    and backtrack to the latest decision point that lead to
    the conflict.

=== References ===

- DPLL: Davis-Putnam-Logemann-Loveland
  SAT
  https://en.wikipedia.org/wiki/DPLL_algorithm

- DPLL(T):
  SAT modulo theory
  https://en.wikipedia.org/wiki/DPLL(T)

- Nelson-Oppen:
  SAT modulo theorieS
  https://web.stanford.edu/class/cs357/lecture11.pdf

- CDCL: Conflict-Driven Clause Learning
  extension of SAT that explores decisions after a conflict
  more efficiently.
  https://en.wikipedia.org/wiki/Conflict-driven_clause_learning
  Optimized/better version
"""

"""
====== The boundary of decidability ======
(Cover very briefly for time)

Just to show one example of how the boundary of decidability can be surprising.

Definitions:
Let F be a set of function symbols (each has an arity n >= N,
    arity == the number of arguments it takes
) each corresponding to a function on the natural numbers,
and R is a set of relation symbols (each has an arity n >= N) each corresponding to a relation on the natural numbers.
We define the quantifier-free theory QF(F, R) coresponding to F and R consists of all formulas which can be formed using
symbols in F and R, as follows:
    IntVar
    IntExpr ::= IntVar | op(IntExpr, ..., IntExpr) (with n coordinates if arity is n)
    Formula φ ::= IntExpr == IntExpr | φ v φ | φ ^ φ | ~φ
                | rel(IntExpr, ..., IntExpr) (with n coordinates if arity is n)

Recall:
Theorem 1. (Hilbert's 10th) The theory QF({+,*},{}) is undecidable.
Proof Omitted (hard).

Theorem 2. The theory QF({+,gcd},{}) is decidable.
Theorem 3. The theory QF({+,lcm},{}) is undecidable.

Proof 2.
(Omitted)

Proof 3. (Sketch)
Suppose x is even, then
    lcm(x - 1, x + 1) = x^2 - 1
Suppose x is odd. Then
    lcm(x - 1, x + 1) = (x^2 - 1) / 2
So using lcm, we can get x^2.
Using squares you can get multiplication:

    (x + y)^2 = x^2 + 2 * x * y + y^2
    2 * x * y = (x + y)^2 - x^2 - y^2

Therefore if I have lcm I can get multiplication,
and by Hilbert 10th this is undecidable. □

General theorem.
If a function or relation has both an existential and a universal definition,
then it can be eliminated: satisfiability can be reduced back to the base theory.
That is, decidability for QF(F U {f}, R) reduces to decidability for QF(F, R).

"""

"""
====== Some end notes ======

=== Other theories ===

We have seen many specific theories that Z3 supports.

There are others, too: lists, bitvectors, strings, floating point, etc.

- What is the general form of a theory?
- How can we understand what theories Z3 is good at, vs. ones it is bad at?

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

=== A "Big Question" ===

What is the boundary between problems that Z3 can solve and problems that it cannot?

-> I.e.: What is the boundary between logics that are tractable and those that are not?

-> One way to study this: which sub-logics are decidable or not?

=== Using Z3 for program testing & counterexample finding ===

We can also use Z3 more like Hypothesis to generate example inputs.
How?

    inputs = ... # Z3 variables
    precondition = ...
    example = get_solution(precondition)

^^ This is basically how Hypothesis works!

=== Main limitations of Z3 ===
(There are two)

1. We have to rewrite the program in Z3
2. Z3 might hang or return unknown

And that's where we are going next!

With general program verification frameworks!

The program and the proof will both be written in the same framework.
"""
