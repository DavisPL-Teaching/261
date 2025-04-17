"""
Z3 extras
- additional syntax and examples

Additional help:

- Useful guide:
  [Z3 py guide](https://ericpony.github.io/z3py-tutorial/guide-examples.htm)

- Documentation:
  [Z3 py docs](https://z3prover.github.io/api/html/namespacez3py.html)

- The Z3 solver API
"""

import pytest
import z3
from helper import prove, solve, SAT, UNSAT, UNKNOWN, PROVED, COUNTEREXAMPLE

"""
Solve and prove

Two main functions of Z3:
z3.solve (or our helper solve) --> ask if formula is satisfiable
z3.prove (or our helper prove) --> ask if formula is valid

Possible answers:
    SAT
    UNSAT
    COUNTEREXAMPLE

Validity and satisfiability are reducible to each other
Specifically: validity of "P" and satisfiability of "Not P" are solving
the same problem.

Thus, how z3.prove works:
- If I run z3.prove(formula) it calls z3.solve(z3.Not(formula))
- If satisfiable: that means there is an input where "NOT formula" is true
    Therefore, "formula" must be false (on that input)
    Therefore, "formula" is not necessarily true for all inputs, i.e. it's not
    provable -- there is a counterexample.
- If unsatisfiable: that means there are no inputs where "NOT formula" is true
    Therefore, "NOT formula" is false for all inputs
    Therefore, "formula" is true for all inputs
    Therefore, formula is provable.
- If unknown: we return unknown.

Q: When does z3.solve (or z3.prove) return unknown?
Intuitively, if the formula is really mathematically complex, involves a lot
of difficult operations and it's too hard to figure out whether it's satisfiable
or not.
--> Booleans are quite easy, so this will rarely happen with booleans.

Q: When should you use z3.prove vs z3.solve?

- z3.prove is useful for proving specifications, and also when
    you want to show that some assertion or some property always holds

- z3.solve is useful for solving equations, solving puzzles, and
    similar tasks where you have some set of constraints, and
    you want to find a solution to those constraints.
    E.g.: you want to solve x^2 - 3x + 2 = 0
    or you want to solve a Sudoku puzzle
"""

# z3.solve(form1)
# z3.solve(form2)
# z3.solve(form3)
# z3.solve(form4)
# =====> Satisfiable, Z3 gives an example

# For all four examples, the formula is satisfiable -- Z3 returns an example
# where the formula is true.
# What about something that's NOT satisfiable?

# form5 = z3.And(a, z3.Not(a))
# # A and Not A --> always false, should be never true, i.e. not satisfiable

# z3.solve(form5)
# # =====> Unsatisfiable, Z3 says "no solution"

"""
Boolean syntax

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

# print("More examples:")
# x = z3.Bool('x')
# y = z3.Bool('y')
# What does implies do?
# z3.solve(z3.Implies(x, y))
# Implies is basically the "if then" function and it has the following meaning:
# if x is true then y, otherwise true.
# arrow (-->)
# If you like you can write z3.If(x, y, True) instead of z3.Implies(...)
# It's reducible to if then.

# XOR implies or?
# XOR is exclusive or (exactly one, but not both of x and y are true)
# x_xor_y = z3.Xor(x, y)
# x_or_y = z3.Or(x, y)
# z3.prove(z3.Implies(x_xor_y, x_or_y))

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
=== Integers ===

z3.Int
z3.Ints -- creates multiple integers

Examples
"""
# x, y = z3.Ints("x y")
# spec = z3.And(x > y, y > 5)
# z3.solve(spec)

"""
What operations are supported here?
You can use most built-in integer operations in Python
on Z3 integers. BUT keep in mind it's not the same as Python
integer arithmetic.
"""

# x + y # <- Z3 expression, NOT a Python integer
# print(x + y) # Prints as "x + y", not as some specific integer

# Problem: find two integers whose sum and product is the same.
# print("Find two integers whose sum and product is equal:")
# z3.solve(x + y == x * y)

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
# a, b, c = z3.Ints("a b c")
# print("Example pythagorean triple:")
# z3.solve(pythagorean_triple(a, b, c))

"""
Q: what if we want more than one answer?

We can try rerunning...

The easiest way is a common technique where
each time we get an answer, we add an assertion that
that answer is excluded.
"""

# First answer: a = 6, b = 8, c = 10
# Second answer
# new_constraint = z3.Or(
#     z3.Not(a == 6),
#     z3.Not(b == 8),
#     z3.Not(c == 10),
# )
# ^ Force the solver to give us a new answer.
# z3.solve(z3.And([
#     pythagorean_triple(a, b, c),
#     new_constraint,
# ]))

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

# x = z3.Int('x')
# print("Solution:")
# z3.solve(x * x + 5 * x + 6 == 0)
# # If we want the other answer?
# y = z3.Int('y')
# z3.solve(z3.And([
#     x * x + 5 * x + 6 == 0,
#     y * y + 5 * y + 6 == 0,
#     x != y,
# ]))

# Another poll
# What would you guess is the output of the following Z3 code?

@pytest.mark.skip
def test_poll_output_2():
    x = z3.Int('x')
    y = z3.Int('y')
    spec = z3.Implies(z3.And(x >= 10, y == x * x), y >= 100)
    prove(spec)

# print("Output:")
# test_poll_output_2()


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

# x = z3.Real('x')
# # what happens?
# print("Square root of two:")
# z3.solve(x * x == 2)

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
More datatypes...

===== Z3 Strings =====

What is a string?
- An array of chars.
What are characters?
ASCII characters? == bytes
In Z3: Characters == Unicode chars
So we will think of strings as:
- A sequence of unicode chars
- We don't care how the sequence is encoded.

- z3.String
- z3.Length

Q: define a name that has at least 10 letters
"""

name = z3.String("name")
constraint = z3.Length(name) >= 10
solve(constraint)

# Comment: In this case it returned ASCII!
# But, if you play around you will quickly encounter cases
# where it returns strange unicode code points, and they
# might even display weirdly on your terminal as things like
#  \u{32} \u{50}

# Often, it's useful to just assume the whole string is ASCII,
# and we will see how to do that in a few minutes.

# Q: What does z3.Length return here?
# A: It's a Z3 integer.
# Fortunately, we already know how to work with integers!
# So you can do any operation you're familiar with on integers,
# on the string length.

"""
- z3.StringVal
- +

Similar for integers: there's Int and there's IntVal.
An IntVal is just a specific (constant) integer.
Similarly, a StringVal is a specific (constant) string like
"Hello" or "Cats and dogs".

Q: define a message for Hello, name!
"""

msg = z3.String("msg")
name_constraint = z3.Length(name) >= 10
# msg_constraint = (msg == z3.StringVal("Hello, ") + name + z3.StringVal("!"))
msg_constraint = (msg == "Hello, " + name + "!")

solve(z3.And(name_constraint, msg_constraint))

# Basically, StringVal converts a Python string into a Z3 string.
# With integers and Booleans, we didn't use this too often, because
# it was happening automatically behind the scenes.

# Can we omit the StringVal?
# Yes! Z3 automatically converts a Python string into a Z3 StringVal in this case.

"""
Constraints between multiple strings

Q: Define strings s1, s2 such that
s1 is three copies of s2
and s2 is not empty
"""

s1 = z3.String("s1")
s2 = z3.String("s2")
constraints = [
  s1 == s2 + s2 + s2,
  s2 != "",
  s2 != "A",
  s2 != "B",
  z3.Length(s2) >= 2,
]
solve(z3.And(constraints))

"""
===== Regular expressions =====

Help notes: regex_help.md

What is a regular expression?
A "pattern" that a string may or may not satisfy.
-> you can think of it as a boolean on strings.
For example:
- the string contains the word "cat" inside it
- the string is only ASCII characters
- the string has no capital letters
- ...
Roughly:
a pattern of characters that is or is not present in the string.

Most important thing: if you have a string s and a regular expression
(or regex, for short) R, you can ask

  Does s match R?

The string "matches" the regex R if the pattern is present/true,
and does not match if it's not present/false.

Q: define a name that has at least 10 letters and only contains a-z.
"""

# What we had before...
name = z3.String("name")
length_constraint = z3.Length(name) >= 10

# Our regex constraint...
# z3.Range
lowercase_letter = z3.Range("a", "z")
"""
matches? "x" "y" "a" "b" "r" --> a single character that is a lowercase letter
doesn't match? "" "cat" "ASDFBDF" "$"
"""
# z3.Star -- kind of like a for loop, it matches
# the same thing zero or more times.
lowercase_letters = z3.Star(lowercase_letter)
"""
matches? "" "cat" "dog" "xyz" "thequickbrownfoxjumpedoverthelazydogs" etc.
doesn't match? "c a t" "$$$" "asdfkl;ajsdg4" etc.
"""
# Last thing we need?
# Turn the regex into a constraint on the string.
# We use the fundamental operation of regexes! Does a string s match
# a regex R?
# In Z3, the operation for this is z3.InRe
regex_constraint = z3.InRe(name, lowercase_letters)

# Now let's solve our constraint
z3.solve(z3.And(
  length_constraint,
  regex_constraint,
))
# Now our name is dcapphpppp!
# Hooray, no capital letters!

"""
Q: Define a string 'name' such that only the first letter
   is capitalized.
"""

capital_letter = z3.Range("A", "Z")

# We already have our lowercase character regex... so let's combine them!
# How do we combine two regex constraints?
# If you want pattern1 **followed by** pattern 2, we use
# z3.Concat

name_regex = z3.Concat(capital_letter, lowercase_letters)
regex_constraint = z3.InRe(name, name_regex)

z3.solve(z3.And(
  length_constraint,
  regex_constraint,
))

"""
How does Z3 regex differ from practical regexes?

Some operations present in practical regex libraries may not
be present in Z3 and will require encoding them in some way,
for example:
  - capture groups
  - anchors like ^ and $
  - case-insensitivity, where we want to automatically consider
    'a' and 'A' to be the same
  - matching any alphanumeric character

While there are more advanced solutions, the easiest way
to do these sorts of constraints is to write your own Ranges and
similar for the different characters you're interested in.
"""

"""
Q: Modify the string to allow spaces.

But: we don't spaces at the beginning or end of the string, we want
something like
  Firstname Lastname
  or
  Firstname Middle Lastname

So how can we do this?
"""

# Let's reuse what we already have!
# How do we convert " " to a Regex (from a Python string)?
# We could use z3.Range, but there's a simpler way
# Let's refer to regex_help.md
# We can use z3.Re
full_name_regex = z3.Concat(
  name_regex,
  z3.Re(" "),
  name_regex,
)

solve(z3.And(
  length_constraint,
  z3.InRe(name, full_name_regex),
))

# Middle names?
# We could do one for 3 names, one for 2 names,
# and z3.Or them
# Let's actually use z3.Union: basically OR for regexes

full_name_regex = z3.Concat(
  # Firstname
  name_regex,
  z3.Re(" "),
  # Middlename
  z3.Union(
    z3.Re(""),
    z3.Concat(name_regex, z3.Re(" "))
  ),
  # Lastname
  name_regex,
)

solve(z3.And(
  length_constraint,
  z3.InRe(name, full_name_regex),
))

# What if we want to allow more than just 3 names?
# (Real names can have any number of parts)
# Use z3.Star?
# Generalization of z3.Concat for any number
# of parts.

full_name_regex_generalized = z3.Concat(
  # Firstname
  name_regex,
  z3.Star(
    # Any further names here (Middle name, last name, etc.)
    z3.Concat(z3.Re(" "), name_regex)
  ),
)

solve(z3.And(
  length_constraint,
  z3.InRe(name, full_name_regex),
))

# Q: How do length_constraint and z3.InRe both know to
# constraint the entire string?
# A: because they both refer to the 'name' variable.

"""
Q: We know that full_name_regex_generalized
refers to a name with any number of spaces
and full_name_regex refers to a name with
exactly 2 or 3 parts.

Is full_name_regex_generalized actually more general?
In other words,
does full_name_regex **imply** full_name_regex_generalized?

(Useful for HW problem 11)

How would we do this?

Use z3.Implies! We've seen this pattern
several times:

    z3.Implies(precondition, postcondition)

To show that R2 is more general than R1,
we could show that

    precondition: s matches R1
    postcondition: s matches R2

How we write that in Z3?

    z3.Implies(z3.InRe(s, r1), z3.InRe(s, r2))
"""

# This should pass
# assert prove(z3.Implies(
#     z3.InRe(name, full_name_regex),
#     z3.InRe(name, full_name_regex_generalized),
# )) == PROVED

# Z3 hangs! :O

# What do we do to fix this?
# Tip: bound your variables.
# Add a constraint that the string is at most, e.g.
# 25 or 100 characters.

# assert prove(z3.Implies(
#     z3.And(
#       z3.InRe(name, full_name_regex),
#       z3.Length(name) <= 20
#     ),
#     z3.InRe(name, full_name_regex_generalized),
# )) == PROVED

# Would also have to use string concatenation like...
# phone_number = first_part + "-" + second_part + "-" + last_part

# What is star? 0 or more repetitions.
# "" or number or number, number or number, number, number or
#      number, number, number, number, ....

"""
===== More on strings and regexes =====

Other Regex operators we haven't seen above (see regex_help.md):
- z3.Plus
  Like Star but one or more times, insetad of zero or more times.
- z3.IntToStr
  z3.IntToStr(9) to get the digit 9
  z3.IntToStr(n) to get the string corresponding to the Z3 int n.
- z3.CharIsDigit
"""

n = z3.Int("n")
s = z3.String("n_to_string")
spec = z3.And(
  n >= 123,
  s == z3.IntToStr(n),
)
solve(spec)

# Q: why a special operation for IntToStr? I didn't learn about this
# in my previous regex tutorial/class
# A: It's a complex operation and it's totally not obvious how to do it
# without built-in support.
# Basically, serializing a number using its base 10 representation.

"""
There are others!
Union is like OR.
What about AND and NOT? Those also have regex equivalents.

- z3.Intersect(R1, R2): a regex
  matching all strings that match both R1 and R2
- z3.Complement(R)
  matches all strings that DON'T match R.

Example:
Q: Use a regex to define a string that is NOT equal to the empty string.
"""

not_empty = z3.String("s")
regex_constraint = z3.Complement(z3.Re(""))

solve(z3.InRe(not_empty, regex_constraint))

# We could have also done this with z3.Length(s) >= 1.

"""
CSV example

Suppose we are asked to write a simple
serialization and deserialization function for a User class.
It looks like this:

def to_csv(user):
  ...

def from_csv(csv):
  ...

It is possible to show using Hypothesis that some inputs can
cause to_csv and from_csv to break.

Bug: where the user sets their name to "Hi,My,Name,Has,Commas"
  age: 50
serialization returns:
  Hi,My,Name,Has,Commas,50
deserialization gets confused!

Q: How could we use Z3 to model this scenario?

Problems to validate with Z3:
- the deserialization doesn't match the original user!
- there are 2 different deserializations for the same string!

Q: How could we use Z3 to validate our solution?

- Restrict the name to not contain commas?
- Change the deserialization function to handle commas?

Z3 could be used to prove that both of these work.
"""

"""
===== Z3 techniques =====

Recall example: Z3 had trouble with proving one regex
constraint implies another
"""

# Regex example from earlier

# assert prove(z3.Implies(
#     z3.And(
#       z3.InRe(name, full_name_regex),
#       z3.Length(name) <= 50
#       # if you had other string variables, add more constraints here
#     ),
#     z3.InRe(name, full_name_regex_generalized),
# )) == PROVED

# (You will need this on HW3 problem 11!)

"""
What do we do if Z3 is having trouble with a problem?

1. Bound the variables

2. Add/modify the constraints
- bounds on the variables are one form of this!
- strengthen the precondition
- relax the postcondition to something weaker
- add lemmas!

  z3.Implies(precond, hard_postcondition)
  Z3 hangs :(

  Split my problem up into two steps:
  z3.Implies(precond, lemma)
  z3.Implies(z3.And(precond, lemma), hard_postcondition)

Ask Z3 to prove each of the two statements separately!

To draw an analogy with Hypothesis: it's like putting
assert() statements earlier on in your program.

3. Use a different encoding
- use Bool, Int, Real instead of more complex types
- avoid Array, Functions

Example: we already saw an example of this
- Pigeonhole principle on HW2 part 3!

4. Do some enumeration or search outside of Z3,
   for example using itertools.

Example: we saw this on HW2 part 2

Python itertools is a way of conveniently enumerating all
permutations (reorderings) of a list.

===== The full power of Z3 =====

(This part will not be on the final)
I just want to briefly mention some of the powerful features available
in Z3 that we haven't covered in this class, in case you want to use
Z3 for your own projects.
Some of the most powerful use cases are when combining general data types
(functions and arrays) with quantifiers.

What are quantifiers?

- z3.ForAll(var_or_list_of_vars, formula)

  It states that for all possible values of the variables, formula
  should hold.
  This should be reminiscent of prove()!

- z3.Exists(var_or_list_of_vars, formula)

  It states that there exists a possible value of the variables,
  such that the formula should hold.
  This should be reimiscent of solve()!

Let's see an example:

Q: Prove that if the sum of an array is positive, then an array has
   an element that is positive.
"""

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

# The result so far?
#    array_sum(-1) = 0
#    array_sum(0) = array[0]
#    array_sum(1) = array[0] + array[1]
#    and so on.

# Now define our problem

# Simpler version of the problem
constraints.append(array_sum(5) > 0)
precond = z3.And(constraints)
postcond = z3.Exists(i, array[i] > 0)

# Prove
prove(z3.Implies(precond, postcond))
# This one works.

# Harder version of the problem?
# N = z3.Int('N')
# constraints.append(N >= 0)
# constraints.append(array_sum(N) > 0)
# This one doesn't work.

"""
If it didn't work?

Q: when does Z3 know to return unknown rather than hang?

A: Z3 tries to identify if it sees a case where it knows it
   beyond the capabilities of its automated decision procedures.

  Ex: one of the cases that Z3 solves very efficiently is if
  using Int and all your constraints are what's called linear constraints:
  a + b + c > 3 * d - e + 4 * f
  No two variables are multiplied
  Z3 has a specific built-in technique that knows how to very efficiently
  solve all linear constraints.

Apply one of our four techniques above for what to try
when getting stuck.
"""

"""
===== Complex data types =====

We've seen the following data types in Z3:
- Int
- Real
- Bool

Z3 has many more complex data types and operations!
- Strings
- Arrays
- Sets
- Fixed-width integers (BitVec)

Z3 also has many operations on these data types.
Remember how with integers, <, +, == etc. have to be overloaded as
operations on Z3 variables?
We do the same thing with these complex data types.

Q: why do we need all these data types and operations?

A: We need these data types to be able to model real programs,
since real programs use strings, arrays, fixed-width integers,
etc.

Security reasons...
"""

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
