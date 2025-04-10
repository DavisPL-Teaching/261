"""
Additional cut content
"""

"""
===== Review on writing specs =====

Some review:
- We talked more about writing specs
- The same function can have multiple specs, and it can have
  incorrect specs
- The process of writing a spec can be a good tool for debugging
  BOTH problems with the function, and problems with the spec.

Also, a *different* function can satisfy the same specification
"""

def list_product_2(l):
    result = 1
    l.reverse()
    for x in l:
        result *= x
    return result

# Fixing the average function

def fixed_average(l):
    l_modified = [x / len(l) for x in l]
    return sum(l_modified)
    # (could also use a built-in)
    # e.g. there's a statistics.mean function

ERROR = .000001

# @given(st.lists(st.floats(allow_nan=False, allow_infinity=False), min_size=1))
# @pytest.mark.xfail
# def test_fixed_average(xs):
#     assert min(xs) - ERROR <= fixed_average(xs) <= max(xs) + ERROR

"""
===== Review on stronger/weaker preconditions and postconditions =====

As we have seen, there are many different specifications
that can be written for a function.
We can speak about these being weaker or stronger than each other...

- Weaker: Less specific, more programs satisfy it
- Stronger: More specific, fewer programs satisfy it

Preconditions affect how many programs satisfy the spec.

Recall a precondition is an assume statement on the input.

- Weaker precondition ==> fewer programs satisfy the spec,
                      ==> stronger spec

- Stronger precondition ==> more programs satisfy the spec,
                        ==> weaker spec

The weakest possible specification is one that is always true,
regardless of the function:

    def test_weakest_spec():
        assert True

Of course, this is rather pointless, but it is a specification!

Similarly, the strongest possible specification is one that is
always false, regardless of the function:

    def test_strongest_spec():
        assert False

This is also not very useful, as it is not true of any function.
But again, it is a specification!

What about "postconditions"?

A postcondition is an assertion after executing
the program, on the program output.

If a precondition is an assumption on the input,
a postcondition is an assertion on the output.

Most/almost all of the specs we have seen before
are preconditions and postconditions.

"""

# SKIP
def count_unique(l):
    """
    Given a list l, returns the number of unique elements in l.
    """
    unique = 0
    l = l.copy()
    while l != []:
        x = l.pop()
        if x not in l:
            unique += 1
    return unique

"""
Some example postconditions:

The output is always an integer.
(weaker postcondition)

The output is between 0 and the length of the input list, inclusive.
(slightly stronger)

The output is equal to a standard implementation of the same function.
(strongest possible postcondition)
"""

"""
=== Review on assume and assert ===

Recap:

- assert means: if the property is not true,
    raise an error.

- assume means: if the property is not ture,
    ignore this branch of computation.

OR (provacatively):
- assume as "if the property is not true, destroy the universe"

=== Q+A ===

Q: Why are preconditions and assume useful?

There are going to be cases where there is an
invariant that should hold when a function is
executed. It makes sense (both for the programmer
and for the test case writer) to assume that the
property holds so that we don't consider edge
cases where it doesn't hold.

Q: Why don't you just handle every edge case in every function?

Reasons?

A1: You can't.
In Python you might be passed some weird/invalid input or type that you don't really know what it is.
def f(x):
    result = x + 1
    print(result)
    return True

Python has what's called "duck typing" which means
- if it acts like a duck and if it talks like duck,
    then it is a duck.
- if it has an x + 1 function, and x + 1 can be printed, then x is a valid input.

Response: why not just specify the types and
enforce them?
You can for example do this using something like
mypy
Mypy is a static type checker for Python.

A2: You're saving yourself work because
you're only testing for the cases you actually
care about rather than the edge cases where
some error occurs.

A3: It's inefficient!!!

If I re-check the invariants on every single
function call, my code will be very inefficient.
It's a significant performance overhead

In OOP it's common to have certain data invariants
that your class enforces.
"""

class MyPerson:
    def __init__(self, name, age):
        # What are the invariants?
        # Here, we assume self is an object
        # with a name and an age field.
        # self.name = name
        # self.age = age

        # You might even want to add other invariants, for example name should be nonempty,
        # age should be between 0 and 120
        # It's good OOP style to check these in the constructor.
        if age < 0 or age > 120:
            raise ValueError("age should be between 0 and 120")
        self.age = age
        if name == "":
            raise ValueError("name should be nonempty")
        self.name = name

    def get_age(self):
        # If you want to re-check invariants
        # on every function call.. this is annoying!
        # We first have to check that self.age and self.name exist
        # assert "age" in self.__dir__ # ???
        # We have to check that age and name
        # satisfy the invariants
        assert self.age >= 0
        assert self.age <= 120
        # ...
        return self.age

    # But this is inefficient! We have to recheck
    # on every call, and we already know that the
    # invariants hold.
    # Because we checked it -- in the constructor.
    # So if they don't hold, the user of the class
    # probably did something terribly terribly wrong

# Exercise: break the class invariant in Python
# We can do this because Python doesn't protect us
# from users misusing our invariants :(

# However, rather than check the invariants again
# on every method call, it's better style to
# assume that the user of the class is using
# your class appropriately, and it's more efficient
# because it doesn't result in unnecessary overheads
# on every method call.

"""
A3 (recap): assume reduces performance
overhead on each function call

A4: assume is also more efficient in compiled
languages because it allows compiler optimizations.

when I write a function like

def process_bool(b):
    if b:
        print("everything went OK")
    else:
        assume(False)

Another word for assume(False) is "unreachable"
Some languages have an unreachable macro: it
tells the compiler this branch of code should not
be reachable

That means the compiler can optimize the code!

Optimize the code to:
def process_bool(b):
    print("Everything went OK.")

We couldn't do this if the else branch
was an assert instead of an assume.
"""

"""
=== Advanced: components of correctness and modeling program behavior ===

Recall: correctness requires:
- Model of what the program does (in our case, a Python program)
- Model of what the program *should* do (a specification)
    -> in Hypothesis, we do this through the @given and assertion statements)

Model?
One thing we have swept under the rug:
- what is the program anyway? What program behaviors are in scope?
  (Generally speaking this is something we can leave up to the PL and compiler
   people)

Comments

"All models are wrong, some are useful."
- attributed to George E. P. Box

"The best model of a cat is a cat, especially the same cat."
- Unknown

# Other formal ways to model specifications?

We defined specifications as denoting a set of programs...
this is agnostic about what a program is (program syntax) and what it does (program semantics).

Are there more specific ways to model the program?

We will get to this topic later in more dedicated verification frameworks.

Often we are interested most in specifications which actually
relate to the program behavior
- (not, e.g., the function contains a comma inside its implementation)

For example, one can view specifications on "program behavior",
such as something like the following:

1. What is a program? For our purposes, a program is something
that you can run and stuff will happen.
It has:
- An input (some keys/words/etc. the user types)
- An output (something that happens or gets returned at the end)
May also have:
- Various other behaviors as the function is executed (e.g.,
prints stuff to stdout, opens up Google.com on your browser,
deletes your home directory, reads from id_rsa and sends it
to an unknown email address, etc.)
To summarize the output and behaviors part:
Basically, a sequence of events/behaviors happen when its executed.
^^ i.e. a program execution

2. What is a specification (or spec, for short)
WORKING DEFINITION: let's say that a
spec on program behavior
- TAKES AS INPUT: a possible input to the program
- DESCRIBES AS OUTPUT: a logical constraint on the behaviors that should occur
when the program is executed.
Specifically this implies:
a) Some sequences of behaviors are OK
b) Some sequences of behaviors are not OK.
In other words, it's a boolean property on program executions.

Relating this to preconditions/postconditions

Relating this to another concept: *assumptions* and *assertions*

(Note: assume statement in Hypothesis if we haven't covered it already)

def divide(x, y):
    return x / y

Notice I haven't asserted that y != 0
Therefore y != 0 is a precondition of this program.

Another example, in lots of C code you'll see things like

void buffer_write(x: *char, idx: i32, val: char):
    x[idx] = char

This is an important example of preconditions because if idx
is outside of the bounds of the array, there's really nothing
that the program can guarantee

A program is **correct** if
for all inputs x satisfying the preconditions,
and if I execute the program on x,
the program execution satisfies the spec.
"""
