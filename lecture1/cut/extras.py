"""
Additional cut content

This will most likely be skipped for time.
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
