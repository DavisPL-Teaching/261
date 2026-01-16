"""
=== Extra Poll ===

Sort the following specifications in Hypothesis by which row is stronger than each column.
That is, check the box if the specification in that row is stronger than the specification in that column.

1. @given(x==1 or x==2), assert f(x) == x
2. @given(x==1), assert f(x) == x
3. @given(x==2), assert f(x) == x
4. @given(x==3), assert f(x) == x
5. f does not crash on inputs x==1 and x==2.

Poll link:

Answers?
.
.
.
.
.

1 is stronger than 1 because any spec is stronger than itself

1 and 2: is 1 stronger than 2 or 2 stronger than 1?

1 is stronger than 2:

    def stronger:

        "any program satisfying 1 satisfies 2"

    - 1 is testing the program f on a *broader range* of inputs

        if 1 is the case, then I can in particular run
        the program on x == 1, and I will get spec 2.

        Similarly, if 1 is in the case, then I can in particular
        run the program on x == 2, and I will get spec 3.

Question: but isn't "x == 1 or x == 2" weaker than just "x == 1"?

    If we have a weaker statement about the input, we get a stronger
    spec!

    Because there are more inputs that the program has to
    follow, we get a stronger spec.

    If you expand the set of inputs, you get a stronger spec.

    as a venn diagram?
    spec S1 is stronger than S2
    means
    the set of programs satisfying S1 is a subset of the set
    of programs satisfying S2, which means

    S1 (thought of as a set of programs) is a smaller circle
    inside S2.

Another way of thinking about it:

    1 is saying: f(1) == 1 and f(2) == 2
    2 is saying: f(1) == 1
    3 is saying: f(2) == 2

so 1 is stronger than 2 and 3.

Answers:
    1 stronger than 1, 2, 3, 5
    2 is stronger than 2
    3 is stronger than 3
    4 is stronger than 4
    5 is stronger than 5
"""
