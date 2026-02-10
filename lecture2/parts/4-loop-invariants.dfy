/*
Lecture 2, Part 4:
Loop invariants

Recap:
We have seen:

- How to write Dafny code with preconditions and postconditions
- Writing assertions, lemmas, and unit tests
- Function/method distinction

The MinFour and ArgMinFour were a bit artificial as they only work with integers.
It would be nice to generalize our functions to work with lists!
Can we?
This requires: loop invariants!

Continuing the 4-step process:
1. Decide on an implementation (or port an existing one); write in Dafny
2. Decide on a spec; write pre/postconditions
3. Write unit tests
4. Help Dafny with the proof (as needed)

=== Poll ===

(Related to some of the discussion from last time.)

Consider the following snippet of a program:

assert P;
assert Q;

Suppose that P implies Q (logically) but Dafny verification passes only for P, and not Q. Which of the following is a possible reason for this? (Select all that apply)

https://forms.gle/q5WiyPwxyoU7KtgMA

.
.
.
.
.
*/

/*
    Exercise:
    Generalize the MinFour implementation and specs
    to lists of integers, rather than just four.

    Two "list"-y types in Dafny: array and seq

    List syntax:
    array<int>
    a.Length
    a[i]

    We did step 1, now step 2:
    Write a precondition and postcondition for MinList
    that matches what we had for MinFour.
    (Your pre and postcondition don't have to be valid Dafny, but they should be
    correct logically)
*/

method MinList(a: array<int>) returns (result: int)
    // TODO
    // example syntax:
    // forall i :: 0 <= i < a.Length ==> a[i] == 0
    // Precondition:
    // requires false
    requires a.Length >= 1
    // Postcondition
    // ensures false
{
    // How we would do this with imperative code?
    // Iteratively: for x in array a, if x < current min, set min := x
    var min := a[0];
    // a.Length - for arrays, |a| would be for sequences.
    for i := 1 to a.Length {
        if a[i] < min {
            min := a[i];
        }
    }

    return min;
}

/*
=== What is a loop invariant? ===

A loop invariant is like a pre/postcondition for the loop body.

A loop invariant must satisfy the following 3 conditions:
1. Loop invariant is true before first entering the loop
    precondition ==> invariant

2. If the loop condition is true, then the loop invariant is preserved
    (loop condition) && invariant holds at the start ===> invariant holds at end

3. If the loop condition is false, then the loop invariant implies the postcondition
    !(loop condition) && invariant holds ==> postcondition.

*/

method ArgMinList(a: array<int>) returns (result: int)
    // TODO
    // Precondition:
    requires false
    // Postcondition
    ensures false
{
    // TODO
}


/*
    (If not already done)
    Write a unit test for the ArgMinList and MinList functions.

    (Compile time unit test - checked at compile time, not executed)
*/

method TestMinList() {
}

/*
    Exercise

    Here is another method and a spec.

    1. Which of the following is a valid loop invariants?

    A. y == 0
    B. y >= 0
    C. y <= x
    D. y != x + 1
    E. True
    F. False

    2. Try them out below. How do violations of (i), (ii), and (iii) appear in
    the Dafny VSCode extension?

    3. If none of the above is correct - write the correct invariant.
*/

// method FindSuccessor(x: int) returns (y: int)
// requires x >= 0
// ensures y == x + 1
// {
//     y := 0;
//     while y <= x
//     invariant ...
//     {
//         y := y + 1;
//     }
//     return y;
// }

/*
    Recap

    - We saw examples of working with arrays: a[i], a.Length etc.

    - We defined loop invariants and saw them in action

        + Loop invariant must satisfy properties (i), (ii), (iii)

        + Practice with loop invariants

    - We discussed the computationally bounded nature of Dafny, and how
      when writing unit tests we may need additional assertions to walk through
      and help Dafny prove the assertion

        + A more general debugging technique: find out what Dafny knows, and what it doesn't.
*/

/*
    Additional loop invariant exercises

    1. Go back to the AbsSum example from part 3. Add a loop invariant.

    2. Write and prove a function to compute the gcd of two integers.
*/
