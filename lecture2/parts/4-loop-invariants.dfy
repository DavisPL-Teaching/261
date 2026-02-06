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

Continuing the -step process:
1. Decide on an implementation (or port an existing one); write in Dafny
2. Decide on a spec; write pre/postconditions
3. Write unit tests
4. Help Dafny with the proof (as needed)

We did step 1, now step 2:

=== Poll ===

Write a precondition and postcondition for MinList
that matches what we had for MinFour.
(Your pre and postcondition don't have to be valid Dafny, but they should be
 correct logically)
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

    Pseudocode:
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
    Additional practice with loop invariants:

    Exercise 5:
    (Skip for time)
    Write a function to compute the gcd of two integers.
*/

/*
    Exercise 6
    Write a unit test for the ArgMinList and MinList functions.

    (Compile time unit test - checked at compile time, not executed)

    What happens?
    This will lead to a topic that we will discuss next.
*/

method TestMinList() {
}

/*
    Recap

    - We saw examples of working with arrays: a[i], a.Length etc.
    - We defined loop invariants and saw them in actino
    - We discussed the computationally bounded nature of Dafny, and how
      when writing unit tests we may need additional assertions to walk through
      and help Dafny prove the assertion
    - This is a more general debugging technique: find out what Dafny knows, and what it doesn't.
*/
