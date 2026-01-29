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

Continuing the 3-step process:
1. Decide on an implementation (or port an existing one); write in Dafny
2. Decide on a spec; write pre/postconditions
3. Help Dafny with the proof (as needed)

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
    Keep track of a minimum value
    Iterate through the array, update the min when a smaller value is encountered
*/

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

method MinList(a: array<int>) returns (result: int)
// Precondition: array is nonempty
requires a.Length > 0
// Postcondition: for all i between 0 and the length, the result should be <= a[i]
// and, there exists an i between 0 and the length, such that the result is == a[i].
ensures forall i :: 0 <= i < a.Length ==> result <= a[i]
ensures exists i :: 0 <= i < a.Length && result == a[i]
{
    var min := a[0];
    // invariant should be true here
    for i := 0 to a.Length
    invariant forall j :: 0 <= j < i ==> min <= a[j]
    invariant 0 <= i <= a.Length // implicitly added for for loops - so not technically needed.
    // Option 1:
    invariant i == 0 ==> min == a[0]
    invariant i >= 1 ==> exists j :: 0 <= j < i && min == a[j]
    // Option 2:
    // invariant exists j :: 0 <= j < a.Length && min == a[j]
    {
        if a[i] < min {
            min := a[i];
        }

        // implicit: at the end of each loop, we do i := i + 1

        // invariant should be true here
        // what is true about the array and the variables min, i at this point in the program?
        // min <= a[0]
        // min <= a[0], a[1], ..., a[i-1]
        // i is between 0 and a.Length -- 0 <= i < a.Length
        // min is an element of the array that we've looked at so far: min == a[0], a[1], ..., a[i-1].
    }
    return min;
}

method ArgMinList(a: array<int>) returns (result: int)
requires a.Length > 0
// What to do about ties?
// In the case of ties: return the first index.
ensures 0 <= result < a.Length
ensures forall i :: 0 <= i < a.Length ==> a[result] <= a[i]
ensures forall i :: 0 <= i < result ==> a[result] < a[i]
{
    var min := a[0];
    var min_index := 0;
    for i := 1 to a.Length
    invariant 0 <= min_index < i
    // proof also goes through with the weaker: 0 <= min_index < a.Length.
    invariant min == a[min_index]
    invariant forall j :: 0 <= j < min_index ==> min < a[j]
    invariant forall j :: 0 <= j < i ==> min <= a[j]
    {
        if a[i] < min {
            min := a[i];
            min_index := i;
        }
    }
    result := min_index;
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
    var a0 := new int[][1]; // new keyword: allocates an array on the heap
    var y0 := MinList(a0);
    assert y0 == 1;
    var a1 := new int[][1, 0, 1];
    var y1 := MinList(a1);
    // Helping Dafny out...
    // assert forall i :: 0 <= i < a1.Length ==> y1 <= a1[i];
    // assert exists i :: 0 <= i < a1.Length && y1 == a1[i];
    // assert a1.Length == 3;
    // assert forall i :: 0 <= i < 3 ==> y1 <= a1[i];
    // assert exists i :: 0 <= i < 3 && y1 == a1[i];
    // assert y1 <= a1[0];
    assert y1 <= a1[1];
    // assert y1 <= a1[2];
    // assert y1 <= 0;

    assert y1 == 0;
    // var a2 := new int[][5, 4, 3, 2, 1];
    // var y2 := MinList(a2);
    // assert ...
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
