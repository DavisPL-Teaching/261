/*
    Some Dafny verification exercises

    Dafny methodology
    (from today's poll):

    - Start with pseudocode, or whatever code you would have written in your favorite
      programming language (C/C++, Python, etc.)
    - Rewrite the code in Dafny
    - What do we want to verify? Add pre and postconditions
    - Add proofs (assertions, loop invariants, ...)
      to help the verification go through (as needed)

    Dafny tutorial guide:
    https://dafny.org/latest/OnlineTutorial/guide

    Dafny reference manual:
    https://dafny.org/dafny/DafnyRef/DafnyRef
*/

/*
    Exercise 1:
    Write a function to compute the minimum of four integers.
*/

method MinFour(a: int, b: int, c: int, d: int) returns (result: int)
// Spec:
// requires true // no precondition
// requires false
ensures result <= a && result <= b && result <= c && result <= d
ensures result == a || result == b || result == c || result == d
{
    if a <= b && a <= c && a <= d {
        return a;
        // Equiv. syntax:
        // result := a;
        // return;
    }
    if b <= c && b <= d {
        return b;
    }
    if c <= d {
        return c;
    }
    return d;
}

/*
    Exercise 2:
    Write a function to compute the *argument minimum* of four integers.

    Note: the "argument min" is the index of the smallest integer.

    Let's say:
    index of a is 0, b is 1, c is 2, and d is 3.

    Start by writing the imperative code
*/

method ArgMinFour(a: int, b: int, c: int, d: int) returns (result: int)
// What should the spec be?
// requires a != b && a != c && a != d && b != c && b != d && c != d
// ensures (result == 0 && a <= b && a <= c && a <= d)
//     || (result == 1 && b <= a && b <= a && b <= d)
//     || (result == 2 && c <= a && c <= b && c <= d)
//     || (result == 3 && d <= a && d <= b && d <= c)
ensures 0 <= result <= 3
ensures result == 0 ==> (a <= b && a <= c && a <= d)
ensures result == 1 ==> (b <= a && b <= c && b <= d)
ensures result == 2 ==> (c <= a && c <= b && c <= d)
ensures result == 3 ==> (d <= a && d <= b && d <= c)
// Note: cannot do a == MinFour(a, b, c, d)
// b.c. cannot call method in a formula/expression context.
// requires ...
// ensures ...
// Note: one way to mark a function as unimplemented:
{
    // Impl. 1: via direct comparison
    // if a <= b && a <= c && a <= d {
    //     return 0;
    // }
    // if b <= c && b <= d {
    //     return 1;
    // }
    // if c <= d {
    //     return 2;
    // }
    // return 3;

    // Or we could use the previous function...
    // Impl 2.: using the previous function
    var y := MinFour(a, b, c, d);
    if y == a {
        return 0;
    } else if y == b {
        return 1;
    } else if y == c {
        return 2;
    } else if y == d {
        return 3;
    } else {
        // This branch is unreachable
        assert false;
    }
}

/*
    Exercise 3:
    Write unit tests for the above.
*/

method TestMin() {
    var result1 := MinFour(1, 2, 3, 4);
    assert result1 == 1;
    var result2 := MinFour(3, 3, 3, 4);
    assert result2 == 3;
}

method TestArgMin() {
    var result1 := ArgMinFour(1, 2, 3, 4);
    assert result1 == 0;
    var result2 := ArgMinFour(3, 3, 3, 4);
    assert result2 == 0 || result2 == 1 || result2 == 2;
}

// Summary: There were 3 possible design choices for ArgMin:
// - Leave the behavior underspecified; has to return one min index, any is OK on tie
// - Exclude the behavior by adding a precondition (require all vals are distinct)
// - Specify the behavior in the case of ties: e.g., return the first or the last index
//   of a min value.

/*
    Exercise 4:
    Generalize the above to lists of integers, rather than just four.

    Two "list"-y types in Dafny: array and seq

    List syntax:
    array<int>
    a.Length
    a[i]

    Pseudocode:
    Keep track of a minimum value
    Iterate through the array, update the min when a smaller value is encountered
*/

// ***** Where we ended for today *****

/*
=== May 6 ===

Recap from last time:
We saw:
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

https://forms.gle/eMc6TRonvMUUHXDc9
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

    ***** Where we ended for today *****
*/

/*
    Additional exercises
    (Optional or skip for time)

    Exercise 7
    Let's try to write a verified version of the
    four-numbers problem solver from HW1.

    Full disclosure: I didn't have a chance to try this offline.
    It is possible, but may be fairly difficult.
*/

/*
=== Poll (to wrap up this section) ===

Consider the following snippet of a program:

assert P;
assert Q;

Suppose that P implies Q (logically) but Dafny verification passes only for P, and not Q. Which of the following is a possible reason for this? (Select all that apply)

https://forms.gle/d4fSLLh3JUaXWpgk9

=== End notes ===

What are the main limitations of Dafny?

1. High effort to write and verify real-world software
2. Q is true, but not provable from P?

(1) is true, but not fundamental.
(2) is actually possible and is more fundamental.

To understand the more fundamental limits of Dafny,
then, we need to go back to the logics on which Dafny is built,
and in particular to first-order logic (FOL).
See the file fol.dfy.
*/
