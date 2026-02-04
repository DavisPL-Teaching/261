/*
Lecture 2, Part 2:
Verification methodology.

=== Dafny methodology ===

    (Optional) 1. Start with pseudocode, or whatever code you would have written in your favorite
       programming language (C/C++, Python, etc.)

    2. Write or rewrite the code in Dafny

    3. Write the spec:
        What do we want to verify?
            Add pre and postconditions to each method

    4. Write some unit test <-- important step I added

    5. Add proofs <-- we have not needed this at all so far
        but it is where ~90% of the effort lies in practice.
        (assertions, loop invariants, ...)
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
// what should the spec be?
// requires ...
// requires ...
ensures result <= a && result <= b && result <= c && result <= d
// ensures ...
ensures result == a || result == b || result == c || result == d
{
    var min := a;
    if b < min {
        min := b;
    }
    if c < min {
        min := c;
    }
    if d < min {
        min := d;
    }

    return min;
}

// Write some unit tests
method TestMinFour() {
    // TODO
}

// ***** Where we ended for Jan 29 *****
// (Still have to complete steps 2-4 for the above)
/*
    === Before we continue: Poll question ===

    This poll question is about the function/method distinction.

    Recall the method ReturnPositiveNumber() from part 1.
    Here is a similar method:
*/

method ReturnLargerNumber(x: int) returns (y: int)
    requires x >= 0
    ensures y > x
{
    return x + 1;
}

/*
    Which of the following is provable in Dafny about this method given its spec?
    (Select all that apply)

    A. ReturnLargerNumber applied to 0 is positive
    B. ReturnLargerNumber applied to 0 is equal to 1
    C. ReturnLargerNumber applied to a positive number is positive
    D. ReturnLargerNumber applied to x equals x + 1
    E. If ReturnLargerNumber(5) is called twice resulting in y1 and y2, then y1 == y2
    F. In any context where ReturnLargerNumber(x) is called, x >= 0.

    https://forms.gle/ySfx55HVhaJaTabS9

    ==========

    .
    .
    .
    .
    .

    (On request: we can test any of these out below.)
*/

// method TestReturnLargerNumber(x: int)
//     requires x >= 0
// {
//     var y1 := ReturnLargerNumber(x);
//     var y2 := ReturnLargerNumber(x);
//     assert y1 > 0;
//     assert y2 > 0;
//     assert y1 > x;
//     assert y1 == y2;
// }

/*
    Exercise 2:
    Write a function to compute the *argument minimum* of four integers.

    Note: the "argument min" is the index of the smallest integer.

    Let's say:
    index of a is 0, b is 1, c is 2, and d is 3.

    Start by writing the imperative code
*/

method ArgMinFour(a: int, b: int, c: int, d: int) returns (result: int)
// requires ...
// ensures ...
requires false
{
}

/*
    Exercise 3:
    Write unit tests for the above.
*/

method TestMin() {
    // var result1 := MinFour(1, 2, 3, 4);
    // assert result1 == 1;
    // var result2 := MinFour(3, 3, 3, 4);
    // assert result2 == 3;
}

method TestArgMin() {
    // var result1 := ArgMinFour(1, 2, 3, 4);
    // assert result1 == 0;
    // var result2 := ArgMinFour(3, 3, 3, 4);
    // assert result2 == 0 || result2 == 1 || result2 == 2;
}

/*
    Some discussion

There are at least 3 possible design choices for ArgMin:
- Leave the behavior underspecified; has to return one min index, any is OK on tie
- Exclude the behavior by adding a precondition (require all vals are distinct)
- Specify the behavior in the case of ties: e.g., return the first or the last index
  of a min value.
*/
