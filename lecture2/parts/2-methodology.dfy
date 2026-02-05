/*
Lecture 2, Part 2:
Verification methodology.

=== Dafny methodology ===

    0. (Optional) Start with pseudocode
        (or whatever code you would have written in your favorite programming language, C/C++, Python, etc.)

    1. Write the code in Dafny

    2. Write the spec:
        What do we want to verify?
            Add pre and postconditions to each method

    3. Write some unit test <-- important step I added

    4. Add proofs <-- we have not needed this at all so far
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

// predicate min_post(result: int, a: int, b: int, c: int, d: int) {
//     result <= a && result <= b && result <= c && result <= d
// }

method MinFour(a: int, b: int, c: int, d: int) returns (result: int)
// Spec:
// what should the spec be?
// requires ...
// requires ...
// requires true
// requires false
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

    // Equivalent:
    // result := min;
}

// ***** Where we ended for Jan 29 *****
// (Still have to complete steps 2-3 for the above)

// Write some unit tests
method TestMinFour() {
    // 1, 2, 3, 4
    var test1 := MinFour(1, 2, 3, 4);
    assert test1 == 1;

    // suggestion... a expression is a function... that should have no effect?

    // This is the method/function distinction!

    // In an expression context, we can only evoke functions, not methods.

    // Assertions make statements about expressions only.

    // Q: Why does Dafny do it this way? Why prevent methods in an expression
    // context?

    // - methods only summarize pre/postconditions, they don't work for
    //   storing or determining the actual result
    // - methods might have side effects!
    //   When calling a method... a "side effect" could occur...
    //       ... program state could be modified
    //       ... I/O could occur (e.g., printing some info to the terminal,
    //                            accessing the filesystem/network)
    //       ... other things could happen unrelated to the input/output
    //           behavior of the function

    // Also: assertions in Dafny get erased at compile time!
    // once I actually run the code ... all assertions get deleted
    // if assertions were allowed to call methods, then deleting the assertions
    // could change the behavior of the program.

    /*
        Another Q: why even write this unit test?
        What's the point, didn't we already prove that the code
        is correct on all inputs?

        Suggestions:
        - It helps check that the method works as we expected?
        - Maybe our specs are not enough!

            We're proving that the spec reflects the expected behavior!

            2 things that very often could go wrong when verifying some code:

            1) precond is too strong

            2) postcond is too weak
               strongest possible postcondition, i.e. full functional correctness

    Two other types of errors in the spec:
        precond is too weak, postcond is too strong

    But both of these will be detected when verifying the method itself
    (no green bar).
    */
}

// What about step 4?
// In this particular case, Dafny is smart enough to come up with the
// proof on its own. So , we don't need to do any additional work.

/*
    === Before we continue: Poll question ===

    This poll question is about the function/method distinction.

    Recall the method ReturnPositiveNumber() from part 1.
    Here is a similar method:
*/

method ReturnLargerNumber(x: int) returns (y: int)
    requires x >= 0
    ensures y > x
    // Uncomment for full functional correctness
    // ensures y == x + 1
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

method TestReturnLargerNumber(x: int)
    requires x >= 0
{
    // var x_other := MinFour(x + 1, x + 2, x + 3, x - 4);
    // var y := ReturnLargerNumber(x_other);

    var y1 := ReturnLargerNumber(x);
    var y2 := ReturnLargerNumber(x);
    assert y1 > 0;
    assert y2 > 0;
    assert y1 > x;
    // assert y1 == y2;

    // assert y1 == x + 1;

    var y3 := ReturnLargerNumber(0);
    // assert y3 != 1;
    // assert y3 == 1;

    // var y4 := ReturnLargerNumber(-1);
    // assert y4
}

/*
    This one is slightly more interesting ... and brings up something
    interesting about methods being black boxes.

    Exercise 2:
    Write a function to compute the *argument minimum* of four integers.

    Note: the "argument min" is the index of the smallest integer.

    Example:
        4, 1, 2, 3
    we should return:
        Index = 1

    Let's say:
    index of a is 0, b is 1, c is 2, and d is 3.

    Start by writing the imperative code
*/

method ArgMinFour(a: int, b: int, c: int, d: int) returns (result: int)
// requires ...
// requires false
ensures result == 0 || result == 1 || result == 2 || result == 3
ensures result == 0 ==> a <= b && a <= c && a <= d
ensures result == 1 ==> b <= a && b <= c && b <= d
ensures result == 2 ==> c <= a && c <= b && c <= d
ensures result == 3 ==> d <= a && d <= b && d <= c
{
    var min := a;
    var idx := 0;

    if b < min {
        min := b;
        idx := 1;
    }
    if c < min {
        min := c;
        idx := 2;
    }
    if d < min {
        // min := d;
        idx := 3;
    }

    return idx;
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
