/*
    Example from piazza and poll.

    === Poll ===

    Consider the program

    HEAD;
    while P
        invariant Inv
    {
        BODY;
    }
    FOOT;

    Suppose two possible invariants are I1 and I2, and
    I1 is *strictly* stronger than I2.
    (meaning some programs satisfy I2 but not I1.)

    Which of the following are possible?
    (select all that apply)

    A. I1 is a valid loop invariant, I2 is not
    B. I2 is a valid loop invariant, I1 is not
    C. Both I1, I2 are valid loop invariants
    D. Neither I1, I2 are valid loop invariants

    https://forms.gle/9Y95S8ftdoxLaTNn8

    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .

    === Example from Piazza (last Thursday) ===

    I made a point in class of saying that the traces on which you evaluate an invariant do not always correspond to real executions, but I didn't provide an example!

    Here is a (possibly a bit contrived) one.
    Consider the following variant of the FindSuccessor example from before, but where we replace `while y < x + 1` with `while y != x + 1` below.

    (you can ignore the `decreases` clauses for now - these are unrelated to the present discussion)

    Functionally speaking, this is equivalent to the code from before! but the replacement of the while condition with `y != x + 1` changes which invariants are valid. Specifically, consider the potential example invariant

        y < x + 10

    see below:
*/

method FindSuccessor(x: int) returns (y: int)
requires x >= 0
ensures y == x + 1
decreases * // ignore this for now
{
    y := 0;
    while y != x + 1
    decreases * // ignore this for now
    // Invalid invariant - even though it's true on every real execution of the program!
    // invariant y < x + 10
    {
        y := y + 1;
    }
}

/*
    Notice that, this invariant is actually true on all executions of the program! it's true before the loop executes - and it's true after each time the body executes.
    However, this invariant satisfies only property (i), and not property (ii).
    The problem is the following trace which could occur in the loop body:

    ```
    // y = x + 9 here
    y := y + 1;
    // now y = x + 10
    // invariant violation!
    ```

    Notice that this trace is never possible on a real execution of the program! Nevertheless, it's a counterexample to (ii), because it indicates that the invariant is not proved by the loop body.

    This is also an example of another interesting phenomenon: that **adding additional properties that are true could actually result in going from code that verifies, to code that doesn't verify!**
    We started with code with the implicit invariant `invariant true` - and you can check that `true` actually satisfies all of properties (i)-(iii): because the loop termination condition is `y != x + 1`, so when the loop terminates, that immediately gives us the postcondition.
    But by adding the property `y < x + 10`, we go from having a valid loop invariant satisfying all of (i)-(iii) to one that satisfies only (i) and (iii), and fails (ii).

    :)
*/
