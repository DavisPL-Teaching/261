/*
    Intro to first-order logic in Dafny.
*/

/*
    First-order logic generalizes the concept of satisfiability and validity from last time.

    Z3 can take as input formulas in first-order logic, but it often isn't very good about solving them!
    (Why?)

    So, for general program verification, we often resort to more powerful techniques where we actually
    work with the tools to help prove the property we have in mind. This is called "interactive verification" or "interactive theorem proving".
*/

/*
    Example.
    Why do we need quantifiers?

    We saw an example with the pigenohole principle where it was most natural
    to express using quantifiers.

    Example using abs():
    Suppose we want to show that abs() is increasing:

        forall x. forall y. 0 <= x < y ==> abs(x) < abs(y)

    Only forall statements in front! So we can do this with a validity check:
*/

function abs(x: int): int {
    if x > 0 then x else -x
}

// Note: more common to see it as a method.
// We will start with functions, more on methods later
// method AbsMethod(x: int) returns (y: int)
//     ensures y >= 0
//     ensures y == x || y == -x
// {
//     if x > 0 {
//         y := x;
//     } else {
//         y := -x;
//     }
// }

lemma AbsCorrect()
ensures forall x :: abs(x) >= x
ensures forall x :: abs(x) == x || abs(x) == -x
{}

lemma AbsIncreasing()
ensures
    forall x :: forall y :: 0 <= x < y ==> abs(x) <= abs(y)
{}

/*
So far, we could do all of this with just validity. (Why?)

Are there things we can't express using only validity?

Yes: for example, abs() is surjective onto nonnegative integers:
*/

predicate is_positive(y: int) {
    y >= 0
}

lemma AbsSurjective()
ensures forall y: int :: is_positive(y) ==> exists x :: abs(x) == y
{
    // Some odd syntax
    forall y: int | is_positive(y)
    ensures exists x :: abs(x) == y
    {
        AbsSurjectiveFor(y);
    }
}

lemma AbsSurjectiveFor(y: int)
requires y >= 0
ensures exists x :: abs(x) == y
{
    assert abs(y) == y;
}

/*
    Eventually, it will become clear that we can also verify arbitrary programs
    and this verification will be built on first-order logic.

    Here's a small sneak peak:

    Below, we wrote a function to add up the absolute value sum of a list, like

    AbsSum([x, y, z]) = abs(x) + abs(y) + abs(z).

    The spec here says that AbsSum is an upper bound on all individual elements of the list.
*/

method AbsSum(l: seq<nat>) returns (result: nat)
ensures
    forall i :: 0 <= i < |l| ==> result >= abs(l[i])
{
    var sum: nat := 0;
    for j := 0 to |l|
        invariant j <= |l|
        invariant forall i :: 0 <= i < j ==> sum >= abs(l[i])
    {
        sum := sum + abs(l[j]);
    }
    result := sum;
}

/*
    Above: we have a program and we have proved it correct!

    But let's go deeper to understand on a fundamental level:
    - What is a proof?
    - What is a program?
*/
