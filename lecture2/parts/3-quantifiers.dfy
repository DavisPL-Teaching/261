/*
    Lecture 2, part 3:
    Quantifiers

So far, we think of

    verification = prove the spec true on all inputs

Q: Are there things we can't express this way?

A: Yes: for example, abs() is surjective onto nonnegative integers:
*/

function abs(x: int): int {
    if x > 0 then x else -x
}

predicate is_nonnegative(y: int) {
    y >= 0
}

lemma AbsSurjective()
ensures forall y: int :: is_nonnegative(y) ==> exists x :: abs(x) == y
{
    // Some odd syntax
    // Commenting the below out - Dafny cannot prove this
    // We need to help Dafny out by providing the proof.
    forall y: int | is_nonnegative(y)
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
    // asserts abs(-y) == y; // also works
}

/*
    Before we discuss the syntax above...
    let's see some simpler examples.

    Eventually, it will become clear that we can also verify arbitrary programs
    and this verification will be built on first-order logic.

    Here's a small sneak peak:

    Below, we wrote a function to add up the absolute value sum of a list, like

    AbsSum([x, y, z]) = abs(x) + abs(y) + abs(z).

    The spec here says that AbsSum is an upper bound on all individual elements of the list.
*/

method AbsSum(l: seq<int>) returns (result: int)
ensures
    forall i :: 0 <= i < |l| ==> result >= abs(l[i])
{
    var sum: nat := 0;
    for j := 0 to |l|
    // While loop version:
    // var j := 0;
    // while j < |l|
        // Unfamiliar concept: loop invariant
        // Think of this as pre and postconditions on the loop. We will
        // see more on this later.
        // Note: the following line would be needed for a while loop,
        // added implicitly for a for loop.
        // invariant j <= |l|
        invariant forall i :: 0 <= i < j ==> sum >= abs(l[i])
    {
        sum := sum + abs(l[j]);
        // While loop version:
        // j := j + 1;
    }
    result := sum;
    // equiv. syntax:
    // return sum;
}

/*
    We can also rewrite our specs for abs ...
*/

// Another way of writing...
lemma AbsCorrectQuantifiers() {
    assert forall x :: abs(x) >= 0;
    assert forall x :: abs(x) == x || abs(x) == -x;
    // ^^ quantifiers!
    //    this takes us away from quantifier-free logics to "first-order logic" (FOL).
    // Try modifying this.

    // What about this?
    // assert exists x :: abs(x) == 1;
    // No proof! More on this soon.

    // Sadly quantifiers are hard! So we have to help Dafny out sometimes.
    // We will need to get our hands dirty with the proofs.

    // Can we add an assertion which helps Dafny to prove the above?
}

// Another way of writing the correctness spec for Abs
lemma AbsCorrect2()
// ensures = a postcondition
ensures forall x :: abs(x) >= x
ensures forall x :: abs(x) == x || abs(x) == -x
{}

/*
    Why do we need quantifiers?

    Another example using abs():
    Suppose we want to show that abs() is increasing:

        forall x. forall y. 0 <= x < y ==> abs(x) < abs(y)

    Only forall statements in front! So we can do this with a validity check:
*/

lemma AbsIncreasing()
ensures
    forall x :: forall y :: 0 <= x < y ==> abs(x) <= abs(y)
{
    // Proof goes through - QED
}
