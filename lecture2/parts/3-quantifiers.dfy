/*
    Lecture 2, part 3:
    Quantifiers

    ===== Poll =====

    After `dafny verify` passes, suppose we run the code,
    either by running the Dafny directly or compiling it
    to Python and running that.

    Which of the following are **removed** from the compiled
    code?
    (Select all that apply)

    A) assert statements
    B) assume{:axiom} statements
    C) preconditions
    D) postconditions
    E) if statements
    F) lemmas
    G) unused method calls.

    https://forms.gle/WGj4PsyZqgVWXugv5

    .
    .
    .
    .
    .

    Note/trivia:
        things that are removed from the compiled code
        are called "ghost" statements.
        More on this later.

        E.g. actually something called a ghost method
*/

/*
So far, we think of

    verification = prove the spec true on all inputs
                                        ^^^^^^^^^^^^ implicitly a quantifier

    Let's say I have a spec with

    def f(x) returns y

        precond(x)

        postcond(x, y)

    What we're really proving is a "for all" statement, which could be
    expressed using a quantifier

        "for all x, if precond(x) then postcond(x, f(x))"

        ^^^^^^^^^ quantifier!

        quantifiers:

            forall = ∀
            exists = ∃

We might want these quantifiers more generally - fortunately,
Dafny gives us direct access to statements involving quantifiers.

Q: Are there things we can't express using quantifiers?

A: Yes: for example, abs() is surjective onto nonnegative integers:

    Surjective:
    for all outputs y (that are nonnegative), there exists at least one input x
    such that
    f(x) = y.
*/

function abs(x: int): int {
    if x > 0 then x else -x
}

// method Abs(x: int) returns (y: int)
//     // You might convince yourself: there's no way to say this
//     // just with a precondition and a postcondition
//     requires ...
//     ensures ...
// }

predicate is_nonnegative(y: int) {
    y >= 0
}

lemma AbsSurjective()
ensures forall y: int :: is_nonnegative(y) ==> exists x :: abs(x) == y
{
    // Some odd syntax
    // We need to help Dafny out by providing the proof.

    // This is a proof (!)
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
    // assert abs(-y) == y; // also works
}

/*
    Dafny is now acting as a proof verification tool!

    We wrote a proof, and Dafny checked that the proof is correct.

    Let's see some simpler examples.

    Logic with quantifiers is called "first-order logic".

    Eventually, it will become clear that we can also verify arbitrary programs using first-order logic.

    Practically speaking - forall/exists come up frequently when verifying
    code involving arrays, strings, sequences, and any other more complex
    data structures.

    Here's a small sneak peak:

    Below, we wrote a function to add up the absolute value sum of a list, like

    AbsSum([x, y, z]) = abs(x) + abs(y) + abs(z).

    The spec here says that AbsSum is an upper bound on all individual elements of the list.
*/

method AbsSum(l: seq<int>) returns (result: int)
// requires |l| == 3
ensures forall i :: 0 <= i < |l| ==> result >= abs(l[i])
{
    var sum: nat := 0;
    for j := 0 to |l|
    // While loop version:
    // var j := 0;
    // while j < |l|
        // Unfamiliar concept: loop invariant
        // Think of this as pre and postconditions on the loop. We will
        // see more on this in the next part.
        // Note: the following line would be needed for a while loop,
        // added implicitly for a for loop.
        // invariant j <= |l|
        invariant forall i :: 0 <= i < j ==> sum >= abs(l[i])
    {
        // assert forall i :: 0 <= i < j ==> sum >= abs(l[i]);
        sum := sum + abs(l[j]);
        // While loop version:
        // j := j + 1;
        // assert forall i :: 0 <= i < j ==> sum >= abs(l[i]);
    }

    // assert forall i :: 0 <= i < |l| ==> result >= abs(l[i]);

    // result := sum;
    // equiv. syntax:
    return sum;
}

/*
    We can also rewrite our specs for abs ...
*/

// Another way of writing...
lemma AbsCorrectQuantifiers() {
    assert forall x :: abs(x) >= 0;
    assert forall x :: abs(x) == x || abs(x) == -x;
    // ^^ quantifiers!

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
