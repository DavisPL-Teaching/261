/*
    Lecture 2, part 2:
    Quantifiers
*/

function abs(x: int): int {
    if x > 0 then x else -x
}

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
}

// Another way of writing the correctness spec for Abs
lemma AbsCorrect2()
// ensures = a postcondition
ensures forall x :: abs(x) >= x
ensures forall x :: abs(x) == x || abs(x) == -x
{}

/*
    ===== First-order logic =====

    First-order logic generalizes the grammars we have seen so far by adding quantifiers:
    recall:
        φ ::= φ ^ φ | φ v φ | !φ | Expr == Expr | rel(Expr, Expr, ..., Expr)
    Now we have:
        | forall x. φ
    and
        | exists x. φ.

    Example.
    Why do we need quantifiers?

    Example using abs():
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
