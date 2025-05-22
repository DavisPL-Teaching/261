/*
    Round to 100
*/

predicate invariant_cond(n: int, x: int, y: int) {
    0 <= n < 100 && (y + n) % 100 == 0 && (y + n) < x + 100
}

predicate invariant_cond_post(n: int, x: int, y: int) {
    invariant_cond(n, x, y + 1)
}

lemma LemmaOne(x: int, y: int)
requires x == y
ensures exists n :: invariant_cond(n, x, y);
{
    // assert invariant_cond(0, x, y);
    // TODO: come back and prove
    assume{:axiom} false;
}

lemma LemmaTwo(x: int, y: int)
requires exists n :: invariant_cond(n, x, y)
requires x <= y < x + 100
requires (y % 100 != 0)
ensures exists n :: invariant_cond_post(n, x, y)
{
    // TODO: come back and prove
    assume{:axiom} false;
}

method RoundTo100(x: int) returns (y: int)
    ensures y % 100 == 0
    ensures x <= y < x + 100
    decreases *
{
    y := x;
    LemmaOne(x, y);
    assert exists n :: invariant_cond(n, x, y);
    while (y % 100 != 0)
        // invariant
        invariant x <= y < x + 100
        invariant exists n :: invariant_cond(n, x, y)
        // invariant ((y % 100) == 0) || ((x % 100) <= (y % 100))
        invariant y < x + 100
        decreases *
    {
        assert exists n :: invariant_cond(n, x, y);

        // What needs to be true here?

        LemmaTwo(x, y);

        // what should be true here?
        // phi(y + 1) should be true here.
        assert exists n :: invariant_cond_post(n, x, y);

        y := y + 1;

        // if I want: phi(y)
        assert exists n :: invariant_cond(n, x, y);
    }
    // What do we know here?
    // (y % 100 == 0)
    // y >= x
}


/*
    One of the example questions on the exam.
*/

// methods F1()

method F1(x: int) returns (y: int)
// ensures y == 2 * (x + 1)
ensures y >= 2 * x
{
    y := 2 * (x + 1);
}

method F2(x: int) returns (y: int)
// ensures y == 2 * (x + 1)
ensures y >= 2 * x
{
    y := 2 * x + 2;
}

method FlipCoin() returns (b: bool)
{
    return true;
}

// What will happen when I uncomment the assertions below?
method TestF1F2Equivalent(x: nat) {
    // assert F1(x) == F2(x);

    var y1 := F1(x);
    var y2 := F1(x);
    // assert y1 == y2;
    // assert y1 >= 2 * x;
    // assert y2 >= 2 * x;
    // assert y1 == 2 * x + 2;
    // assert y2 == 2 * x + 2;
    // assert y1 == y2;
}
