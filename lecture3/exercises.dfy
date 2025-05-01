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

method MinList(a: array<int>) returns (result: int)
requires a.Length >= 1
{
    var min := a[0];
    for i := 0 to a.Length {
        if a[i] < min {
            min := a[i];
        }
    }
    return min;
}

// ***** Where we ended for today *****

method ArgMinList(a: array<int>) returns (result: int)
requires false
{
    // TODO
}

/*
    Exercise 5:
    Write a function to compute the gcd of two integers.
*/

/*
    Exercise 6:
    Let's try to write the four-numbers problem solver from HW1.

    Note: I didn't have a chance to try this offline!
    So it may or may not be easy.
*/
