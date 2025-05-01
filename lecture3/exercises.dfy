/*
    Some Dafny verification exercises

    Dafny methodology
    (from today's poll):

    - Start with pseudocode, or whatever code you would have written in your favorite
      programming language (C/C++, Python, etc.)
    - Rewrite the code in Dafny
    - What do we want to verify? Add pre and postconditions
    - Add proofs to help the verification go through (as needed)

    Dafny reference manual:
    https://dafny.org/dafny/DafnyRef/DafnyRef

    Dafny tutorial guide:
    https://dafny.org/latest/OnlineTutorial/guide
*/

/*
    Exercise 1:
    Write a function to compute the minimum of four integers.
*/

// method MinFour(a: int, b: int, c: int, d: int) returns (result: int)
// requires ...
// ensures ...
// {
// }

/*
    Exercise 2:
    Write a function to compute the *argument minimum* of four integers.

    Note: the argument min is
*/

method ArgMinFour(a: int, b: int, c: int, d: int) returns (result: int)
// requires ...
// ensures ...
// Note: one way to mark a function as unimplemented:
requires false
{
    // TODO
}

/*
    Exercise 3:
    Write unit tests for the above.
*/

// method TestMin() {
// }

// method TestArgMin() {
// }

/*
    Exercise 4:
    Generalize the above to lists of integers, rather than just four.

    List syntax:
    array<int>
    a.Length
    a[i]
*/

method MinList(a: array<int>) returns (result: int)
requires false
{
    // TODO
}

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
