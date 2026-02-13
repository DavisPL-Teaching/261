/*
Lecture 2, Part 4:
Loop invariants

Recap:
We have seen:

- How to write Dafny code with preconditions and postconditions
- Writing assertions, lemmas, and unit tests
- Function/method distinction

The MinFour and ArgMinFour were a bit artificial as they only work with integers.
It would be nice to generalize our functions to work with lists!
Can we?
This requires: loop invariants!

Continuing the 4-step process:
1. Decide on an implementation (or port an existing one); write in Dafny
2. Decide on a spec; write pre/postconditions
3. Write unit tests
4. Help Dafny with the proof (as needed)

=== Poll ===

(Related to some of the discussion from last time.)

Consider the following snippet of a Dafny program:

assert P;
assert Q;

Suppose that P implies Q (logically) but Dafny verification passes only for P, and not Q. Which of the following is a possible reason for this? (Select all that apply)

https://forms.gle/q5WiyPwxyoU7KtgMA

.
.
.
.
.
*/

/*
    Exercise:
    Generalize the MinFour implementation and specs
    to lists of integers, rather than just four.

    Two "list"-y types in Dafny: array and seq

    List syntax:
    array<int>
    a.Length
    a[i]

    We did step 1, now step 2:
    Write a precondition and postcondition for MinList
    that matches what we had for MinFour.
    (Your pre and postcondition don't have to be valid Dafny, but they should be
    correct logically)
*/

method MinList(a: array<int>) returns (min: int)
    // TODO
    // example syntax:
    // forall i :: 0 <= i < a.Length ==> a[i] == 0
    // Precondition:
    // requires false
    requires a.Length >= 1
    // Postcondition
    // - The value min should be one of the elements of the array
    //   "There exists an index i (within correct bounds) such that a[i] == min"
    ensures exists i :: (0 <= i < a.Length) && a[i] == min
    // - The value min should be <= each element of the array.
    ensures forall i :: 0 <= i < a.Length ==> min <= a[i]

    // Q: can you combine exists and forall?
    // forall i :: exists j :: forall k :: a[i] = a[j] + a[k]
{
    // How we would do this with imperative code?
    // Iteratively: for x in array a, if x < current min, set min := x
    min := a[0];
    // a.Length - for arrays, |a| would be for sequences.
    // Loop invariant should be true "on every iteration"

    // <-------- ***here***
    var i := 1;
    // for i := 1 to a.Length

    // **Property (i)** I is true here
    // assert Inv;

    while i < a.Length
        // What we need to do:
        // Add a "loop invariant" here to explain to Dafny
        // how the postcondition will be true after executing
        // any number of iterations of the loop.
        invariant 0 < i <= a.Length
        // invariant: min <= any value in the array before index i
        invariant forall j :: 0 <= j < i ==> min <= a[j]
        // invariant: min is an element of the array so far
        invariant exists j :: 0 <= j < i && min == a[j]
        // Q: do we need old() syntax?
        // A: hopefully not (sometimes for other examples)
    {
        // what is true at this point of the loop?
        // assert Inv && i < a.Length;

        if a[i] < min {
            min := a[i];
        }
        i := i + 1;

        // (ii) precond = Inv && i < a.Length
        //      postcond = Inv
        // <-------- ***here***
        // assert Inv

    }

    // (iii)
    // Inv && (i >= a.Length) ==> postcondition.
    // Inv implies the postcondition.
    // assert Inv && (i >= a.Length);
    // assert postcond
    return min;
}

/*
=== What is a loop invariant? ===

A loop invariant is like a pre/postcondition for the loop body.

A loop invariant is a Boolean property I such that:

i. Loop invariant is true before first entering the loop
    precondition ==> invariant

ii. If the loop condition is true, then the loop invariant is preserved
    (loop condition) && invariant holds at the start ===> invariant holds at end

iii. If the loop condition is false, then the loop invariant implies the postcondition
    !(loop condition) && invariant holds ==> postcondition.
*/

/*
    (If not already done)
    Write a unit test for the MinList function.

    (Compile time unit test - checked at compile time, not executed)
*/

method TestMinList1() {
    var a0 := new int[][1]; // new keyword: allocates an array on the heap
    a0[0] := 3;
    var result := MinList(a0);
    assert result == 3;

    // Try more complicated examples here.
}

/*
    Exercise

    Here is another method and a spec.

    1. Which of the following is a valid loop invariants?
    Check the properties (i)-(iii) for each one.

    A. y == 0
    B. y >= 0
    C. y <= x
    D. y != x + 1
    E. True
    F. False

    2. Try them out below. How do violations of (i), (ii), and (iii) appear in
    the Dafny VSCode extension?

    3. If none of the above is correct - write the correct invariant.
*/

method FindSuccessor(x: int) returns (y: int)
// Uncomment to work on the problem
// requires x >= 0
// ensures y == x + 1
{
    y := 0;
    /*
        (i) : true before loop executes
        (ii) : preserved by the loop: if Inv && cond is true at top of loop,
               Inv is true at bottom of loop
        (iii) : implies postcondition: if Inv && !cond is true,
                then postcond is true.
    */
    while y <= x
    // invariant ...
    // A. y == 0
    // No because y is not always zero?
    // (i) is satisfied -- before entering loop, y == 0
    // (ii) fails: if y == 0 at the top of the loop, y == 1 at the botto
    //      of the loop, which does not imply y == 0
    // (iii) fails: if y == 0 and y > x. Does not imply postcond

    // B. y >= 0
    // (i) is true
    // (ii) is true - if y >= 0 and we execute y := y + 1, y is still >= 0
    // (iii) fails: assuming y >= 0 and y > x ==> does not imply postcond.

    // C. y == x + 1
    // (i) is false - *not* true before entering
    // (ii) is true
    //       precond loop body: y <= x && y == x + 1
    //       postcond loop body: y == x + 1
    //       *is* preserved by the loop body
    // (iii) is true - does imply the postcondition.

    // C. y <= x
    // D. y != x + 1
    // E. True
    // F. False
    {
        y := y + 1;
    }
    return y;
}

/*
    Recap

    - We saw examples of working with arrays: a[i], a.Length etc.

    - We defined loop invariants and saw them in action

        + Loop invariant must satisfy properties (i), (ii), (iii)

        + Practice with loop invariants

    - We discussed the computationally bounded nature of Dafny

        + Sometimes we need additional assertions to walk through
          and help Dafny prove an assertion

        + A more general debugging technique: find out what Dafny knows, and what it doesn't.

*/

/*
    (Picking up here for Thursday, February 12)

    Review on loop invariants:

    - A loop invariant is a property that should be true
        (1) immediately before the loop executes
        (2) immediately following the loop body, after each loop iteration

    - BUT: Dafny does not know what is true at all points in time!
        (To do so, you'd have to run the loop / have infinite amount of time)

        Properties (1) and (2) - intuitively "intractable"

    - So Dafny does not actually check (1) and (2) above, instead it needs to check a stronger condition in three parts:

        For a program

        method Example()
            requires precond
            ensures postcond
        {

            HEADER;

            while cond {

                BODY;

            }

            FOOTER;
        }

        (i) precond ==> after executing HEADER, Inv
        (ii) Inv ^ cond ==> after executing BODY, Inv
        (iii) Inv ^ !cond ==> after executing FOOTER, postcond

    - It is condition (ii) that makes us refer to this as a loop
      *invariant,* i.e. it is invariant under the execution of the program
      BODY.
      This works by analogy with mathematical induction. It's exactly like

        property we want to show: "for all x, x + x is even"

        but in order to *prove* that it's true, we need to show
        it via some invariant on all integers: that is we need to show
        a property P(n) such that

            if P(n) holds, then P(n+1) holds.

        proof: need to show "if n + n is even, then (n + 1) + (n + 1) even".

        Just like properties about integers are proven by induction on n,
        properties about programs are proven by induction on the number
        of iterations of the while loop.

    - Foreshadowing:
        You'll notice all of the above have the form

            "if P, then after executing C, Q"

        This is known as a Hoare triple and will be the foundation for
        Hoare Logic. It's written

            { P } C { Q }

    - Extra-foreshadowing:

        There is another logic that is more general called Dynamic Logic,
        in which we can write it this way

            P => [ C ] Q
            (P => [ C ] Q && [ C2 ] Q2) => ~ [ C3 ] Q3

            P        =>       [ C ]                            Q.
            ^^ if P
                     ^^ then
                              ^^^^^ after all executions of C,
                                                               ^^ Q holds.

    - Definition we will take:
        A loop invariant is any property Inv satisfying
        conditions (i)-(iii).

    - Any loop invariant also satisfies (1) and (2) above.
      (In fact, satisfying only (i) and (ii) is enough!)
      But not necessarily vice versa.

Before we continue:

Let's fill in the correct loop invariant for FindSuccessor
from last time.
*/

method FindSuccessor2(x: int) returns (y: int)
// Uncomment to work on the problem
requires x >= 0
ensures y == x + 1
{
    y := 0;

    while y <= x
    invariant 0 <= y <= x + 1
    {
        // What does Dafny know here
        assert 0 <= y <= x;

        y := y + 1;

        // What does Dafny know here
        assert 0 <= y <= x + 1;
    }
    return y;
}

/*
    === Poll ===

    Consider the following method.

    In the postcondition, assume that s * n is valid Dafny syntax
    (even though it isn't), and works as in Python -
    i.e., multiply a string by an integer to repeat it n times.
*/

// btw.: nat = nonnegative integer (natural number)
// (unsigned integer)

// method HelloNTimes(n: nat) returns (result: string)
// requires n > 0
// ensures result == ("Hello " * (n - 1)) + ("Hello")
// {
//      result := "Hello";
//      var i := 1;
//      while (i < n) {
//           result := result + " Hello";
//           i := i + 1;
//      }
//      return result;
// }

/*
    For each of the following, which of the conditions of a loop invariant are satisfied?

    (i) Invariant is true before entering the loop.
    (ii) Invariant is preserved by the loop body (given the while condition is true)
    (iii) Invariant implies the postcondition (given the while condition is false).

    https://forms.gle/wr6km15E8sH12YYs5

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

    None of the invariants was correct

    But we can get a correct invariant with (4) && (5)

    i <= n && result == ("Hello "* (i - 1)) + "Hello".

    after loop executes:
    1 <= i <= n && result == ("Hello " * (i - 1)) + "Hello".

    === Exercises ===

    Additional loop invariant exercises

    1. Above, we wrote MinList.
       Now Implement and verify the ArgMinList method.

    2. Go back to the AbsSum example from part 3. Add a loop invariant.

    3. Write and prove a function to compute the gcd of two integers.
*/

method ArgMinList(a: array<int>) returns (result: int)
    // TODO
    // Precondition:
    requires false
    // Postcondition
    ensures false
{
    // TODO
}
