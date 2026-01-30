/*
    Intro to Dafny and program verification
*/

/*
    ===== What is Dafny? =====

    Dafny is a verification-aware programming language.
    (An interactive program verification framework.)

    It allows us to develop a program and its spec and proof together / in tandem.

    Dafny is widely used in industry applications of verification
    (perhaps seeing a bit more use than tools like Coq/Rocq or Agda, Isabelle, Idris, Lean)
    because it supports transpilation:

    --> Transpile your Dafny code to Python, C#, Java, JavaScript, Go, ...
    --> Interact with external libraries written in those languages
    --> Thus you only have to write and verify the code once, then you can integrate it
        into your project.

    https://dafny.org/

    Reminder/summary: Dafny advantages over automated verification such as Z3: see slides.

    Example: here's our abs function from before.

    In Z3 remember we had to write Abs using Z3 formulas: something like
        z3.If(x > 0, x, -x).
        ^^ mathematical formula

    This was sort of annoying, and also wouldn't work for more complex software
    (think about loops.)
*/

// This function is executable! (like a Python function)
// This function is mathematically understandable! (like a Z3 formula)
// (notice the types)
function abs(x: int): int {
    if x > 0 then x else -x
}

// both a mathematical formula and ane executable program.
// (This is the paradigm of functional programming)

method Main() {
    var x := -3;
    var y := abs(x);
    print x, "\n";
    print y, "\n";
}

lemma AbsCorrect(x: int) {
    assert abs(x) >= 0;
    assert abs(x) == x || abs(x) == -x;
    // Try uncommenting
    // assert abs(x) == x;
}

/*
Above:

- We wrote a program & proved it correct (in the same framework)

- We used a lemma instead of an executable spec.

    No code was executed during verification!

- abs() is **both** an executable function and understandable to the verification engine

  (unlike writing Python functions and translating them to Z3.)

=== Poll ===

(Review question)

Which of the following is a limitation of testing?

https://forms.gle/i5yZ3BSVaZpnjcCX6

.
.
.
.
.

======
*/

/*
    Preconditions and postconditions

    Using a method means we can directly specify pre/posts on
    the method:

        requires = precondition

        ensures = postcondition

    Exercise:

    Add a precondition to the above
    and strengthen the postcondition
*/

// Below: alternate way of writing Abs as a method.
method AbsMethod(x: int) returns (y: int)
    ensures y >= 0
    ensures y == x || y == -x
{
    if x > 0 {
        y := x;
    } else {
        y := -x;
    }
}

/*
    Why is Abs a Method instead of a function?

    === Method/function distinction ===

    Roughly speaking:
    function = mathematical function
    method = imperative code, i.e. Python/C/C++ function

    Methods need pre/postconditions to work! functions don't

    Methods are opaque!
    (Let's illustrate this)
*/

/*
    === Stronger/weaker specs, revisited ===

    I got some questions about stronger and weaker specs
    (Q2 on HW1),
    so I wanted to give some clarification.

Method 1:
    larger input set, smaller output set = stronger spec
    smaller input set, larger output set = weaker spec

    weaker input requirement + stronger output requirement = stronger spec
    stronger input requirement + weaker output requirement = weaker spec

    weaker precondition + stronger postcondition = stronger spec
    stronger precondition + weaker postcondition = weaker spec

Example:

    spec1:
        On all inputs x, f(x) = x

    spec2:
        On all inputs x, f(x) >= x

*/

method F1(x: int)
requires false
{
}

/*
Method 2:
    if Method 1 fails (input/output sets are incomparable)

    If Method 1 fails:

    Try to come up with a function that satisfies spec1 but not spec2.

    - If you can, that means spec1 is NOT stronger than spec2

    - If you can't, then spec1 IS stronger than spec2.

    Try to come up with a function that satisfies spec2 but not spec1

    - If you can, that means spec2 is NOT stronger than spec1

Example:

    spec1:
        On all inputs x, f(x) = x

    spec2:
        On all inputs x, y, f(x) < f(y).
*/

method F2(x: int)
requires false
{
}
