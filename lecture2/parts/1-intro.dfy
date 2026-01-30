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

method MainOld() {
    var x := -3;
    var y := abs(x);
    print x, "\n";
    print y, "\n";
}

// def spec(x):
//     assert x >= 0
//     assert abs(x) == x or abs(x) == -x

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

    Key property of formal verification -- always done statically

    proving code correct without ever running it.

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

Correct answers: 1, 2, 3, 5.

======
*/

/*
    Preconditions and postconditions

    Abs is rewritten as a Method below.

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
    // try commenting
    // requires x != 0
    ensures y >= 0
    ensures y == x || y == -x
{
    if x > 0 {
        y := x;
    } else {
        y := -x;
    }
}

// second example: spec is we want f(x) == x for x == 1 and x == 2.

method AbsMethod2(x: int) returns (y: int)
    requires x == 1 || x == 2
    ensures y == x
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
    function = mathematical function (if you're familiar, think of it as a Haskell function)
    method = imperative code, e.g., Python/C/C++ function

    Methods need pre/postconditions to work! functions don't

    Methods are opaque!
    (Let's illustrate this)

    What would happen if I tried to prove the same lemma
    about AbsMethod instead of abs?
*/

method AbsMethod3(x: int) returns (y: int)
    ensures y >= 0
    ensures y == x || y == -x
{
    if x > 0 {
        y := x;
    } else {
        y := -x;
    }
}

// lemma AbsCorrect2(x: int) {
// ^^^ error: lemmas can't call methods.

method AbsCorrect2(x: int) {
    var y := AbsMethod3(3);
    assert y == 3;
    // var y := AbsMethod3(x);
    // assert y >= 0;
    // assert y == x || y == -x;
}

// assertion might not hold!
// methods are opaque in the following sense: the entire behavior
// of the method is treated as a black box and only abstracted by
// its precond/postcond.
// In contrast, a function can be expanded by the verifier.

// Why are methods useful compared to functions?
// 1. methods represent imperative code, so I should use methods if I want
//    to verify real-world imperative library.
// 2. sometimes abstracting a spec separate from its implementation is useful!
method ReturnPositiveNumber() returns (y: int)
    ensures y > 0
{
    // Placeholder implementation; TODO: fix later
    return 5;
}

method TestReturnPositiveNumber() {
    var y := ReturnPositiveNumber();
    // assert y == 7;

    assert y >= 0;
}

/*
    Preconditions are enforced by the Dafny verifier!
*/

// Function that enforces the return value is positive
method SubtractPositive(x: int, y: int) returns (z: int)
    requires x > y
    ensures z > 0
{
    return x - y;
}

// Dafny will prevent me from calling SubtractPositive if the
// preconditions are not met

method TestSubtractPositive() {
    var x := 5;
    var y := 7;
    // var z := SubtractPositive(x, y);
    var z := SubtractPositive(y, x);
}

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

    Input set is the same for spec1, spec2

    Output is strictly stronger requirement for spec1

    Therefore: spec1 stronger than spec2.

    Task: show that spec1 is stronger than spec2 using Dafny.
*/

method F1(x: int) returns (y: int)
    // spec1:
    requires true
    ensures y == x
{
    // we want to leave F1 impl as opaque!
    // bc we are interested in **all** functions satisfying spec1
    // fortunately Dafny does that for me by making methods opaque.
    // one option:
    // return x;
    // another option: omit the impl entirely
    // assume{:axiom} false;
    // ^^^ general technique for making stubs in Dafny
    // kind of like raise NotImplementedError
    // A better way (actually crashes the program):
    expect false;
}

method TestSpec1StrongerThanSpec2(x: int) {
    var y := F1(x);
    assert y >= x;
    // passes!
    // Therefore, F1 satisfies spec2
    // Therefore, spec1 is stronger than spec2.
}

method Main() {
    var x := 5;
    var y := F1(x);
    print y, "\n";
}

/*
Method 2:

    if Method 1 fails (input/output sets are incomparable)

    If Method 1 fails:

    Try to come up with a function that satisfies spec1 but not spec2.

    - If you can, then spec1 is NOT stronger than spec2

    - If you can't, then spec1 IS stronger than spec2.

    Try to come up with a function that satisfies spec2 but not spec1

    - If you can, then spec2 is NOT stronger than spec1

    - If you can't, then spec2 IS stronger than spec1.

Example:

    spec1:
        On all inputs x, f(x) = x

    spec2:
        On all inputs x, y, f(x) < f(y).
*/

// Our task: we want to come up with F_ex
// which satisfies spec2 but not spec1.

// method F_ex(x: int) returns (y: int)
// // spec1:
// requires true
// ensures y == x
// {
// }

// spec 2 is false: make some inputs where this fails.
// method TestSpec2(x: int, y: int) {
//     var x_out := F_ex(x);
//     var y_out := F_ex(y);
//     assert x_out < y_out;
// }

/*
    Quick recap:

    We learned about writing pre/postconditions for Dafny code

    Method/function distinction - methods are opaque & summarized by their
    pre and postconditions only

    - use methods to represent general/imperative code

    Along the way: some ways of stubbing functions using

        assume{:axiom}
        expect
        ensures false

    (more about some of these later)

    We saw how Dafny can be used to check stronger/weaker specifications.
*/
