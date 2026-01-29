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
Recap:

- We wrote a program & proved it correct (in the same framework)

- abs() is **both** an executable function and mathematically understandable (verifiable) code

Poll:


=====

*/

/*
    === Method/function distinction ===

    The main difference between methods and functions is that
    methods need pre/postconditions to work, functions don't need
    pre/postconditions and are purely mathematical functions.
    function = mathematical function
    method = imperative code, i.e. Python/C/C++ function

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
    Preconditions and postconditions

    Using a method means we can directly specify pre/posts on
    the method:

        requires = precondition

        ensures = postcondition

    Exercise:

    Add a precondition to the above
    and strengthen the postcondition
*/

/*
=== Recap ===

/*
