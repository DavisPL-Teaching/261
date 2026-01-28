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
    print(x);
    print(y);
}

lemma AbsCorrect(x: int) {
    assert abs(x) >= 0;
    assert abs(x) == x || abs(x) == -x;
    // Try uncommenting
    // assert abs(x) == x;
}

/*

Poll:
Which of the following are most likely to be useful steps for verification of a real-world software project?

https://forms.gle/fHwrbRw6JGfscLab9

=====

So far, we could do all of this with just validity. (Why?)

Q: Are there things we can't express using only validity?

Yes: for example, abs() is surjective onto nonnegative integers:
*/

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
    Above: we have a program and we have proved it correct!

    Let's see how this is accomplished by starting with some mini verification
    exercises.

    After this I want to go deeper to understand on a fundamental level:
    - What is a proof?
    - What is a program?
*/

// Note: alternate way of writing Abs as a method.
// The main difference between methods and functions is that
// methods need pre/postconditions to work, functions don't need
// pre/postconditions and are purely mathematical functions.
//    function = mathematical function
//    method = imperative code, i.e. Python/C/C++ function
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

/*
    === Recap ===

    We saw some examples of writing
    functions, assertions, lemmas, and postconditions in Dafny.
    (The postconditions are the "ensures" statements.)
    We also saw examples of quantifiers.

    forall x :: formula
    exists x :: formula

    ===== A note on industry applications =====

    Course goals:
    - to understand how verification works
    - to apply verification to real-word projects

    The methodology of verification:

    1. We encode the problem we are considering
      (based on real software, in a real industry application)
      in preconditions, postconditions, and other domain-specific constraints
      in an appropriate verification framework.

    2. We use the tool to prove the property, thus proving the code 100% free from bugs.

    When is this methodology useful in practice?
    Not always! But often in cases where correctness, safey, or security is critical
    to system functioning.
    Investment examples:

    - Amazon: verifying low-level cryptographic libraries using tools
      like Dafny and CBMC, verifying domain-specific security constraints
      (e.g., your cloud data cannot be accessed by untrusted users)

    - Microsoft: many applications of Z3 and other techniques internally, verifying network code,
      device and kernel drivers, etc.

    - Hardware bugs & hardware verification:

        Pentium FDIV bug: affected Intel Pentium processors in 1994.
        recall of all defective Intel processors at the time
        $475 million in losses!

    - Signal messaging app: verification effort for core messaging protocol going back to 2017

    - Larger-scale realistic software projects coming from academia:
        CompCert: a verified optimizing C compiler
        CertiKOS: a verified operating system kernel
        Increasing interest from the systems community and more work every year on building
        bigger verified file systems, network controllers, etc.

    - More generally, at large industry scale, security bugs cost a LOT of money.
      Higher-ups will throw money at any technique which even has a chance of preventing large-scale
      security risks (willing to invest).

    - The argument is that despite a much greater effort, we also get a greater payoff.
      Verify your library ==> greater assurance against threats, more people want to use it,
      maintain the verification conditions on all future software updates
/*
