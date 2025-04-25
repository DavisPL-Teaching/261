/*
    Intro to first-order logic in Dafny.

    ===== A note on industry and applications =====

    Goals:
    - to understand how verification works
    - to apply verification to real-word projects

    The methodology of verification:

    1. We encode the problem we are considering
      (based on real software, in a real industry application)
      including preconditions and postconditions or other
      domain-specific constraints
      in an appropriate verification framework.
      We can translate formulas and program behavior to Z3,
      or rewrite all of the code in a dedicated verification language like Dafny (, Coq/Rocq, Agda, Lean ...)
      or use a language-specific verification
      tool to verify code natively (e.g., CBMC for C, Flux or Verus for Rust, etc.).

    2. We use the tool to prove the property, thus proving the code 100% free from bugs.

    This methodology has been really used in practice.
    Amazon, Microsoft, etc. have invested millions into verification project sin practice.

    - Amazon: verifying low-level cryptographic libraries using tools
      like Dafny and CBMC, verifying domain-specific security constraints
      (e.g., your cloud data cannot be accessed by untrusted users)

    - At large industry scale, security bugs cost a LOT of money. Higher-ups will throw money at
      any technique which has a chance of preventing large-scale security risks, willing to invest.

    - The argument is that despite a much greater effort, we also get a greater payoff.
      Verify your library ==> greater assurance against threats, more people want to use it,
      maintain the verification conditions on all future software updates

    - Larger-scale realistic software projects built in industry:
        CompCert: a verified optimizing C compiler
        CertiKOS: a verified operating system kernel
        Increasing interest from the systems community and more work every year on building
        bigger verified file systems, network controllers, etc.

    But writing these verified applications is really hard!
    (Often: a PhD project or an entire team of researchers)
    I find that you will need a strong foundation in logic to use and understand
    these tools, so I need to cover the logic foundations first.

    In short, we are covering the theory so as to give you the foundation I believe
    you need to really apply these tools to real-world software projects.

    ===== Poll =====

    https://forms.gle/uXELPFiRY85kb97Y6
*/

/*
    ===== First-order logic =====

    First-order logic generalizes the grammars we have seen so far by adding quantifiers:
    forall x. φ
    and
    exists x. φ.

    Z3 can take as input formulas in first-order logic, but it often isn't very good about solving them!
    (Why?)

    So, for general program verification, we often resort to more powerful techniques where we actually
    work with the tools to help prove the property we have in mind. This is called "interactive verification" or "interactive theorem proving".
*/

/*
    Example.
    Why do we need quantifiers?

    We saw an example with the pigenohole principle where it was most natural
    to express using quantifiers.

    Example using abs():
    Suppose we want to show that abs() is increasing:

        forall x. forall y. 0 <= x < y ==> abs(x) < abs(y)

    Only forall statements in front! So we can do this with a validity check:
*/

function abs(x: int): int {
    if x > 0 then x else -x
}

// Note: more common to see it as a method.
// We will start with functions, more on methods later
// method AbsMethod(x: int) returns (y: int)
//     ensures y >= 0
//     ensures y == x || y == -x
// {
//     if x > 0 {
//         y := x;
//     } else {
//         y := -x;
//     }
// }

lemma AbsCorrect()
ensures forall x :: abs(x) >= x
ensures forall x :: abs(x) == x || abs(x) == -x
{}

lemma AbsIncreasing()
ensures
    forall x :: forall y :: 0 <= x < y ==> abs(x) <= abs(y)
{}

/*
So far, we could do all of this with just validity. (Why?)

Are there things we can't express using only validity?

Yes: for example, abs() is surjective onto nonnegative integers:
*/

predicate is_positive(y: int) {
    y >= 0
}

lemma AbsSurjective()
ensures forall y: int :: is_positive(y) ==> exists x :: abs(x) == y
{
    // Some odd syntax
    forall y: int | is_positive(y)
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
}

/*
    Eventually, it will become clear that we can also verify arbitrary programs
    and this verification will be built on first-order logic.

    Here's a small sneak peak:

    Below, we wrote a function to add up the absolute value sum of a list, like

    AbsSum([x, y, z]) = abs(x) + abs(y) + abs(z).

    The spec here says that AbsSum is an upper bound on all individual elements of the list.
*/

method AbsSum(l: seq<nat>) returns (result: nat)
ensures
    forall i :: 0 <= i < |l| ==> result >= abs(l[i])
{
    var sum: nat := 0;
    for j := 0 to |l|
        invariant j <= |l|
        invariant forall i :: 0 <= i < j ==> sum >= abs(l[i])
    {
        sum := sum + abs(l[j]);
    }
    result := sum;
}

/*
    Above: we have a program and we have proved it correct!

    But let's go deeper to understand on a fundamental level:
    - What is a proof?
    - What is a program?
*/
