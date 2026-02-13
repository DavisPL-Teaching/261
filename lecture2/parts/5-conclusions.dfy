/*
  Lecture 2, Part 5:
  Conclusions

  === When assertions do not pass ===

  Last time's poll (Tuesday) also hinted at another issue.
  Recall:

    assert P;
    assert Q;

    ^^^ suppose P ==> Q is logically true, but P passes and Q fails, why might
        this be?

  Sometimes, Dafny assertions do not pass.

  Above, we did a simple unit test for MinList.
  What happens when we try a more complicated unit test?
*/

// Import syntax
include "4-loop-invariants.dfy"

lemma MissingStep(
  a: array<int>,
  result: int
)
  requires a.Length > 3
  requires a[1] == 2
  requires a[2] == 3
  requires a[3] == 4
  ensures result == 1
{
  // Omit for now
  assume{:axiom} false;
}

method TestMinList2() {
    // previous test:
    var a0 := new int[][1];
    // a0[0] := 3;
    var result1 := MinList(a0);
    assert result1 == 1;

    // Try more complicated examples here.

    // New example syntax:
    var a1 := new int[][1, 2, 3, 4, 5];
    // var a1 := new int[][1, 2, 3, 4, 0];
    var result2 := MinList(a1);

    // (Us trying to figure out what Dafny knows)
    var a2 := new int[][1, 2, 3, 4, 5];
    // assert a1 == a2;
    // assert a1[0] == 1;
    assert a1[1] == 2;
    assert a1[2] == 3;
    assert a1[3] == 4;
    // assert a1[4] == 0;

    MissingStep(a1, result2);

    assert result2 == 1;

    // Why did first unit test pass, but second unit test failed?
    // Dafny is a "computationally bounded verifier"
    // Dafny is not executing the unit test, it's verifying that it's
    // logically provable.
    // So?
    // Does Dafny even know the array is [1, 2, 3, 4, 5]?
    // Evaluating the array a1 is doing computation!
    // What's happening - 1 is below the length of an array that Dafny
    // is willing to evaluate; 5 is above that amount.
}

/*
    === Tips when you get stuck ===

    Some techniques for when you get stuck on a Dafny proof.

    1. Find out what Dafny knows.

    You can query with assertions!

        assert P

      If it passes - either Dafny knows P (or Dafny did not previously
          know P, but now does)

      If it fails - Dafny does not know P.

    2. Abstract the missing step or cases
       into a lemma with a precond and postcond.

    3. Convince yourself the thing you're trying to prove is true!
       Once you are convinced, *assume* away the lemma you need (or axiom it),
       and come back to it later,
       to make the proof go through.

    The above technique will allow you to decompose any proof into smaller
    parts, and tackle each part one at a time.

    If you've simplified the property at all - you've made progress!
    That's all we need in order to guarantee we eventually complete it.

=== End notes ===

What are the main advantages of Dafny?

1. Prove arbitrary code correct
2. Don't need to rewrite the code in verification language (executable/verifiable code in same framework)
3. Compile & integrate with other languages

What are the main limitations of Dafny?

1. High effort to write and verify real-world software
2. Q is true, but not provable from P?

(1) is true, but not fundamental.
(2) is actually possible and is more fundamental.

To understand the more fundamental limits of Dafny,
then, we need to go back to the logics on which Dafny is built,
and in particular to proofs in first-order logic (FOL).
We will spend some more time going forward on foundations.
*/

/*
    ===== Discussion on industry applications =====

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
*/

// FYI: same thing happens for seq<int> instead of array<int>.

method MinList3(a: seq<int>) returns (min: int)
    requires |a| >= 1
    ensures exists i :: (0 <= i < |a|) && a[i] == min
    ensures forall i :: 0 <= i < |a| ==> min <= a[i]
{
    min := a[0];
    var i := 1;
    while i < |a|
        invariant 0 < i <= |a|
        // invariant: min <= any value in the array before index i
        invariant forall j :: 0 <= j < i ==> min <= a[j]
        // invariant: min is an element of the array so far
        invariant exists j :: 0 <= j < i && min == a[j]
    {
        if a[i] < min {
            min := a[i];
        }
        i := i + 1;
    }
    return min;
}

method TestMinList3() {
    var a1 := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    var result1 := MinList3(a1);

    // Needed for the proof to go through
    // (Try commenting this out)
    assert a1[0] == 1;

    assert result1 == 1;
}
