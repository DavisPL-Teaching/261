/*
Lecture 2, Part 5:
Conclusions

=== When assertions do not pass ===

Last time's poll (Tuesday) also hinted at another issue.
Sometimes, Dafny assertions do not pass.

Above, we did a simple unit test for MinList.
What happens when we try a more complicated unit test?
*/

// Import syntax
include "4-loop-invariants.dfy"

method TestMinList2() {
    // previous test:
    // var a0 := new int[][1];
    // a0[0] := 3;
    // var result := MinList(a0);
    // assert result == 3;

    // Try more complicated examples here.

    // New example syntax:
    // var a1 := new int[][1, 2, 3, 4, 5];
    // var result := MinList(a1);
    // assert result == 1;
}

/*
    === Tips when you get stuck ===

    Some techniques for when you get stuck on a Dafny proof.

    1. Find out what Dafny knows.

    You can query with assertions!

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
