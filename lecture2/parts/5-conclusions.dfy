/*
Lecture 2, Part 5:
Conclusions

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
