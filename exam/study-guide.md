# Study guide

Review all the in class polls!

Try the practice final (provided on Piazza)

There are 2 additional practice questions with worked solutions in Dafny
in `practice-final-examples.dfy`
(both of these questions are from the practice final).

## 1: Program Specifications

- Definition of specifications

- Stronger and weaker specs

- Types of specs: functional correctness, full functional correctness, safety, and liveness

- Preconditions and postconditions

- Assume and assert

- Difference between testing and verification; advantages and limitations

## 2: Interactive verification in Dafny

- When is interactive verification useful / worth investing in?
    + industry applications and determining impact
    + correctness is critical (bugs are catastrophic); security; cost ($$$)

- Verification methodology: 4-step process
    1. Write the code
    2. Write the spec
    3. Write unit tests (to check if the spec is strong enough)
    4. Add proofs (loop invariants, assertions, lemmas, etc.)

- Quantifiers

    when proofs are necessary: quantifiers, complex data types, loops

- Function/method distinction - "methods are opaque"

    + Advantages of leaving the spec underspecified!

- Compile-time vs. runtime (assertions are compiled out)

- Axioms and assume statements; external methods
    assume{:axiom}, lemma{:axiom}, method{:axiom}
    what can go wrong

- Loop invariants (3 conditions (i), (ii), (iii). Definition, purpose, and application)

     example problems:
     - here is a program, come up with a loop invariant that can be used to verify it
     - here is a possible invariant, which of (i) (ii) (iii) does it satisfy?

- Dafny as a computationally bounded verifier

- Advantages and limitations of Dafny

## 3: Proofs and Programs

- Hoare logic: definition of { P } C { Q }, Hoare logic rules and their application

    + I will give the rules if the specific syntax is needed, but
      you should understand them conceptually


- Definition of computer program:
    variables and expressions
    sequencing, branching, assignment, and loops

    + distinction between programs and logical propositions

- Strongest preconditions and strongest postconditions

    Know: given a predicate φ and program C, how to
    compute WP(C, φ) and SP(C, φ)

- Automating verification; loop-free code

- Difference between partial and total correctness

- Soundness and completeness; relative completeness of Hoare logic

- First order logic:

    + expressions + quantifiers

    + difference between syntax and semantics

    + difference between truth and provability.

    + what a proof rule is (from X deduce Y)

--------------------
--------------------
--------------------

## Not covered this year (WQ 26)

The following were **not** covered this year and will not appear on the final.

## Logic and satisfiability

- Logical formulas
- Theories for integers, real numbers, and strings (you do not need to know the specific grammar by heart, but should be familiar with the concepts)
- Definition of satisfiability and validity
- Translation of programs to (Z3) formulas
- Satisfiability algorithms: DPLL (unit propagation, pure literal elimination)
    + DPLL(T), Nelson-Oppen and CDCL (basic overview only)
- Decidability of theories; boundary of decidability and expressiveness (an example problem might be a reduction like the PrefixOf problem or the fixed-width integer theory problem you saw on HW2)
- Limitations of Z3
