# Study guide

**Midterm date:** In class, May 20, 2025.

## Specifications

- Definition of specifications
- Stronger and weaker specs
- Types of specs (functional correctness, safety, and liveness)
- Preconditions and postconditions
- Assume and assert
- Difference between testing and verification

## Logic and satisfiability

- Logical formulas
- Theories for integers, real numbers, and strings (you do not need to know the specific grammar by heart, but should be familiar with the concepts)
- Definition of satisfiability and validity
- Translation of programs to (Z3) formulas
- Satisfiability algorithms: DPLL (unit propagation, pure literal elimination), DPLL(T), Nelson-Oppen and CDCL (basic overview only)
- Decidability of theories; boundary of decidability and expressiveness (an example problem might be a reduction like the PrefixOf problem or the fixed-width integer theory problem you saw on HW2)
- Limitations of Z3

## Interactive verification

- Verification methodology; industry applications and determining impact
- First-order logic: extending formulas with quantifiers
- Assertions and pre/postconditions (revisited)
- Lemmas and unit tests
- Function/method distinction - "methods are opaque"
- Loop invariants (definition, purpose, and application - an example problem is, here is a program, come up with a loop invariant that can be used to verify it)
- Dafny as a computationally bounded verifier
- Difference between truth and provability
- Axioms and assume statements; external methods
- Limitations of Dafny

## Remaining topics

There will be 1-2 questions on the exam about the following topics.
We will cover these today:

Dafny internals:
- Hoare triples
- Hoare logic rules (these generalize what we have seen with assertions and loop invariants)
- Relative completeness of Hoare logic
- Strongest postconditions and weakest preconditions

I will hope to cover the following in class, but will NOT include a question on the exam:
- Dynamic logic.
