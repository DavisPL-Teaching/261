# Study guide

**Midterm date:** In class, Tuesday, May 20, 2025 (10:30-11:50am)

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
These will be covered in class this week:

Dafny internals:
- Hoare triples
- Hoare logic rules (these generalize what we have seen with assertions and loop invariants)
- Relative completeness of Hoare logic
- Strongest postconditions and weakest preconditions

Additional topics will be covered in class (time permitting), but will NOT apepar on the exam.

## Practice exam

I have posted a practice exam on Piazza (this was the final exam for ECS 189C last year, and will be useful to help you study). It does not 100% overlap, but it contains much of the same material and the format of the midterm this year for ECS 261 will be similar. (Please do not share the exam or post it online!)

Please note that in addition to multiple choice and short answer questions, unlike the practice exam, there will be 1-2 longer form problems which may involve a proof or explanations (worth approximately 10-20% of the points). These problems will be similar to HW2.
