/*
    Lecture 3, Part 0:
    Outline

    This lecture will study the foundations behind how Dafny works behind the scenes.

    We will cover:

    - Foundations behind how Dafny works: what proofs (and proof systems) is Dafny
        based on?

        + Hoare Logic (system of proofs about programs)

        + First-order logic (underlying system of logic - not about programs)

    - How does Dafny determine whether a program is correct behind the scenes?

        Basically, it's checking the rules above.

    A good understanding of these topics is useful!
    It will help you understand why verification in Dafny works,
    when it doesn't, and how to go about fixing it (see below).

    If time, some possible advanced topics:
    dynamic logic, and the Curry-Howard correspondence.

    === Why learn about proofs? ===

    Sometimes, Dafny gets stuck and we need to help out.
    We saw examples of this with the unit tests.

    To do so, I find that it will help you be successful to understand the logic behind how
    Dafny works and what steps are needed to get from
        point A = what Dafny knows
    to
        point B = what we want to show.

    That is:
    We must know how to do the proof ourselves, so that we can walk through
    the steps in case it is needed.

    Basically:
    We should be the expert, Dafny is the assistant.

    This part of the lecture (and the following one) will get a bit more into how Dafny
    works "under the hood".
    The concepts covered will be more general than just Dafny, and would be applicable to any other
    modern proof assistant (Coq/Rocq, Lean, Isabelle, Idris, Agda, etc.)

    === Important concepts ===

    - Partial vs. total correctness
    - Strongest and weakest preconditions
    - Predicate vs. program distinction
    - Syntax vs. semantics distinction
    - Provable vs. true distinction.
*/
