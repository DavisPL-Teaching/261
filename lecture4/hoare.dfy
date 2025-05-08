/*
    Hoare logic.

    Probably the most foundational paper in program verification:

    - An Axiomatic Basis for Computer Programming. C A R (Tony) Hoare, 1969.
      https://dl.acm.org/doi/pdf/10.1145/363235.363259

    The question is what it means to prove a program correct.
    Hoare showed that programs can be proven via a small set of
    simple rules.

    === Q: What is a program? ===

    Suggestions?

    Answer:

    === Hoare triples ===

    Definition.
*/

/*
    1. The sequencing rule
*/


/*
    2. The conditional rule
*/

/*
    3. The assignment rule
*/

/*
    4. Weakening and strengthening
*/

/*
    5. Rules for assume and assert
*/

/*
    6. The loop rule.
*/

/*
    === Automating verification ===

    As we have previously hinted,
    all of the above rules can be automated, aside from the loop rule.

    === Weakest preconditions and strongest postconditions ===

    Definition:

    Given a precondition

    - A **weakest precondition**

    Examples:
*/

/*
    === Relative completeness of Hoare logic ===

    You might ask the question:
    - Can everything that is true about a program be proven in Hoare logic?

    See the section at the end of last lecture (fol.dfy) for some additional discussion on this.

    The main result about Hoare logic from this standpoint is that it is *relatively complete*,
    meaning that it can prove anything about a program that can be proven in first-order logic.

    Formal theorem statements:

    **Theorem 1.**
    Hoare logic is sound. That is ...

    **Theorem 2.**
    Hoare logic is not complete. That is: ...

    **Theorem 3.**
    Hoare logic is relatively complete. That is: ...
*/
