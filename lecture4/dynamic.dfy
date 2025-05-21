/*
    Dynamic logic.

    === Motivation ===

    I would like to make two points:

    1. Hoare logic limitations

    Hoare logic encompasses all of Dafny programs that we write in practice!
    But it does have some limitations.

    One of the best-understood of these goes back to some concepts we saw in
    lecture 1, but have not revisited since:

    - Safety properties

    - Liveness properties

    - Testing properties on multiple traces?

    2. Nondeterministic programs

        What if the program is nondeterminstic?

        A program that flips a coin? That reads a file on the operating system?

    3. Properties on multiple traces

    Sometimes we want to test properties on multiple traces of a program.

    Why? This is especially relevant for computer security:

    - famous attacks: Meltdown and Spectre

    - Constant-time programming

    - Determinism

    - Non-interference

    So for all of the above reasons, it would be nice to be able to
    talk about properties that have to do with multiple traces, and
    not just one trace.
    Hoare triples are rather rigid:

        { P } C { Q }

    and only talks about precond/postcond on a single program trace!
    They can't express the above cases.

    === Generalizing Hoare logic ===

    Let's take a closer look at the triple:

        { P } C { Q }

    What does it mean? ...

    How can we say this differently?

    (answer here)

    - "On all programs"

      This suggests some kind of nondeterminism.

      In fact, nondeterministic pr

    What's possibly even more surprising is that this leads to an even simpler formulation of programs and proofs, that is (arguably) more fundamental and, perhaps, more elegant than Hoare logic.

    === Q: What is a program? (revisited) ===

    We said from (hoare.dfy)?

    - Programs are just everything that can be created using ...

    For Dynamic logic, we'll generalize the above to talk about
    nondeterministic programs. We need:

    Modifying our grammar:

    Grammar for specifications?

*/

/*
    === Revisiting the Hoare logic proof rules ===

    We will only do some of these, time permitting.

    The point I want to make is that these become simpler
    (and perhaps more natural) in the new formulation.

    1. The sequencing rule

    2. The branching rule

    3. The assignment rule

    4. Weakening and strengthening

    5. Rules for assume and assert

    6. The loop rule.
*/
