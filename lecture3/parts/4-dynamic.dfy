/*
    Lecture 3, Part 4:
    Dynamic logic.

    We ended this lecture early due to time!
    For full details see: :-)
    https://en.wikipedia.org/wiki/Dynamic_logic_(modal_logic)

    This material will not appear on the final.

    === Motivation ===

    Hoare logic limitations?

    Hoare logic encompasses all of Dafny programs that we write in practice!
    But it does have some limitations.

    1. One of the best-understood of these goes back to some concepts we saw in
    lecture 1, but have not revisited since:

        - Safety properties

            "something bad never happens"

            Encode in a logical way:
            "for every execution of the program, along every program trace, event X never occurs"

            ^^^^ problem is Hoare logic only talks about after the program has already
                 terminated.

        - Liveness properties

            "something good does happen"

    2. Nondeterministic programs

        What if the program is nondeterminstic?

        A program that flips a coin? That reads a file on the operating system?

        ^^^^^ we can't model it using the existing grammar from part 1

    3. More generally: testing properties on multiple traces!

    Sometimes we want to test properties on multiple traces of a program.

    Why? This is especially relevant for computer security:

    - famous attacks: Meltdown and Spectre

        Timing attacks! Have to do with how long the code takes to run

        In order to protect against these attacks: we need something like:

            "for all inputs x1 and x2, if x1 and x2 differ only on secret information
             (such as a private key), then C(x1) and C(x2) take the same time to run."

            Hoare triple:

                { P } C { Q }

            For all inputs x, of P(x) is true, and we execute C with output y, then Q(y)
            is true.

                For any specific

                precond P
                C
                postcond Q

            A: it talks about two different program executions

            I'm only talking about one trace of the program, but I need to say that
            on two different executions of the program, running time is the same.

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

    - "For all inputs x satisfying the precondition P, in all executions of C, the postcondition
       satisfies Q."

       set of inputs X
       set of outputs Y

       for all x, if P(x) is true, for *any* y such that there is an execution of C ending
            in y, Q(y) is true.

      This suggests some kind of nondeterminism.

    What's possibly even more surprising is that this leads to an even simpler formulation of programs and proofs, that is (arguably) more fundamental and more general than Hoare logic.

    === Q: What is a program? (revisited) ===

    We said from (hoare.dfy)?

    - Programs are just everything that can be created using ...

        expressions and variables

        sequencing, assignment, looping, and branching

        ```
        Prog ::=
            | Var := IE // Assignment statement
            | if BE then Prog else Prog end
            | while BE do Prog end
            | Prog ; Prog
        ```

        Let's keep sequencing and assignment

        Nondeterministic version of looping:

            while flip_coin() {
                BODY;
            }

            repeat {
                BODY;
            }

            ^^^ nondet version of while

            Repeat statement: "Repeat this block of code some number of times."

            That's a nondeterministic while loop.

        What's a nondeterministic branching statement?

            Guess or do both?
            ^^^^^

            Construct that allows us to guess one of two branches

            choose C1 OR C2 ;

        Program Prog ::=
            | Var := IE // Assignment statement
            | Prog ; Prog
            | choose Prog OR Prog ;
            | repeat Prog ;

        We can't recover regular deterministic imperative programs from
        this grammar alone...
        but if we add:

            | assume BE;

        we can actually encode all deterministic programs from our previous grammar.

        How?

            if b C1 else C2

                ===> choose (assume b; C1) OR (assume !b; C2) ;

            This is an exact, faithful encoding of if in this new program syntax.

        Similarly:

            while b do C;

                ===> repeat (assume b; C); assume !b

    For Dynamic logic, we first generalize the grammar for programs
    to the above one for nondeterministic programs.

    Grammar for specifications?

    Sketch: instead of

        { P } C { Q }

    we will have two constructs for creating new propositions:

        [ C ] Q
        ^^^^^^ Box C. Q
        "After all executions of C, postcondition Q holds."

        < C > Q
        ^^^^^ Diamond C Q
        "After some execution of C, postcondition Q holds."

    We can encode the hoare triple { P } C { Q } as

        P ==> [ C ] Q.

    Diamond can't be encoded in Hoare logic.
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

        In Dynamic logic: we can simply say:

            From:
                Q ==> [ C ] Q

            Deduce:
                Q ==> [ repeat C ] Q
*/
