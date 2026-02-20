/*
    Lecture 3, Part 1:
    Hoare Logic

    ===

    Foundations behind how Dafny works:

    Dafny is able to (sometimes automatically, sometimes
    with assistance validate how programs work).

    How?
    We need a system of formal rules for determining whether
    programs are valid according to their specifications -
    i.e., we need

        *Proofs about programs.*

    === Hoare paper (1969) ===

    Tony Hoare:
    - https://en.wikipedia.org/wiki/Tony_Hoare
    - also known as: C. A. R. Hoare
    - British computer scientist
    - Born 1934 (still alive!)
    - Won the Turing award in 1980 (46 years ago now)
    - Also famous for: inventing the null reference (calling it his "billion-dollar mistake")

    Probably the most foundational paper in program verification:

    - An Axiomatic Basis for Computer Programming. C A R (Tony) Hoare, 1969.
      https://dl.acm.org/doi/pdf/10.1145/363235.363259

    The question is what it means to prove a program correct?

    Hoare showed that programs can be proven via a small set of simple rules.

    === Q: What is a program? ===

    Definition suggestions?

    - (A list of) Executable instructions

    - A function that takes in fields and returns some
      output

    - A sequence of symbols in some alphabet
      (e.g., in binary, sequence of 0s and 1s)

    Other answers:

    - A Turing machine
      (or your favorite other model of computation)

    - An expression in the lambda calculus

    Definition we want:

        We want to decompose verifying properties
        of programs into verifying properties of
        smaller programs.
        (Most of the above abstractions do not
        give us this property)

    So we really want a definition of
    *structured program.*

    So let's define a program via a structured grammar.
    - Basically, a simple programming language.

    A program P is defined by the grammar

        Var ::= n1 | n2 | n3 | ...

        IntExpr
            IE ::=
                IE + IE
                | IE - IE
                | IE * IE
                | 0
                | 1
                | Var

        BoolExpr ::=
            BE ::=
                true
                | false
                | not BE
                | BE or BE
                | BE and BE
                | IE == IE
                | IE < IE

            // Could add, but probably unneeded
                | BoolVar

        Prog ::=
            | Var := IE // Assignment statement
            | if BE then Prog else Prog end
            | while BE do Prog end
            | Prog ; Prog

    Fundamentally - if we have
    expressions, variables, assignment, branching, looping, and sequencing --
        we have arbitrary programs.

    === Hoare triples ===

    Definition. The Hoare triple

        { P } C { Q }

    where P is a precondition, C is a program, and Q is a postcondition.
        - precondition is a formula (can have quantifiers)
        - program is a Prog (above grammar)
        - postcondition is a formula (can have quantifiers)

    To write proofs about programs, we just need rules for how we can deduce
    the statement

        { P } C { Q }

    For each grammar construct for constructing programs, i.e.

        Var := IE
        if BE then Prog else Prog end
        while BE do Prog end
        Prog ; Prog

    we will give a corresponding proof rule for how to deduce the corresponding
    Hoare triple.

*/

/*
    1. The sequencing rule

    Suppose we want to show

        { P } C1 ; C2 { Q }

    We show this by proving, for some intermediate condition R, that
    { P } C1 { R } and  { R } C2 { Q }.

    Thinking of this as a proof rule:

    From:

        { P } C1 { R }
        { R } C2 { Q }.

    We can deduce:

        { P } C1 ; C2 { Q }.

    (In fact, this is what Dafny is basically doing internally.)

    We should also give a grammar for preconditions and postconditions
    P, Q.

    Recap:

        - Hoare logic is an axiomatic system for writing proofs
          about programs (via a finite number of possible rules)

        - All programs are just assignments, conditionals, sequencing, and loops

            (and expressions and variables - used to build the above)

        - The Hoare triple { P } C { Q } means that C is correct with precond
          P and postcond Q

        - Game plan:
          For each program syntax constructor, we are going to give a Hoare logic
          rule for deducing (proving) the triple { P } C { Q }
          from some already-proven triples.

          That is, we give a "proof rule" which has the form:

          From:

            <some things we have already proven>

          ------------------------------

          Deduce that:

            <some things we can conclude>.

    ***** Where we ended for today, Feb 17. *****

    === Resuming from last time: the sequencing rule ===

    Recall sequencing rule above. As a deduction rule:

    From:

        { P } C1 { R }
        { R } C2 { Q }.

    We can deduce:

        { P } C1 ; C2 { Q }.

    === Sequencing rule in Dafny ===

    What does this look like in Dafny?

    Example:
*/

method Prog1(x: nat) returns (y: nat)
requires x >= 1
ensures y >= 2
{
    y := x + 1;
}

method Prog2(x: nat) returns (y: nat)
requires x >= 2
ensures y >= 4
{
    y := 2 * x;
}

method Prog(x: nat) returns (z: nat)
requires x >= 1
ensures z >= 4
{
    var y := Prog1(x);
    z := Prog2(y);
    return z;
}

// Or as a single inline program:

method ProgInline(x: nat) returns (z: nat)
requires x >= 1
ensures z >= 4
{
    var y := x + 1;
    // ***
    // Dafny implicitly figures out the intermediate condition required here!
    // Q: what is the intermediate condition?
    // How to check?

    // TODO

    // ***
    z := 2 * y;
    // return z;
}

/*
    Why don't we have to write the intermediate condition

        assert y >= 2

    explicitly?

    A:

    .
    .
    .
    .
    .

    This has to do with a topic we will cover in Part 3,
    Automating verification with weakest preconditions and strongest postconditions!

    === Poll ===

    Consider the Hoare triple

        { x == 1 } x += 1; x += 1; { y is odd }

    1. Suppose we wanted to prove this Hoare triple using the sequencing rule.
       How many logically inequivalent possible choices are there for R?

        A. 0
        A. 1
        B. 2
        C. 3 or more, but finite
        D. Infinite

    2. (Skip if you answered A or B :-) )
        Why is this not a problem in Dafny?
        That is, why does Dafny not get stuck having to search the space of possible choices if
        there is not a unique possible choice?

    https://forms.gle/Hs6piKkygQaaQYR28

    .
    .
    .
    .
    .
    .
    .
    .
    .
    .

*/

/*
    2. The conditional rule

    Q: How do we prove an if statement?

        if cond then C1 else C2 end

    (don't peak at the answer)

    From:



    Deduce:



    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...

    From:

        { P ^ cond } C1 { Q }
        { P ^ !cond } C2 { Q }

    Deduce:

        { P } if cond then C1 else C2 end { Q }.

    Examples:
*/

method ProgIf(x: nat) returns (y: nat)
requires 1 <= x <= 2
ensures (y == 2) || (y == 4)
{
    var x := x;
    if x == 1 {
        // assert (1 <= x <= 2) && (x == 1);
        x := x + 1;
        // x := Prog1(x);
        // assert (x == 2 || x == 4);
    } else if x >= 2 {
        // assert (1 <= x <= 2) && (x >= 2);
        x := 2 * x;
        // x := Prog2(x);
        // assert (x == 2 || x == 4);
    } else {
        // Do something else
    }
    y := x;
}

/*
    3. The assignment rule

    Assignment is the most interesting and surprising
    of the Hoare logic rules. (Even more counterintuitive than loop invariants?)
    It's the backbone of how Hoare logic works:

    Amazingly, it turns out that to prove a program about assignment, it suffices
    to evaluate the program "in reverse", in the following sense:

    Program we are given:

        x := E

    The Hoare rule:
    We may deduce:

        { Q[substitute x := E] } x := E { Q }.

    Examples:
*/

method Prog1Revisited(x: nat) returns (y: nat)
requires x >= 1
ensures y >= 2
{
    // what should be true here?
    // (x + 1) >= 2
    y := x + 1;
    // we want y >= 2
}

method Prog2Revisited(x: nat) returns (y: nat)
requires x >= 2
ensures y >= 4
{
    // need: (2 * x) >= 4
    y := 2 * x;
    // want: y >= 4
}

/*
    4. Weakening and strengthening

    So far our rules are self-contained and don't relate to the underlying
    logic for formulas.

    (In fact, I have left the logic of how to describe formulas (preconditions and postconditions)
    completely abstract! When we have

        { P } C { Q }

    I haven't said what P and Q are.
    We will give this in the next part.)

    This rule changes this:

    Example:
*/

method UseProg1(x: nat) returns (y: nat)
requires x == 10
ensures y >= 3
{
    y := Prog1(x); // how are we allowed to do this?
    y := y + 1;
}

/*
    Deduction rule:

    From:

        P ==> P'
        { P' } C { Q' }
        Q' ==> Q

    We can deduce:

        { P } C { Q }.
*/

/*
    5. Rules for assume and assert

    Early on in the class, we saw about assume and assert.
    We can also give Hoare rules for these, and they are quite interesting.

    What's the Hoare rule for assume?

    (don't peak at the answer)

    From:



    Deduce:



    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...

        { ? } assume φ; { Q }

    What's the Hoare rule for assert?

    (don't peak at the answer)

    From:



    Deduce:



    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...
    ...

        { ? } assert φ; { Q }

*/

/*
    6. The loop rule.

    It just is loop invariants.

    We need to invent a loop invariant (cleverly, from scratch)
    to prove the loop correct. Call this invariant Inv

    From:

        (i) P ==> Inv
        (ii) { Inv ^ cond } C { Inv }
        (iii) Inv ^ !cond ==> Q

    We can deduce:

        { P } while cond do C end { Q }

    Loops are the cases where we have to go in and help.
*/

/*
    ===== What is tractable / what is decidable? =====

    Ideally, we'd like to decide Hoare triples automatically; that is, we'd love to have a program
    that takes as input a triple like

        { P } C { Q }

    and decides if the Hoare triple is true or false for the program.

    Of course, as you might imagine, this is in general impossible!
    But what is surprising is that it is essentially possible for a large subset of programs,
    namely the loop-free programs.

    We will say what we mean more formally in part 3 (3-wp-sp.dfy).
    For now, the informal statement.
    First define the following:

        Definitions:

        Let φ be a formula and C be a program.

        - The **weakest precondition** of C is the weakest possible statement ψ
        such that

            { ψ } C { φ }

        is true.
        (I haven't proven that such a weakest statement exists, but it always
        does, at least for loop-free programs.)

        - The **strongest postcondition** of C is the strongest possible statement
        Ψ such that

            { φ } C { ψ }

        is true.

    Claim:
    Given any loop-free program C, precondition P, and postcondition Q, we can calculate automatically:

        + the weakest precondition Q' such that { Q' } C { Q } holds;

        + the strongest postcondition Q such that { P } C { P' } holds.

    Dafny is calculating these automatically.
*/

/*
    ===== On termination =====

    I've been ignoring an important point: termination!

    Dafny actually cares about termination.

    So far, the rules we gave for

        { P } C { Q }

    are what's called *partial correctness*.

        Def. Partial correctness:

    We also need *total correctness:

        Def. Total correctness:

    We can solve this by defining a triple like

        { P }_T C { Q }_T

    to denote total correctness.

    Q: Which rules need to change to support total correctness? :-)

    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
*/

/*
    ===== Relative completeness of Hoare logic =====

    You might ask the question:
    - Can everything that is true about a program be proven in Hoare logic?

    See the next part (2-fol.dfy) for some additional discussion on this.

    The main result about Hoare logic from this standpoint is that it is *relatively complete*,
    meaning that it can prove anything about a program that can be proven in first-order logic (FOL).

    Formal theorem statements:

    **Theorem 1.**
    Hoare logic is sound. That is:

        For all programs C and preconditions P and postconditions Q,
        if { P } C { Q } is provable in Hoare logic, then it is true:
        C satisfies the spec with precondition P and postcondition Q.

    **Theorem 2.**
    Hoare logic is not complete. That is: There is some program C,
    precondition P, and postcondition Q such that

        { P } C { Q }

    is true, but not provable in Hoare logic. In fact, we can just
    take C to be the empty program, and P to be true, and Q to be
    any true statement not provable in first-order logic. Any optional problem on HW4
    explores this a little more with more complex programs.

    Even though Hoare logic is not complete, we have:

    **Theorem 3.**
    Hoare logic is relatively complete. That is:
    For all preconds P, programs C, and postconds Q, if the fact

        "{ P } C { Q } is true"

    is provable *in an appropriate encoding using natural numbers in
    first-order logic*, then

        { P } C { Q }

    is provable in Hoare logic.
    Intuitively: we can prove in Hoare logic exactly what we can prove
    in FOL, it does not fundamentally increase expressiveness beyond
    FOL. It just introduces new syntax that is useful for verifying
    programs.

    ===== Summary and review =====

    Review:

    - Hoare triple: { P } C { Q } means

    - Grammar for programs C: to get arbitrary programs, we need

      + Expressions and variables

      + Assignment, Branching, Sequencing, and Loops

    - distinction between programs and logical propositions

        { P } C { Q }

        P, Q: propositions

        C: a program

        (Are logical propositions just Boolean expressions?
         No, they will be slightly more general!
         We allow Boolean expressions but we also want to allow quantifiers.)

    - giving additional rules: if we add additional syntax elements to our grammar for programs, we can
      give corresponding additional rules in Hoare logic. Above, we saw rules for

        assume
        assert

      On the HW you will explore this further, there is a problem that asks you to come up with a rule for
      a "case" statement, matching for two integers on whether
      they are <, =, or >.

    - def. of weakest precondition and strongest postcondition

      sneak peak: automatically deciding Hoare logic: for loop-free programs, weakest preconditions
      and strongest postconditions can be calculated automatically.

    - termination: distinction between *partial correctness* triples { P } C { Q } and *total correctness* triples,

        { P } C { Q }_T

    - soundness and relative completeness theorem for Hoare logic.

*/
