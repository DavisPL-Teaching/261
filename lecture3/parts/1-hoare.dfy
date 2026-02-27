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
requires x >= 1 // P
ensures y >= 2 // R
{
    y := x + 1;
}

method Prog2(x: nat) returns (y: nat)
requires x >= 2 // R
ensures y >= 4 // Q
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
requires x >= 3
ensures z >= 8
{
    var y := x + 1;

    // ***
    // Dafny implicitly figures out the intermediate condition required here!
    // Q: what is the intermediate condition?
    // How to check?

    // TODO
    assert y >= 4;

    // ***
    z := 2 * y;

    // return z;
}

/*
    Why don't we have to write the intermediate condition

        assert y >= 2

    explicitly?

    Dafny infers it automatically.
    This has to do with a topic we will cover in Part 3,
    Automating verification with weakest preconditions and strongest postconditions!

    Observation:
        - R appears in the premises of the sequencing rule but not in the conclusion -
          therefore we have to synthesize it from scratch

        - there may be multiple possible Rs.

    === Poll ===

    Consider the Hoare triple

        { x == 1 } x += 1; x += 1; { x is odd }

    1. Suppose we wanted to prove this Hoare triple using the sequencing rule.
       How many logically inequivalent possible choices are there for R?

        A. 0
        B. 1
        C. 2
        D. 3 or more, but finite
        E. Infinite

    2. (Skip if you answered A or B :-) )
        Why is this not a problem in Dafny?
        That is, why does Dafny not get stuck having to search the space of possible choices if
        there is not a unique possible choice?

    https://forms.gle/Hs6piKkygQaaQYR28

    1. The space of possible valid Rs is basically any set of integers which contains 2 and is contained
       in all even numbers.

        e.g.,

            x == 2
            x == 2 or x == 42
            x == 2 or x == 4 or x == 8
            x is even
            x is even and x <= 10
            x is even and x <= 12
            x is even and x >= -10
            x is even and x >= -12

        2. Dafny is not searching over all of these automatically, but just computes one "canonical" representative
           assertion, which it turns out (we will see) can be computed in a completely algorithmic way.

            possible canonical choices?

                x == 2
                ^^^^^^ strongest possible intermediate condition R
                       (i.e. smallest set)

                          i.e. strongest postcondition under which { x == 1 } x + 1 { R } is valid.

                x is even
                ^^^^^^^^^ weakest possible intermediate condition R
                          (i.e. largest set)

                          i.e., weakest precondition under which { R } x += 1 { x is odd } is valid.

            Claim: either of these can be computed algorithmically.

            Dafny can just either:

                - compute strongest postcondition for x == 1 and C1 = x += 1; use that for R

            or:

                - compute weakest precondition for "x is even" and C2 = x += 1; use that for R.
*/

/*
    2. The conditional rule

    Q: How do we prove an if statement?

        if cond then C1 else C2 end

    (don't peak at the answer)

    From:

        { P && cond } C1 { Q }

        { P && !cond } C2 { Q }

    Deduce:

        { P } if cond then C1 else C2 end { Q }

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

    Amazingly, it turns out that to prove a Hoare triple about assignment, it suffices
    to evaluate the program "in reverse", in the following sense:

    Given a program:

        x := E

    and any postcondition

        Q

    We may deduce:

        { Q[substitute x := E] } x := E { Q }.

    Examples:
*/

method Prog1Revisited(x: nat) returns (y: nat)
requires x >= 1
ensures y >= 2
{
    // what do I know here:
    // x + 1 >= 2
    // equiv.: x >= 1

    y := x + 1;

    // we want y >= 2
}

// trying to prove the triple: { x >= 1 } y := x + 1 { y >= 2 }

method Prog2Revisited(x: nat) returns (y: nat)
requires x >= 2
ensures y >= 4
{
    // need: (2 * x) >= 4
    // need: (thing that we set y to) >= 4
    y := 2 * x;
    // want: y >= 4
}

/*
    4. The loop rule.

    It just is loop invariants.

    We need to invent a loop invariant (cleverly, from scratch)
    to prove the loop correct. Call this invariant Inv

    From:

        (i) P ==> Inv
        (ii) { Inv ^ cond } C { Inv }
        (iii) Inv ^ !cond ==> Q

    We can deduce:

        { P } while cond do C end { Q }

    Observations:

    - This reduces verification of a program involving loops to that of a program not involving loops
      (as we've seen)

    - Like the sequencing rule, there is stuff that appears in the premises of the rule that didn't
      show up in the conclusion.

        (i.e., this loop invariant Inv)

    - Unlike with sequencing, there's not in general any way to come up with Inv algorithmically.

    We truly need to resort to some sort of flash of insight of some kind
    (reasoning task - invariant synthesis)

    Loops are the cases where we have to go in and help.
*/

/*
    5. Weakening and strengthening

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
    That's it!
    Rule 1-5 is Hoare logic.

    Using rules 1-5, we can verify properties of arbitrary programs purely by reduction
    to properties about the underlying logic.

    But real programming languages have other syntax

    - maybe you want to do for loops, not just while loops!

    - maybe you want to add something for functions, function application, etc.

    - general process: add some other syntax element; then add a corresponding rule for that syntax element.

      (HW has a question that explores this)

    One example:

    === Adding additional rules ===

    6. Rules for assume and assert

    Early on in the class, we saw about assume and assert.

        in Dafny: assert and assume{:axiom}

    We can also give Hoare rules for these, and they are quite interesting.

    What's the Hoare rule for assume?

    (don't peak at the answer)

    From:

        P ==> R
        R ==> Q

    Deduce:

        { P } assert R; { Q }

    (I think this works)

    Equivalent rule:

    From:

        ---

    Deduce:

        { P && Q } assert P; { Q }

    for assume:

    From:

        ---

    Deduce:

        { P ==> Q } assume P; { Q }

        or equivalently:

        { not P or Q } assume P; { Q }

    in particular:

        { false ==> Q } assume false; { Q }

        i.e.

        { true } assume false; { Q }
                               ^^^^^ any postcondition we want!
                                     (cheating)

    ***** where we ended for today *****

*/

/*
    ===== Poll =====

    Consider the following program to multiply two numbers:

*/

method Multiply(x: nat, y: nat) returns (result: nat)
    // Comment out to test this example
    // requires false
    ensures result == x * y
{
    // {{ Q6[substitute result := 0] }}
    result := 0;
    // {{ Q6 }}

    // {{ Q5[substitute x_ := x] }}
    var x_ := x;
    // {{ Q5 }}

    while x_ > 0
        invariant x >= x_ >= 0
        invariant result == y * (x - x_)
    {

        // {{ Q4[substitute y_ := y_] }}
        var y_ := y;
        // {{ Q4 }}

        while y_ > 0
            invariant x >= x_ >= 0
            invariant y >= y_ >= 0
            invariant result == y * (x - x_ + 1) - y_
        {

            // {{ Inv && y_ > 0 }}
            // BODY
            // {{ Inv }}

            // have from top of the loop is:
            // Inv && y_ > 0
            // which is:
            /* {{
                x >= x_ >= 0
                && y >= y_
                && result == y * (x - x_ + 1) - y_
                && y_ > 0
            }} */

            // ** application of strengthening/weakening here

            // NEED:
            /* {{
                x >= x_ >= 0
                && y >= (y_ - 1)
                && y_ > 0
                && result == y * (x - x_ + 1) - y_
            }} */
            y_ := y_ - 1;
            /* {{
                x >= x_ >= 0
                && y >= y_ >= 0
                && result + 1 == y * (x - x_ + 1) - y_
            }} */

            /* {{
                x >= x_ >= 0
                && y >= y_ >= 0
                && result + 1 == y * (x - x_ + 1) - y_
            }} */
            result := result + 1;
            /* {{
                x >= x_ >= 0
                && y >= y_ >= 0
                && result == y * (x - x_ + 1) - y_
            }} */


        }

        // {{ Q3[substitute x_ := x_ - 1] }}
        x_ := x_ - 1;
        // {{ Q3 }}
    }
}

/*
    1. Is the program correct?

    2. To prove the program correct via Hoare logic, how many times should we apply each of the 5 rules?

        (sequencing rule, conditional rule, assignment rule, loop rule, strengthening/weakening)

    https://forms.gle/JPMp8CVJnbVGRcKj7

    ===== What is tractable / what is decidable? =====

    Ideally, we'd like to decide Hoare triples automatically; that is, we'd love to have a program
    that takes as input a triple like

        { P } C { Q }

    and decides if the Hoare triple is true or false for the program.

    Of course, as you might imagine, this is in general impossible!

        (Any nontrivial semantic property about computer programs
         is undecidable -- Rice's theorem)
        (e.g.: { True } C { x == 1 } -- already provably undecidable.)

    But what is surprising is that it is essentially possible for a large subset of programs,
    namely the loop-free programs.

    We will say what we mean more formally in part 3 (3-wp-sp.dfy).
    For now, the informal statement.
    First define the following:

        Definitions:

        Let φ be a formula and C be a program.

        - The **weakest precondition** of C is the weakest possible statement ψ (up to logical equivalence)
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

        + the strongest postcondition P' such that { P } C { P' } holds.

    Dafny is calculating these automatically.
*/

/*
    ===== On termination =====

    I've been ignoring an important point: termination!

    Dafny actually cares about termination.

    So far, the rules we gave for

        { P } C { Q }

    are what's called *partial correctness Hoare logic*.

        Def. Partial correctness:
            A program is partially correct if, in any input
            satisfying the precondition P,
            if we execute the program, and **if** it terminates,
            the end state satisfies the postcondition Q

    We also need *total correctness:

        Def. Total correctness:
            A program is totally correct if, in any input
            satisfying the precondition P,
            if we execute the program, **then** the program terminates, **and**
            the end state satisfies the postcondition Q
            We can solve this by defining a triple like

        { P }_T C { Q }_T

    to denote total correctness.

    Q: Which rules need to change to support total correctness? :-)

    For this class, we will only care about partial correctness,
    but Dafny is internally using total correctness;
    and this is the reason for those `decreases` clauses
    that you may have seen come up.

    To ask Dafny to do partial correctness, just add
    `decreases *` to every method and loop (usually not necessary).

    *** where we ended for Feb 24 ***

    A to Q above: only the while rule

    we should guarantee that the loop terminates...

    rough idea: we have to define some positive integer quantity
    that is always decreasing on every iteration.

        e.g. quantity: x + y

        in Dafny: `decreases x + y`

        Just need to add a condition (iv) to the while rule for
        this decreases thing.
*/

/*
    ===== Relative completeness of Hoare logic =====

    You might ask the question:
    - Can everything that is true about a program be proven in Hoare logic?

    See the next part (2-fol.dfy) for some additional discussion on this.

    The main result about Hoare logic from this standpoint is that it is *relatively complete*,
    meaning that it can prove anything about a program that can be proven in first-order logic (FOL).

    In logic we care about soundness & completeness:

        The logic is sound = "everything that is provable is true"

        The logic is complete = "everything that is true is provable"

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

    I.e.: we've proven everything that we possibly can about programs,
    i.e., we are no weaker than the underlying logic for proving properties
    about P and Q.

    ===== Summary and review =====

    Review:

    - Hoare triple: { P } C { Q } means

        (We use the partial correctness version:
         *if* the program is executed in a state satisfying P,
         and we execute C, *and if* it terminates, then the end
         state satisfies Q.)

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
