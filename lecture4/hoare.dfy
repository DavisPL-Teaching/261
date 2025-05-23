/*
    === May 13 ===

    === Poll ===

    Poll: some review and practice with loop invariants.

    https://forms.gle/1qEvaDUcmPjhxFg49

    Example program:

    Assume that the syntax s * n works as in Python
    (multiply a string by an integer to repeat it n times).
*/

method HelloNTimes(n: nat) returns (result: string)
// requires n > 0
// ensures result == ("Hello " * (n - 1)) + ("Hello")
{
    result := "Hello";
    var i := 1;
    while (i < n) {
        result := result + " Hello";
        i := i + 1;
    }
    return result;
}

/*
    For each of the following, which of the conditions of a loop invariant are satisfied?
    ((i), (ii), and (iii))?

    - result == "Hello"
    - exists m: result == ("Hello " * (m - 1)) + ("Hello")
    - 0 <= i < n
    - 1 <= i <= n
    - result == ("Hello " * (i - 1)) + "Hello"

    === Truth vs. provability in first-order logic ===

    Finishing up and recap from last time:
    see fol.dfy.

    Summarize key points from fol.dfy:

    + Truth vs. provability distinction: remember we defined what it means
        for a formula to be true in a structure (like the natural numbers or real
        numbers) - this was a recursive/inductive definition.

        A statement is provable though if it can be deduced by a finite sequence
        of allowed rules (in FOL),
        including from axioms.

        Incompleteness theorem (Godel):
            Not all true statements are provable.
            Formally: For any finite set of axioms A, such that
            every axiom in A is true (in the natural numbers N),
            there is a formula φ such that
            - φ is true (in the natural numbers N), but
            - φ is not provable in FOL from the set of axioms A.

            (More generally: this is true if A is a recursively enumerable set of axioms,
             not just finite.)

    + Axioms and assume: are used for:

        - statements about the base theory (nat, real numbers, strings)

        - external functions

        - you can't figure a certain case, add

            assume{:axiom} false;

          as a temporary case, come back to it later!

    === Connection between proofs and programs? ===

    The connection between proofs and programs is demonstrated in a formalism
    known as Hoare logic.

    Tony Hoare:
    - https://en.wikipedia.org/wiki/Tony_Hoare
    - also known as: C. A. R. Hoare
    - British computer scientist
    - Born 1934 (still alive!)
    - Won the Turing award in 1980 (45 years ago now)
    - Also famous for: inventing the null reference (calling it his "billion-dollar mistake")

    Probably the most foundational paper in program verification:

    - An Axiomatic Basis for Computer Programming. C A R (Tony) Hoare, 1969.
      https://dl.acm.org/doi/pdf/10.1145/363235.363259

    The question is what it means to prove a program correct?

    Hoare showed that programs can be proven via a small set of simple rules.

    === Q: What is a program? ===

    We have a grammar for formulas, but not programs...

    Suggestions?

    - A Turing machine with input and output

    - Structured programs:
        Assignments for variables, conditionals (if-then-else) and loops
        and...?
        input?
        output?
        data types or numbers?
        expressions or operations?
        Sequencing: C1; C2

    This is correct:
    To write arbitrary programs, we just need constructs for
    variable assignment, some construct for conditional branching,
    loops, and sequencing.

    How is the program executed? (Program semantics - we will assume
    the intuitive semantics we have in mind for the above is correct.)

    Is a program with a syntax error a program?
    Let's say no.

    So let's give a grammar:

    Expr ::= 0 | 1 | Var | Expr + Expr | Expr * Expr | Expr - Expr

    (same as formulas, but no quantifiers)
    BoolExpr ::= True | False | BoolExpr ^ BoolExpr | BoolExpr v BoolExpr
        | !BoolExpr | Expr < Expr | Expr == Expr

    Prog ::=
        Var := Expr
        | if BoolExpr then Prog else Prog end
        | while BoolExpr do Prog end
        | Prog ; Prog

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
*/

/*
    1. The sequencing rule

    Suppose we want to show

        { P } C1 ; C2 { Q }

    We show this by proving, for some intermediate condition R, that
    { P } C1 { R } and  { R } C2 { Q }.

    Thinking of this as an "introduction rule"

    From:

        { P } C1 { R }
        { R } C2 { Q }.

    We can deduce:

        { P } C1 ; C2 { Q }.

    Recap:

        - Hoare logic is an axiomatic system for writing proofs
          about programs (via a finite number of possible rules)

        - All programs are just assignments, conditionals, sequencing, and loops

        - The Hoare triple { P } C { Q } means that C is correct with precond
          P and postcond Q

        - For each program syntax constructor, we are going to give a Hoare logic
          rule for deducing (proving) the triple { P } C { Q }.

    ***** Where we ended for today. *****

    === May 15 ===

    Poll:
    https://forms.gle/mZhY57M6o5PKecbB6

    1. A few more loop invariants about HelloNTimes

    2. Which of the following is true about the relationship between Dafny and logic?
    (select all that apply)

    Assume we are just working with programs that operate over integers (with axioms over the integers), and that there are no other axioms/assume or external functions.

    A. Everything provable in first-order logic is provable in Dafny.
    B. Everything provable in Hoare logic is provable in Dafny.
    C. Everything provable in Dafny is provable in Hoare logic.
    D. Everything provable in Dafny is provable in first-order logic.

    === Resuming from last time: the sequencing rule ===

    Recall sequencing rule above. As a deduction rule:

    From:

        { P } C1 { R }
        { R } C2 { Q }.

    We can deduce:

        { P } C1 ; C2 { Q }.

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
    // How to check?
    // assert y >= 2;
    // Why don't we have to write this explicitly?
    // (More on this soon)
    // ***
    z := 2 * y;
    // return z;
}

/*
    **Aside:**
    Automating verification with weakest preconditions and strongest postconditions

    Definition:

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

    Examples:

    - Weakest precondition of x := x + 1 with respect to x == 2?

        Weakest possible precondition is?
        x == 1.

    - Strongest postcondition of y := x with respect to x >= 4?

        Strongest possible postcondition is?
        x >= 4 && y >= 4 && x == y

    Both weakest precondition and strongest postcondition are defined up to
    formula equivalence, i.e., weakest/strongest possible formula (up to equivalence)
    such that ...

    We will see that weakest preconditions and strongest postconditions can be
    computed automatically for any loop-free program.
    This means taht all of the rules for Hoare logic can be automated, aside from the loop rule.
*/

/*
    2. The conditional rule

    How do we prove an if statement?

        if cond then C1 else C2 end

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
    first-order logic for formulas.

    This rule changes this:
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

    Then I can deduce:

        { P } C { Q }.
*/

/*
    5. Rules for assume and assert

    Early on in the class, we saw about assume and assert.
    We can also give Hoare rules for these, and they are quite interesting.

    What's the Hoare rule for assume?

        { ? } assume φ; { Q }

    What's the Hoare rule for assert?

        { ? } assert φ; { Q }

*/

/*
    6. The loop rule.

    It just is loop invariants.

    We need to invent a loop invariant (cleverly, from scratch)
    to prove the loop correct. Call this invariant I

    From:

        (i) P ==> I
        (ii) { I ^ cond } C { I }
        (iii) I ^ !cond ==> Q

    We can deduce:

        { P } while cond do C end { Q }

    Loops are the cases where we have to go in and help.
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
    any statement not provable in FOL. Any optional problem on HW4
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
*/
