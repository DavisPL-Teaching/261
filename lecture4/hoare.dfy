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
            Formally: For any finite system of axioms A, such that
            every axiom in A is true (in the natural numbers N),
            there is a formula
            phi such that phi is true (in the natural numbers N), but
            phi is not provable in FOL from the axioms.

    + Axioms and assume: are used for:

        - statements about the base theory (nat, real numbers, strings)

        - external functions

        - you can't figure a certain case, add

            assume{:axiom} false;

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

        - Hoare logic is an axiom system for writing proofs
          about programs (via a finite number of possible rules)

        - All programs are just assignments, conditionals, sequencing, and loops

        - The Hoare triple { P } C { Q } means that C is correct with precond
          P and postcond Q

        - For each program syntax constructor, we are going to give a Hoare logic
          rule for deducing (proving) the triple { P } C { Q }.

    ***** Where we ended for today. *****
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
