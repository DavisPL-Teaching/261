/*

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
*/
