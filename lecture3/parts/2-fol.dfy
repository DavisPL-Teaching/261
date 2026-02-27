/*
    Lecture 3, Part 2:
    First-order logic (FOL)

    In the Hoare triple:

        { P } C { Q }

    P and Q are propositions.

    It was rightly pointed out that we have given only a grammar for C, and not for P and Q!

    P and Q can be given in any (plain) logic (not a program logic like Hoare logic),
    but we will take first-order logic to be our foundation here.

    Important concepts:

    - Syntax vs. semantics distinction.
    - True vs. provability distinction.

    ===== Poll =====

    Let WP(C, phi) denote the weakest precondition of C with postcondition phi.
    Let SP(C, phi) denote the strongest postcondition of C with precondition phi.

    1. Calculate WP(x := x + y; x := x * y, x == 10).

    2. Calculate SP(x := x + y; x := x * y, x == 10).

    https://forms.gle/wHyfU9g5MrwKQSZE8

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
    .
    .
    .
    .
    .
*/

/*
    ===== Syntax and semantics =====

    Let's start with the difference between syntax and semantics.
    We saw a bit of this in Lecture 2.

    SYNTAX

    A **logic** consists of
    - A set of variables
    - A set of function symbols (combine these to form expressions)
        // ex. function symbols: +, *, -
    - A set of relation symbols (combine these to form formulas, along with AND, OR, NOT, and equality)
        // ex. relation symbols: <, InRe, PrefixOf
    - Quantifiers forall and exists

    And a formal grammar for each of the above:

        Var ::= Var1 | Var2 | Var3 | ...
        Expr ::= FnSymbol(Expr, ..., Expr)
        Formula φ ::= φ ^ φ | φ v φ | !φ | Expr == Expr | RelSymbol(Expr, ..., Expr)
            | True
            | False
            | forall Var φ
            | exists Var φ.

    Examples:
        natural number arithmetic
        real number arithmetic
        theory of strings and regular expressions
        etc.
        (any other data type you might be interested in)

    Emphasize:
        A formula is just symbols! (syntax)
        We can *evaluate* a formula by plugging in a variable assigment (semantics)

    A "well-formed formula" is any formula created using the above rules --
    i.e. a sequence fo symbols from the above grammar (with parentheses to disambiguate as required).

    Examples in Dafny:
*/

method MethodName(x: int) returns (y: int)

method FormulaExamples() {
    // assert 1 + 1 == 2;
    // assert exists x : nat :: x + x == 2;
    // assert forall x : nat :: x + x == 2;
    // assert 1 + 1 == 3;
    // var x;
    // assert x + 1 == 2;

    // NOT well-formed-formulas:
    // assert + 1 1 == 2;
    // assert exists x : bool :: x + x == 2;
    // assert MethodName(x) == 3; // MethodName is a method, not a mathematical function
    // etc.

    // Think of: well-formed formula == valid Dafny syntax for an expression.
    // Expressions can be created from functions, but not methods.
}

/*
    SEMANTICS:

    Syntax is just symbols; it doesn't say anything about what the symbols mean.
    Semantics is how we plug in values and evaluate the symbols as real operations on
    a data type.

    For our purposes, we think of semantics as providing a particular meaning to each
    of the expressions, functions, and relations.

    A data type is defined by its function and relation symbols.

    Formally:
    A **structure** (think of: data type)
    is a set X together with operations for each function symbol and relation symbol.
    Example:
    - X := set of integers
    - operations:
        + := addition on integers
        * := multiplication on integers
        - := subtraction on integers.
        < := comparison on integers

    We have to define what it means to plug in (or evaluate)
    a variable assignment on a formula.

    A formula is *true* for a variable assignment v if...

    A variable assignment is a map:
        v: Var -> X

    Defined inductively:

        - for any expression e, e[v] evaluates to an element of X
          inductive case: if we encounter
          f(e_1, ..., e_n)
          we evaluate each of e_1, ..., e_n, then we apply the semantics for symbol f.

        - for a formula phi:

            (phi1 ^ phi2)[v] evaluates to (phi1[v]) and (phi2[v])
            (phi1 v phi2)[v] evaluates to (phi1[v]) or (phi2[v])

            (forall x: phi)[v] evaluates to?
                for any natural number n, we can modify v by adding x maps to n

            + true if phi[v[x ↦ n]] is true for *every* n
            + false if phi[v[x ↦ n]] is false for *some* n.

            (Note that if X is an infinite domain or infinite data type,
             this evaluation works over infinitely many n, so this is not
             evaluation in a strictly computable sense.)

    E.x. 1:

        (x + 3 == y + 4) ^ (x + 3 != y + 3) (evaluate at x = 1, y = 2)

        evaluates to false

    plug in and evaluate as we are used to.

    E.x. 2:

        for all x, there exists y such that y == x + 1

        evaluates to true because for any intenger literal n, if we map x ↦ n
        we get
            there exists y such that y == n + 1
        and from there we can plug in the integer literal n + 1 to get
            n + 1 == n + 1
        which is true.

    A *closed formula* is one in which all variables are bound by quantifiers.
    Typically we only consider truth for closed formulas.

    For a closed formula, the variable assignment v doesn't actually matter.

    So we can say that a closed formuila phi is true if phi[v]
    is true for any variable assigments v
    (or equivalently, if it is true for all variable assignments v).

    True is a special case of satisfiable and valid (why)?
    - Every true closed formula is satisfiable
    - Every true closed formula is valid
    - A formula phi with free variables x, y, z is satisfiable just means

        exists x: exists y: exists z: phi

    is true, and valid means

        forall x: forall y: forall z: phi

    is true.
*/

/*
    Dafny is a a proof assistant: it allows us to write proofs about
    formulas and programs.

    PROOFS:

    A proof is an argument via a sequence of lines that convinces the reader a
    statement is true.

    (We will see provability and truth are different.)

    === Proof Rules ===

    Syntax:
        "Γ ⊢ φ"
    means that φ is provable from the set of formulas Γ.
    (Think of Γ as the preconditions and φ as the postcondition or assertion we want to show.)

    What are the rules of proof?

    For each type of logical construct, we have to give a way to prove that construct --
    an "introduction rule" --
    and a way to use that construct to prove other things --
    an "elimination rule".

    True introduction:
        Γ ⊢ True.

    False elimination:
    If
        Γ ⊢ False
    Then:
        Γ ⊢ φ.

    From this point, let's start writing the rules in Dafny.
*/

lemma TrueIntro()
ensures true
{
    // Proof omitted - Dafny understands FOL introduction rules
}

predicate p() // Any predicate
// Note: a predicate in Dafny is just a Boolean-valued formula.
// It is equivalent to write the following:
function p_alt(): bool

lemma FalseElim()
requires false
ensures p()
{
    // sometimes known as: "Ex falso quodlibet"
    // or the "rule of explosion"
}

/*
    And introduction:
    If:
        Γ ⊢ φ1
    and
        Γ ⊢ φ2
    then:
        Γ ⊢ φ1 ^ φ2

    And elimination:
    If:
        Γ ⊢ φ1 ^ φ2
    then:
        Γ ⊢ φ1
    and
        Γ ⊢ φ2
*/

predicate q()
// function q() returns (y: bool)

lemma AndIntro()
requires p()
requires q()
ensures p() && q()
{}

// Is Dafny just giving us a green check on everything? (Try something to check)

lemma AndElim()
requires p() && q()
ensures p()
ensures q()
{}

/*
    Are all the elim-rules just the intro-rules in reverse?

    No:
    Or introduction is a bit more asymmetric!
*/

lemma OrIntro1()
requires p()
ensures p() || q()
{}

lemma OrIntro2()
requires q()
ensures p() || q()
{}

// This fails - why?
// lemma OrElimAttempt()
// requires p() || q()
// ensures p() // <-- ?
// {}

predicate r()

lemma OrElim()
requires p() || q()
requires p() ==> r()
requires q() ==> r()
ensures r()
{}

/*
    I will just mention that there are deeper reasons that Or is not symmetric with And.
    It has to do with the difference between classical logic and "constructive" logic,
    where the latter is more useful for capturing the rules of proofs, because proofs have to
    be constructive.

    (I cannot claim I have a proof, without actually showing one)
    (take a class in proof theory if interested
    some video lectures:
    https://www.youtube.com/watch?v=YRu7Xi-mNK8
    https://www.youtube.com/watch?v=grjMRgmjddE
    )

    Dafny works in classical logic.
    Some proof assistants work in constructive logic (Coq/Rocq)

    Not introduction:

    Not is closely related to False.

    Not has two elim rules!
    (This is again an artifact of our classical logic proof system.
     It is a bit of a red flag that perhaps we are not doing things correctly,
     which we are not, and in Gentzen's sequent calculus this defect is not present.)
*/

lemma NotIntro()
requires p() ==> false
ensures !p()
{}

lemma NotElim1()
requires !p()
requires p()
ensures false
{}

// Constructive logic drops this rule
// If you venture to use other proof assistants, many are constructive; see Coq/Rocq.
lemma NotElim2()
requires !!p()
ensures p()
{
    // The fact that this rule passes, means that Dafny is using classical logic,
    // not constructive logic.
}

/*
    At this point, I've given enough information that we could prove any Boolean formula.

    Have we covered everything?

    No: we have no rules for expressions and relations.

    We also have no theory-specific rules...
*/

// Some integer variables
const x: int
const y: int
const z: int

lemma EqIntro1()
ensures x == x
{}

lemma EqIntro2()
requires x == y
ensures y == x
{}

lemma EqIntro3()
requires x == y
requires y == z
ensures x == z
{}

// Equality elim rule?
// It goes like this:

predicate p_of_x(x: int)

predicate q_of_x(x: int)

// Intuition: if x == y, we can substitute y for x.
lemma EqElim()
requires p_of_x(x)
requires x == y
ensures p_of_x(y)
{}

/*
    Theory-specific rules:
    For theories we rely on axioms for the base theory.

    If we're doing proofs, we formalize the data type we have in mind via
    a set of axioms.

    Axiom = unproven assumption

    Related to the assume keyword (see lecture 1)

    For integers: most commonly axiomatized via "Peano arithmetic"
*/

// example
method IntegerSuccesor(n: nat)
ensures n + 1 != n
{
    // This is not provable using any of the rules so far!
    // So it requires an axiom that explains what + is and what it does.
}

// Useful when modeling external/foreign functions or libraries (why?)...

// example
method{:axiom} SysInfo() returns (s: string)
ensures s == "macOS" || s == "windows" || s == "linux"

// another example
method{:axiom} DisplayPixels(
    window_width: nat,
    window_height: nat,
    x: nat,
    y: nat,
    w: nat,
    h: nat
) returns (success: bool)
requires x + w <= window_width
requires y + h <= window_height
ensures success

// - After compiling the code, Dafny will then link it with the external method at runtime.

// Assume keyword

method TestAssume(x: nat) returns (result: nat)
ensures
    result == x + 1
{
    result := x;
    if x == 0 {
        result := 1;
    } else {
        // some proof case I am stuck on - skip for now
        result := result + 1;
        assume{:axiom} result == x + 1;
    }
}

/*
    Axioms are very powerful but be especially careful!
    What can go wrong?
*/

method TestAssume2(x: nat) returns (y: nat)
ensures
    y == x
{
    // oops...
    assume{:axiom} x == 5;
    y := 5;
}

// Has global implications: one assume statement somewhere in the code,
// if it assumes something false,
// can invalidate the entire verification of the entire code base.

// ********** Where we left off for today **********

/*
    === May 12 ===

    Recap from last time:

    * Truth vs. provability distinction



    * This connects back to some questions from HW2!
    Remember problem 2 about integers vs. reals. vs. truncated integers?


    * Axioms, assume statements (and their purpose)

      (See examples above and below for good usage & what can go wrong)

    * External methods

      Something to demonstrate: `dafny build --target:py exercises.dfy

*/

// lemma{:axiom} AssumeFalse()
// ensures false

// lemma YourProgramIsCorrect()
// ensures 1 + 1 == 3 {
//     AssumeFalse();
// }

/*
    Finally, quantifiers

    Here for the first time we will see that Dafny cannot do the proof automatically.
    Also the syntax is a little less intuitive.
    (There are deeper reasons for this -- for now we can consider it as a minor inconvenience.)
*/

// Function representing an arbitrary expression
function expr(): int

// could also do it with a function with arguments or any other expression... e.g.:
// const expr: int
// function expr(x: int): int

lemma ForallElim(a: int)
requires forall x: int :: p_of_x(x)
ensures p_of_x(expr())
{}

// Forall intro requires some more idiosyncratic syntax.
// One way to show it is with an axiom lemma, as follows:

lemma {:axiom} ForallIntroEx(a: int)
ensures p_of_x(a)
// {} // What happens if we uncomment this line?

lemma ForallIntro()
ensures forall x: int :: p_of_x(x)
{
    // This is special Dafny syntax: a forall proof statement block
    forall x: int
    ensures p_of_x(x)
    {
        ForallIntroEx(x);
    }
}

// The idea of the axiom approach is to show how you would apply this in your own projects,
// where in that case it would not actually be an axiom, it would be something you already proved.

// Rules for exists

lemma ExistsIntro()
requires p_of_x(expr())
ensures exists x: int :: p_of_x(x)
{
}

lemma ExistsElim() returns (y: int)
requires exists x: int :: p_of_x(x)
ensures p_of_x(y)
{
    // This is again special Dafny syntax: the *assign such that* block:
    var x :| p_of_x(x);
    // Assign to our return value
    y := x;
}

/*
    We are done!

    === Philosophical discussion ===

    Why do we care about first-order logic?

    -> All verification is built on the base logic.

    -> As a result, FOL also gives us the limits of what we can prove, and what we cannot.
        (Foreshadowing:
            Most program logics are what we call "relatively complete", meaning we can prove anything
            for programs that we could have proved in the base logic.
            That means, that if we can't prove something in FOL we are out of luck for proving it about
            your favorite computer program :)
        )

    === Some provocative questions ===

    Q: Is Dafny and its FOL base
       sufficient to prove all true statements that come in practice?

    Arguments for:
    (These are just included as curiosities, we did not cover this in class)

        Argument from set theory:
        All of computer science can be formalized in mathematics,
        and all of known mathematics can be formalized in set theory
        (most commonly a set theory known as ZFC).
        Set theory is a theory of axioms in first-order logic,
        so first-order logic is enough.

        The argument from "code that is actually written":
        People don't write code that they don't know why is true!

        Godel's completeness theorem:
        Godel showed that FOL formulas are provable if and only if
        they are true in *every* structure satisfying the axioms.

    Arguments against:

        Fitch's paradox:
        If all truths are knowable, then all truth's are known.
        https://en.wikipedia.org/wiki/Fitch%27s_paradox_of_knowability

        Godel's incompleteness theorem:
        Shows that not all statements that are true are provable.

    Q: why is it called first-order logic?

    A: Variables (x, y, z) range over elements of some structure
       (natural numbers, reals, etc.), so called "first-order" quantification.
       Second-order quantification involves quantifying over sets of elements,
       not single elements. (Like sets of natural numbers, or even
       relations between natural numbers.)
*/

/*
    === End notes ===

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

    The connection between proofs and programs is demonstrated in Hoare logic, as we covered last time.
    See relative completeness statements at the bottom
    of that lecture.
*/
