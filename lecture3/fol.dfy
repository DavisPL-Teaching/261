/*
    First-order logic (FOL)

    ===== Syntax and semantics =====

    Let's start from the beginning.
    This time, we don't prove anything without checking in Dafny.
    So we can be assured we aren't making any mistakes.

    Difference between syntax and semantics.

    SYNTAX

    Recall:

    A logic consists of
    - A set of variables
    - A set of function symbols (combine these to form expressions)
    - A set of relation symbols (combine these to form formulas, along with AND, OR, NOT, and equality)
    - Quantifiers forall and exists

    And a formal grammar for each of the above:

        Var ::= Var1 | Var2 | Var3 | ...
        Expr ::= FnSymbol(Expr, ..., Expr)
        Formula φ ::= φ ^ φ | φ v φ | !φ | Expr == Expr | RelSymbol(Expr, ..., Expr)
            | forall Var φ
            | exists Var φ.

    A "well-formed formula" is any formula created using the above rules --
    i.e. a sequence fo symbols from the above grammar (with parentheses to disambiguate as required).

    SEMANTICS:

    A **structure** is a set X together with operations over the functions and relation symbols.
    Example: natural numbers, real numbers, ...

    A formula is *true* if... (special case of satisfiable and valid)
    Defined inductively:

        ...

    PROOFS:
    What about proofs?
    Traditionally in logic, after we define syntax and semantics
    we wish to define two notions:

    Syntactic implication:

        Gamma ⊢ φ

    where Gamma is a set of formulas (axioms) and φ is the implied formula, and semantic implication:

        Gamma ⊨ φ

    where Gamma is a set of formulas and φ is the implied formula.

    We are interested in provability (because we want to know what we can prove about programs), so we focus
    on syntactic implication.

    For this we have "introduction" and "elimination" rules for each type of operator in our grammar.

    True introduction:
        Γ ⊢ True.
    False elimination:
    If
        Γ ⊢ False
    Then:
        Γ ⊢ φ.

    ***** Wait a second!!!!! *****
    Ugh, this is just math! I thought we were going to use computers to write and check proofs for us!

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
{}

/*
    Have we covered everything?

    No: we have no rules for expressions and relations.

    We also have no theory-specific rules, but this is OK - for theories we rely
    on axioms for the base theory.
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

lemma EqElim()
requires p_of_x(x)
requires x == y
ensures p_of_x(y)
{}

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

    Why do we care about first-order logic?

    -> All verification is built on the base logic.

    -> As a result, FOL also gives us the limits of what we can prove, and what we cannot.
        (Foreshadowing:
            Most program logics are what we call "relatively complete", meaning we can prove anything
            for programs that we could have proved in the base logic.
            That means, that if we can't prove something in FOL we are out of luck for proving it about
            your favorite computer program :)
        )

    Are there things that are true that we can't prove in FOL?

    Yes and No:

        Godel's completeness theorem:

        Godel's incompleteness theorem:

    Q: why is it called first-order logic?

    A:
*/
