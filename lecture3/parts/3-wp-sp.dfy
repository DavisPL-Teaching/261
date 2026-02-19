/*
    Lecture 3, Part 2:

    Automating verification with weakest preconditions and strongest postconditions

    === Definitions ===

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

    Weakest preconditions and strongest postconditions can be
    computed automatically for any loop-free program.
    This means that all of the rules for Hoare logic can be automated, aside from the loop rule.
*/
