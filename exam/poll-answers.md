# Poll answers

April 1:
Either answer is valid (it depends on the definition you came up with).

April 3: E Only.
"The input to is_even is always between 0 and 4" is not a valid specification as it is a property
that constraints how is_even is used, not a true-or-false property about the function itself.

April 8 poll #1:
True, False
A, B, C, E, and G.

April 8 poll #2:
all of row 4, all of column 3, and the diagonal, and 1 => 2.
```
x x x _ _ _ _
_ x x _ _ _ _
_ _ x _ _ _ _
x x x x x x x
_ _ x _ x _ _
_ _ x _ _ x _
_ _ x _ _ _ x
```

April 10 poll:
A, C, E, F (assert True, assume True, assert P if it immediately follows assume P, and assume P if it immediately follows assert P).

April 15 poll:
A, B, C, and E

April 17 poll:
1. Satisfiable only
2. B only (all valid formulas are satisfiable)

April 22 poll:
Yes to both: decidable and NP-hard.

April 24:
C, D, E, and F.

April 29:
B, C, and F.
(A and G are limitations of Dafny.)

May 1:
All answers (A, B, C, D, E, F). (F optional)

May 6:
(Your answers do not have to be valid Dafny syntax, but the Dafny syntax version is below)
1. Precondition:
    a.Length >= 1
2. Postconditions:
    exists i :: 0 <= i < a.Length && a[i] == result
    forall i :: 0 <= i < a.Length ==> a[i] >= result

May 8:
D, E, F, and H.
