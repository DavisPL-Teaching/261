# Poll answers

Jan 6:
Can be correct or incorrect, depending on the spec

Jan 8:
All except E (The input x is always between 0 and 4)

Jan 13:
1. True
2. False
3. A, B, C, E, G

Jan 15:
1. FC, not FFC
2. FC, not FFC
3. not FC or FCC
4. not FC or FCC

Jan 27:
A, C, E, and F

Jan 29:
A, B, C, and E

Feb 3:
A, C, F.

Feb 5:
A, B, C, D, F. (All except: if statements, unused method calls.)

Feb 10:
D, E, F, I.
not G and H because we are assuming P and Q are syntactically valid Dafny expressions.

Feb 12:
1)
    1. (i) only
    2. (i) and (ii) only
    3. None (1 <= i <= n would be (ii) only)
    4. (i) and (ii) only
    5. (i) and (ii) only
    6. (i) and (ii)
    7. (ii) and (iii)
    8. (iii) only

2)
    result == ("Hello " * (i - 1)) + "Hello"
    AND i <= n.

Feb 17:
    All are possible: I, II, III, and IV.
    This remains true even if we restrict to candidate invariants I1, I2 that are actually true on all
    real traces of the program, as we discussed in class.

Feb 19:
1. E
2. We don't need to store all possibilities, because we can compute only one and use that.
   In fact, we can algorithmically compute the strongest possibility via the "strongest poscondition", and weakest possibility
   via the "weakest precondition", we will see roughly how this works in class.

Feb 24:
1. Yes
2.
    Sequencing: 5
    Branching: 0
    Assignment: 6 or more
    Loop: 3
    Strengthening/weakening: 3

Feb 26:
