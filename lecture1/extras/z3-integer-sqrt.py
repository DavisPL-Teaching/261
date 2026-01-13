"""
This example was skiped in lecture.

Spoiler: it doesn't work! Z3 fails to prove the spec in this case.
"""

import pytest
import z3

def integer_sqrt_z3(x):
    return z3.ToInt(z3.Sqrt(z3.ToReal(x)))

def spec_integer_sqrt_z3(x):
    ans = integer_sqrt_z3(x)
    return z3.And(ans * ans <= x, (ans + 1) * (ans + 1) > x)

# ignore this line - helper file, will also be used on the HW!
from helper import prove, PROVED

@pytest.mark.skip
def test_prove_z3():
    # prove the spec on all inputs!
    x = z3.Int("x")
    spec = spec_integer_sqrt_z3(x)
    assert prove(z3.Implies(x == 5, spec)) == PROVED
