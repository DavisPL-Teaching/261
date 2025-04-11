"""
Z3 helper functions

This file provides three functions:

- prove(spec) can be used instead of z3.prove.
  It tries to prove that the spec is always true.
  It returns PROVED, COUNTEREXAMPLE, or UNKNOWN.

- solve(spec) can be used instead of z3.solve.
  It tries to find a solution to the spec.
  It returns SAT, UNSAT, or UNKNOWN.

- get_solution(spec) can be used to get a solution
  to the spec, assuming that it is satisfiable (SAT).
  Otherwise it returns None.
"""

import z3

## Constants
SAT = z3.sat
UNSAT = z3.unsat
UNKNOWN = z3.unknown
PROVED = UNSAT
COUNTEREXAMPLE = SAT

"""
prove(spec)

Returns PROVED, COUNTEREXAMPLE, or UNKNOWN
"""
def prove(spec):
    solver = z3.Solver()
    solver.add(z3.Not(spec))
    result = solver.check()
    if result == UNSAT:
        print("proved")
    elif result == UNKNOWN:
        print("failed to prove")
    else:
        # result == SAT
        print("counterexample")
        print(solver.model())
    return result

"""
solve(spec)

Returns SAT, UNSAT, or UNKNOWN
"""
def solve(spec):
    solver = z3.Solver()
    solver.add(spec)
    result = solver.check()
    if result == UNSAT:
        print("no solution")
    elif result == UNKNOWN:
        print("failed to solve")
    else:
        # result == SAT
        print("solution found")
        print(solver.model())
    return result

"""
get_solution(spec)

The solution is returned as a Z3 "Model" object.
You can get the value of a variable x from a model by doing
    model[x]

Here is an example usage:
    x = z3.Int('x')
    spec = x > 5
    model = get_solution(spec)
    print(model[x])

Returns: either a Z3 model solution or None
"""
def get_solution(spec):
    solver = z3.Solver()
    solver.add(spec)
    result = solver.check()
    if result == SAT:
        return solver.model()
    else:
        return None
