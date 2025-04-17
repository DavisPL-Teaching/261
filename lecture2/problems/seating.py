"""
Seating arrangment generator

- All your family and friends are coming over for Thanksgiving dinner.
- You have a big round table that can seat everyone.
- You want to make sure that everyone has a seat at the table,
  but you don't want to sit any two people next to each other
  if they don't get along or if they are a risk of starting a
  heated argument.

How can you generate a valid seating arrangement?

=== Input ===

- A list of people, where each person is represented by a unique integer ID.
- A list of pairs of people who don't get along.

=== Example input ===

people: 1, 2, 3, 4
conflicts: (1, 2), (3, 4)

=== Example output ===

[1, 3, 2, 4]

or:
No solution
"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN
