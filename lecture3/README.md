# Lecture 3: Proofs and programs

  AKA: Dafny foundations

## Tuesday, February 17

Announcements:

- Project proposals due today!

  + I have created the assignment in Gradescope

- HW3 released: due next Tuesday (Feb 24, 11:59pm)

  https://piazza.com/class/mk1iokbuqef52p/post/59

  https://github.com/DavisPL-Teaching/261-hw3

Plan:

- Finish a few loose ends from last time

- Example from Piazza and poll (see `piazza-example.dfy`)

- Outline

- Hoare logic.

Questions?

Q about termination?
  - Dafny cares about termination, (i)-(iii) that we gave in class do not
  - There will be two variants of Hoare logic, one that cares about termination and one that doesn't
  - Note that if you add `decreases *` to any method/loop that
    might not terminate, and Dafny will accept the code.
