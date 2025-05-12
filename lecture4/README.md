# Lecture 4: Proofs and programs

## Tuesday, May 13

Announcements:

- I will give feedback on proposals soon, by the end of this week!

- HW3 is due Friday
  https://github.com/DavisPL-Teaching/261-hw3

- Midterm study guide:
  `exam/study-guide.md`

    + Midterm is in class 1 week from today: Tuesday, May 20

- Project presentations and final report:
  see `project/presentation.md`, `project/report.md`

- **Optional HW4:**

Plan today:

- Cover some things from lecture3/fol.dfy

- Cover lecture 4 on Hoare logic.

## Lecture

This lecture will study the foundations behind proofs and programs,
and the concepts of how Dafny works behind the scenes.

We have seen:

- proofs in FOL

Underlying questions:

- How does Dafny determine whether a program is correct?
- How to proofs in first-order logic relate to programs?

We will study three topics:
Hoare logic, dynamic logic, and the Curry-Howard correspondence.

A good understanding of these topics (just like the first-order logic material)
will help you understand why verification in Dafny works,
and when it doesn't (and how to go about fixing it).
