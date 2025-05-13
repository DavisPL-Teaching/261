# Lecture 4: Proofs and programs

## Tuesday, May 13

Several announcements:

- HW3 is due Friday

  + https://github.com/DavisPL-Teaching/261-hw3

- HW4 **(optional)** (last HW of the class):

  + https://github.com/DavisPL-Teaching/261-hw4

  + if completed, due May 30 and replaces lowest HW grade (lowest of 4 dropped)

- Midterm & study guide:

  + `exam/poll-answers.md`

  + `exam/study-guide.md`

  + practice exam has been posted on Piazza

  + Midterm is in class 1 week from today: Tuesday, May 20

- I will give feedback on proposals soon, by the end of this week!

- Details about the project presentations:

  + `project/presentation.md`

  + Feel free to review the above for now, I will go over these in class on Thursday.
    And I will post a similar document about the final project report.

Plan for this week:

- Poll (practice with loop invariants)

- Cover some things from lecture3/fol.dfy & summary of main takeaways

- Introduction to Hoare logic.

- Go back and cover the rest of fol.dfy, if time.

## Lecture

This lecture will study the foundations behind how Dafny works behind the scenes.

We have seen:

- proofs in FOL

But we have not seen:

- How to proofs in first-order logic relate to programs?

- How does Dafny determine whether a program is correct behind the scenes?

We will cover Hoare logic first.
If time, we will cover: dynamic logic, and the Curry-Howard correspondence.

A good understanding of these topics (like the first-order logic material) is useful!
It will help you understand why verification in Dafny works,
when it doesn't, and how to go about fixing it.
