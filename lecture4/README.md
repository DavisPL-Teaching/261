# Lecture 4: Proofs and programs

## Tuesday, May 13

Several announcements:

- HW3 is due Friday

  + https://github.com/DavisPL-Teaching/261-hw3

- HW4 **(optional)** (last HW of the class):

  + https://github.com/DavisPL-Teaching/261-hw4

  + if completed, due May 30 and replaces lowest HW grade (lowest of 4 dropped)

- Midterm & study guide:

  + Midterm is in class 1 week from today: Tuesday, May 20

  + `exam/poll-answers.md`

  + `exam/study-guide.md`

  + practice exam has been posted on Piazza

- I will give feedback on proposals soon, by the end of this week!

- Details about the project presentations:

  + `project/presentation.md`

  + Feel free to review the above for now, I will go over these in class on Thursday.
    And I will post a similar document about the final project report.

Plan for today:

- Poll (practice with loop invariants)

- Cover some things from lecture3/fol.dfy & summary of main takeaways

- Introduction to Hoare logic: proofs about programs.

- Go back and cover the rest of fol.dfy, if time.

### Lecture Outline

This lecture will study the foundations behind how Dafny works behind the scenes.

We have seen:

- proofs in FOL

But we have not seen:

- How do proofs in first-order logic relate to programs?

- How does Dafny determine whether a program is correct behind the scenes?

We will cover Hoare logic first.

A good understanding of these topics (like the first-order logic material) is useful!
It will help you understand why verification in Dafny works,
when it doesn't, and how to go about fixing it.

### Advanced topics (will not appear on exam):

If time, we will cover: dynamic logic, and the Curry-Howard correspondence.

## Thursday, May 15

Announcements:

- Project Proposals have been graded and I have provided feedback in Gradescope!
  A few things that were common to multiple submissions:

  + Many of you said things like, we will implement this in Python and then verify it in Dafny.
    Don't do this!
    Dafny can compile to Python! (Or Java, C#, or Go) This will save many of you a lot of time.
    Demo to demonstrate:
    ```
    dafny build --target:py exercises.dfy
    ```

  + Z3 vs Dafny (pick one)

  + Identify a "minimum skeleton" as a checkpoint (set a deadline: 1 week in) that will help
    assess project size and scope.

- Project presentations and final report

  + Sign-up sheet: see Piazza, sign up by Friday, May 23.

    Please plan to stick to the time you signed up for!
    You can edit the schedule, but only if you can agree with another group to switch.
    No changes will be possible within 24 hours before the presentation.

  + Presentation changes: see `presentation.md`

  + Final report: see `report.md`

Upcoming deadlines:

- Midterm is on Tuesday (May 20) - see study resources pinned on Piazza and `exam/` folder

- Thursday (May 22) is an optional bonus lecture (Dynamic Logic), for those interested.

- HW3 due tomorrow (Friday)

- HW4 (optional) due May 30

Plan for today:

- Finish Hoare logic.
