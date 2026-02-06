# Lecture 2: Interactive Program Verification

Introduction to interactive program verification in Dafny.

## Tuesday, January 27

Announcements/reminders:

- I am still sick, hope to be back in person soon

- Polls synced over the weekend -- if you have a 0 on all polls, check
  that you have submitted HW0 with your email and student ID.

Lecture plan going forward:

- I am going to switch Lecture 2 and Lecture 3 from how it was taught last iteration of
  the class.

  + This means we will start with Dafny, then come back to Z3 later.

  + Reason: I want to give you experience with Dafny earlier on as it will be useful
    for the final project!

- Plan for today:

  + Loose ends from Lecture 1 + the poll

  + Introductory slides for lecture 2

  + Introduction to Dafny.

## Thursday, January 29

Announcements/reminders:

- I am still symptomatic so we are still on Zoom, hope to be back in person soon!

- OH moved to 2-3pm Thursdays going forward

- HW2 not ready yet, but hope to release soon!

- I will speak more about the project and timeline (for project proposal etc.) on Tuesday

Plan:

- Finish example from part 1

    Start with the poll

    Preconditions and postconditions

    Function/method distinction

    Stronger and weaker specs, revisited

- Part 2: Dafny methodology.

Questions before we get started?

## Tuesday, February 3

Announcements:

- HW2 was released on Friday - due Tuesday, Feb 10

  + "Show counterexample" feature has been renamed to
    "Show verification trace"
    Also try: press F7

  + You should be able to complete most of part 1 and all of part 2
    Part 1, binary search impl (1C) + part 3 require loop invariants
    Plan is to cover these on Thursday.

- Project proposal deadline: Tuesday, February 17

Plan:

- Continue Part 2: Dafny Methodology.

  + Finish MinFour example

  + Poll

  + ArgMinFour example: a more interesting case!

- If time: we can start Part 3, quantifiers

- End (last 25 mins): Talk about project. (5:35)

Questions about HW2 or plan?

## Thursday, February 5

Announcements/reminders:

- HW2 due: Tuesday, Feb 10

  + TBD: will extend the deadline if we don't cover
    loop invariants today.

- Project proposal due: Tuesday, Feb 17.

Plan:

- Briefly discuss project proposal, project examples, Q+A

- Show you how to compile Dafny code to Python (or other languages).

  + Important point that I didn't emphasize enough earlier!
    This will be useful for your projects

- Finish ArgMinFour example from part 2

- Poll

- Part 3: Quantifiers

- (If time) Part 4: Loop invariants.

Questions?

### Compiling Dafny to Python

  - Here is a command we can run:

    `dafny build --target:py 1-intro.dfy`

    Then look at `1-intro-py/module_.py`.

    By default, Dafny builds by compiling to C Sharp
    (see 1-intro.cs)
