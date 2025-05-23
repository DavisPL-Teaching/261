# Lecture 1: Program Specifications

## Following along

You can follow along with the lectures!

- https://github.com/DavisPL-Teaching/261
- `git clone git@github.com:DavisPL-Teaching/261.git`
  (Every week to get the latest changes: `git stash` then `git pull`)
- Also allows you to access the poll link we do in lecture.
- You will need to complete HW0 to be able to run the code successfully.

## Plan for today (Thursday, April 3)

1. Announcements
2. Start with a poll
3. Finish demos from last time
4. Introduction to program specifications

## Announcements

1. Homework 0 is out!

    [HW0](https://forms.gle/KPTipNm5ZjjznLL48)

    - **Suggested deadline:** tomorrow Friday
    - can be submitted late - but please try it out :)
    - Installation help office hours: tomorrow 2pm

2. Waitlist update: 50 + 4 students on waitlist (as of this morning)

3. If new to the class:

    - Please monitor Piazza
    - Lecture 0 slides are available on GitHub
    - Lecture recordings are available on Canvas.

## Plans for lectures going forward:

- Most lectures going forward will be live coding.
  Bring your laptop to follow along!

- Keeping things interactive: live polls, + programming exercises

## Topics covered over the next few lectures:

(Overflow) Demos from last time explained in a bit more detail (~15 min)

1. Program specifications

    - Writing specifications
    - Testing specifications

2. Exploring and testing specifications with Hypothesis

    (Putting Dafny aside for a bit - we will come back to Dafny in a few weeks!)

3. Facets

    - Types of specifications
    - Preconditions and postconditions

4. Limitations and discussion

    - Specification is wrong

    - Specification is incomplete

    - Program model is wrong

    - Precondition is wrong

    - Mutability issues

    - Techniques for validating specifications

    - Important distinctions (terminology to be aware of)
        + Testing vs. verification
        + Static/dynamic
        + Soundness/completeness
        + White-box vs. black-box

## Key definitions

(We can come back and fill these in post-lecture)

**Specification:**

**Testing** vs **Verification**

**Safety property:**

**Precondition** and **Postcondition**

**Assert** and **Assume**

## Poll

Today's poll:

- Some questions about your prior background (to help me out with gauging the material)

- Question asking you to think about specifications for the is_even function

https://forms.gle/AG5XoCkBiiGKK7WZA

(Answer: Only F)
(All others are true/false properties of the program, so they are valid specifications.)

## Tuesday, April 8

(Reminder for following along)

Announcements:

- HW1 is released:

    https://github.com/DavisPL-Teaching/261-hw1

    Due: next Friday, April 18

    Covers:
    Writing specifications in both Hypothesis and Z3
    Introductory-level examples

- Office hours: TA (Weds 1-2pm), Mine (Fridays 3-4pm)

- I am confirming that the exam will be an in-class midterm, not a final.

Plan for today:

- Formal definition of specification and examples

    (Poll somewhere in here)

- Stronger and weaker specifications

- Types of specifications. The important ones:

    + Safety properties

    + Functional correctness

    + Preconditions and postconditions

    + Assume and assert

- Goal: finish up Hypothesis by today + next time at the latest.

## Thursday, April 10

Announcements and reminders:

- Reminder: HW1 due a week from tomorrow
    (come to OH tomorrow!)

- Undergraduate enrollment

Plan:

- Last time: Stronger and weaker specifications.

- Today: finish Lecture 1

    + Types of specifications
    + Preconditions and postconditions
    + Assume and assert
