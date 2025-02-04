# ECS 261: Program Verification - Spring Quarter 2025

## Contents

1. [Welcome and Course Information](#welcome-and-course-information)
2. [Lectures](#lectures)
3. [Course Description](#course-description)
4. [Schedule](#schedule)
5. [Grade Breakdown](#grade-breakdown)
6. [Policies](#policies)
7. [Disclaimers](#disclaimers)
8. [Contact and Office Hours](#contact-and-office-hours)

## Welcome and Course Information

Welcome to ECS 261! I am super excited to have you all here.

- **Instructor:** [Caleb Stanford](https://web.cs.ucdavis.edu/~cdstanford/)
- **TA:** [Enzuo Zhu](https://zhuez16.github.io/)
- **CRN:** 55799
- **Units:** 4
- **Lectures:** Tuesdays and Thursdays, 10:30am-11:50am in [Maria Manetti Shrem Art Hall](https://manettishremmuseum.ucdavis.edu/) room 204
- **Exams:** One exam planned, either a midterm or a final (TBD). If it is a final it will be on Thursday, June 12, 10:30am-12:30pm.
- **[Piazza](https://piazza.com/class/m8t4cwl1qsm6yw)** for class Q+A, announcements, and office hours

## Lectures

I often lecture via live coding. I will post the code and other materials for each lecture in this repository.
To follow along with the lectures, clone the repository:
```shell
git clone git@github.com:DavisPL-Teaching/261.git
```

If you make changes to the code after each lecture, you will need to discard them before pulling again.
For example, you can run:
```shell
git stash
git pull
```

### Lecture Recordings and Zoom

If you miss class, you can make up the lectures (and class polls) at any time
prior to the last day of class.
All lectures will be broadcast and recorded on Zoom.
However, this is a best-effort process, so please keep in mind that occasional technical
difficulties are possible (e.g., lost video recording, poor audio).
Zoom recordings will be made available on Canvas.

## Course Description

Introduction to the formal verification of software.
Topics include a survey on tools and techniques, including: writing specifications, difference between testing and verification, Hoare logic, dynamic logic, program safety properties and termination, automated verification tools including SMT solvers, and advanced topics such as advanced type systems, verification, and symbolic execution. Students will gain hands-on experience with writing program specifications using tools used in industry at companies like Amazon and Microsoft.
Tools covered will include Z3 (via its Python API) and Dafny.
This course can be considered as a graduate version of [189C](https://github.com/DavisPL/189C).

### Intended Audience and Prerequisites

Some prior background in mathematical reasoning (writing proofs) or formal logic (e.g., Phil 112 or its equivalent) at the undergraduate level is helpful, though not required.
I will assume a general audience.
As a graduate course, it will not be solely tool-based, and will also include some theory (writing proofs) and a project component.
You may ignore the prerequisite listed on [the department website](https://cs.ucdavis.edu/schedules-classes/ecs-261-program-verification).

This course is appropriate for graduate students or advanced undergraduates.
Please note if you have taken 189C, there may be a substantial overlap of material.

### Textbook

The following textbook is optional but recommended:

- [**Program Proofs**](https://mitpress.mit.edu/9780262546232/program-proofs/). K. Rustan M. Leino, MIT Press, 2023.

### Learning Objectives

By the end of the course, students will be able to:

- Understand the concept of software verification and its importance.
- Understand and apply automated verification tools like Z3 for software analysis and logical reasoning tasks.
- Understand and use dedicated verification tools such as Dafny to develop formally verified software.
- Understand the logical underpinnings of verification tools, and program logics for program reasoning.

## Schedule

See `schedule.md`.

## Grade Breakdown

Your grade is evaluated based on:

- **Participation (10%):** via in-class polls
- **Homeworks (20%):** I am planning to assign about 3 assignments, give or take (plus homework 0)
- **Midterm or Final Exam (30%):** I am planning to do one exam, either a midterm or a final (TBD)
- **Project (40%):** Project applying the concepts in the class to verification of a real-world software project of your choosing, including a project proposal and presentation

### Attendance and Participation (10%)

To encourage class attendance, there are in-class polls that are worth a small amount of credit.
If you miss class, you may make up the polls at any time (up to and including the last day of class) by watching the lectures and filling out your responses offline. Please note that your poll scores will be automatically updated on the next Canvas sync and you do not need to notify me of make-up poll submissions.

You will also give a short presentation on your final project (likely 10-20 minutes).
More details on the project presentation will be announced later on in the class.

### Homeworks (20%)

Homeworks will consist of programming assignments to bring together concepts we learned in class
and to give you practice using all of the tools we cover.
I plan to assign about 3 homework assignments (give or take), plus homework 0, which is designed to help you install the relevant software for the course.

**Important: your code must run to get credit!**
Frequently running and testing your code during development is an essential part of computer programming -- and a very important skill in the real world, including making sure that your code works on someone else's machine. The graders won't be able to debug your submission, and will generally be able to give at most 10% partial credit for code that does not run.

Homeworks will be graded primarily for correctness and completion.
There will also be a small number of points reserved for code quality (at most 10% of each assignment).
That is: does your program exhibit high code quality standards?
Is it readable, shareable, well-documented, well-commented, logically separated into modules and functions, and reasonably efficient?
Are your free response answers thoughtful?
I plan to use Gradescope for homework submissions and grading.

### Midterm/Final Exam (30%)

There will be a single midterm or final exam.
The exam will be closed-book, but you may bring a cheat sheet (single-sided) to each exam.
The exam will be graded on Gradescope.

I reserve the right to curve exams (this can only help you). That means, for example, if 100 points are possible, it may be entered as out of a smaller number of points like 95 or 85 for the purposes of calculating your grade, if the average score of the class was low or if there were unexpectedly difficult questions.

### Final Project (40%)

There will be a final project (including a project proposal and a presentation) to put the concepts in class to practice.
The project will focus on formal verification applied to a real-world software project of your choosing.
I will announce more details in class!

### Final Grade

For the final (letter) grade, the following are minimum cutoffs. That is, if your grade is above the given percentage, you will definitely receive at least the given grade. However, I reserve the right to lower the cutoffs (i.e. you might get a better grade than what the table says).
I will use this to help students who may be on the boundary between two grades at the end of the quarter.

| Percentage | Minimum Grade |
| --- | --- |
| 93 | A  |
| 90 | A- |
| 87 | B+ |
| 83 | B  |
| 80 | B- |
| 77 | C+ |
| 73 | C  |
| 70 | C- |
| 67 | D+ |
| 63 | D  |
| 60 | D- |

## Policies

### AI Policy

AI collaboration is allowed for homework assignments.
I encourage you to use AI in a way that is helpful to you, and to use caution that your use of AI is aiding (and not preventing) your own understanding of the material and critical thinking skills.
Exams are held in-class and closed-book.
Please see also [Prof. Jason Lowe-Power's advice here](https://jlpteaching.github.io/comparch/syllabus/#using-generative-ai-tools).

### Collaboration Policy and Academic Integrity

This class will encourage collaboration; however, each person should complete their own version of the assignment. **You should not directly copy code from someone else, even within your study group,** but you can receive help and give help on individual parts of an assignment.
In a real software development job, it is common to seek and get help; this class will be no different!

You may work on homework assignments in groups of up to 3 people, as long as everyone is working on their own copy of the code. If you do this, please list the names of your collaborators at the top of your submission.

Here are some examples of good (allowed) collaboration:

- Sharing of resources
- Sharing of inspiration
- Sharing questions about the assignment on Piazza
- Helping out classmates on Piazza
- Collaboration at a low level (e.g., hey, what's the syntax for X, again? Why does this code print Y?)
- Collaboration at a high level (why did they tell us to do this in that way?)
- Searching the internet (here's an example of how to do that on Google or StackOverflow)

Here are examples of disallowed collaboration:

- Sharing large amounts of code with others within your group or others in the course.
- Sharing the exact solution to a specific mid-level programming problem.
- Asking a stranger to finish your work for you or copying and pasting what you find online for submission.

In other words, please use common sense!
This course strictly follows the [UC Davis Code of Academic Integrity](https://ossja.ucdavis.edu/academic-integrity).

### Late Policy

In-class participation points (polls) as well as HW0 can be made up at any point during the quarter (prior to the last day of class), by submitting the Google form link. The forms will remain open and can be found by viewing the lecture recording or lecture notes for that day.
I will not be able to provide a consolidated list of the form links, as their purpose is to encourage you to attend and watch the lectures.

Homeworks and the project are due at 11:59pm on the due date.
**I cannot guarantee that late work will be graded.**
Despite this, I encourage you to update your assignments even after the deadline -- Gradescope will allow you to upload late work up to a few days after the assignment deadline.
At grading time, we may choose to grade the more recent version at our discretion.

## Disclaimers

1. **Job scams**

    Please be vigilant of job scams impersonating faculty members.
    Communication from the instructor will only be sent through official UC Davis email addresses and channels.
    For more information, visit [UC Davis Job Scams Prevention](https://careercenter.ucdavis.edu/job-and-internship-search/job-scams).

2. **Respectful discourse policy**

    Please be kind and respectful to each other!
    UC Davis has [policies against harassment and discrimination](https://hr.ucdavis.edu/departments/elr/preventing-discrimination-harassment).
    Be inclusive of your classmates in group discussions and in your questions and answers in class.
    If you need to, you may reach me by email to report an issue with a classmate.
    Please be aware that as a [responsible employee](https://hdapp.ucdavis.edu/responsible-employee), I am required to report certain disclosures under California and federal law.

3. **Mental health and international student support**

    Many students face a variety of challenges, including with respect to mental health, food and housing, visa and travel issues, and other basic needs.
    If you need help, please use the resources available to you!
    Graduate studies has compiled a [list of resources for student health and well-being](https://grad.ucdavis.edu/health-and-well-being).
    For international student challenges, please reach out to [SISS](https://siss.ucdavis.edu/) and your graduate program advisors.

## Contact and Office Hours

Please use the Piazza for questions related to course material. Some Piazza guidelines:

* If you send me an email, I will most likely respond to post your question on Piazza :)

* Please ask all questions publicly - if you have a question, someone else probably has the same question, too! The only exception to this rule is if your post contains a large snippet of code (more than 10-20 lines is a good rule of thumb).

* I encourage you to ask anonymously if you feel more comfortable.

The instructor and TAs will be available during office hours for additional support on course material and assignments. The schedule of office hours will be announced in a pinned post on Piazza.
If you have a question that is more sensitive or unrelated to the course, please email me (at `cdstanford` `ucdavis` `edu`).
