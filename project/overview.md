# ECS 261 Project Overview

I encourage you to start thinking about your project now! Here are some guidelines:

The goal of the project is to apply the tools used in this course to build a small verified software project of your choice. Your project will have three components: First, the project proposal; second the project presentation; and third, the project report.

## Choosing a Project

Three things to think about:
1. Application domain
2. Forming a group (1-3 people)
3. Plan for implementation.

### 1. Choosing an application domain

In the early stages, I'd like for you to be thinking about what software domain or application domain you are interested in.

- Think about this as: pick your favorite area of computer science and pick a toy project in that area.

- It can be a research problem but it should be a relatively simple one (aim for an existing paper, not a new one). I will ask you to cite some literature in your project report.

- If the problem is related to your research, that's great! (And if you need help thinking of something related to your research, come talk to me!)

- It doesn't have to be verification-related -- the project will be to pick a more-or-less standard piece of software, and build a verified version of that software.

#### For example:

- Operating systems: build a process tracer, a file syncing utility, or a process scheduler

- Computer networks or distributed systems: build a simple a messaging chat, a server/client app, an RPC protocol, a three-phase commit or Paxos implementations

- Game development: build a text-based adventure game or a terminal Snake client,
  verified implementation of chess/checkers/some other strategy game

- Algorithms and data structures: build a union find data structure, an implementation of balanced binary trees, or some more complex data structure

- Computability: a Turing machine or finite automaton simulator; a finite automata library supporting various constructions and operations

- Programming languages: an esoteric programming language interpreter or compiler; an interpreter, optimizer, lexer, or parser; a static analyzer

- Formalized mathematics or theorem proving: a proof of a theorem in some area of mathematics

- Machine learning: an implementation of neural networks supporting gradient descent, an implementation of SVM or logistic regression, online learning like multi-armed bandit problem, etc.

- Other areas: computational biology, graphics, databases, NLP, etc.

#### Constraints to think about

While all of the above domains are great, you will want to pick a project which minimizes
the need of your application to interact with external libraries.
(Interacting with external libraries is not impossible! But it can make the project significantly more difficult.)
For example, if you are working on something in game design, avoid something which requires a GUI and do something purely text-based.

Estimating difficulty:

- Formally verified software is much more difficult to develop than normal software! As a rule of thumb, expect to spend **approximately 10x** the time that you would normally spend on the project to get the software working. Please keep this in mind! For example, you shouldn't have an application with too many features; focus on the simplest possible version of your application or a "minimum working prototype" that will demonstrate the main ideas.

- In my experience, most people tend to underestimate how much work a project will require, even for *unverified* software!

- At the same time, do be ambitious! I would much rather you work on a project that is related to your research interests even if it turns out to be difficult and you do not fully succeed, than you pick an "easy" project that isn't related to your interests.
The purpose of the project proposal is to help gauge your project difficulty so that I can give you some feedback before you get started.

Thinking about verification properties: what will you verify about your software?

- Start with functional correctness (baseline)
  Think of it as adding preconditions, postconditions (or assume/asserts) to your code

- Then think about more interesting properties: are there any safety properties or liveness properties you are interested in? Properties that require running the code multiple times?

### 2. Choosing a group

You may form groups of 1-3 people for the project.
Most likely, I will be able to accommodate any group sizes in this range.
If there are too many groups of size 1, there is a chance I will need to ask some groups to combine.
If you need to find group members, I will enable the "find groups" feature on Piazza.

### 3. Plan for implementation

Since the goal is to build a verified piece of software, I recommend Dafny as
it will be the most useful tool for most projects.
If you are interested in building a project with a different tool -- please talk with me or come
to office hours! I may approve a limited number of projects using other tools.

To help you think about this: verified projects can be divided into roughly three categories:

- Projects which want to build and verify a correct piece of software.
This is the most straightforward project to do. Pick any basic software component or algorithm, and your goal will be to verify the correctness of your algorithm.
For example, take any project at an "undergraduate" level that you already know how to build.

- Projects which want to introduce specific targeted verification into an existing real-world software project, or integrate verified code with unverified code:
For this project direction, you may need to think about how to write Dafny functions which
wrap a Python library. Some of your project could be working with and specifying on, e.g., the Python code side!
However, if you choose this direction you should also plan to verify at least some of the code in Dafny by translating it manually to those settings; prepare to explain in your report how you approached the translation process and what aspects of it were interesting and challenging.

- Projects which aim to build a "proof of concept" for something related to your research (PhD or MS project).
Please be careful about projects in this category!
This should be a **very minimal** proof of concept for some piece of verified software related to your
area of research. Just as with the first category, it should be something you already know how to build unverified! For example, you could also pick a recent paper in the last 15-20 years with a simple algorithm somewhere in the paper, and try to implement and verify it.

For all categories: think about *what* you want to build and *what* you want to verify.

This step should be in the early stages right now!
Many things will change as you actually go through the work of building the project.
You should have a tentative idea of what tools and languages you are planning on by the time you submit your project proposal.

## Examples

(I am happy to elaborate on any of the example ideas above)

## Getting feedback

Come to office hours to get feedback on your idea!

## Mid-quarter: Project Proposal

For the project proposal, I will ask you to write a 2-4 page report.
I recommend (but do not require) that the report be written in LaTeX.
It should have the following sections:
(1) Introduction and problem selection
(2) Implementation plan
(3) Collaboration plan
(4) Conclusion
See `proposal.md` for more details.

## Late-quarter: Presentation

The length of presentations will vary depending on how many groups are formed and how many people remain in the class after the drop deadline. I expect we will do presentations to be roughly 10-15 minutes each. See `presentation.md` for more details.

## End-of-quarter: Project Report

At the end of the quarter, you will turn in a full project report (5-15 pages) describing your software and what it does, as well as your software package itself.
This project report can expand on your proposal.
See `report.md` for more details.
