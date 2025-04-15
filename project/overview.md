# ECS 261 Project Overview

I encourage you to start thinking about your project now! Here are some guidelines:

The goal of the project is to apply the tools used in this course to build a small verified software project of your choice. Your project will have three components: First, the project proposal; second the project presentation; and third, the project report.

## Choosing a Project

Three things to think about:
1. Application domain
2. Forming a group (2-3 people)
3. Tool selection

### 1. Choosing an application domain

In the early stages, I'd like for you to be thinking about what software domain or application domain you are interested in.

- Think about this as: pick your favorite area of computer science and pick a toy project in that area.

- It can be a research problem but it should be a relatively simple one (aim for an existing paper, not a new one). I will ask you to cite some literature in your project report.

- If the problem is related to your research, that's great! (And if you need help thinking of something related to your research, come talk to me!)

- It doesn't have to be verification-related -- the project will be to pick a more-or-less standard piece of software, and build a verified version of that software.

#### For example:

- Operating systems: build a process tracer, a file syncing utility, or a process scheduler

- Computer networks or distributed systems: build a simple a messaging chat, a server/client app, an RPC protocol, a three-phase commit or Paxos implementations

- Game development: build a text-based adventure game or a terminal Snake client

- Algorithms and data structures: build a union find data structure, an implementation of balanced binary trees, or some more complex data structure

- Computability: a Turing machine or finite automaton simulator; a finite automata library supporting various constructions and operations

- Programming languages: an esoteric programming language interpreter or compiler; an interpreter, optimizer, lexer, or parser; a static analyzer or optimizer

- Formalized mathematics or theorem proving: a proof of a theorem in some area of mathematics

- Machine learning: an implementation of neural networks spuporting gradient descent, an implementation of SVM or logistic regression

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

You may form groups of 2-3 people for the project. (Of course, you may also work alone if you prefer!)

Please use Piazza to form your groups if needed - I have opened a thread for finding teammates.

### 3. Tool selection

Since the goal is to build a verified piece of software, I expect that Dafny will be the most useful tool for most projects. However, you may use any of the tools we cover in this class -- or a different verification tool, with prior approval (you should detail this in your project proposal).

To help you think about this: verified projects can be divided into roughly three categories:

- Projects which want to verify the correctness of some piece of software at compile time.
This is the most straightforward project to do. Pick any basic software component or algorithm, and your goal will be to verify the correctness of your algorithm.
For example, take any recent paper in the last 15-20 years with a simple algorithm somewhere in the paper, and try to implement and verify it.

- Projects which want to verify some domain-specific property at runtime: As an example of this, see the "rectangle collision calculator" on your homework (part 2), or the four numbers game in part 3. The key here is that you want to verify something about data that arrives at runtime. Talk to me if you aren't sure if your project falls in this space.

- Projects which want to introduce lightweight verification into an existing real-world software project:
This is the only type of project for which Hypothesis may be a good fit.
For this project direction, I'd like you to annotate some real-world Python software (could be software you wrote) with preconditions and postconditions,
as well as extend it with additional functions and methods.
If you choose this direction you should also plan to verify at least some of the code in Dafny or Z3 by translating it manually to those settings; prepare to explain in your report how you approached the translation process and what aspects of it were interesting and challenging.

Languages:
With few exceptions, software should either be in Dafny, or in Python using Z3/Hypothesis.

This step should be in the early stages right now!
I'm more interested in having you think about application domains first.
You should have a tentative idea of what tools and languages you are planning on by the time you submit your project proposal.

## Examples

(Pick a few example ideas from the above for me to elaborate on)

## Getting feedback

Come to office hours to get feedback on your idea!

## Mid-quarter: Project Proposal

For the project proposal, I will ask you to write a 2-3 page report.
I recommend (but do not require) that the report be written in LaTeX.
It should have the following sections:
(1) Introduction and problem selection
(2) Implementation plan
(3) Collaboration plan
(4) Conclusion
See `proposal.md` for more details!

## Late-quarter: Presentation

The length of presentations will vary depending on how many groups are formed and how many people remain in the class after the drop deadline. I expect we will dopresentations to be roughly 10-15 minutes each. See `2-presentation.md` for more details!

## End-of-quarter: Project Report

At the end of the quarter, you will turn in a full project report (5-15 pages) describing your software and what it does, as well as your software package itself.
This project report can expand on your proposal.
I will provide more details on the final report later in the quarter.
