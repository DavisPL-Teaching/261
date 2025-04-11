# ECS 261 Project

Your final project will be to apply the tools used in this course to a real software project of your choice. You may use any tool that we have covered, though I suggest using Dafny as it is the most general and flexible way to develop verified software components. For some projects, Z3 may be appropriate if the project is focused on automated verification. You may also use another tool for program verification not covered in the course, with prior permission from the instructor.

Your project will have three components: First, the project proposal; second the project presentation; and third, the project report.

## Choosing a project

In the early stages, I'd like for you to be thinking early on about what software domain or application domain you are interested in. Think about this as: pick your favorite area of computer science and pick a toy project in that area. For example:

- Computer networks or distributed systems (e.g., a messaging chat or server/client app)

- Operating systems (e.g., a file syncing utility or process manager)

- Game development (e.g. a basic game with a simple interface, very simple GUI or text-based)

- Algorithms and data structures (e.g., a union find data structure, a balanced binary tree implementation)

- Computability (e.g., an implementation of Turing machines or finite automata supporting various constructions and operations)

- Programming languages (e.g., a simple language compiler, interpreter, optimizer, lexer, or parser)

- Formalized mathematics or theorem proving (e.g., a proof of a theorem in some area of mathematics)

- Machine learning (e.g., an implementation of neural networks spuporting gradient descent, an implementation of SVM or logistic regression)

- Other areas: computational biology, graphics, databases, NLP, etc.

I especially encourage you to pick something related to your own research! I would much rather you work on a project that is related to your research interests even if it turns out to be difficult and you do not fully succeed, than you pick an "easy" project that isn't related to your interests.

Please note: **formally verified software is much more difficult to develop than normal software.** As a rule of thumb, you should expect to spend approximately 10x the time that you would normally spend on the project to get the software working. Please keep this in mind! For example, you shouldn't have an application with too many features; focus on the simplest possible version of your application or a "minimum working prototype" that will demonstrate the main ideas.

## Choosing a Group

You may form groups of 2-3 people for the project (you may also work alone if you prefer!) Please use Piazza to form your groups if needed. I will open a thread for finding teammates.

## Part 1: Proposal

For the project proposal, you should provide a 2-3 page report.
I recommend (but do not require) that the report be written in LaTeX.
Your report should address the following 8 sections:

1. **Problem domain and motivation.**
State what problem your application is intending to solve, and why it is interesting. This can include some papers if your project is related to your research area.

2. **Program.** What will the software do to solve the above problem? How do you interact with it? What is the input and output? What are the goals of the project? What indicates a "good" solution to the problem?

3. **Scope.** Is the solution to the problem already known? (It should be already known!) I strongly do not recommend implementing a verified software project for a problem that you do not already know how to solve in an existing programming language, like Python or C++! A good target to aim for would be something you can build in 2 weeks of dedicated effort in an existin glanguage.

4. **Specifications of interest.** What are important correctness properties that are important for your problem domain? For example, what behavior of the software do you want to ensure is true on each function call? These can be properties about the input, properties related to the output, or properties that encode the full functional correctness of your application.

- I recommend starting with functional correctness, at least with some core components.

- You may also have some properties not related to functional correctness (for example, timing of your code, safety properties, interaction with the OS) but there should be at least some functional correctness you are interested in.

5. **Verification effort.** Which functions or components of your software will you need to verify to ensure the above properties?

- It may help to draw an architecture diagram for your software here. Which parts interact in interesting ways?

- Give at least one example specific function or method, with preconditions and postconditions that would be added to the method.

- If you have non-functional correctness properties: you will need to think of how to verify these using preconditions and postconditions! What additional state will you need to track in your application to verify these properties?

- Which parts of your application will *not* be verified? For the parts will be written outside of Dafny, will you have to assume anything about their behavior for your verification proofs to go through? What properties about your software are out of scope?

5. **Development and timeline.** State your development strategy. If you are working in a team, I suggest dividing the project into different components that can be developed separately. Please include your plans to meet with the whole group -- will you be meeting once a week to discuss the project? Twice a week? How will you communicate with your group? Also, please give a specific timeline with who will be working on which components during which weeks; this timeline can just be "expected", I won't be holding you to these deadlines, but I want to see that you are thinking about what components need to be worked on and how the pieces fit together.

6. **Challenges.** Do you foresee any challenges coming up during the project? What could go wrong when attempting to write down the specifications? When attempting to prove the specifications? What do you plan to do if either of these steps becomes difficult?
Here are some specific things to think about:

- **Interaction features.** Will your application include features which interact with the outside world (outside of the verified code base in Dafny), such as network, filesystem interaction, GUI interaction, etc.? What interface will you define for this interaction?

- **Properties which go beyond functional correctness.** Do you want to prove safety or liveness properties for any components? Any complex properties, for example related to the timing of your code?

7. **Impact.** Finally, state what will happen when the verified software is finished. What is exciting about it? What is interesting about it? Why is your application domain important?

8. **References cited.** Include any papers or websites related to what your project is going to do and citations at the bottom of your document. Please include at least 2-3 citations at a minimum.

## Part 2: Presentation

The length of presentations will vary depending on how many groups are formed and how many people remain in the class after the drop deadline. I expect presentations to be roughly 10-15 minutes each. Please come prepared with your slides and a laptop that can plug in to usb-c, and give everyone in the group an equal chance to present. Please be sure to practice your presentation to stay within the time limit!

Before you jump into your project (what you did), start with at least 2-3 slides of general background on the area and problem.
Show us at least 1 slide that has code (for example, a method with its preconditions and postconditions), but no more than 2 such slides.
You don't have to be fully finished with your project by the time of the presentation, but you should have made significant progress.

Include some slides with what you want feedback on! Questions for the audience: should we do X, or should we do Y? How can we help guide your project in the remaining time before the final report?

Include a Q+A at the end of your presentation. Additionally, please include 5 "optional" slides that include candidate questions that the audience might ask, in case you do not get any questions or if there is ample extra time.

## Part 3: Project Report

At the end of the quarter, you will turn in a full project report (5-15 pages) describing your software and what it does, as well as your software package itself.
This project report can expand on your proposal.
I will provide more details on the final report later in the quarter.
