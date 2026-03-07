# Project proposal

For the project proposal, you should provide a 2-4 page proposal.

**Report length:**
Minimum 2 full pages, maximum 4 pages (not including references) -- these are hard cutoffs! If you need more material, you should include it only in an "appendix" and it will not be graded.
Do not change the font, margins or do other spacing tricks to fit within the page limit.

**Deadline:**
Tuesday, February 17 at 11:59pm.

The report should be typed. I recommend (but do not require) that the proposal be written in LaTeX.

Your proposal should address the following 4 sections.
The subsections may vary, but should address at least the points outlined below.

## Title and group members

At the top of your proposal, list the title of your project and all of your group members.

Please form groups of size 1-3!
Most likely, I will be able to accommodate any group sizes in this range.
If there are too many groups of size 1, there is a chance I will need to ask some groups to combine.
If you need to find group members, I will enable the "find groups" feature on Piazza.

### 1.  Introduction, problem selection, and goals

1.1 **Problem domain and motivation.**
State what problem your application is intending to solve, and why it is interesting.
This should include some papers related to your chosen research area or domain.

1.2 **Program.** What should the software do to solve the above problem? How do you interact with it? What is the input and output? What indicates a "good" solution to the problem?

1.3. **Scope.** Is the solution to the problem already known? (It should be already known!) I strongly do not recommend implementing a verified software project for a problem that you do not already know how to solve in an existing programming language, like Python or C++. A good target to aim for would be something you can build in 2 weeks of dedicated effort in an existin glanguage.

1.4. **Specifications of interest.** What are important correctness properties that are important for your problem domain? For example, what behavior of the software do you want to ensure is true on each function call? These can be properties about the input, properties related to the output, or properties that encode the full functional correctness of your application.

- I recommend starting with functional correctness, at least with some core components.

- Give at least one example with a **specific function or method,** with preconditions and postconditions that would be needed to verify the method.

- You may also have some properties not related to functional correctness (for example, timing of your code, safety properties, interaction with the OS) but there should be at least some functional correctness you are interested in.

1.5 **Goals.**
What are the high-level goals of the project? What do you hope to have working by the end of the project?
Please divide your goals into three categories:

- **Minimum goal:** This is the minimum version of your code that you **must** have working by the end of the quarter. I recommend keeping this to Dafny code only (no other code), for example, just the core verified logic for your application domain.

- **Target goal:** This is the version of your code that you **plan** to have working by the end of the quarter, as a target deliverable. This could, for example, have Dafny together with an interface to run the code, together with the main components of your application or algorithms that it will use.

- **Reach goal:** This is the version of your code that has all the additional features you might want, if you have extra time. This may include additional features, etc. as needed, but none of them on the "critical path" to make a working version of your project.

These should be described at a high level. The specific component(s) that are included in each goal may refer to the following section and should be described in more detail below.

### 2. Implementation plan

Your implementation plan should address the following:

2.1. **Tool and language selection.** What tools and languages will you use for your project? This should include Dafny, but may also include other tools.
If your project involves porting or interacting with another code base, describe that code base.

2.2. **Architecture of your code.**
Lay out an expected architecture for how your tool will work. What component(s) are there and how do they interact? Consider drawing a diagram. This can be tenative at this stage!

2.3. **Verification effort.** Which functions, components, or properties of your software will you need to verify to ensure the above properties?
Will these properties be verified at compile-time?
Is there anything that would be useful to verify at run-time -- will you include specifications for these
properties?

- It may help to draw an architecture diagram for your software here. Which parts interact in interesting ways?

- If you have non-functional correctness properties: you will need to think of how to verify these using preconditions and postconditions! What additional state will you need to track in your application to verify these properties?

- Which parts of your application will *not* be verified? For the parts will be written outside of Dafny, will you have to assume anything about their behavior for your verification proofs to go through? What properties about your software are out of scope?

2.4. **Challenges.** Do you foresee any challenges coming up during the project? What could go wrong when attempting to write down the specifications? When attempting to prove the specifications? What do you plan to do if either of these steps becomes difficult?
Here are some specific things to think about:

  - **Interaction features.** Will your application include features which interact with the outside world (outside of the verified code base in Dafny), such as network, filesystem interaction, GUI interaction, etc.? What interface will you define for this interaction?

  - **Properties which go beyond functional correctness.** Do you want to prove safety or liveness properties for any components? Any complex properties, for example related to the timing of your code?

### 3. Development and timeline

State your development strategy.

- If you are working in a team, how will you divide into different components that can be developed separately?

- Please include your plans to meet with the whole group.
  Will you be meeting once a week to discuss the project? Twice a week? What platform will you use to communicate with your group?

- **Timeline:** Give a specific weekly timeline with which components will be developed in each week. This timeline can just be "expected", I won't be holding you to these deadlines, but I want to see that you are thinking about what components need to be worked on and how the pieces fit together.

- **Commitment statement:** Lastly, In addition to the group members, please list a statement that each person commits to work and contribute equally to the project. This statement should be included once, for each group member: "I commit to work and contribute equally to this project" with the group member's name signed.

The meeting plan and commitment statement are not required for groups of size 1.

### 4. Conclusion and questions for feedback

This section can be short (e.g., 1-2 paragraphs).
State what will happen if the project is successful. What is exciting about it? What is interesting about it? Why is your application domain important?

Do you have any questions about the project? What are some things you are uncertain about that should be resolved, what would be helpful to get feedback on?

## References cited

References cited is mandatory!
Include any papers or websites related to what your project is going to do and citations at the bottom of your document. Please include at least 3 citations at a minimum.
