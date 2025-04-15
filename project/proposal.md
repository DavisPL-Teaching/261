# Project proposal

For the project proposal, you should provide a 2-3 page report.
I recommend (but do not require) that the report be written in LaTeX.

Your report should address the following 4 sections:

### 1. Introduction and problem selection

1.1 **Problem domain and motivation.**
State what problem your application is intending to solve, and why it is interesting.
This should include some papers related to your chosen research area or domain.

1.2 **Program.** What will the software do to solve the above problem? How do you interact with it? What is the input and output? What are the goals of the project? What indicates a "good" solution to the problem?

1.3. **Scope.** Is the solution to the problem already known? (It should be already known!) I strongly do not recommend implementing a verified software project for a problem that you do not already know how to solve in an existing programming language, like Python or C++! A good target to aim for would be something you can build in 2 weeks of dedicated effort in an existin glanguage.

1.4. **Specifications of interest.** What are important correctness properties that are important for your problem domain? For example, what behavior of the software do you want to ensure is true on each function call? These can be properties about the input, properties related to the output, or properties that encode the full functional correctness of your application.

- I recommend starting with functional correctness, at least with some core components.

- You may also have some properties not related to functional correctness (for example, timing of your code, safety properties, interaction with the OS) but there should be at least some functional correctness you are interested in.

### 2. Implementation plan

Your implementation plan should address the following:

2.1. **Tool and language selection.** What tools and languages will you use for your project?

2.2. **Architecture of your code.**
Lay out an expected architecture for how your tool will work. What component(s) are there and how do they interact? Consider drawing a diagram. This can be tenative at this stage!

2.3. **Verification effort.** Which functions, components, or properties of your software will you need to verify to ensure the above properties?
Will these properties be verified at compile-time (e.g., Dafny) or run-time (e.g., using domain-specific Z3 constraints)?

- It may help to draw an architecture diagram for your software here. Which parts interact in interesting ways?

- Give at least one example specific function or method, with preconditions and postconditions that would be added to the method.

- If you have non-functional correctness properties: you will need to think of how to verify these using preconditions and postconditions! What additional state will you need to track in your application to verify these properties?

- Which parts of your application will *not* be verified? For the parts will be written outside of Dafny, will you have to assume anything about their behavior for your verification proofs to go through? What properties about your software are out of scope?

2.4. **Challenges.** Do you foresee any challenges coming up during the project? What could go wrong when attempting to write down the specifications? When attempting to prove the specifications? What do you plan to do if either of these steps becomes difficult?
Here are some specific things to think about:

  - **Interaction features.** Will your application include features which interact with the outside world (outside of the verified code base in Dafny), such as network, filesystem interaction, GUI interaction, etc.? What interface will you define for this interaction?

  - **Properties which go beyond functional correctness.** Do you want to prove safety or liveness properties for any components? Any complex properties, for example related to the timing of your code?


### 3. Development and timeline

State your development strategy. If you are working in a team, I suggest dividing the project into different components that can be developed separately. Please include your plans to meet with the whole group -- will you be meeting once a week to discuss the project? Twice a week? How will you communicate with your group? Also, please give a specific timeline with who will be working on which components during which weeks; this timeline can just be "expected", I won't be holding you to these deadlines, but I want to see that you are thinking about what components need to be worked on and how the pieces fit together.

### 4. Conclusion (optional)

This section is optional.
State what will happen when the verified software is finished. What is exciting about it? What is interesting about it? Why is your application domain important?

## References cited

Include any papers or websites related to what your project is going to do and citations at the bottom of your document. Please include at least 2-3 citations at a minimum.
