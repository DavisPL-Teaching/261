# Project final report

**Due: Thursday, March 19, 11:59pm**

For the final submission of your project, you should provide a 5-10 page report.
You will submit both your project report *and* your project code in Gradescope.

Your report may adapt the same document from your proposal, but it should be modified based on the following outline to include your results and conclusions.
Your proposal should address the following 6 sections and should address at least the points outlined below.
(You may add additional subsection(s) as needed, but should keep the structure with the 6 sections and address at least all of the following points.)
Please also address any feedback from your project proposal, for example, if there were any suggestions for things you should fix or describe.

As with the proposal, I recommend (but do not require) that the report be written in LaTeX.

**Report length:** Minimum 5 full pages, maximum 10 pages (not including references) -- these are hard cutoffs! If you need more material, you should include it only in an "appendix" and it may not be graded (at our discretion).
Do not change the font, margins or do other spacing tricks to fit within the page limit.

## 1. Introduction, problem selection, and goals

This can be similar to your proposal. At the end of this section, make sure you add specific goals that you had at the time of your project proposal (even if these weren't included in your proposal, this is new for the final report -- it may be helpful to structure as minimum goal, target goal, reach goal).

## 2. Implementation

Instead of an implementation plan (that was in your proposal), here you should describe your actual implementation! Please make sure to update this from your proposal.

2.1. **Tool selection.** What tools and languages did you use for your project? (In most cases, this will include at least Dafny, but could include other languages/tools)

2.2. **Architecture of your code.**
What component(s) are there in your final code and how do they interact? Which of them are implemented and which were you unable to implement? Which are verified? Consider drawing a diagram of all the components.

2.3. **Verification effort.** Which functions, components, or properties of your software have you verified?
Were these verified at compile-time or at run-time?

## 3. Challenges

What challenges did you identify throughout the course of your project?

This could be interaction features, properties which go beyond functional correctness, difficulty verifying certain cases, or other challenges.

Were there any methods or sections of the code you were unable to verify, despite trying? Any parts of the proof you were unable to complete or axioms (or assume statements) you had to assume away?

(Note: you can use `lemma{:axiom} ensures <formula>` or `assume{:axiom} <formula>` to add assumptions which you believe are true, but you are unable to prove. Be careful about using these!)

## 4. Results

Summarize your results!

- On the implementation side, what happens when you run your code? Show some input and output! Which features did you implement, which did you not get to?

- On the verification side, what is the overall "QED" that you got? Please include some specific methods with pre/postconditions, or formulas, that you were able to prove about your application at a high level. Which parts of the code, overall, were you able to verify?

Then, tie this back to your goals from the introduction.
Which goals that you set out to do were you able to complete?
Please note that it is not required that you complete all of the goals you set out to do! It's possible that some parts of your project ended up being too hard to fully verify.
You won't be graded on whether you completed all of your goals, but on whether: (1) you made a serious effort to do so; and (2) whether you describe and document clearly what it is you were able to do, as well as what you were not able to complete for the project, including any unimplemented code, unproven assumptions, axioms, or lemmas, etc.

Please also state some details about the amount of effort required. For example, how many weeks did you spend on each component? How many lines of code did you write? You don't have to break these numbers up by different project members.
(Please note that there is no specific requirement that you write a certain number of lines of code. I'm more interested in whether you can explain your results clearly and what progress you were able to make. Lines of code is one way of describing at a bird's eye level the complexity of the various components that made it into your final code.)

## 5. Contribution statement

**Contributors:**
Please include a list of the members of your group and what each person contributed to (in 2-3 sentences). For example, built components X, Y, Z, participated in weekly discussions, helped prepare the proposal (sections A, B, and C) and report (sections D, E, and F).

**AI statement:**
This year it is also mandatory to include an AI statement.
AI tools are allowed in the course syllabus.
Please state how you used AI, for which parts, and in what manner. What did you find it helpful/not helpful for?
Your grade will not be penalized for using AI.

## 6. Conclusions

Overall: What did you learn? Did you enjoy this project?
What was the most interesting or surprising part? What was the most difficult or challenging part?
What would you do differently if you did the project again?
Will you continue working on this code?
What features will you tackle next?

Please summarize your honest experience! The above are some of the questions to consider. I want to hear how the project worked for you. If you have any constructive criticism about how the project might have been better structured for the future, you can also share that here.

## References cited

Include any papers or websites related to what your project is going to do and citations at the bottom of your document.
This can be the same list of references from your proposal, or it can include additional references.
Please include at least 5 citations for your final report.
At least 2 of these should be research papers or textbooks, not websites/repositories.
