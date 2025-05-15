# Project final report

For the project proposal, you should provide a 5-10 page report (not including references).
I recommend (but do not require) that the report be written in LaTeX.

Your report may adapt the same document from your proposal, but it should be modified based on the following outline to include your results and conclusions.
Please address at least the following sections
(these are required, but not exhaustive, that is, you may also add additional subsections if you like).
Please also address any feedback from your project proposal, for example, if there were any suggestions for things you should fix or describe.

**Page limit:**
For the final report, the 10-page limit is strict!
If you have over 10 pages, you may include an "Appendix" after the references, this
may contain additional details but may not be used during grading (at our discretion).
Don't change the font, margins or do other spacing tricks to fit within 10 pages.
The 5-page minimum is also strict (it should be 5 full pages, not including references).

## 1. Introduction, problem selection, and goals

At the end of this section, make sure you add specific goals that you want your project to have.

## 2. Implementation

Instead of an implementation plan (that was in your proposal), here you should describe your implementation.

2.1. **Tool and language selection.** What tools and languages did you use for your project? (Including, Dafny or Z3?)

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
(Please note that it is not required that you complete all of the goals you set out to do! I expect that for some of you, your proejcts will end up being too hard to fully verify. But, you should make a serious effort.)

Please also state some details about the amount of effort required. For example, how many weeks did you spend on each component? How many lines of code did you write? You don't have to break these numbers up by different project members.
(Please note that there is no specific requirement that you write a certain number of lines of code. I'm more interested in whether you can explain your results clearly and what progress you were able to make.)

## 5. Contribution statement

Please include a list out the members of your group and what each person contributed to (in 2-3 sentences). For example, built components, participated in discussions, helped prepare the proposal (sections A, B, and C) and report (sections D, E, and F).

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
Please include at least 3-5 citations for your final report.
