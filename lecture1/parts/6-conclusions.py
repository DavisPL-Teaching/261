"""
Lecture 1, Part 6:
Conclusions

===== Poll =====

Which of the following has no effect? (Select all that apply)
- assert True
- assert False
- assume True
- assume False
- assert P if it occurs immediately following assume P
- assume P if it occurs immediately following assert P

https://forms.gle/x673cssDmmY9aDKH9

===== Discussion and limitations =====

Testing

# Advantages

Some more about advantages:
https://news.ycombinator.com/item?id=34450736

"I've never introduced property tests [random tests] without finding a bug in either the specification or implementation. I have repeatedly spent time figuring out where the bug was in my property testing library before realising that it was correct and the obviously correct code I was testing was actually wrong."

# Disadvantages

Most important limitation:

- Testing might not find the bug!

Edsger Dijkstra:

    "Program testing can be a very effective way to show the presence of bugs, but it is hopelessly inadequate for showing their absence."

This is not a problem with the spec itself, but with using random testing
as a method of validating the spec.

Limitations related to writing specs -- these are not specific to testing (!)

- Specification could be wrong

- Specification could be incomplete

Other limitations of Hypothesis specifically?

- Customization

- Testing can be redundant.

Quick recap:
- we talked about different types of specifications
    (functional correctness, safety, liveness)
- we talked about preconditions and postconditions
- we talked about assert/assume

    + A pre/post condition based spec is called
        functional correctness

    + assume/assert based spec is everything that testing can express
        (slightly more general)

- we talked about limitations of testing: it can't
    prove there are no bugs.
    That is what the remaining tools in this class
    will be about.
"""
