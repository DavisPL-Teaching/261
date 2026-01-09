# Some more "interesting" examples of specifications

## Exercises

Exercise: determine which of these are:
(i) expressible in Hypothesis
(ii) easily checkable more generally.

8. For all sufficiently large x, ...
9. The source code of integer_sqrt contains...
10. If integer_sqrt(x) is run on an arbitrary Python object x...
11. The program integer_sqrt(x) always terminates for all x such that...

## More complex specifications

Just as a fun side note - you don't need to know these!

- A **security property** says that a program behaves in a certain way,
  for all instantiations of some "threat model", basically no matter what some adversary does. It typically has the form:

  "For all adversarial programs (or inputs x) Q, the program P(Q, x) does..."

- A **hyperproperty** is a property that describes a program on more than one input. For example:

  "For all x and for all y, if x is equivalent to y, then P(x) is equivalent to P(y)"

- A **side effect** of a program is some behavior it has other than its input/output behavior (like opening a file). The following is an important safety property:

  "The program P(x) does not have any side effects for any x."
