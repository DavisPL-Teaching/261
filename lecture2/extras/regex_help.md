# RegEx help

The full Z3 Python API documentation can be found
[here](https://z3prover.github.io/api/html/namespacez3py.html).
Here are a few of the key regular expression operators that you will need:

- `z3.InRe`: this creates an assertion that a string matches a regular expression.
    For example, if `s` is a string and `s` is "cat", then
    `z3.InRe(s, z3.Re("c.*t"))` is true.
    This is how you get a (boolean) formula out of a regular expression.

- `z3.Full`: matches any character.
    For technical reasons, it has to be passed a single argument, which is the "sort" (or type) of the characters that it matches. For this reason we provide a helper funcion ReFull which does this for you.

- `z3.Re`: this turns a string into a regular expression.
    For example, `z3.Re("cat")` matches the string "cat".

- `z3.Length`: this creates an integer variable for the length
    of a string `s`. For example, if `s` is "cat", then
    `z3.Length(s)` will be a `z3.Int` that would be equal to 3.

- `z3.Range`: this creates a regular expression that matches
    a single character in a given range of the ASCII table.
    For example, `z3.Range("a", "z")`
    matches any lowercase letter -- any character between "a" and "z"
    in the ASCII table.

- `z3.AllChar`: this creates a regular expression that matches any character.
    (For example, it matches "a", ".", "$", or anything else.)

- `z3.Concat`: this creates a regular expression that matches
    a string with several parts, each of which is a regular expression.
    For example, `z3.Concat(z3.Re("c"), z3.Re("at"))`
    matches the string "cat".
    For an example of how this is useful, see the `ReContaining` function.

- `z3.Union`: this creates a regular expression that matches a string
    if it matches any of a list of regular expressions.
    For example, `z3.Union(z3.Re("cat"), z3.Re("dog"))`
    matches either "cat" or "dog".

- `z3.Star`: this creates a regular expression that matches a string
    if it matches the given regular expression zero or more times.
    For example, `z3.Star(z3.Re("a"))` matches any string of consecutive
    "a"s, including the empty string.

- `z3.Plus`: this is like `z3.Star`, but it must match
    one or more times instead of zero or more times. So,
    `z3.Plus(z3.Re("a"))` matches any string of at least one consecutive
    "a"s.

- `z3.IntToStr`: this converts an integer to a string.
    For example, if `d` is a `z3.Int` that is equal to 42,
    then `z3.IntToStr(d)` would be the string "42".

- `z3.CharIsDigit`: a boolean expression that is true if
    a character is a digit.
    To use this: if you have a string `s`, and an integer `d`,
    `s[d]` is a specific digit (for example), then

- `z3.CharToInt`: this converts a character to its integer
    character code. If you use this, you will need to refer to
    the ASCII table to see full list of codes. The codes for the
    numbers "0" through "9" are 48 through 57.
