# The conformance corpus

A language-neutral JSON corpus of (pattern, options, subject, expected result,
expected bounds) with a small runner per backend. It is what makes "the Python
interpreter, the generated Go, and the generated JavaScript agree bit for bit"
a thing that gets checked rather than hoped for.

It arrives with M4, when there is generated code to run it against. Until then
the differential cases live next to the oracle, in `oracle/corpus/seed.json`,
because pcre2 is the only implementation there is so far.
