"""pcre-vera: a generator for a formally verified PCRE engine.

The engine itself is authored once, in TIR (the small typed IR described in
DESIGN.md section 3), and everything else in this package either produces
that IR, consumes it, or checks it against the pinned pcre2 reference build.
"""

__version__ = "0.0.0"
