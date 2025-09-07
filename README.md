# Pytest Test Minimizer with Z3

This is the preliminary proof of concept of a pytest plugin that minimizes test cases using the Z3 theorem prover.

It will output different test combinations,
and how much coverage each combination achieves,
at which efficiency gain.

## How does it work

It uses coverage.py to measure code coverage of each test case,
and translates each pass as:

this tast case X if enabled cover lines XNN

X implies lines XNN are covered

Or, in prolog:

covers(X, Line).

After this, we try to find how each combination of test cases
can cover the same lines,
using the Z3 theorem prover.

This allows to achieve significant reduction in test cases,
while still covering the same lines of code.