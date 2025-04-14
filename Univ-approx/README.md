# Proving Universal Approximation Theorem using Lean 4

Overall topic reference: https://en.wikipedia.org/wiki/Universal_approximation_theorem

# This version
Scratch proof: A 2-layered SIGN-activated Multi-layer perceptron is able to approximate any 1d-Real-to-1d-Real Liptchitz function at any precision given sufficient width.

Proof topic reference: https://mjt.cs.illinois.edu/dlt/#classical-approximations-and-universal-approximation

```
cd /path/to/Univ-approx
lake +leanprover/lean4:v4.15.0 new Univ-approx math
```