# Riemann Hypothesis in Lean

_by Brandon H. Gomes and Alex Kontorovich through the Department of Mathematics, Rutgers University_

## Formalization

The Riemann Hypothesis is formalized by assuming some algebraic properties of the real and complex numbers and the existence/properties of the complex exponential function and the real logarithm. These axioms are then used to construct the Dirichlet η function which we use to define the Riemann Hypothesis as the following type:

```lean
(Re s ∈ (0,1)) ∧ (eta s = 0) → (Re s = 1/2)
```

We also include the file, `mathlib/impl.lean`, which is a witness that the axioms can be proved using [`mathlib`](https://github.com/leanprover-community/mathlib).

## Acknowledgements

We would like to thank Alex Best, Kevin Buzzard, Colin Fan, Sebastien Gouezel, Heather Macbeth, and the Zulip Lean community for many suggestions that made this project possible.

The work of the first-named author was supported by the Rutgers Math Department through the DIMACS REU, and both are supported in part by the second-named author's NSF grant DMS-1802119.
