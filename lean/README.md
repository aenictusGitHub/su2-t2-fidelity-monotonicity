# Lean certificate: the scalar proof for fidelity at t = 2

This project checks the real-algebra part of the companion proof of Conjecture 1
for the fidelity total candidate at `t = 2`, including every `N ≥ 3` and every
finite probability mixture of the covariant-channel vertices.

**Scope:** this is a certificate of the complete scalar reduction. It is not an
end-to-end formalization of the original statement in terms of Hilbert spaces,
SU(2) representations, completely positive maps, and partial traces. The
companion mathematical proof establishes that physical data satisfy the explicit
hypotheses of the final Lean theorem. These hypotheses are visible in the theorem
statement; they are not introduced as axioms.

## What is checked

| File | Results |
| --- | --- |
| `Multipliers.lean` | Exact vertex multiplier formulas; the bounds for every natural `N ≥ 3` and `0 ≤ K ≤ N`; the weighted-square inequality; all multiplier restrictions for arbitrary probability mixtures. |
| `Determinant.lean` | Schur's cubic inequality; the deviation bound; unpolarized determinant expansion; both cofactor cases; determinant monotonicity, including singular inputs. |
| `Qutrit.lean` | The elementary qutrit spectral argument from determinant increase and purity decrease to increase of the normalized fidelity candidate. |
| `Certificate.lean` | Purity contraction and the final composition of all the preceding results. |

The principal theorem is

```lean
SU2T2.channel_fidelity_monotone_from_scalar_reduction
```

Its conclusion is

```lean
((x+y+z)^2-1)/2 ≤ ((X+Y+Z)^2-1)/2
```

where `x,y,z` and `X,Y,Z` are the nonnegative square roots of the input and
output marginal eigenvalues. This is exactly the `t = 2` normalization of
`𝒜₂^{T,F}` in the manuscript.

The scalar hypotheses of this theorem are:

- `N ≥ 3` and nonnegative channel weights summing to one;
- the stated rank-one and rank-two multiplier formulas, averaged with those weights;
- eigenvalues `a,b,c` of the real symmetric matrix `A`, lying in `[0,3/2]` and
  summing to two;
- the affine action `A′ = 2(1-g)I/3 + gA` and `r′ = fr`, encoded in the output
  purity and determinant formulas;
- nonnegative normalized eigenvalue square roots and their exact purity and
  determinant identities.

The following parts are proved in the companion mathematical document and are
**not formalized** here:

1. The Choi decomposition and Casimir calculation reducing an SU(2)-covariant
   channel to the displayed probability weights and multiplier formulas.
2. The Cartesian form of the symmetric marginal and the finite-`N`
   representability bound `0 ≤ A ≤ N/(N-1) I ≤ 3/2 I`.
3. The finite-dimensional spectral theorem identifying the scalar purity and
   determinant expressions with the marginal's eigenvalues.

## Reproduce the check

The project pins Lean **4.24.0** and mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (the mathlib `v4.24.0` release).
The complete transitive dependency lock is `lake-manifest.json`.

With Lean's `elan` toolchain manager installed, run in this directory:

```sh
lake update
lake exe cache get Mathlib/Tactic.lean
lake build
lake env lean Certificate.lean
```

The cache command retrieves compiled dependencies; it does not replace checking
this project's proof terms. `lake build` checks the four source modules.

`Certificate.lean` prints the axiom dependencies of the main theorems. The
verification recorded in `verification.log` reports only Lean/mathlib's standard
foundational axioms:

```text
propext, Classical.choice, Quot.sound
```

There are no `sorry`, `admit`, custom `axiom`, or `native_decide` declarations in
the project sources. In particular, there is no `sorryAx` dependency.

`source-sha256.txt` records the exact checked source and configuration files.
