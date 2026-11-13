# Lean certificate of the full fidelity theorem at t = 2

Version 2.0.0 proves the full fidelity case of manuscript Conjecture 1 at proper
order `t = 2`, for every natural `N ≥ 3`. The principal theorem is
[`SU2T2.conjecture1_fidelity_t2`](FullTheorem.lean).

```lean
theorem conjecture1_fidelity_t2 (N : ℕ) (hN : 3 ≤ N)
    (Φ : Spin.Mat N →ₗ[ℂ] Spin.Mat N)
    (hCP : Choi.CompletelyPositive Φ)
    (hTP : ∀ A, (Φ A).trace = A.trace)
    (hSU2 : Dicke.CovariantStates N Φ)
    (ρ : Spin.Mat N) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    fidelityTotal2 N hN ρ ≤ fidelityTotal2 N hN (Φ ρ)
```

These are exactly the physical hypotheses. The theorem has no assumed channel
multipliers, Choi decomposition, marginal bounds, moment identities, eigenvalue
identifications, or scalar fidelity reduction.

## Definitions and correspondence with the manuscript

- `Spin.Mat N` is the algebra of complex `(N+1) × (N+1)` matrices in the normalized
  Dicke basis, with magnetic quantum number `m = k - N/2`.
- `Choi.CompletelyPositive` means positivity under every finite ancillary matrix
  amplification. It is not an assumed Kraus or Choi decomposition.
- `Dicke.CovariantStates` quantifies over actual
  `Matrix.specialUnitaryGroup (Fin 2) ℂ` elements and every density matrix. The
  spin action is `Dᴴ * tensorPower U N * D`, where `D` is the proved isometric
  normalized Dicke embedding. `DensitySpan` proves extension to all operators.
- `marginal2 N hN ρ` is the actual two-qubit partial trace of the symmetric
  embedding, compressed to the orthonormal Cartesian triplet basis. The dimension
  transport in its definition merely writes `N = (N-3)+3`.
- `fidelityTotal2` is `((Re Tr (CFC.sqrt ρ₂))² - 1)/2`. For positive matrices the
  square-root trace is real, as proved through its eigenvalues. This is exactly
  the manuscript's `𝒜₂^{T,F}`, using squared Uhlmann–Jozsa fidelity.

## What is proved

| Files | Checked mathematical content |
| --- | --- |
| `DickeEmbedding`, `DickeGenerators`, `DickeSU2`, `DensitySpan` | Normalized symmetric embedding, concrete spin generators, genuine SU(2) rotations, differentiation of covariance, and extension from states to operators. |
| `SpinHighestWeight`, `SpinGenerators`, `SpinCovariance`, `TraceDual` | Elementary highest-weight uniqueness, spin commutators and Casimir, unitality, real first/second-rank multipliers, and the same action for the actual trace adjoint. |
| `SU2Choi` | Complete positivity implies Choi positivity; exact trace pairing; the two Casimir polynomial identities; Choi variance implies the curved multiplier bound. |
| `PhysicalMarginal`, `PhysicalEmbedding`, `PhysicalNBody` | The actual symmetric partial trace is positive and trace preserving; its Cartesian matrix obeys `0 ≤ A ≤ 3I/2`, `Tr A = 2`, for every `N ≥ 3`. |
| `PhysicalCovariance`, `PhysicalTransfer`, `PhysicalTwoCovariance`, `PhysicalTwoTrace`, `SpinOneAction`, `PhysicalAffine` | Covariance of the physical marginal, highest-weight transfer, complete spin-one basis identification, and the actual affine marginal law. |
| `CoherentBounds`, `ChoiScalarBounds` | The coherent-state marginal and its output positivity give the linear multiplier bounds; Choi variance supplies `g ≥ -2/3`. |
| `BroadDeterminant`, `Qutrit`, `Certificate` | Determinant increase, purity contraction, and the elementary square-root eigenvalue comparison, including singular states. |
| `Spectral`, `CartesianSpectral` | Real orthogonal diagonalization, determinant and purity formulas, spectral identification of `CFC.sqrt`, and the actual matrix fidelity inequality. |
| `PhysicalCertificate`, `ManuscriptNotation`, `FullTheorem` | Composition of all proved bridges into the exact manuscript theorem. |
| `Audit` | Public statement, physical definitions, and axiom dependencies of the theorem and its main bridges. |

`Determinant`, `Multipliers`, and the original theorem in `Certificate` retain the
version 1 scalar certificate. `SU2Differential` additionally proves the generic
exponential covariance differentiation lemma. The full theorem uses the direct
SU(2) rotation curves in `DickeSU2`.

The full proof needs only the first two tensor ranks. A direct Choi variance
argument replaces a Clebsch–Gordan decomposition and channel-vertex enumeration.
The slightly broader lower bound `g ≥ -2/3` is sufficient for the determinant
argument. The corresponding written proof is `../proof.pdf`.

## Reproduce the check

The project pins Lean **4.24.0**, mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and the transitive dependencies in
`lake-manifest.json`. With Lean's `elan` manager installed, run here:

```sh
lake update
lake exe cache get
lake build
lake env lean Audit.lean
```

The cache retrieves compiled mathlib dependencies. `lake build` checks all 32
project modules from their source; it does not substitute a downloaded proof of
this theorem. The recorded `verification.log` was produced after removing the
project's local build artifacts. `axiom-audit.log` records a separate execution
of the audit.

The complete theorem and every audited physical bridge depend only on:

```text
propext, Classical.choice, Quot.sound
```

There are no `sorry`, `admit`, custom `axiom`, or `native_decide` declarations in
the project sources, and no `sorryAx` dependency. `source-sha256.txt` records the
exact source and configuration files checked in this release.
