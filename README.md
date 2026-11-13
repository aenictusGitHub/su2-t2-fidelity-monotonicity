# Fidelity total anticoherence at order two

This repository proves the fidelity part of Conjecture 1 in
*Total, quantum, and classical measures of anticoherence for mixed spin states*
(`resub_v0.tex`, 13 November 2026), for every proper order-two reduction,
that is, every **N ≥ 3**.

For every density operator on the spin-`N/2` sector and every completely positive,
trace-preserving SU(2)-covariant channel on that same sector, the result is

\[
\mathcal A^{T,F}_2(\Phi(\rho))\ge\mathcal A^{T,F}_2(\rho),\qquad
\mathcal A^{T,F}_2(\rho)=\frac{(\operatorname{Tr}\sqrt{\rho_2})^2-1}{2}.
\]

The statement includes mixed inputs, singular reductions, every finite `N ≥ 3`,
and all covariant channels. It does not settle the trace-distance candidate or
fidelity at orders `t ≥ 3`.

## Read the proof

- [Self-contained proof (PDF)](proof.pdf)
- [Editable LaTeX source](proof.tex)
- [Lean certificate and exact verification scope](lean/README.md)
- [BibTeX citation](citation.bib)
- [Companion manuscript changes](manuscript.patch)

The proof derives the relevant channel multipliers from the Choi matrix and
angular-momentum Casimirs, obtains the physical marginal constraint
`0 ≤ A ≤ 3I/2`, and proves determinant increase and purity decrease. An elementary
three-eigenvalue lemma then gives the exact fidelity normalization above.

Compared with the supplied eight-page proof, this version treats arbitrary
channel mixtures directly, uses polynomial identities for the cofactor and
determinant steps, handles singular states without a limiting argument, and
replaces the square-root integral by an elementary algebraic comparison.

## What Lean certifies

**The written mathematical proof is complete. The Lean certificate verifies its
scalar algebraic reduction; it is not an end-to-end formalization of the SU(2)
quantum-channel theorem.**

The principal checked theorem is
`SU2T2.channel_fidelity_monotone_from_scalar_reduction`.
It combines the multiplier bounds for every `N ≥ 3` and every probability mixture,
the determinant and purity inequalities, and the final fidelity comparison.

The Choi/Casimir representation of physical channels, the Cartesian form and
symmetric-extension constraint of the marginal, and its spectral identities are
derived in the PDF. These identifications remain explicit hypotheses of the Lean
theorem. The files introduce no additional axioms or unfinished proofs.

Lean **4.24.0** and mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7` are pinned. The build and axiom audit are
recorded in [verification.log](lean/verification.log); the exact checked files are
listed in [source-sha256.txt](lean/source-sha256.txt).

## Reproduce

With Lean's `elan` manager installed:

```sh
cd lean
lake update
lake exe cache get Mathlib/Tactic.lean
lake build
lake env lean Certificate.lean
```

The final command prints the standard foundational dependencies
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`.
See [lean/README.md](lean/README.md) for the full theorem-to-proof mapping.

To rebuild the PDF with a LaTeX installation containing the packages used by
`proof.tex`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error proof.tex
pdflatex -interaction=nonstopmode -halt-on-error proof.tex
```

## Provenance and manuscript citation

The basis supplied for this work was `su2_t2_full_direct_proof.pdf`, SHA-256
`8cb23bd374a7bcb7e4f405fb632c02cdc0a6e298dba6a7caf8787e846f68325c`.
The target manuscript was `Overleaf131126/First reply/resub_v0.tex`, whose
pre-edit SHA-256 was
`57edc7f8601f872009415b92ce6298833ebb64528d8461abd04fa95055a1fe81`.
The full manuscript and original supplied PDF are not redistributed here.

The manuscript retains the wording and numbering of Conjecture 1 and identifies
its fidelity `t = 2` case as proved. Its remaining-open statements are narrowed
accordingly. The bibliography describes the Lean component as a certificate of
the algebraic reduction.

This repository is initially **private**, as requested. Its citation is therefore
a draft reference until the repository is made accessible to readers. No change
to public visibility is part of this version. Authorship metadata is left for the
manuscript authors to settle.
