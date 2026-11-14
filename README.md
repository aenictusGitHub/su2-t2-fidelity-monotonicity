# Order-two fidelity monotonicity under SU(2)-covariant channels: full proof and Lean certificate

This repository proves the fidelity part of Conjecture 1 in
*Total, quantum, and classical measures of anticoherence for mixed spin states*
(`resub_v0.tex`, 13 November 2026), for every proper order-two reduction,
that is, every **N ≥ 3**.

The companion manuscript is by Jérôme Denis, Tara Lacaille, John Martin, and
Eduardo Serrano-Ensástiga (2026):
[arXiv:2605.29436](https://arxiv.org/abs/2605.29436).
Its BibTeX reference is included in [citation.bib](citation.bib).

For every density operator on the spin-`N/2` sector and every completely positive,
trace-preserving SU(2)-covariant channel on that same sector, the result is

```math
\mathcal A^{T,F}_2(\Phi(\rho))\ge\mathcal A^{T,F}_2(\rho),\qquad
\mathcal A^{T,F}_2(\rho)=\frac{(\mathrm{Tr}\sqrt{\rho_2})^2-1}{2}.
```

The statement includes mixed inputs, singular reductions, every finite `N ≥ 3`,
and all covariant channels. It does not settle the trace-distance candidate or
fidelity at orders `t ≥ 3`.

## Read the proof

- [Self-contained proof (PDF)](proof.pdf)
- [Editable LaTeX source](proof.tex)
- [Lean certificate and exact verification scope](lean/README.md)
- [BibTeX citation](citation.bib)
- [Companion manuscript changes](manuscript.patch)

The proof derives the relevant channel multipliers from covariance and the Choi
variance, obtains the physical marginal constraint
`0 ≤ A ≤ 3I/2`, and proves determinant increase and purity decrease. An elementary
three-eigenvalue lemma then gives the exact fidelity normalization above.

Compared with the supplied eight-page proof, this version treats arbitrary
channel mixtures directly, uses polynomial identities for the cofactor and
determinant steps, handles singular states without a limiting argument, and
replaces the square-root integral by an elementary algebraic comparison.

## What Lean certifies

**Version 2.1.0 proves the full quantum-channel theorem in Lean.** The principal
theorem is `SU2T2.conjecture1_fidelity_t2` in [FullTheorem.lean](lean/FullTheorem.lean).
Its hypotheses are precisely `N ≥ 3`, complete positivity, trace preservation,
SU(2) covariance on density matrices, and a positive trace-one input.

The certificate derives the SU(2) generator reduction, Choi positivity and
variance, physical marginal constraints, the two-multiplier action on the actual
partial trace, and the spectral identities for the actual positive matrix square
root. None of these is an additional assumption of the final theorem.

The shorter argument uses only the first two tensor ranks and a Choi variance
bound. It does not require a Clebsch–Gordan decomposition. The original scalar
certificate is retained as a subsidiary result; version 1.0.0 remains available.

Lean **4.24.0** and mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7` are pinned. The clean build is recorded in
[verification.log](lean/verification.log), and the theorem and bridge assumptions
are printed in [axiom-audit.log](lean/axiom-audit.log). Only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound` occur. There are no unfinished
proofs, additional axioms, or `sorryAx` dependencies.

## Reproduce

With Lean's `elan` manager installed:

```sh
cd lean
lake update
lake exe cache get
lake build
lake env lean Audit.lean
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
the full theorem.

This repository is **public**. Cite the published
[v2.1.0 release](https://github.com/aenictusGitHub/su2-t2-fidelity-monotonicity/releases/tag/v2.1.0)
using [citation.bib](citation.bib). Authorship metadata is left for the manuscript
authors to settle.

Version 2.1.0 additionally certifies the spin-action group law and unitarity.
See [basis conversion](BASIS_ORDER.md) and [the revised audit](audit/v2.1.0-audit.txt).
