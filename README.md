# Total, quantum, and classical measures of anticoherence for mixed spin states

Proofs, exact data, verification programs, and a Lean certificate accompanying
Jérôme Denis, Tara Lacaille, John Martin, and Eduardo Serrano-Ensástiga,
[*Total, quantum, and classical measures of anticoherence for mixed spin states*](https://arxiv.org/abs/2605.29436)
(arXiv:2605.29436).

This repository brings together the two companion proof collections.

| Collection | Contents | Start here |
|---|---|---|
| Order-two fidelity monotonicity | Full proof of the fidelity part of Conjecture 1 at t = 2, for every N ≥ 3 and all SU(2)-covariant channels; Lean certificate of the full theorem | [Guide](su2-t2-fidelity-monotonicity/README.md) · [Proof PDF](su2-t2-fidelity-monotonicity/proof.pdf) · [Lean certificate](su2-t2-fidelity-monotonicity/lean/README.md) |
| Spin-5/2 purity and convex roofs | Exact global purity optima at orders 2, 3, and 4; exact convex roofs for the rank-four state; coefficient data and verification programs | [Guide](spin52-purity-certificates/README.md) · [Purity proof PDF](spin52-purity-certificates/docs/purity-certificates.pdf) · [Convex-roof proof PDF](spin52-purity-certificates/docs/convex-roof-certificates.pdf) |

## Reproduce the certificates

Run each collection's commands from its own directory. Their source files,
relative paths, dependency versions, verification logs, and checksum manifests
are preserved from the original repositories.

For the Lean certificate, with Lean's `elan` manager installed:

```sh
cd su2-t2-fidelity-monotonicity/lean
lake update
lake exe cache get
lake build
lake env lean Audit.lean
```

For the spin-5/2 certificates, with Python 3.10 or later, start from the repository root:

```sh
cd spin52-purity-certificates
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python verify_all.py
```

On Windows, activate the environment with `.venv\Scripts\activate`.
The [spin-5/2 guide](spin52-purity-certificates/README.md) documents the optional
checks. Do not run the Python verifiers with `python -O`: their exact proof
checks use assertions.

## Cite and identify the version

Cite the [manuscript](https://arxiv.org/abs/2605.29436) and the relevant proof
collection at its release or commit. See [citation.bib](citation.bib) and
[CITATION.cff](CITATION.cff).

The [v2.1.0 release](https://github.com/aenictusGitHub/mixed-spin-anticoherence/releases/tag/v2.1.0) remains the published
order-two fidelity proof and Lean certificate. Its tag and PDF attachment are
preserved; it predates this combined layout and does not package the spin-5/2
collection. The spin-5/2 collection retains its original version 1.1.0 commit.

Both original Git histories are preserved. See [MIGRATION.md](MIGRATION.md) for
source commits, integrity checks, and compatibility with existing citations.
