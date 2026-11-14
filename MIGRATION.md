# Repository consolidation — 14 November 2026

The canonical public repository is [mixed-spin-anticoherence](https://github.com/aenictusGitHub/mixed-spin-anticoherence).
Its title is the title of the companion [arXiv submission](https://arxiv.org/abs/2605.29436).

## Imported snapshots and histories

| Original repository | Original main commit | Directory in the combined repository |
|---|---|---|
| `su2-t2-fidelity-monotonicity` | `151f48ce9a4621f0789facee7b94b157cb9efbd3` | `su2-t2-fidelity-monotonicity/` |
| `spin52-purity-certificates` | `455931c12d0475a3ad8e314ea9867437345bd75d` | `spin52-purity-certificates/` |

The fidelity files were moved without modification. The spin-5/2 history was
merged as a second parent, with its complete tree imported into its directory.
Both original main commits are ancestors of the combined main branch. No
original commits or tags were rewritten.

At consolidation, each imported directory's Git tree is identical to its source:

- Fidelity: `7057ff0b01e0b156b9d2c198c96bb2fa6b9873c8`.
- Spin-5/2: `2660954b11517de5a1e1ddd102748cf0029a161b`.

All 37 entries in the Lean `source-sha256.txt` manifest and all 44 entries in the
spin-5/2 `SHA256SUMS` manifest were checked successfully after import. These checks
establish preservation of the previously verified artifacts; the consolidation
does not constitute a new mathematical audit or a rerun of the proof verifiers.

## Existing citations and releases

The fidelity repository was renamed to the canonical repository, preserving its
GitHub release and old-address redirects. The tags `v1.0.0`, `v2.0.0`, and
`v2.1.0` still identify their original fidelity-only snapshots. The v2.1.0 PDF
attachment is preserved unchanged.

The spin-5/2 repository is retained as an archived citation destination with a
notice pointing here. Its original commit remains available in both histories.
Commit-pinned links therefore continue to identify the same files and proofs.

On the combined main branch, component files now live in the directories shown
above. Historical component documentation is retained verbatim, including its
original repository links. Use the root [citation.bib](citation.bib) for canonical
repository URLs and the root [README](README.md) to navigate the current layout.
