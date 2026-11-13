# Magnetic-basis order and conversion

The abstract theorem is independent of basis order. Lean indexes `k = 0,…,N`
with `m = k - N/2` (ascending magnetic order). The manuscript's numerical HOAP
arrays in Appendix C use `m = N/2 - q` (descending magnetic order). Thus
`q = N-k`. No phase is introduced by this reordering.

Let `R[k,q] = 1` when `q=N-k`, and zero otherwise. Then `R†=R=R⁻¹`.
The complete conversion is

- Vectors: `v_asc[k] = v_desc[N-k]`, or `v_asc = R v_desc`.
- Matrices: `A_asc[k,l] = A_desc[N-k,N-l]`, or `A_asc = R A_desc R`.
- Channels: `Φ_asc(A) = R Φ_desc(R A R) R`.
- Rotation matrices: `U_asc = R U_desc R`.

For N=3, a descending array `[v_(3/2), v_(1/2), v_(-1/2), v_(-3/2)]`
becomes `[v_(-3/2), v_(-1/2), v_(1/2), v_(3/2)]`. Reverse both indices of
a density matrix; reversing only its rows is incorrect.

The Lean functions `Spin.reverseVector`, `Spin.reverseMatrix`, and
`Spin.reverseChannel` implement these formulas using `Fin.rev`. The vector
and matrix conversions are proved involutive in `BasisOrder.lean`.

If `D_asc` is the normalized embedding used in Lean, the descending embedding
is `D_desc = D_asc R`; consequently
`D_asc ρ_asc D_asc† = D_desc ρ_desc D_desc†`. The physical partial trace and
fidelity therefore represent the same state in both conventions. The
Cartesian triplet basis is a separate, explicitly unitary change of basis
already certified in `SpinOneAction.lean`.

## Certified group action

`Dicke.action_intertwines` proves `U⊗N D = D action(N,U)` for every SU(2)
element and every N. `action_one`, `action_mul`, and `action_unitary` prove
the identity, group law, and unitarity. `unitaryAction` packages all three
as a group homomorphism into the unitary group.

The invariant-range proof uses the generating polynomial
`Σ_c (U⊗N)[b,c] X^(weight(c))`, which equals
`(U00+U01 X)^(N-weight(b)) (U10+U11 X)^weight(b)`. Its coefficients depend
only on the row's Hamming weight. A proved projection identity then places
each transformed Dicke column back in the normalized Dicke subspace.
