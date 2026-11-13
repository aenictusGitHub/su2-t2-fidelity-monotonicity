import PhysicalCertificate

/-! The manuscript's proper-order fidelity total candidate, with N explicit. -/
namespace SU2T2
noncomputable section

/-- The physical two-qubit marginal on the symmetric spin-one space.
The dimension transport merely writes every N≥3 as (N−3)+3. -/
def marginal2 (N : ℕ) (hN : 3 ≤ N) (ρ : Spin.Mat N) : Cartesian.ComplexThree :=
  Physical.twoMarginal (N-3)
    (ρ.submatrix (Fin.cast (by omega : N-3+4=N+1))
      (Fin.cast (by omega : N-3+4=N+1)))

/-- Exactly 𝒜₂^{T,F}(ρ)=((Tr √ρ₂)²−1)/2 in the manuscript. -/
def fidelityTotal2 (N : ℕ) (hN : 3 ≤ N) (ρ : Spin.Mat N) : ℝ :=
  matrixFidelity2 (marginal2 N hN ρ)

@[simp] lemma marginal2_add_three (n : ℕ) (hN : 3 ≤ n+3)
    (ρ : Spin.Mat (n+3)) : marginal2 (n+3) hN ρ = Physical.twoMarginal n ρ := by
  rfl

@[simp] lemma fidelityTotal2_add_three (n : ℕ) (hN : 3 ≤ n+3)
    (ρ : Spin.Mat (n+3)) :
    fidelityTotal2 (n+3) hN ρ = matrixFidelity2 (Physical.twoMarginal n ρ) := by
  simp [fidelityTotal2]

end
end SU2T2
