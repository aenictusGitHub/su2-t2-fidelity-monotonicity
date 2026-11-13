import ManuscriptNotation
import DensitySpan
import PhysicalAffine

/-!
# Conjecture 1 for the fidelity total candidate at t = 2

This theorem has only the original physical hypotheses: N≥3, a completely
positive trace-preserving SU(2)-covariant channel on the spin-N/2 sector,
and a positive trace-one input state. The two-body marginal is the actual
partial trace of the normalized Dicke embedding, and fidelity uses the
positive matrix square root from continuous functional calculus.

The SU(2) generators, Choi variance, marginal constraints, attenuation law,
and spectral identifications are conclusions of imported proved lemmas;
none is an additional hypothesis of this theorem.
-/
namespace SU2T2
open Matrix
open scoped ComplexOrder
noncomputable section

/-- Precisely the fidelity part of Conjecture 1 at proper order t=2. -/
theorem conjecture1_fidelity_t2_of_operator_covariance (N : ℕ) (hN : 3 ≤ N)
    (Φ : Spin.Mat N →ₗ[ℂ] Spin.Mat N)
    (hCP : Choi.CompletelyPositive Φ)
    (hTP : ∀ A, (Φ A).trace=A.trace)
    (hSU2 : Dicke.Covariant N Φ)
    (ρ : Spin.Mat N) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    fidelityTotal2 N hN ρ ≤ fidelityTotal2 N hN (Φ ρ) := by
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, N=n+3 := ⟨N-3,by omega⟩
  obtain ⟨hE,hF,hH⟩ := Dicke.covariant_generators (n+3) Φ hSU2
  obtain ⟨f,g,hI,hlow,hdual,hcurve⟩ :=
    Spin.covariant_channel_reduction (n+3) (by omega) Φ hCP hTP hE hH hF
  have haction := Physical.twoMarginal_action n Φ hTP hF f g hdual
  simpa only [fidelityTotal2_add_three] using
    physical_fidelity_mono_of_action n Φ hCP hTP f g haction hcurve ρ hρ htr

/-- The exact manuscript statement: covariance is required only on states.
Complex linearity extends it to all operators by the proved density-span lemma. -/
theorem conjecture1_fidelity_t2 (N : ℕ) (hN : 3 ≤ N)
    (Φ : Spin.Mat N →ₗ[ℂ] Spin.Mat N)
    (hCP : Choi.CompletelyPositive Φ)
    (hTP : ∀ A, (Φ A).trace=A.trace)
    (hSU2 : Dicke.CovariantStates N Φ)
    (ρ : Spin.Mat N) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    fidelityTotal2 N hN ρ ≤ fidelityTotal2 N hN (Φ ρ) := by
  exact conjecture1_fidelity_t2_of_operator_covariance N hN Φ hCP hTP
    (Dicke.covariant_of_covariantStates N Φ hSU2) ρ hρ htr

end
end SU2T2

#print axioms SU2T2.conjecture1_fidelity_t2
#check SU2T2.conjecture1_fidelity_t2
