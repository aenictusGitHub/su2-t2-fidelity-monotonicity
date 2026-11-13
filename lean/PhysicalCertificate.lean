import CoherentBounds
import SpinCovariance

/-! Composition of the actual physical marginal and spectral inequalities. -/
namespace SU2T2
open Matrix
open scoped ComplexOrder
noncomputable section

lemma spin_size_bound (n : ℕ) : 15 ≤ ((n+3 : ℕ) : ℝ)*((n+3 : ℕ)+2) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  nlinarith

/-- The physical conclusion once the low-rank attenuation law has been derived.
The final group-covariant theorem discharges that law from SU(2) covariance. -/
theorem physical_fidelity_mono_of_action (n : ℕ)
    (φ : Choi.Mat (n+4) →ₗ[ℂ] Choi.Mat (n+4))
    (hCP : Choi.CompletelyPositive φ) (hTP : ∀ X, (φ X).trace=X.trace)
    (f g : ℝ)
    (haction : ∀ ρ, ρ.PosSemidef → ρ.trace=1 →
      Physical.twoMarginal n (φ ρ) =
        Cartesian.covarianceAction f g (Physical.twoMarginal n ρ))
    (hcurve : 3*(((n+3 : ℕ) : ℝ)*((n+3 : ℕ)+2))*f^2-6*f-
      ((n+3 : ℕ) : ℝ)*((n+3 : ℕ)+2) ≤
      2*(((n+3 : ℕ) : ℝ)*((n+3 : ℕ)+2)-3)*g)
    (ρ : Choi.Mat (n+4)) (hρ : ρ.PosSemidef) (ht : ρ.trace=1) :
    matrixFidelity2 (Physical.twoMarginal n ρ) ≤
      matrixFidelity2 (Physical.twoMarginal n (φ ρ)) := by
  have hcoh := Physical.coherent_posSemidef n
  have hct := Physical.coherent_trace n
  have hcohout := (Physical.twoMarginal_physical_constraints n (φ (Physical.coherent n))
    (Choi.positive φ hCP hcoh) ((hTP _).trans hct)).1
  rw [haction _ hcoh hct, Physical.twoMarginal_coherent] at hcohout
  obtain ⟨hplus,hminus,hzero⟩ := Physical.coherent_action_bounds f g hcohout
  obtain ⟨hg₀,hg₁,hfabs⟩ := region_from_coherent_and_choi _ f g
    (spin_size_bound n) hcurve hplus hminus hzero
  obtain ⟨hred,hredt,hA,hAt,hupper⟩ :=
    Physical.twoMarginal_physical_constraints n ρ hρ ht
  have hout := (Physical.twoMarginal_physical_constraints n (φ ρ)
    (Choi.positive φ hCP hρ) ((hTP _).trans ht)).1
  exact Cartesian.fidelity_mono_of_action _ _ _ f g hred hredt hout hupper
    (haction ρ hρ ht) (spin_size_bound n) hg₀ hg₁ (by linarith) (by linarith) hcurve

end
end SU2T2

#print axioms SU2T2.physical_fidelity_mono_of_action
