import PhysicalTwoTrace
import SpinOneAction

/-! The physical two-body attenuation law derived from actual channel covariance. -/
namespace SU2T2.Physical
open Matrix
open scoped ComplexOrder
noncomputable section

lemma cartesianTriplet_eq_dicke2_change :
    cartesianTriplet=dicke2*Spin.cartesianChange :=
  cartesianTriplet_eq_dicke2_explicit

lemma twoMarginal_eq_spinOne (n : ℕ) (ρ : Spin.Mat (n+3)) :
    twoMarginal n ρ=Spin.cartesianChangeᴴ*spinOneMarginal n ρ*Spin.cartesianChange := by
  rw [twoMarginal_eq_grouped,cartesianTriplet_eq_dicke2_change]
  change _ = Spin.cartesianChangeᴴ * (dicke2ᴴ * partialTraceLast
    (groupedTwoDicke n*ρ*(groupedTwoDicke n)ᴴ) * dicke2) * Spin.cartesianChange
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

lemma spinOneMarginal_posSemidef (n : ℕ) (ρ : Spin.Mat (n+3)) (hρ : ρ.PosSemidef) :
    (spinOneMarginal n ρ).PosSemidef :=
  (partialTraceLast_posSemidef _ (hρ.mul_mul_conjTranspose_same (groupedTwoDicke n))).conjTranspose_mul_mul_same dicke2

/-- The actual two-body reduction commutes with a globally covariant channel,
with the same two multipliers as its actual trace dual. -/
theorem spinOneMarginal_action (n : ℕ)
    (φ : Spin.Mat (n+3) →ₗ[ℂ] Spin.Mat (n+3))
    (hTP : ∀ X, (φ X).trace=X.trace)
    (hF : Spin.CommutesWithCommutator φ (Spin.lowering (n+3)))
    (f g : ℝ) (hlow : Spin.LowRankAction (n+3) (Choi.traceDual φ) f g)
    (ρ : Spin.Mat (n+3)) :
    spinOneMarginal n (φ ρ)=Spin.spinOneAction f g (spinOneMarginal n ρ) := by
  have hhigh := marginalDual_highest_eigenvectors n (Choi.traceDual φ)
    (f:ℂ) (g:ℂ) hlow.raising hlow.raising_sq
  have hI : Choi.traceDual φ (Choi.traceDual (spinOneMarginal n) 1)=
      Choi.traceDual (spinOneMarginal n) 1 := by
    rw [marginalDual_identity,Choi.traceDual_unital φ hTP]
  have hΦ : Spin.CommutesWithCommutator (Choi.traceDual φ) (Spin.lowering (n+3)) :=
    Choi.traceDual_commutator φ _ hF
  have htransfer := Spin.spinOne_transfer (Choi.traceDual (spinOneMarginal n))
    (Choi.traceDual φ) f g (marginalDual_lowering n) hΦ hI hhigh.1 hhigh.2
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro B
  rw [← Choi.traceDual_pairing,← Choi.traceDual_pairing,htransfer,
    Choi.traceDual_pairing,Spin.spinOneAction_trace_pairing]

/-- Full physical affine law: no marginal moment identification is assumed. -/
theorem twoMarginal_action (n : ℕ)
    (φ : Spin.Mat (n+3) →ₗ[ℂ] Spin.Mat (n+3))
    (hTP : ∀ X, (φ X).trace=X.trace)
    (hF : Spin.CommutesWithCommutator φ (Spin.lowering (n+3)))
    (f g : ℝ) (hlow : Spin.LowRankAction (n+3) (Choi.traceDual φ) f g)
    (ρ : Spin.Mat (n+3)) (hρ : ρ.PosSemidef) (ht : ρ.trace=1) :
    twoMarginal n (φ ρ)=Cartesian.covarianceAction f g (twoMarginal n ρ) := by
  rw [twoMarginal_eq_spinOne,twoMarginal_eq_spinOne,
    spinOneMarginal_action n φ hTP hF f g hlow]
  exact Spin.spinOneAction_cartesian f g (spinOneMarginal n ρ)
    (spinOneMarginal_posSemidef n ρ hρ).isHermitian ((spinOneMarginal_trace n ρ).trans ht)

end
end SU2T2.Physical
