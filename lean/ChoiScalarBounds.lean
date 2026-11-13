import BroadDeterminant

/-! The moment inequality alone supplies the relaxed g bound. -/
namespace SU2T2
noncomputable section

/-- No discrete angular-momentum spectrum is needed for this lower bound. -/
theorem lower_bound_from_choi_variance (S f g : ℝ) (hS : 15 ≤ S)
    (hvar : 3*S*f^2-6*f-S ≤ 2*(S-3)*g) : -(2/3) ≤ g := by
  by_contra hg
  have hprod := mul_neg_of_pos_of_neg (show 0 < S-3 by linarith)
    (show g+2/3 < 0 by linarith)
  have hsmall : 9*S*f^2-18*f+S-12 < 0 := by nlinarith
  have hscaled := mul_neg_of_pos_of_neg (show 0 < S by linarith) hsmall
  have hsize := mul_nonneg (show 0 ≤ S-15 by linarith) (show 0 ≤ S+3 by linarith)
  nlinarith [sq_nonneg (S*f-1)]

/-- PSD of the coherent output is sufficient for the linear multiplier region. -/
theorem region_from_coherent_and_choi (S f g : ℝ) (hS : 15 ≤ S)
    (hvar : 3*S*f^2-6*f-S ≤ 2*(S-3)*g)
    (hplus : 0 ≤ (2+g)/3+f) (hminus : 0 ≤ (2+g)/3-f)
    (hzero : 0 ≤ 1-g) :
    -(2/3) ≤ g ∧ g ≤ 1 ∧ 3*|f| ≤ 2+g := by
  refine ⟨lower_bound_from_choi_variance S f g hS hvar, by linarith, ?_⟩
  rcases le_total 0 f with hf | hf
  · rw [abs_of_nonneg hf]; linarith
  · rw [abs_of_nonpos hf]; linarith

end
end SU2T2
