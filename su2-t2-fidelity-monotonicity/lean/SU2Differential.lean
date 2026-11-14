import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic

/-!
# Covariance implies infinitesimal covariance

This file differentiates actual conjugation by matrix exponentials. The
infinitesimal intertwining relation is a conclusion, not part of a channel's
definition.
-/

namespace SU2T2
namespace Differential

open NormedSpace

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Derivative at zero of conjugation by a one-parameter exponential group. -/
theorem conjugation_hasDerivAt_zero (G X : A) :
    HasDerivAt (fun t : ℝ => exp ℝ (t • G) * X * exp ℝ (t • (-G)))
      (G*X-X*G) 0 := by
  have hp : HasDerivAt (fun t : ℝ => exp ℝ (t • G)) G 0 := by
    simpa using (hasDerivAt_exp_smul_const G (0 : ℝ))
  have hm : HasDerivAt (fun t : ℝ => exp ℝ (t • (-G))) (-G) 0 := by
    simpa using (hasDerivAt_exp_smul_const (-G) (0 : ℝ))
  simpa [sub_eq_add_neg] using (hp.mul_const X).mul hm

/-- An actual covariance identity for all real rotations implies the generator
commutator identity, by uniqueness of derivatives. -/
theorem intertwines_commutator_of_exp_covariant (φ : A →L[ℝ] A) (G : A)
    (hcov : ∀ (t : ℝ) (X : A),
      φ (exp ℝ (t • G) * X * exp ℝ (t • (-G))) =
        exp ℝ (t • G) * φ X * exp ℝ (t • (-G))) (X : A) :
    φ (G*X-X*G) = G*φ X-φ X*G := by
  have hleft := φ.hasFDerivAt.comp_hasDerivAt 0 (conjugation_hasDerivAt_zero G X)
  have heq : (fun t : ℝ => φ (exp ℝ (t • G) * X * exp ℝ (t • (-G)))) =
      (fun t : ℝ => exp ℝ (t • G) * φ X * exp ℝ (t • (-G))) := by
    funext t
    exact hcov t X
  change HasDerivAt (fun t : ℝ => φ (exp ℝ (t • G) * X * exp ℝ (t • (-G))))
    (φ (G*X-X*G)) 0 at hleft
  rw [heq] at hleft
  exact hleft.unique (conjugation_hasDerivAt_zero G (φ X))

end Differential
end SU2T2

#print axioms SU2T2.Differential.intertwines_commutator_of_exp_covariant
