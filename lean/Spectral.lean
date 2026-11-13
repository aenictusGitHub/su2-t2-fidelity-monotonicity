import Qutrit
import Mathlib.Analysis.Matrix.Order

namespace SU2T2
open Matrix
open scoped MatrixOrder ComplexOrder
noncomputable section

abbrev QutritMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-- The manuscript's normalized fidelity against the maximally mixed qutrit,
using the actual positive matrix square root. -/
def matrixFidelity2 (A : QutritMatrix) : ℝ :=
  (((CFC.sqrt A).trace.re)^2-1)/2

lemma hermitian_trace_pow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (A^k).trace = ∑ i, ((hA.eigenvalues i : ℂ)^k) := by
  let U := hA.eigenvectorUnitary
  let D := diagonal (Complex.ofReal ∘ hA.eigenvalues)
  have hs : A = (U : Matrix n n ℂ) * D * star (U : Matrix n n ℂ) := hA.spectral_theorem
  have hp : ∀ m : ℕ, A^m = (U : Matrix n n ℂ) * D^m * star (U : Matrix n n ℂ) := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
      rw [pow_succ, hm, hs]
      calc
        _ = (U : Matrix n n ℂ) * D^m *
            (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) * D * star (U : Matrix n n ℂ) := by
              simp only [mul_assoc]
        _ = _ := by simp [pow_succ, mul_assoc]
  rw [hp, Matrix.trace_mul_cycle]
  simp [D, Function.comp_def, Matrix.diagonal_pow]

/-- Eigenvalues of the actual positive matrix square root. -/
def rootEigenvalues (A : QutritMatrix) : Fin 3 → ℝ :=
  (CFC.sqrt_nonneg A).posSemidef.isHermitian.eigenvalues

lemma rootEigenvalues_nonneg (A : QutritMatrix) (i : Fin 3) :
    0 ≤ rootEigenvalues A i :=
  (CFC.sqrt_nonneg A).posSemidef.eigenvalues_nonneg i

lemma rootEigenvalues_trace (A : QutritMatrix) :
    (CFC.sqrt A).trace.re = ∑ i, rootEigenvalues A i := by
  have h := (CFC.sqrt_nonneg A).posSemidef.isHermitian.trace_eq_sum_eigenvalues
  have := congrArg Complex.re h
  simpa [rootEigenvalues] using this

lemma rootEigenvalues_trace_real (A : QutritMatrix) :
    (CFC.sqrt A).trace = ((∑ i, rootEigenvalues A i : ℝ) : ℂ) := by
  simpa [rootEigenvalues] using
    (CFC.sqrt_nonneg A).posSemidef.isHermitian.trace_eq_sum_eigenvalues

lemma rootEigenvalues_sq_sum {A : QutritMatrix} (hA : A.PosSemidef) :
    ∑ i, (rootEigenvalues A i)^2 = A.trace.re := by
  have h := hermitian_trace_pow (CFC.sqrt_nonneg A).posSemidef.isHermitian 2
  rw [CFC.sq_sqrt A hA.nonneg] at h
  have := congrArg Complex.re h
  simpa [rootEigenvalues, ← Complex.ofReal_pow] using this.symm

lemma rootEigenvalues_fourth_sum {A : QutritMatrix} (hA : A.PosSemidef) :
    ∑ i, (rootEigenvalues A i)^4 = (A^2).trace.re := by
  have h := hermitian_trace_pow (CFC.sqrt_nonneg A).posSemidef.isHermitian 4
  have hp : (CFC.sqrt A)^4 = A^2 := by
    rw [show 4=2*2 by norm_num, pow_mul, CFC.sq_sqrt A hA.nonneg]
  rw [hp] at h
  have := congrArg Complex.re h
  simpa [rootEigenvalues, ← Complex.ofReal_pow] using this.symm

lemma rootEigenvalues_prod_sq {A : QutritMatrix} (hA : A.PosSemidef) :
    ∏ i, (rootEigenvalues A i)^2 = A.det.re := by
  have hd := (CFC.sqrt_nonneg A).posSemidef.isHermitian.det_eq_prod_eigenvalues
  have h : A.det = ∏ i, ((rootEigenvalues A i : ℂ)^2) := by
    calc
      A.det = ((CFC.sqrt A)^2).det := congrArg Matrix.det (CFC.sq_sqrt A hA.nonneg).symm
      _ = _ := by rw [Matrix.det_pow, hd]; simp [rootEigenvalues, Finset.prod_pow]
  have := congrArg Complex.re h
  simpa only [← Complex.ofReal_pow, ← Complex.ofReal_prod, Complex.ofReal_re] using this.symm

/-- Spectral comparison for genuine positive trace-one matrices.  No eigenvalue,
trace, determinant, or square-root identification is assumed. -/
theorem matrix_fidelity2_mono_of_purity_det
    {A B : QutritMatrix} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrA : A.trace = 1) (htrB : B.trace = 1)
    (hpur : (B^2).trace.re ≤ (A^2).trace.re)
    (hdet : A.det.re ≤ B.det.re) : matrixFidelity2 A ≤ matrixFidelity2 B := by
  have hnormA := rootEigenvalues_sq_sum hA
  have hnormB := rootEigenvalues_sq_sum hB
  have hpurA := rootEigenvalues_fourth_sum hA
  have hpurB := rootEigenvalues_fourth_sum hB
  have hdetA := rootEigenvalues_prod_sq hA
  have hdetB := rootEigenvalues_prod_sq hB
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ] at hnormA hnormB hpurA hpurB hdetA hdetB
  rw [htrA] at hnormA
  rw [htrB] at hnormB
  have hnormA' : rootEigenvalues A 0 ^ 2 + rootEigenvalues A 1 ^ 2 +
      rootEigenvalues A 2 ^ 2 = 1 := by simpa [add_assoc] using hnormA
  have hnormB' : rootEigenvalues B 0 ^ 2 + rootEigenvalues B 1 ^ 2 +
      rootEigenvalues B 2 ^ 2 = 1 := by simpa [add_assoc] using hnormB
  have hp : rootEigenvalues B 0 ^ 4 + rootEigenvalues B 1 ^ 4 + rootEigenvalues B 2 ^ 4 ≤
      rootEigenvalues A 0 ^ 4 + rootEigenvalues A 1 ^ 4 + rootEigenvalues A 2 ^ 4 := by
    linarith
  have hd : rootEigenvalues A 0 ^ 2 * rootEigenvalues A 1 ^ 2 * rootEigenvalues A 2 ^ 2 ≤
      rootEigenvalues B 0 ^ 2 * rootEigenvalues B 1 ^ 2 * rootEigenvalues B 2 ^ 2 := by
    simpa [mul_assoc] using hdetA.trans_le (hdet.trans_eq hdetB.symm)
  have hc := qutrit_fidelity_mono_of_purity
    (rootEigenvalues A 0) (rootEigenvalues A 1) (rootEigenvalues A 2)
    (rootEigenvalues B 0) (rootEigenvalues B 1) (rootEigenvalues B 2)
    (rootEigenvalues_nonneg A 0) (rootEigenvalues_nonneg A 1) (rootEigenvalues_nonneg A 2)
    (rootEigenvalues_nonneg B 0) (rootEigenvalues_nonneg B 1) (rootEigenvalues_nonneg B 2)
    hnormA' hnormB' hp hd
  unfold matrixFidelity2
  rw [rootEigenvalues_trace, rootEigenvalues_trace]
  simpa [Fin.sum_univ_succ, add_assoc] using hc

end
end SU2T2

#print axioms SU2T2.hermitian_trace_pow
#print axioms SU2T2.matrix_fidelity2_mono_of_purity_det
