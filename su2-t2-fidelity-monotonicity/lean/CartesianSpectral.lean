import Spectral
import BroadDeterminant
import Certificate

/-!
# Cartesian-to-spectral identification for actual qutrit matrices

Real orthogonal diagonalization supplies the eigenvalue bounds and the three
skew coordinates used by the scalar certificate.  Determinant and purity formulas
are proved by matrix calculation, then the positive matrix square root is handled
by `Spectral`.  No spectral identities are hypotheses of the final theorems.
-/
namespace SU2T2.Cartesian
open Matrix
open scoped MatrixOrder ComplexOrder
noncomputable section

abbrev RealThree := Matrix (Fin 3) (Fin 3) ℝ
abbrev ComplexThree := Matrix (Fin 3) (Fin 3) ℂ

def complexify (A : RealThree) : ComplexThree := A.map Complex.ofReal

def matrix (A K : RealThree) : ComplexThree :=
  (1/2 : ℂ) • (complexify A + Complex.I • complexify K)

def affineMatrix (g : ℝ) (A : RealThree) : RealThree :=
  (2*(1-g)/3) • 1 + g • A

@[simp] lemma complexify_mul (A B : RealThree) :
    complexify (A*B)=complexify A*complexify B := by
  exact (Complex.ofRealHom.mapMatrix).map_mul A B

@[simp] lemma complexify_one : complexify (1 : RealThree)=1 := by
  exact (Complex.ofRealHom.mapMatrix).map_one

@[simp] lemma complexify_add (A B : RealThree) :
    complexify (A+B)=complexify A+complexify B := by
  exact (Complex.ofRealHom.mapMatrix).map_add A B

@[simp] lemma complexify_smul (r : ℝ) (A : RealThree) :
    complexify (r • A) = (r : ℂ) • complexify A := by
  ext i j
  simp [complexify]

@[simp] lemma complexify_transpose (A : RealThree) :
    complexify A.transpose=(complexify A).conjTranspose := by
  ext i j
  simp [complexify]

lemma matrix_conjugate (A K U : RealThree) :
    (complexify U)ᴴ * matrix A K * complexify U =
      matrix (Uᵀ*A*U) (Uᵀ*K*U) := by
  simp only [matrix, complexify_mul, complexify_transpose,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

lemma real_skew_of_hermitian {ρ : ComplexThree} (hρ : ρ.IsHermitian) :
    (fun i j => 2*(ρ i j).im : RealThree)ᵀ = -(fun i j => 2*(ρ i j).im) := by
  ext i j
  have h := congrArg Complex.im (hρ.apply i j)
  simp only [Complex.star_def, Complex.conj_im] at h
  change 2*(ρ j i).im = -(2*(ρ i j).im)
  linarith

lemma real_imag_decomposition (ρ : ComplexThree) :
    matrix (fun i j => 2*(ρ i j).re) (fun i j => 2*(ρ i j).im) = ρ := by
  ext i j
  simp [matrix, complexify, Matrix.smul_apply, Complex.ext_iff, Complex.mul_re,
    Complex.mul_im]

/-- A real orthogonal matrix, regarded as a complex unitary matrix. -/
def complexUnitary (U : Matrix.unitaryGroup (Fin 3) ℝ) : Matrix.unitaryGroup (Fin 3) ℂ :=
  ⟨complexify (U : RealThree), by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [Matrix.star_eq_conjTranspose, ← complexify_transpose, ← complexify_mul]
    have h : (U : RealThree)ᵀ * (U : RealThree) = 1 := by
      simpa only [unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using unitary.coe_star_mul_self U
    rw [h, complexify_one]⟩

lemma unitary_conjugate_trace (A : ComplexThree) (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    (star (U : ComplexThree) * A * (U : ComplexThree)).trace = A.trace := by
  rw [Matrix.trace_mul_cycle]
  simp

lemma unitary_conjugate_det (A : ComplexThree) (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    (star (U : ComplexThree) * A * (U : ComplexThree)).det = A.det := by
  calc
    _ = ((U : ComplexThree) * star (U : ComplexThree) * A).det := by
      simp only [Matrix.det_mul]
      ring
    _ = _ := by simp

lemma unitary_conjugate_purity (A : ComplexThree) (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    ((star (U : ComplexThree) * A * (U : ComplexThree))^2).trace = (A^2).trace := by
  have he : (star (U : ComplexThree) * A * (U : ComplexThree))^2 =
      star (U : ComplexThree) * A^2 * (U : ComplexThree) := by
    rw [pow_two, pow_two]
    calc
      _ = star (U : ComplexThree) * A *
          ((U : ComplexThree) * star (U : ComplexThree)) * A * (U : ComplexThree) := by
            simp only [mul_assoc]
      _ = _ := by simp [mul_assoc]
  rw [he, unitary_conjugate_trace]

lemma skew_conjugate (K U : RealThree) (hK : Kᵀ = -K) :
    (Uᵀ*K*U)ᵀ = -(Uᵀ*K*U) := by
  simp [Matrix.transpose_mul, hK, mul_assoc]

lemma affineMatrix_conjugate (A : RealThree) (g : ℝ)
    (U : Matrix.unitaryGroup (Fin 3) ℝ) :
    (U : RealThree)ᵀ * affineMatrix g A * (U : RealThree) =
      affineMatrix g ((U : RealThree)ᵀ * A * (U : RealThree)) := by
  have h : (U : RealThree)ᵀ * (U : RealThree) = 1 := by
    simpa only [unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using unitary.coe_star_mul_self U
  simp [affineMatrix, Matrix.mul_add, Matrix.add_mul, h]

lemma skew_trace_zero (K : RealThree) (hK : Kᵀ = -K) : K.trace=0 := by
  have h := congrArg Matrix.trace hK
  simp at h
  linarith

lemma diagonal_matrix_trace (a : Fin 3 → ℝ) (K : RealThree) (hK : Kᵀ = -K) :
    (matrix (diagonal a) K).trace = ((∑ i, a i : ℝ) : ℂ)/2 := by
  have ht := skew_trace_zero K hK
  have ht' : (complexify K).trace = 0 := by
    have hm : (complexify K).trace = (K.trace : ℂ) := by
      simp [complexify, Matrix.trace]
    rw [hm, ht, Complex.ofReal_zero]
  simp only [matrix, Matrix.trace_smul, Matrix.trace_add, ht', smul_eq_mul, mul_zero, add_zero]
  simp [complexify]
  ring

def cross (r s t : ℝ) : RealThree := !![0,-t,s; t,0,-r; -s,r,0]

lemma skew_eq_cross (K : RealThree) (hK : Kᵀ = -K) :
    K = cross (K 2 1) (K 0 2) (K 1 0) := by
  have h (i j : Fin 3) : K j i = -K i j := congrFun (congrFun hK i) j
  have h00 := h 0 0
  have h11 := h 1 1
  have h22 := h 2 2
  have h01 := h 0 1
  have h02 := h 0 2
  have h12 := h 1 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cross] <;> linarith

lemma cross_smul (f r s t : ℝ) : f • cross r s t = cross (f*r) (f*s) (f*t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cross]

lemma affineMatrix_diagonal (g : ℝ) (a : Fin 3 → ℝ) :
    affineMatrix g (diagonal a) = diagonal (fun i => Broad.affine g (a i)) := by
  ext i j
  by_cases h : i=j
  · subst j; simp [affineMatrix, Broad.affine]
  · simp [affineMatrix, Broad.affine, h]

lemma diagonal_cross_det (a : Fin 3 → ℝ) (r s t : ℝ) :
    8*(matrix (diagonal a) (cross r s t)).det.re = Broad.det8 (a 0) (a 1) (a 2) r s t := by
  simp [matrix, complexify, cross, Matrix.det_fin_three,
    Matrix.smul_apply, Complex.mul_re, Complex.mul_im, Broad.det8]
  ring

lemma diagonal_cross_purity (a : Fin 3 → ℝ) (r s t : ℝ) :
    4*((matrix (diagonal a) (cross r s t))^2).trace.re = purity4 (a 0) (a 1) (a 2) r s t := by
  simp [matrix, complexify, cross, Matrix.trace, pow_two, Matrix.mul_apply,
    Fin.sum_univ_succ, Matrix.diagonal_apply, Matrix.smul_apply,
    Complex.mul_re, Complex.mul_im, purity4]
  ring

lemma eigenvalues_upper {A : RealThree} (hA : A.PosSemidef)
    (hupper : ((3/2 : ℝ) • (1 : RealThree)-A).PosSemidef) (i : Fin 3) :
    hA.isHermitian.eigenvalues i ≤ 3/2 := by
  let U := hA.isHermitian.eigenvectorUnitary
  have hUU : (U : RealThree)ᵀ * (U : RealThree) = 1 := by
    simpa only [unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using unitary.coe_star_mul_self U
  have he : (U : RealThree)ᵀ*A*(U : RealThree) = diagonal hA.isHermitian.eigenvalues := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Function.comp_def, RCLike.ofReal_real_eq_id] using hA.isHermitian.star_mul_self_mul_eq_diagonal
  have hp := hupper.conjTranspose_mul_mul_same (U : RealThree)
  have ht : (U : RealThree)ᵀ*((3/2 : ℝ) • (1 : RealThree)-A)*(U : RealThree) =
      diagonal (fun i => 3/2-hA.isHermitian.eigenvalues i) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU, he]
    ext i j
    by_cases hij : i=j
    · subst j; simp
    · simp [hij]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, ht] at hp
  have h := Matrix.posSemidef_diagonal_iff.mp hp i
  linarith

lemma matrix_trace (A K : RealThree) (hK : Kᵀ = -K) :
    (matrix A K).trace = (A.trace : ℂ)/2 := by
  have ht := skew_trace_zero K hK
  have hm (B : RealThree) : (complexify B).trace = (B.trace : ℂ) := by
    simp [complexify, Matrix.trace]
  simp only [matrix, Matrix.trace_smul, Matrix.trace_add, hm, ht,
    Complex.ofReal_zero, smul_eq_mul, mul_zero, add_zero]
  ring

lemma affineMatrix_trace (A : RealThree) (g : ℝ) (ht : A.trace=2) :
    (affineMatrix g A).trace=2 := by
  simp [affineMatrix, Matrix.trace_smul, ht]
  ring

/-- Matrix-level monotonicity, with the scalar reduction proved by real
orthogonal diagonalization.  No eigenvalues or spectral equalities are hypotheses. -/
theorem fidelity_mono (A K : RealThree) (M f g : ℝ)
    (hA : A.PosSemidef) (ht : A.trace=2)
    (hupper : ((3/2 : ℝ) • (1 : RealThree)-A).PosSemidef)
    (hK : Kᵀ = -K)
    (hρ : (matrix A K).PosSemidef)
    (hρ' : (matrix (affineMatrix g A) (f • K)).PosSemidef)
    (hM : 15 ≤ M) (hg₀ : -(2/3) ≤ g) (hg₁ : g ≤ 1)
    (hflo : -(2+g) ≤ 3*f) (hfhi : 3*f ≤ 2+g)
    (hcurve : 3*M*f^2-6*f-M ≤ 2*(M-3)*g) :
    matrixFidelity2 (matrix A K) ≤ matrixFidelity2 (matrix (affineMatrix g A) (f • K)) := by
  let U := hA.isHermitian.eigenvectorUnitary
  let a := hA.isHermitian.eigenvalues
  let K' := (U : RealThree)ᵀ*K*(U : RealThree)
  let r := K' 2 1
  let s := K' 0 2
  let t := K' 1 0
  have hAR : (U : RealThree)ᵀ*A*(U : RealThree) = diagonal a := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Function.comp_def, RCLike.ofReal_real_eq_id] using hA.isHermitian.star_mul_self_mul_eq_diagonal
  have hKR : K' = cross r s t := skew_eq_cross K' (skew_conjugate K (U : RealThree) hK)
  have hin : star (complexUnitary U : ComplexThree) * matrix A K * (complexUnitary U : ComplexThree) =
      matrix (diagonal a) (cross r s t) := by
    change (complexify (U : RealThree))ᴴ * matrix A K * complexify (U : RealThree) = _
    rw [matrix_conjugate, hAR]
    change matrix (diagonal a) K' = _
    rw [hKR]
  have hout : star (complexUnitary U : ComplexThree) * matrix (affineMatrix g A) (f • K) *
      (complexUnitary U : ComplexThree) =
      matrix (diagonal (fun i => Broad.affine g (a i))) (cross (f*r) (f*s) (f*t)) := by
    change (complexify (U : RealThree))ᴴ * matrix (affineMatrix g A) (f • K) *
      complexify (U : RealThree) = _
    rw [matrix_conjugate, affineMatrix_conjugate, hAR, affineMatrix_diagonal]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [show (U : RealThree)ᵀ*K*(U : RealThree)=K' from rfl, hKR, cross_smul]
  have hdi := diagonal_cross_det a r s t
  rw [←hin, unitary_conjugate_det] at hdi
  have hdo := diagonal_cross_det (fun i => Broad.affine g (a i)) (f*r) (f*s) (f*t)
  rw [←hout, unitary_conjugate_det] at hdo
  have hpi := diagonal_cross_purity a r s t
  rw [←hin, unitary_conjugate_purity] at hpi
  have hpo := diagonal_cross_purity (fun i => Broad.affine g (a i)) (f*r) (f*s) (f*t)
  rw [←hout, unitary_conjugate_purity] at hpo
  have ha (i : Fin 3) : 0 ≤ a i := hA.eigenvalues_nonneg i
  have hau (i : Fin 3) : a i ≤ 3/2 := eigenvalues_upper hA hupper i
  have has : a 0+a 1+a 2=2 := by
    have he := hA.isHermitian.trace_eq_sum_eigenvalues
    simpa [a, Fin.sum_univ_succ, add_assoc] using he.symm.trans ht
  have hdin : 0 ≤ Broad.det8 (a 0) (a 1) (a 2) r s t := by
    have hr : 0 ≤ (matrix A K).det.re := (RCLike.nonneg_iff.mp hρ.det_nonneg).1
    linarith
  have hdout : 0 ≤ Broad.det8 (Broad.affine g (a 0)) (Broad.affine g (a 1))
      (Broad.affine g (a 2)) (f*r) (f*s) (f*t) := by
    have hr : 0 ≤ (matrix (affineMatrix g A) (f • K)).det.re :=
      (RCLike.nonneg_iff.mp hρ'.det_nonneg).1
    linarith
  have hdm := Broad.determinant_monotone (a 0) (a 1) (a 2) r s t M f g
    (ha 0) (ha 1) (ha 2) (hau 0) (hau 1) (hau 2) has hM hg₀ hg₁ hflo hfhi hcurve hdin hdout
  have hf : f^2 ≤ 1 := by
    have hp := mul_nonneg (show 0 ≤ 1-f by linarith) (show 0 ≤ 1+f by linarith)
    nlinarith
  have hg : g^2 ≤ 1 := by
    have hp := mul_nonneg (show 0 ≤ 1-g by linarith) (show 0 ≤ 1+g by linarith)
    nlinarith
  have hpm := purity_monotone (a 0) (a 1) (a 2) r s t f g has hf hg
  change purity4 (Broad.affine g (a 0)) (Broad.affine g (a 1)) (Broad.affine g (a 2))
    (f*r) (f*s) (f*t) ≤ purity4 (a 0) (a 1) (a 2) r s t at hpm
  apply matrix_fidelity2_mono_of_purity_det hρ hρ'
  · rw [matrix_trace A K hK, ht]; norm_num
  · have hK' : (f • K)ᵀ = -(f • K) := by simp [Matrix.transpose_smul, hK]
    rw [matrix_trace _ _ hK', affineMatrix_trace A g ht]; norm_num
  · linarith
  · linarith

def realPart2 (ρ : ComplexThree) : RealThree := fun i j => 2*(ρ i j).re

def imagPart2 (ρ : ComplexThree) : RealThree := fun i j => 2*(ρ i j).im

/-- Rank-one/rank-two attenuation in Cartesian spin-one coordinates. -/
def covarianceAction (f g : ℝ) (ρ : ComplexThree) : ComplexThree :=
  matrix (affineMatrix g (realPart2 ρ)) (f • imagPart2 ρ)

lemma covarianceAction_apply (f g : ℝ) (ρ : ComplexThree) (i j : Fin 3) :
    covarianceAction f g ρ i j =
      (if i=j then ((1-g)/3 : ℂ) else 0) +
      (g : ℂ)*(ρ i j).re + Complex.I*(f : ℂ)*(ρ i j).im := by
  by_cases hij : i=j
  · subst j
    simp [covarianceAction, realPart2, imagPart2, matrix, affineMatrix, complexify, Matrix.smul_apply]
    ring
  · simp [covarianceAction, realPart2, imagPart2, matrix, affineMatrix, complexify, Matrix.smul_apply,
      hij]
    ring

/-- The matrix-level theorem directly on density matrices.  The only remaining
channel input is the Cartesian attenuation law, and the only extension input
is the upper bound on twice the real part. -/
theorem fidelity_mono_of_action (ρ ρ' : ComplexThree) (M f g : ℝ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (hρ' : ρ'.PosSemidef)
    (hupper : ((3/2 : ℝ) • (1 : RealThree) - realPart2 ρ).PosSemidef)
    (haction : ρ' = covarianceAction f g ρ)
    (hM : 15 ≤ M) (hg₀ : -(2/3) ≤ g) (hg₁ : g ≤ 1)
    (hflo : -(2+g) ≤ 3*f) (hfhi : 3*f ≤ 2+g)
    (hcurve : 3*M*f^2-6*f-M ≤ 2*(M-3)*g) :
    matrixFidelity2 ρ ≤ matrixFidelity2 ρ' := by
  let A : RealThree := fun i j => 2*(ρ i j).re
  let K : RealThree := fun i j => 2*(ρ i j).im
  have hRe : Matrix.PosSemidef (fun i j => (ρ i j).re : RealThree) := by
    constructor
    · ext i j
      have h := congrArg Complex.re (hρ.isHermitian.apply i j)
      simpa [Matrix.conjTranspose_apply] using h
    · intro x
      have h := hρ.re_dotProduct_nonneg (fun i => (x i : ℂ))
      simpa [dotProduct, Matrix.mulVec, map_sum, Complex.mul_re] using h
  have hA : A.PosSemidef := by
    simpa [A] using hRe.smul (show (0:ℝ)≤2 by norm_num)
  have ht : A.trace=2 := by
    have h := congrArg Complex.re htr
    simpa [A, Matrix.trace, Finset.mul_sum, map_sum] using congrArg (fun x : ℝ => 2*x) h
  have hK : Kᵀ = -K := real_skew_of_hermitian hρ.isHermitian
  have hd : matrix A K = ρ := real_imag_decomposition ρ
  have hd' : matrix (affineMatrix g A) (f • K) = ρ' := haction.symm
  have hm := fidelity_mono A K M f g hA ht hupper hK
    (hd.symm ▸ hρ) (hd'.symm ▸ hρ') hM hg₀ hg₁ hflo hfhi hcurve
  simpa only [hd, hd'] using hm

end
end SU2T2.Cartesian

#print axioms SU2T2.Cartesian.fidelity_mono
#print axioms SU2T2.Cartesian.fidelity_mono_of_action
