import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Finite-matrix Choi foundations

Complete positivity below has its usual literal meaning: every finite ancillary
amplification preserves positive semidefinite matrices. Choi positivity is proved
from that definition, rather than assumed. No SU(2) decomposition is assumed here.
-/

namespace SU2T2
namespace Choi

open Matrix
open scoped ComplexOrder
noncomputable section

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def amplification {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n) (k : ℕ)
    (X : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ) :
    Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ :=
  fun a b => φ (fun i j => X (i,a.2) (j,b.2)) a.1 b.1

/-- The ordinary definition of complete positivity in finite matrix coordinates. -/
def CompletelyPositive {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n) : Prop :=
  ∀ (k : ℕ) (X : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ),
    X.PosSemidef → (amplification φ k X).PosSemidef

/-- Unnormalized Choi matrix, with output factor first. -/
def matrix {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun a b => φ (Matrix.single a.2 b.2 1) a.1 b.1

def omega (n : ℕ) : Matrix (Fin n × Fin n) Unit ℂ :=
  fun a _ => if a.1 = a.2 then 1 else 0

lemma omega_block (n : ℕ) (i j : Fin n) :
    (fun a b => (omega n * (omega n)ᴴ) (a,i) (b,j)) =
      Matrix.single i j (1 : ℂ) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, omega, Matrix.single,
    Matrix.of_apply]
  by_cases ha : a = i <;> by_cases hb : b = j <;>
    simp [ha, hb] <;> aesop

lemma amplification_omega {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n) :
    amplification φ n (omega n * (omega n)ᴴ) = matrix φ := by
  ext a b
  simp only [amplification, matrix, omega_block]

/-- Complete positivity implies positivity of the unnormalized Choi matrix. -/
theorem matrix_posSemidef {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (hφ : CompletelyPositive φ) : (matrix φ).PosSemidef := by
  rw [← amplification_omega]
  exact hφ n _ (Matrix.posSemidef_self_mul_conjTranspose (omega n))

/-- A completely positive map preserves positivity on the original matrix space. -/
theorem positive {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (hφ : CompletelyPositive φ) {X : Mat n} (hX : X.PosSemidef) :
    (φ X).PosSemidef := by
  have h := hφ 1 (X.submatrix Prod.fst Prod.fst) (hX.submatrix Prod.fst)
  have h' := h.submatrix (fun a : Fin n => (a, (0 : Fin 1)))
  simpa [amplification, Matrix.submatrix] using h'

lemma map_single_conjTranspose {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (hφ : CompletelyPositive φ) (i j : Fin n) :
    φ (Matrix.single j i 1) = (φ (Matrix.single i j 1))ᴴ := by
  ext a b
  have h := congrArg
    (fun C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => C (a,j) (b,i))
    (matrix_posSemidef φ hφ).isHermitian.eq
  simpa only [matrix, Matrix.conjTranspose_apply] using h.symm

/-- Every linear map is reconstructed from its matrix-unit images. -/
theorem apply_eq_sum {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n) (X : Mat n) :
    φ X = ∑ i, ∑ j, X i j • φ (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  congr 1
  funext i
  congr 1
  funext j
  rw [← map_smul, Matrix.smul_single]
  simp

/-- Complete positivity entails preservation of the conjugate transpose. -/
theorem map_conjTranspose {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (hφ : CompletelyPositive φ) (X : Mat n) :
    φ Xᴴ = (φ X)ᴴ := by
  rw [apply_eq_sum φ Xᴴ, apply_eq_sum φ X]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    ← map_single_conjTranspose φ hφ]
  rw [Finset.sum_comm]
  simp only [Matrix.conjTranspose_apply]

/-- Complete positivity entails preservation of Hermitian matrices. -/
theorem map_isHermitian {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (hφ : CompletelyPositive φ) {X : Mat n} (hX : X.IsHermitian) :
    (φ X).IsHermitian := by
  rw [Matrix.IsHermitian, ← map_conjTranspose φ hφ, hX.eq]

/-- The partial trace over the output factor of a trace-preserving map's Choi
matrix is exactly the identity. -/
theorem partial_trace_output {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (hφ : ∀ X, (φ X).trace = X.trace) (i j : Fin n) :
    ∑ a, matrix φ (a,i) (a,j) = if i = j then 1 else 0 := by
  change (φ (Matrix.single i j 1)).trace = _
  rw [hφ]
  by_cases hij : i = j
  · subst j
    simp [Matrix.trace, Matrix.single]
  · have hh : ∀ a, ¬(i = a ∧ j = a) := by
      intro a ⟨hi,hj⟩
      exact hij (hi.trans hj.symm)
    simp [Matrix.trace, Matrix.single, hh, hij]

theorem trace_matrix {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (hφ : ∀ X, (φ X).trace = X.trace) :
    (matrix φ).trace = n := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [partial_trace_output φ hφ]
  simp


/-- Expansion of the Choi matrix in matrix units. -/
theorem matrix_eq_sum_kronecker {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n) :
    matrix φ = ∑ i, ∑ j,
      Matrix.kronecker (φ (Matrix.single i j 1)) (Matrix.single i j 1) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp [matrix, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.single, mul_ite, ite_and]

lemma trace_single_mul_transpose {n : ℕ} (B : Mat n) (i j : Fin n) :
    (Matrix.single i j 1 * Bᵀ).trace = B i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single, Matrix.transpose_apply,
    Matrix.diag_apply, ite_and]

/-- Choi trace pairing with a tensor product of observables. -/
theorem trace_pairing {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n) (A B : Mat n) :
    (matrix φ * Matrix.kronecker A Bᵀ).trace = (A * φ B).trace := by
  rw [matrix_eq_sum_kronecker, apply_eq_sum φ B]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    trace_single_mul_transpose, Matrix.trace_mul_comm]
  ring

/-- Choi pairing for a family on which the map acts by one multiplier. -/
theorem eigenfamily_pairing {n : ℕ} {ι : Type*} [Fintype ι]
    (φ : Mat n →ₗ[ℂ] Mat n) (J : ι → Mat n) (f c : ℝ)
    (heig : ∀ a, φ (J a) = (f : ℂ) • J a)
    (hcas : ∑ a, J a * J a = (c : ℂ) • (1 : Mat n)) :
    (matrix φ * ∑ a, Matrix.kronecker (J a) (J a)ᵀ).trace =
      (f*c*n : ℂ) := by
  simp only [Matrix.mul_sum, Matrix.trace_sum, trace_pairing, heig,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [← Finset.mul_sum]
  have htr := congrArg Matrix.trace hcas
  simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul] at htr
  rw [htr]
  ring

/-- Normalized Choi state of a channel on a positive-dimensional matrix algebra. -/
def normalizedMatrix {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  (1 / (n : ℝ)) • matrix φ

theorem normalizedMatrix_posSemidef {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (hφ : CompletelyPositive φ) : (normalizedMatrix φ).PosSemidef := by
  exact (matrix_posSemidef φ hφ).smul (by positivity : (0 : ℝ) ≤ 1/(n : ℝ))

theorem normalizedMatrix_trace {n : ℕ} (hn : 0 < n)
    (φ : Mat n →ₗ[ℂ] Mat n) (hφ : ∀ X, (φ X).trace = X.trace) :
    (normalizedMatrix φ).trace.re = 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [normalizedMatrix, Matrix.trace_smul, trace_matrix φ hφ, hnR]

/-- Bilinear tensor pairing with a transpose on its second factor. -/
def tensorTranspose {n : ℕ} (A B : Mat n) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  Matrix.kroneckerMap (· * ·) A Bᵀ

lemma tensorTranspose_mul {n : ℕ} (A B D E : Mat n) :
    tensorTranspose A B * tensorTranspose D E = tensorTranspose (A*D) (E*B) := by
  simp only [tensorTranspose, Matrix.transpose_mul, Matrix.mul_kronecker_mul]

/-- Coupled-spin Casimir observable in the original Choi convention.
No time-reversal basis change is needed. -/
def casimirTensor {n : ℕ} (Jx Jy Jz : Mat n) :=
  -(tensorTranspose Jx Jx + tensorTranspose Jy Jy + tensorTranspose Jz Jz)

def rawQuadrupoleTensor {n : ℕ} (Jx Jy Jz : Mat n) :=
  tensorTranspose (Jx*Jx) (Jx*Jx) + tensorTranspose (Jy*Jy) (Jy*Jy) +
  tensorTranspose (Jz*Jz) (Jz*Jz) + (1/2 : ℂ) •
    (tensorTranspose (Jx*Jy+Jy*Jx) (Jx*Jy+Jy*Jx) +
     tensorTranspose (Jy*Jz+Jz*Jy) (Jy*Jz+Jz*Jy) +
     tensorTranspose (Jz*Jx+Jx*Jz) (Jz*Jx+Jx*Jz))

/-- The quadratic tensor identity before substituting commutation relations. -/
lemma rawQuadrupoleTensor_identity {n : ℕ} (Jx Jy Jz : Mat n) :
    rawQuadrupoleTensor Jx Jy Jz - casimirTensor Jx Jy Jz * casimirTensor Jx Jy Jz =
      (1/2 : ℂ) •
       (tensorTranspose (Jx*Jy-Jy*Jx) (Jx*Jy-Jy*Jx) +
        tensorTranspose (Jy*Jz-Jz*Jy) (Jy*Jz-Jz*Jy) +
        tensorTranspose (Jz*Jx-Jx*Jz) (Jz*Jx-Jx*Jz)) := by
  dsimp [rawQuadrupoleTensor, casimirTensor]
  simp only [neg_mul, mul_neg, add_mul, mul_add, tensorTranspose_mul]
  ext ⟨a,i⟩ ⟨b,j⟩
  simp [tensorTranspose, Matrix.kroneckerMap, Matrix.transpose_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The raw quadrupole pairing is a quadratic polynomial in the coupled Casimir. -/
theorem rawQuadrupoleTensor_casimir {n : ℕ} (Jx Jy Jz : Mat n)
    (hxy : Jx*Jy-Jy*Jx = Complex.I • Jz)
    (hyz : Jy*Jz-Jz*Jy = Complex.I • Jx)
    (hzx : Jz*Jx-Jx*Jz = Complex.I • Jy) :
    rawQuadrupoleTensor Jx Jy Jz =
      casimirTensor Jx Jy Jz * casimirTensor Jx Jy Jz +
        (1/2 : ℂ) • casimirTensor Jx Jy Jz := by
  have h := rawQuadrupoleTensor_identity Jx Jy Jz
  rw [hxy, hyz, hzx] at h
  have hcomm : (1/2 : ℂ) •
       (tensorTranspose (Complex.I • Jz) (Complex.I • Jz) +
        tensorTranspose (Complex.I • Jx) (Complex.I • Jx) +
        tensorTranspose (Complex.I • Jy) (Complex.I • Jy)) =
      (1/2 : ℂ) • casimirTensor Jx Jy Jz := by
    ext ⟨a,i⟩ ⟨b,j⟩
    simp [tensorTranspose, casimirTensor, Matrix.kroneckerMap, Matrix.transpose_apply,
      Matrix.smul_apply, smul_eq_mul, mul_mul_mul_comm, Complex.I_mul_I]
    ring
  rw [hcomm] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

def quadrupoleTensor {n : ℕ} (Jx Jy Jz : Mat n) (c : ℝ) :=
  tensorTranspose (Jx*Jx - (c/3 : ℂ) • 1) (Jx*Jx - (c/3 : ℂ) • 1) +
  tensorTranspose (Jy*Jy - (c/3 : ℂ) • 1) (Jy*Jy - (c/3 : ℂ) • 1) +
  tensorTranspose (Jz*Jz - (c/3 : ℂ) • 1) (Jz*Jz - (c/3 : ℂ) • 1) + (1/2 : ℂ) •
    (tensorTranspose (Jx*Jy+Jy*Jx) (Jx*Jy+Jy*Jx) +
     tensorTranspose (Jy*Jz+Jz*Jy) (Jy*Jz+Jz*Jy) +
     tensorTranspose (Jz*Jx+Jx*Jz) (Jz*Jx+Jx*Jz))

lemma tensorTranspose_one {n : ℕ} :
    tensorTranspose (1 : Mat n) 1 = 1 := by
  simp [tensorTranspose ]

lemma quadrupoleTensor_expand {n : ℕ} (Jx Jy Jz : Mat n) (c : ℝ) :
    quadrupoleTensor Jx Jy Jz c = rawQuadrupoleTensor Jx Jy Jz -
      (c/3 : ℂ) • tensorTranspose (Jx*Jx+Jy*Jy+Jz*Jz) 1 -
      (c/3 : ℂ) • tensorTranspose 1 (Jx*Jx+Jy*Jy+Jz*Jz) +
      (c^2/3 : ℂ) • tensorTranspose (1 : Mat n) 1 := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp [quadrupoleTensor, rawQuadrupoleTensor, tensorTranspose,
    Matrix.kroneckerMap, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The full quadrupole Choi observable equals the Casimir polynomial. -/
theorem quadrupoleTensor_casimir {n : ℕ} (Jx Jy Jz : Mat n) (c : ℝ)
    (hxy : Jx*Jy-Jy*Jx = Complex.I • Jz)
    (hyz : Jy*Jz-Jz*Jy = Complex.I • Jx)
    (hzx : Jz*Jx-Jx*Jz = Complex.I • Jy)
    (hcas : Jx*Jx+Jy*Jy+Jz*Jz = (c : ℂ) • (1 : Mat n)) :
    quadrupoleTensor Jx Jy Jz c =
      casimirTensor Jx Jy Jz * casimirTensor Jx Jy Jz +
        (1/2 : ℂ) • casimirTensor Jx Jy Jz - (c^2/3 : ℂ) • 1 := by
  rw [quadrupoleTensor_expand, rawQuadrupoleTensor_casimir Jx Jy Jz hxy hyz hzx, hcas]
  have hleft : tensorTranspose ((c : ℂ) • (1 : Mat n)) 1 =
      (c : ℂ) • (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) := by
    simp [tensorTranspose, Matrix.smul_kronecker ]
  have hright : tensorTranspose (1 : Mat n) ((c : ℂ) • 1) =
      (c : ℂ) • (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) := by
    simp [tensorTranspose, Matrix.kronecker_smul ]
  rw [hleft, hright, tensorTranspose_one]
  ext a b
  simp [Matrix.smul_apply, smul_eq_mul]
  ring

def rawQuadrupoleNormDouble {n : ℕ} (Jx Jy Jz : Mat n) :=
  2 * (Jx*Jx*Jx*Jx + Jy*Jy*Jy*Jy + Jz*Jz*Jz*Jz) +
    (Jx*Jy+Jy*Jx)*(Jx*Jy+Jy*Jx) +
    (Jy*Jz+Jz*Jy)*(Jy*Jz+Jz*Jy) +
    (Jz*Jx+Jx*Jz)*(Jz*Jx+Jx*Jz)

lemma rawQuadrupoleNormDouble_identity {n : ℕ} (Jx Jy Jz : Mat n) :
    rawQuadrupoleNormDouble Jx Jy Jz =
      2 * (Jx*(Jx*Jx+Jy*Jy+Jz*Jz)*Jx +
           Jy*(Jx*Jx+Jy*Jy+Jz*Jz)*Jy +
           Jz*(Jx*Jx+Jy*Jy+Jz*Jz)*Jz) +
       (Jx*Jy-Jy*Jx)*(Jx*Jy-Jy*Jx) +
       (Jy*Jz-Jz*Jy)*(Jy*Jz-Jz*Jy) +
       (Jz*Jx-Jx*Jz)*(Jz*Jx-Jx*Jz) := by
  dsimp [rawQuadrupoleNormDouble]
  noncomm_ring

lemma rawQuadrupoleNormDouble_casimir {n : ℕ} (Jx Jy Jz : Mat n) (c : ℝ)
    (hxy : Jx*Jy-Jy*Jx = Complex.I • Jz)
    (hyz : Jy*Jz-Jz*Jy = Complex.I • Jx)
    (hzx : Jz*Jx-Jx*Jz = Complex.I • Jy)
    (hcas : Jx*Jx+Jy*Jy+Jz*Jz = (c : ℂ) • (1 : Mat n)) :
    rawQuadrupoleNormDouble Jx Jy Jz = (2*c^2-c : ℂ) • (1 : Mat n) := by
  rw [rawQuadrupoleNormDouble_identity, hxy, hyz, hzx, hcas]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    smul_smul, Complex.I_mul_I, neg_one_smul]
  have he : (c : ℂ) • (Jx*Jx) + (c : ℂ) • (Jy*Jy) + (c : ℂ) • (Jz*Jz) =
      (c^2 : ℂ) • (1 : Mat n) := by
    rw [← smul_add, ← smul_add, hcas, smul_smul]
    congr 1
    ring
  rw [he]
  have hh : - (Jz*Jz) + - (Jx*Jx) + - (Jy*Jy) = -(c : ℂ) • (1 : Mat n) := by
    rw [neg_smul]
    rw [← hcas]
    abel
  calc
    2 * ((c^2 : ℂ) • (1 : Mat n)) - Jz*Jz - Jx*Jx - Jy*Jy =
      2 * ((c^2 : ℂ) • (1 : Mat n)) + (-(Jz*Jz) + -(Jx*Jx) + -(Jy*Jy)) := by abel
    _ = (2*c^2-c : ℂ) • (1 : Mat n) := by
      rw [hh, two_mul]
      ext a b
      simp [Matrix.smul_apply, smul_eq_mul]
      ring

def quadrupoleNorm {n : ℕ} (Jx Jy Jz : Mat n) (c : ℝ) :=
  (Jx*Jx - (c/3 : ℂ) • 1)*(Jx*Jx - (c/3 : ℂ) • 1) +
  (Jy*Jy - (c/3 : ℂ) • 1)*(Jy*Jy - (c/3 : ℂ) • 1) +
  (Jz*Jz - (c/3 : ℂ) • 1)*(Jz*Jz - (c/3 : ℂ) • 1) + (1/2 : ℂ) •
    ((Jx*Jy+Jy*Jx)*(Jx*Jy+Jy*Jx) +
     (Jy*Jz+Jz*Jy)*(Jy*Jz+Jz*Jy) +
     (Jz*Jx+Jx*Jz)*(Jz*Jx+Jx*Jz))

lemma quadrupoleNorm_expand {n : ℕ} (Jx Jy Jz : Mat n) (c : ℝ) :
    (2 : ℂ) • quadrupoleNorm Jx Jy Jz c = rawQuadrupoleNormDouble Jx Jy Jz -
      (4*c/3 : ℂ) • (Jx*Jx+Jy*Jy+Jz*Jz) + (2*c^2/3 : ℂ) • (1 : Mat n) := by
  dsimp [quadrupoleNorm, rawQuadrupoleNormDouble]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_smul, smul_add, two_mul,
    ← Matrix.mul_assoc]
  ext a b
  simp [Matrix.smul_apply, smul_eq_mul]
  ring

/-- Sum of squared quadrupole observables in a spin representation. -/
theorem quadrupoleNorm_casimir {n : ℕ} (Jx Jy Jz : Mat n) (c : ℝ)
    (hxy : Jx*Jy-Jy*Jx = Complex.I • Jz)
    (hyz : Jy*Jz-Jz*Jy = Complex.I • Jx)
    (hzx : Jz*Jx-Jx*Jz = Complex.I • Jy)
    (hcas : Jx*Jx+Jy*Jy+Jz*Jz = (c : ℂ) • (1 : Mat n)) :
    quadrupoleNorm Jx Jy Jz c = (c*(4*c-3)/6 : ℂ) • (1 : Mat n) := by
  have h := quadrupoleNorm_expand Jx Jy Jz c
  rw [rawQuadrupoleNormDouble_casimir Jx Jy Jz c hxy hyz hzx hcas, hcas] at h
  ext a b
  have hh := congrArg (fun M : Mat n => M a b) h
  simp [Matrix.smul_apply, smul_eq_mul] at hh ⊢
  linear_combination hh / 2

lemma trace_tensorTranspose {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n) (A B : Mat n) :
    (matrix φ * tensorTranspose A B).trace = (A * φ B).trace := by
  simpa only [tensorTranspose, Matrix.kronecker] using trace_pairing φ A B

lemma tensorTranspose_isHermitian {n : ℕ} (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (tensorTranspose A B).IsHermitian := by
  simp [Matrix.IsHermitian, tensorTranspose, Matrix.conjTranspose_kronecker,
    hA.eq, hB.transpose.eq]

lemma casimirTensor_isHermitian {n : ℕ} (Jx Jy Jz : Mat n)
    (hx : Jx.IsHermitian) (hy : Jy.IsHermitian) (hz : Jz.IsHermitian) :
    (casimirTensor Jx Jy Jz).IsHermitian :=
  ((tensorTranspose_isHermitian Jx Jx hx hx).add
    (tensorTranspose_isHermitian Jy Jy hy hy) |>.add
    (tensorTranspose_isHermitian Jz Jz hz hz)).neg

lemma casimir_trace_pairing {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (Jx Jy Jz : Mat n) (c f : ℝ)
    (hJx : φ Jx = (f : ℂ) • Jx) (hJy : φ Jy = (f : ℂ) • Jy)
    (hJz : φ Jz = (f : ℂ) • Jz)
    (hcas : Jx*Jx+Jy*Jy+Jz*Jz = (c : ℂ) • (1 : Mat n)) :
    (matrix φ * casimirTensor Jx Jy Jz).trace = -(f*c*n : ℂ) := by
  simp only [casimirTensor, Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_add,
    Matrix.trace_add, trace_tensorTranspose, hJx, hJy, hJz,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have htr := congrArg Matrix.trace hcas
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul] at htr
  linear_combination -(f : ℂ) * htr

lemma quadrupole_trace_pairing {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (Jx Jy Jz : Mat n) (c g : ℝ)
    (hxx : φ (Jx*Jx-(c/3 : ℂ) • 1) = (g : ℂ) • (Jx*Jx-(c/3 : ℂ) • 1))
    (hyy : φ (Jy*Jy-(c/3 : ℂ) • 1) = (g : ℂ) • (Jy*Jy-(c/3 : ℂ) • 1))
    (hzz : φ (Jz*Jz-(c/3 : ℂ) • 1) = (g : ℂ) • (Jz*Jz-(c/3 : ℂ) • 1))
    (hxy : φ (Jx*Jy+Jy*Jx) = (g : ℂ) • (Jx*Jy+Jy*Jx))
    (hyz : φ (Jy*Jz+Jz*Jy) = (g : ℂ) • (Jy*Jz+Jz*Jy))
    (hzx : φ (Jz*Jx+Jx*Jz) = (g : ℂ) • (Jz*Jx+Jx*Jz)) :
    (matrix φ * quadrupoleTensor Jx Jy Jz c).trace =
      (g : ℂ) * (quadrupoleNorm Jx Jy Jz c).trace := by
  simp only [quadrupoleTensor, quadrupoleNorm, Matrix.mul_add, Matrix.trace_add,
    Matrix.mul_smul, Matrix.trace_smul, trace_tensorTranspose,
    hxx, hyy, hzz, hxy, hyz, hzx, smul_eq_mul]
  ring

/-- Real expectation of an observable against a finite positive matrix. -/
def expectation {ι : Type*} [Fintype ι] (C X : Matrix ι ι ℂ) : ℝ :=
  (C * X).trace.re

lemma expectation_normalized {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (X : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    expectation (normalizedMatrix φ) X = (matrix φ * X).trace.re / n := by
  rw [expectation, normalizedMatrix, Matrix.smul_mul, Matrix.trace_smul]
  rw [Complex.smul_re]
  simp only [smul_eq_mul]
  ring

lemma expectation_add {ι : Type*} [Fintype ι] (C X Y : Matrix ι ι ℂ) :
    expectation C (X+Y) = expectation C X + expectation C Y := by
  simp [expectation, Matrix.mul_add, Matrix.trace_add]

lemma expectation_sub {ι : Type*} [Fintype ι] (C X Y : Matrix ι ι ℂ) :
    expectation C (X-Y) = expectation C X - expectation C Y := by
  simp [expectation, Matrix.mul_sub, Matrix.trace_sub]

lemma expectation_real_smul {ι : Type*} [Fintype ι] (C X : Matrix ι ι ℂ) (r : ℝ) :
    expectation C ((r : ℂ) • X) = r * expectation C X := by
  simp [expectation, Matrix.mul_smul, Matrix.trace_smul, Complex.mul_re]

lemma expectation_one {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℂ) :
    expectation C 1 = C.trace.re := by
  simp [expectation]

/-- A square has nonnegative expectation in every positive matrix state. -/
theorem expectation_square_nonneg {ι : Type*} [Fintype ι]
    (C X : Matrix ι ι ℂ) (hC : C.PosSemidef) (hX : X.IsHermitian) :
    0 ≤ expectation C (X * X) := by
  have h := (hC.conjTranspose_mul_mul_same X).trace_nonneg
  rw [hX.eq, Matrix.trace_mul_cycle, Matrix.trace_mul_comm (X*X) C] at h
  exact (Complex.nonneg_iff.mp h).1

/-- Expanding the expectation of the centered observable. -/
theorem expectation_centered_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C X : Matrix ι ι ℂ) (m : ℝ) :
    expectation C ((X - (m : ℂ) • 1) * (X - (m : ℂ) • 1)) =
      expectation C (X * X) - 2*m*expectation C X + m^2*C.trace.re := by
  simp [expectation, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.mul_re, Complex.mul_im]
  ring

/-- Nonnegative variance, proved from positivity rather than assumed spectral data. -/
theorem variance_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C X : Matrix ι ι ℂ) (hC : C.PosSemidef) (hX : X.IsHermitian)
    (htr : C.trace.re = 1) :
    (expectation C X)^2 ≤ expectation C (X * X) := by
  let m := expectation C X
  have hH : (X - (m : ℂ) • 1).IsHermitian := by
    simp [Matrix.IsHermitian, hX.eq]
  have h := expectation_square_nonneg C (X - (m : ℂ) • 1) hC hH
  rw [expectation_centered_square, htr] at h
  dsimp [m] at h
  nlinarith

/-- Completing the square for the Choi Casimir polynomial. -/
theorem quadratic_moment_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C X : Matrix ι ι ℂ) (hC : C.PosSemidef) (hX : X.IsHermitian)
    (htr : C.trace.re = 1) :
    -(1/16 : ℝ) ≤ expectation C (X*X) + expectation C X / 2 := by
  have hH : (X - ((-(1/4) : ℝ) : ℂ) • 1).IsHermitian := by
    simp [Matrix.IsHermitian, hX.eq]
  have h := expectation_square_nonneg C (X - ((-(1/4) : ℝ) : ℂ) • 1) hC hH
  rw [expectation_centered_square, htr] at h
  nlinarith


/-- A scalar consequence of actual positive-matrix variance, in the spin convention
S = 4c. The two moment hypotheses are ordinary equalities to be supplied by the
Choi trace pairing and the angular-momentum identities. -/
theorem variance_implies_multiplier_curve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C X : Matrix ι ι ℂ) (hC : C.PosSemidef) (hX : X.IsHermitian)
    (htr : C.trace.re = 1) (c f g : ℝ) (hc : 0 < c)
    (hmean : expectation C X = -c*f)
    (hquad : expectation C (X*X) + expectation C X / 2 - c^2/3 =
      c*(4*c-3)/6*g) :
    3*(4*c)*f^2-6*f-4*c ≤ 2*(4*c-3)*g := by
  have h := variance_nonneg C X hC hX htr
  rw [hmean] at h hquad
  have he : c * (2*(4*c-3)*g - (3*(4*c)*f^2-6*f-4*c)) =
      12*(expectation C (X*X) - (-c*f)^2) := by
    nlinarith [hquad]
  have hh : 0 ≤ c * (2*(4*c-3)*g - (3*(4*c)*f^2-6*f-4*c)) := by
    rw [he]
    nlinarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hh)


/-- The curved rank-one/rank-two multiplier restriction follows from complete
positivity and explicit spin-observable action. No Choi block decomposition,
Clebsch–Gordan theorem, or spectral assumption appears in this theorem. -/
theorem cp_multiplier_curve {n : ℕ} (hn : 0 < n) (φ : Mat n →ₗ[ℂ] Mat n)
    (hCP : CompletelyPositive φ) (hTP : ∀ A, (φ A).trace = A.trace)
    (Jx Jy Jz : Mat n) (c f g : ℝ) (hc : 0 < c)
    (hx : Jx.IsHermitian) (hy : Jy.IsHermitian) (hz : Jz.IsHermitian)
    (hcommxy : Jx*Jy-Jy*Jx = Complex.I • Jz)
    (hcommyz : Jy*Jz-Jz*Jy = Complex.I • Jx)
    (hcommzx : Jz*Jx-Jx*Jz = Complex.I • Jy)
    (hcas : Jx*Jx+Jy*Jy+Jz*Jz = (c : ℂ) • (1 : Mat n))
    (hJx : φ Jx = (f : ℂ) • Jx) (hJy : φ Jy = (f : ℂ) • Jy)
    (hJz : φ Jz = (f : ℂ) • Jz)
    (hxx : φ (Jx*Jx-(c/3 : ℂ) • 1) = (g : ℂ) • (Jx*Jx-(c/3 : ℂ) • 1))
    (hyy : φ (Jy*Jy-(c/3 : ℂ) • 1) = (g : ℂ) • (Jy*Jy-(c/3 : ℂ) • 1))
    (hzz : φ (Jz*Jz-(c/3 : ℂ) • 1) = (g : ℂ) • (Jz*Jz-(c/3 : ℂ) • 1))
    (hxy : φ (Jx*Jy+Jy*Jx) = (g : ℂ) • (Jx*Jy+Jy*Jx))
    (hyz : φ (Jy*Jz+Jz*Jy) = (g : ℂ) • (Jy*Jz+Jz*Jy))
    (hzx : φ (Jz*Jx+Jx*Jz) = (g : ℂ) • (Jz*Jx+Jx*Jz)) :
    3*(4*c)*f^2-6*f-4*c ≤ 2*(4*c-3)*g := by
  let C := normalizedMatrix φ
  let X := casimirTensor Jx Jy Jz
  have hC : C.PosSemidef := normalizedMatrix_posSemidef φ hCP
  have hX : X.IsHermitian := casimirTensor_isHermitian Jx Jy Jz hx hy hz
  have htr : C.trace.re = 1 := normalizedMatrix_trace hn φ hTP
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmean : expectation C X = -c*f := by
    dsimp [C,X]
    rw [expectation_normalized, casimir_trace_pairing φ Jx Jy Jz c f hJx hJy hJz hcas]
    simp
    field_simp
  have hquad : expectation C (quadrupoleTensor Jx Jy Jz c) = c*(4*c-3)/6*g := by
    dsimp [C]
    rw [expectation_normalized,
      quadrupole_trace_pairing φ Jx Jy Jz c g hxx hyy hzz hxy hyz hzx,
      quadrupoleNorm_casimir Jx Jy Jz c hcommxy hcommyz hcommzx hcas]
    simp [Matrix.trace_smul, Matrix.trace_one, Complex.mul_re, Complex.mul_im]
    field_simp
  have hpoly := congrArg (expectation C)
    (quadrupoleTensor_casimir Jx Jy Jz c hcommxy hcommyz hcommzx hcas)
  change expectation C (quadrupoleTensor Jx Jy Jz c) =
    expectation C (X*X + (1/2 : ℂ) • X - (c^2/3 : ℂ) • 1) at hpoly
  have hs₁ := expectation_real_smul C X (1/2)
  norm_num at hs₁
  have hs₂ := expectation_real_smul C (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (c^2/3)
  push_cast at hs₂
  rw [expectation_sub, expectation_add, hs₁, hs₂, expectation_one, htr] at hpoly
  apply variance_implies_multiplier_curve C X hC hX htr c f g hc hmean
  rw [hquad] at hpoly
  nlinarith

end
end Choi
end SU2T2

#print axioms SU2T2.Choi.cp_multiplier_curve
