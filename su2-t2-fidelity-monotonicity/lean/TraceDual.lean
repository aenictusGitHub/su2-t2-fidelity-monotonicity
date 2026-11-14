import SU2Choi

/-! The trace dual is constructed from the actual linear map. -/
namespace SU2T2
namespace Choi
open Matrix
noncomputable section

def traceDual {n m : ℕ} (φ : Mat n →ₗ[ℂ] Mat m) : Mat m →ₗ[ℂ] Mat n where
  toFun B i j := (B * φ (Matrix.single j i 1)).trace
  map_add' B C := by ext i j; simp [Matrix.add_mul,Matrix.trace_add]
  map_smul' c B := by ext i j; simp [Matrix.trace_smul]

lemma traceDual_pairing {n m : ℕ} (φ : Mat n →ₗ[ℂ] Mat m) (B : Mat m) (A : Mat n) :
    (traceDual φ B * A).trace = (B * φ A).trace := by
  have hsum : φ A = ∑ i, ∑ j, A i j • φ (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp only [map_sum]
    congr 1
    funext i
    congr 1
    funext j
    rw [←map_smul,Matrix.smul_single]
    simp
  rw [hsum]
  simp only [Matrix.mul_sum,Matrix.trace_sum,Matrix.mul_smul,Matrix.trace_smul,
    smul_eq_mul]
  conv_lhs => simp only [Matrix.trace,Matrix.diag_apply]
  simp only [Matrix.mul_apply,traceDual,LinearMap.coe_mk,AddHom.coe_mk]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma trace_commutator_flip {n : ℕ} (J B A : Mat n) :
    ((J*B-B*J)*A).trace = -(B*(J*A-A*J)).trace := by
  simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.trace_sub]
  rw [Matrix.trace_mul_cycle J B A, Matrix.trace_mul_cycle A J B]
  simp only [Matrix.mul_assoc]
  ring

/-- Covariance of the original map implies covariance of its actual trace dual. -/
theorem traceDual_commutator {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n) (J : Mat n)
    (hcov : ∀ A, φ (J*A-A*J)=J*φ A-φ A*J) (B : Mat n) :
    traceDual φ (J*B-B*J)=J*traceDual φ B-traceDual φ B*J := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  rw [traceDual_pairing,trace_commutator_flip,←hcov,←traceDual_pairing,
    ←trace_commutator_flip]

lemma traceDual_trace_preserving {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (hφ : φ 1=1) (B : Mat n) : (traceDual φ B).trace=B.trace := by
  have h := traceDual_pairing φ B 1
  simpa [hφ] using h

lemma traceDual_unital {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n)
    (hφ : ∀ A, (φ A).trace=A.trace) : traceDual φ 1=1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  rw [traceDual_pairing]
  simp [hφ]

lemma traceDual_involutive {n : ℕ} (φ : Mat n →ₗ[ℂ] Mat n) :
    traceDual (traceDual φ)=φ := by
  ext B i j
  have h : traceDual (traceDual φ) B = φ B := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro A
    rw [traceDual_pairing,Matrix.trace_mul_comm,traceDual_pairing,Matrix.trace_mul_comm]
  exact congrArg (fun M => M i j) h

/-- The trace dual of an intertwiner intertwines the reversed actions. -/
theorem traceDual_intertwiner {n m : ℕ} (φ : Mat n →ₗ[ℂ] Mat m)
    (Jin : Mat n) (Jout : Mat m)
    (hcov : ∀ A, φ (Jin*A-A*Jin)=Jout*φ A-φ A*Jout) (B : Mat m) :
    traceDual φ (Jout*B-B*Jout)=Jin*traceDual φ B-traceDual φ B*Jin := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  rw [traceDual_pairing,trace_commutator_flip,←hcov,←traceDual_pairing,
    ←trace_commutator_flip]

/-- Star preservation passes to the actual rectangular trace dual. -/
theorem traceDual_conjTranspose {n m : ℕ} (φ : Mat n →ₗ[ℂ] Mat m)
    (hstar : ∀ A, φ Aᴴ=(φ A)ᴴ) (B : Mat m) :
    traceDual φ Bᴴ=(traceDual φ B)ᴴ := by
  ext i j
  change (Bᴴ*φ (Matrix.single j i 1)).trace =
    star (B*φ (Matrix.single i j 1)).trace
  rw [←Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,←hstar]
  simp only [Matrix.conjTranspose_single,star_one]
  rw [Matrix.trace_mul_comm]

/-- A Hermitian input has a Hermitian image under the trace dual. -/
theorem traceDual_isHermitian {n m : ℕ} (φ : Mat n →ₗ[ℂ] Mat m)
    (hstar : ∀ A, φ Aᴴ=(φ A)ᴴ) {B : Mat m} (hB : B.IsHermitian) :
    (traceDual φ B).IsHermitian := by
  change (traceDual φ B)ᴴ=traceDual φ B
  rw [←traceDual_conjTranspose φ hstar,hB.eq]

end
end Choi
end SU2T2
