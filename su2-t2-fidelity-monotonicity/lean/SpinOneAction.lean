import SpinCovariance
import CartesianSpectral

/-! Concrete spin-one coordinates and the finite-dimensional marginal transfer. -/
namespace SU2T2.Spin
open Matrix
noncomputable section

def cartesianChange : Mat 2 :=
  !![-(Real.sqrt 2 : ℂ)/2,Complex.I*(Real.sqrt 2 : ℂ)/2,0;
      0,0,1;
      (Real.sqrt 2 : ℂ)/2,Complex.I*(Real.sqrt 2 : ℂ)/2,0]

def timeReverseOne : Mat 2 := !![0,0,1;0,-1,0;1,0,0]

/-- Complex-linear extension of the Cartesian first/second-rank action. -/
def spinOneAction (f g : ℝ) : Mat 2 →ₗ[ℂ] Mat 2 where
  toFun B := (((f+g)/2 : ℝ) : ℂ) • B +
    (((g-f)/2 : ℝ) : ℂ) • (timeReverseOne*Bᵀ*timeReverseOne) +
    (((1-g)/3 : ℝ) : ℂ) • (B.trace • (1 : Mat 2))
  map_add' A B := by
    simp only [Matrix.transpose_add,Matrix.mul_add,Matrix.add_mul,Matrix.trace_add,
      add_smul,smul_add]
    abel
  map_smul' c B := by
    change _ = c • _
    simp only [Matrix.transpose_smul,Matrix.mul_smul,Matrix.smul_mul,Matrix.trace_smul,
      smul_smul,smul_add,smul_eq_mul]
    module

lemma spinOneAction_apply (f g : ℝ) (B : Mat 2) :
    spinOneAction f g B = (((f+g)/2 : ℝ) : ℂ) • B +
    (((g-f)/2 : ℝ) : ℂ) • (timeReverseOne*Bᵀ*timeReverseOne) +
    (((1-g)/3 : ℝ) : ℂ) • (B.trace • (1 : Mat 2)) := rfl

lemma sqrt_two_sq_complex : (Real.sqrt 2 : ℂ)^2 = 2 := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

lemma raising_two : raising 2 =
    !![0,0,0;(Real.sqrt 2 : ℂ),0,0;0,(Real.sqrt 2 : ℂ),0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [raising,weight]

lemma lowering_two : lowering 2 =
    !![0,(Real.sqrt 2 : ℂ),0;0,0,(Real.sqrt 2 : ℂ);0,0,0] := by
  rw [lowering,raising_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

lemma zAxis_two : zAxis 2 = !![-1,0,0;0,0,0;0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [zAxis,magnetic,Matrix.diagonal_apply]

lemma casimir_two : casimir 2 = 2 := by norm_num [casimir]

lemma quadrupoleZ_two : quadrupoleZ 2 = !![1/3,0,0;0,-2/3,0;0,0,1/3] := by
  rw [quadrupoleZ,zAxis_two,casimir_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply,Fin.sum_univ_three,Matrix.one_apply]

set_option maxHeartbeats 1000000 in
lemma spinOne_decomposition (B : Mat 2) :
    B = (B.trace/3) • (1 : Mat 2) +
      ((Real.sqrt 2 : ℂ)/4*(B 1 0+B 2 1)) • raising 2 +
      ((B 2 2-B 0 0)/2) • zAxis 2 +
      ((Real.sqrt 2 : ℂ)/4*(B 0 1+B 1 2)) • lowering 2 +
      (B 2 0/2) • (raising 2*raising 2) +
      ((Real.sqrt 2 : ℂ)/4*(B 2 1-B 1 0)) •
        (zAxis 2*raising 2+raising 2*zAxis 2) +
      ((B 0 0+B 2 2-2*B 1 1)/2) • quadrupoleZ 2 +
      ((Real.sqrt 2 : ℂ)/4*(B 1 2-B 0 1)) •
        (zAxis 2*lowering 2+lowering 2*zAxis 2) +
      (B 0 2/2) • (lowering 2*lowering 2) := by
  rw [raising_two,lowering_two,zAxis_two,quadrupoleZ_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Matrix.trace,Matrix.diag_apply,Fin.sum_univ_three,
      Matrix.one_apply, map_ofNat] <;>
    ring_nf <;> simp [sqrt_two_sq_complex] <;> ring

lemma spinOne_ext {V : Type*} [AddCommGroup V] [Module ℂ V]
    (μ ν : Mat 2 →ₗ[ℂ] V)
    (hI : μ 1 = ν 1) (hE : μ (raising 2) = ν (raising 2))
    (hH : μ (zAxis 2) = ν (zAxis 2)) (hF : μ (lowering 2) = ν (lowering 2))
    (hEE : μ (raising 2*raising 2) = ν (raising 2*raising 2))
    (hHE : μ (zAxis 2*raising 2+raising 2*zAxis 2) =
      ν (zAxis 2*raising 2+raising 2*zAxis 2))
    (hZZ : μ (quadrupoleZ 2) = ν (quadrupoleZ 2))
    (hHF : μ (zAxis 2*lowering 2+lowering 2*zAxis 2) =
      ν (zAxis 2*lowering 2+lowering 2*zAxis 2))
    (hFF : μ (lowering 2*lowering 2) = ν (lowering 2*lowering 2)) : μ=ν := by
  apply LinearMap.ext
  intro B
  conv_lhs => rw [spinOne_decomposition B]
  conv_rhs => rw [spinOne_decomposition B]
  simp only [map_add,map_smul,hI,hE,hH,hF,hEE,hHE,hZZ,hHF,hFF]

set_option maxHeartbeats 2000000 in
lemma spinOneAction_basis (f g : ℝ) :
    spinOneAction f g 1 = 1 ∧
    spinOneAction f g (raising 2) = (f : ℂ) • raising 2 ∧
    spinOneAction f g (zAxis 2) = (f : ℂ) • zAxis 2 ∧
    spinOneAction f g (lowering 2) = (f : ℂ) • lowering 2 ∧
    spinOneAction f g (raising 2*raising 2) = (g : ℂ) • (raising 2*raising 2) ∧
    spinOneAction f g (zAxis 2*raising 2+raising 2*zAxis 2) =
      (g : ℂ) • (zAxis 2*raising 2+raising 2*zAxis 2) ∧
    spinOneAction f g (quadrupoleZ 2) = (g : ℂ) • quadrupoleZ 2 ∧
    spinOneAction f g (zAxis 2*lowering 2+lowering 2*zAxis 2) =
      (g : ℂ) • (zAxis 2*lowering 2+lowering 2*zAxis 2) ∧
    spinOneAction f g (lowering 2*lowering 2) = (g : ℂ) • (lowering 2*lowering 2) := by
  simp only [raising_two,lowering_two,zAxis_two,quadrupoleZ_two]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [spinOneAction_apply, timeReverseOne,Matrix.mul_apply,Matrix.transpose,
      Matrix.trace,Matrix.diag_apply,Fin.sum_univ_three,Matrix.one_apply,
      Matrix.vecHead,Matrix.vecTail] <;>
    push_cast <;> ring

lemma lowering_quadrupoleZ_commutator (N : ℕ) :
    lowering N*quadrupoleZ N-quadrupoleZ N*lowering N =
      zAxis N*lowering N+lowering N*zAxis N := by
  calc
    _ = (lowering N*zAxis N-zAxis N*lowering N)*zAxis N+
        zAxis N*(lowering N*zAxis N-zAxis N*lowering N) := by
      simp only [quadrupoleZ,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,
        mul_one,one_mul]
      noncomm_ring
    _ = _ := by rw [lowering_zAxis_commutator]; abel

lemma lowering_zLowering_commutator (N : ℕ) :
    lowering N*(zAxis N*lowering N+lowering N*zAxis N)-
      (zAxis N*lowering N+lowering N*zAxis N)*lowering N =
      (2 : ℂ) • (lowering N*lowering N) := by
  calc
    _ = (lowering N*zAxis N-zAxis N*lowering N)*lowering N+
        lowering N*(lowering N*zAxis N-zAxis N*lowering N) := by noncomm_ring
    _ = _ := by rw [lowering_zAxis_commutator]; module

lemma transfer_commutator {N : ℕ} (ψ : Mat 2 →ₗ[ℂ] Mat N)
    (Φ : Mat N →ₗ[ℂ] Mat N)
    (hψ : ∀ B, ψ (lowering 2*B-B*lowering 2) = lowering N*ψ B-ψ B*lowering N)
    (hΦ : CommutesWithCommutator Φ (lowering N))
    (A : Mat 2) (c : ℂ) (hA : Φ (ψ A) = c • ψ A) :
    Φ (ψ (lowering 2*A-A*lowering 2)) = c • ψ (lowering 2*A-A*lowering 2) := by
  rw [hψ,hΦ,hA]
  simp only [mul_smul_comm,smul_mul_assoc,smul_sub]

lemma transfer_remove_smul {N : ℕ} (ψ : Mat 2 →ₗ[ℂ] Mat N)
    (Φ : Mat N →ₗ[ℂ] Mat N) (A : Mat 2) (c d : ℂ) (hd : d ≠ 0)
    (h : Φ (ψ (d • A)) = c • ψ (d • A)) : Φ (ψ A) = c • ψ A := by
  simp only [map_smul] at h
  rw [smul_comm c d] at h
  exact (smul_right_injective _ hd) h

/-- Agreement on the rank-zero and the two highest-weight vectors extends to
all spin-one matrices. Only actual lowering covariance is used in this step. -/
theorem spinOne_transfer {N : ℕ} (ψ : Mat 2 →ₗ[ℂ] Mat N)
    (Φ : Mat N →ₗ[ℂ] Mat N) (f g : ℝ)
    (hψ : ∀ B, ψ (lowering 2*B-B*lowering 2) = lowering N*ψ B-ψ B*lowering N)
    (hΦ : CommutesWithCommutator Φ (lowering N))
    (hI : Φ (ψ 1) = ψ 1)
    (hE : Φ (ψ (raising 2)) = (f : ℂ) • ψ (raising 2))
    (hEE : Φ (ψ (raising 2*raising 2)) = (g : ℂ) • ψ (raising 2*raising 2)) :
    ∀ B, Φ (ψ B) = ψ (spinOneAction f g B) := by
  have hH₀ := transfer_commutator ψ Φ hψ hΦ _ f hE
  rw [lowering_raising_commutator] at hH₀
  have hH := transfer_remove_smul ψ Φ _ f (-2) (by norm_num) hH₀
  have hF := transfer_commutator ψ Φ hψ hΦ _ f hH
  rw [lowering_zAxis_commutator] at hF
  have hHE₀ := transfer_commutator ψ Φ hψ hΦ _ g hEE
  rw [lowering_raising_sq_commutator] at hHE₀
  have hHE := transfer_remove_smul ψ Φ _ g (-2) (by norm_num) hHE₀
  have hZZ₀ := transfer_commutator ψ Φ hψ hΦ _ g hHE
  rw [lowering_zRaising_commutator] at hZZ₀
  have hZZ := transfer_remove_smul ψ Φ _ g (-6) (by norm_num) hZZ₀
  have hHF := transfer_commutator ψ Φ hψ hΦ _ g hZZ
  rw [lowering_quadrupoleZ_commutator] at hHF
  have hFF₀ := transfer_commutator ψ Φ hψ hΦ _ g hHF
  rw [lowering_zLowering_commutator] at hFF₀
  have hFF := transfer_remove_smul ψ Φ _ g 2 (by norm_num) hFF₀
  obtain ⟨bI,bE,bH,bF,bEE,bHE,bZZ,bHF,bFF⟩ := spinOneAction_basis f g
  have he : Φ.comp ψ = ψ.comp (spinOneAction f g) := by
    apply spinOne_ext <;> simp only [LinearMap.comp_apply]
    · rw [hI,bI]
    · rw [hE,bE,map_smul]
    · rw [hH,bH,map_smul]
    · rw [hF,bF,map_smul]
    · rw [hEE,bEE,map_smul]
    · rw [hHE,bHE,map_smul]
    · rw [hZZ,bZZ,map_smul]
    · rw [hHF,bHF,map_smul]
    · rw [hFF,bFF,map_smul]
  intro B
  exact congrArg (fun μ : Mat 2 →ₗ[ℂ] Mat N => μ B) he

lemma timeReverseOne_transpose : timeReverseOneᵀ=timeReverseOne := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [timeReverseOne,Matrix.transpose_apply]

lemma transpose_trace_pairing (A B : Mat 2) : (Aᵀ*B).trace=(A*Bᵀ).trace := by
  rw [← Matrix.trace_transpose (Aᵀ*B),Matrix.transpose_mul,Matrix.transpose_transpose,
    Matrix.trace_mul_comm]

/-- The concrete two-multiplier map is its own trace dual. -/
theorem spinOneAction_trace_pairing (f g : ℝ) (A B : Mat 2) :
    (spinOneAction f g A*B).trace = (A*spinOneAction f g B).trace := by
  have ht : (timeReverseOne*Aᵀ*timeReverseOne*B).trace =
      (A*(timeReverseOne*Bᵀ*timeReverseOne)).trace := by
    calc
      _ = (Aᵀ*(timeReverseOne*B*timeReverseOne)).trace := by
        calc
          _ = (timeReverseOne * (Aᵀ * (timeReverseOne*B))).trace := by
            simp only [Matrix.mul_assoc]
          _ = ((Aᵀ * (timeReverseOne*B)) * timeReverseOne).trace :=
            Matrix.trace_mul_comm _ _
          _ = _ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [transpose_trace_pairing]
        simp only [Matrix.transpose_mul,timeReverseOne_transpose]
        simp only [Matrix.mul_assoc]
  simp only [spinOneAction_apply,Matrix.add_mul,Matrix.mul_add,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_smul,
    Matrix.one_mul,Matrix.mul_one,smul_eq_mul,ht]
  ring

set_option maxHeartbeats 1000000 in
lemma cartesianChange_unitary :
    cartesianChangeᴴ*cartesianChange=1 ∧ cartesianChange*cartesianChangeᴴ=1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cartesianChange,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_three,
      Matrix.one_apply, map_ofNat] <;>
    norm_num <;> ring_nf <;> simp [sqrt_two_sq_complex,Complex.I_sq] <;> ring

lemma cartesianChange_reverse_left :
    cartesianChangeᴴ*timeReverseOne = -cartesianChangeᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartesianChange,timeReverseOne,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose,
      Fin.sum_univ_three, map_ofNat] <;> norm_num <;> ring

lemma cartesianChange_reverse_right :
    timeReverseOne*cartesianChange = -(cartesianChangeᴴ)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartesianChange,timeReverseOne,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose,
      Fin.sum_univ_three, map_ofNat] <;> norm_num <;> ring

lemma cartesianChange_reverse (B : Mat 2) :
    cartesianChangeᴴ*(timeReverseOne*Bᵀ*timeReverseOne)*cartesianChange =
      (cartesianChangeᴴ*B*cartesianChange)ᵀ := by
  calc
    _ = (cartesianChangeᴴ*timeReverseOne)*Bᵀ*(timeReverseOne*cartesianChange) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [cartesianChange_reverse_left,cartesianChange_reverse_right]
      simp only [Matrix.neg_mul,Matrix.mul_neg,neg_neg,Matrix.transpose_mul,
        Matrix.mul_assoc]

lemma cartesianChange_trace (B : Mat 2) :
    (cartesianChangeᴴ*B*cartesianChange).trace = B.trace := by
  rw [Matrix.trace_mul_cycle,cartesianChange_unitary.2,Matrix.one_mul]

lemma spinOneAction_cartesian_formula (f g : ℝ) (B : Mat 2) :
    cartesianChangeᴴ*spinOneAction f g B*cartesianChange =
      (((f+g)/2 : ℝ) : ℂ) • (cartesianChangeᴴ*B*cartesianChange) +
      (((g-f)/2 : ℝ) : ℂ) • (cartesianChangeᴴ*B*cartesianChange)ᵀ +
      (((1-g)/3 : ℝ) : ℂ) •
        ((cartesianChangeᴴ*B*cartesianChange).trace • (1 : Mat 2)) := by
  simp only [spinOneAction_apply,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.mul_one,cartesianChange_unitary.1,cartesianChange_reverse,
    cartesianChange_trace]

lemma linear_cartesianAction_eq (f g : ℝ) (B : Mat 2) (hB : B.IsHermitian)
    (htr : B.trace=1) :
    (((f+g)/2 : ℝ) : ℂ) • B + (((g-f)/2 : ℝ) : ℂ) • Bᵀ +
      (((1-g)/3 : ℝ) : ℂ) • (B.trace • (1 : Mat 2)) =
      Cartesian.covarianceAction f g B := by
  rw [htr]
  ext i j
  have hji : B j i = star (B i j) := by
    have h := hB.apply j i
    exact h.symm
  simp only [Cartesian.covarianceAction_apply,Matrix.add_apply,Matrix.smul_apply,
    Matrix.transpose_apply,smul_eq_mul,hji,Matrix.one_apply]
  by_cases hij : i=j <;> simp [hij] <;> apply Complex.ext <;>
    simp [Complex.mul_re,Complex.mul_im] <;> ring

/-- On actual Hermitian trace-one matrices, the complex-linear spin-one action
is precisely the manuscript's Cartesian attenuation law. -/
theorem spinOneAction_cartesian (f g : ℝ) (B : Mat 2)
    (hB : B.IsHermitian) (htr : B.trace=1) :
    cartesianChangeᴴ*spinOneAction f g B*cartesianChange =
      Cartesian.covarianceAction f g (cartesianChangeᴴ*B*cartesianChange) := by
  rw [spinOneAction_cartesian_formula]
  apply linear_cartesianAction_eq
  · change (cartesianChangeᴴ*B*cartesianChange)ᴴ = cartesianChangeᴴ*B*cartesianChange
    simp [Matrix.conjTranspose_mul, hB.eq, Matrix.mul_assoc]
  · rw [cartesianChange_trace,htr]

end
end SU2T2.Spin
