import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! Concrete matrix lemmas for the physical marginal bridge. -/
namespace SU2T2
namespace Physical
open Matrix
open scoped ComplexOrder Matrix
noncomputable section

/-- Twice the real part of a qutrit density matrix, in a Cartesian spin-one basis. -/
def cartesianReal (ρ : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => 2 * (ρ i j).re

lemma realPart_posSemidef {n : Type*} [Fintype n]
    (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    Matrix.PosSemidef (fun i j => (ρ i j).re : Matrix n n ℝ) := by
  constructor
  · ext i j
    have h := congrFun (congrFun hρ.isHermitian i) j
    simpa [Matrix.conjTranspose_apply] using congrArg Complex.re h
  · intro x
    have h := hρ.re_dotProduct_nonneg (fun i => (x i : ℂ))
    simpa [dotProduct, Matrix.mulVec, map_sum, Complex.mul_re] using h

lemma cartesianReal_posSemidef (ρ : Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ρ.PosSemidef) : (cartesianReal ρ).PosSemidef := by
  have h := (realPart_posSemidef ρ hρ).smul (show (0 : ℝ) ≤ 2 by norm_num)
  simpa [cartesianReal] using h

lemma cartesianReal_trace (ρ : Matrix (Fin 3) (Fin 3) ℂ)
    (ht : ρ.trace=1) : (cartesianReal ρ).trace=2 := by
  have h := congrArg Complex.re ht
  simpa [cartesianReal, Matrix.trace, Finset.mul_sum, map_sum] using
    congrArg (fun x : ℝ => 2*x) h

/-- Unscaled Kraus matrices for tracing one qubit from the spin-3/2 sector.
The output basis is Cartesian spin one; the input basis is the ordered Dicke basis. -/
def marginalKraus0 : Matrix (Fin 3) (Fin 4) ℂ :=
  !![-(Real.sqrt 3 : ℂ), 0, 1, 0;
     -Complex.I*(Real.sqrt 3 : ℂ), 0, -Complex.I, 0;
     0, 2, 0, 0]

def marginalKraus1 : Matrix (Fin 3) (Fin 4) ℂ :=
  !![0, -1, 0, (Real.sqrt 3 : ℂ);
     0, -Complex.I, 0, -Complex.I*(Real.sqrt 3 : ℂ);
     0, 0, 2, 0]

/-- The symmetric three-to-two-qubit partial trace, in Cartesian output coordinates. -/
def threeToTwo (ρ : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1/6 : ℝ) • (marginalKraus0 * ρ * marginalKraus0ᴴ +
    marginalKraus1 * ρ * marginalKraus1ᴴ)

lemma threeToTwo_posSemidef (ρ : Matrix (Fin 4) (Fin 4) ℂ)
    (hρ : ρ.PosSemidef) : (threeToTwo ρ).PosSemidef := by
  exact ((hρ.mul_mul_conjTranspose_same marginalKraus0).add
    (hρ.mul_mul_conjTranspose_same marginalKraus1)).smul (by norm_num : (0:ℝ) ≤ 1/6)

lemma marginalKraus_complete :
    marginalKraus0ᴴ * marginalKraus0 + marginalKraus1ᴴ * marginalKraus1 =
      (6 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [marginalKraus0, marginalKraus1, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.smul_apply, Complex.ext_iff, Complex.mul_re, Complex.mul_im] <;>
    norm_num

lemma threeToTwo_trace (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    (threeToTwo ρ).trace=ρ.trace := by
  unfold threeToTwo
  rw [Matrix.trace_smul, Matrix.trace_add]
  have h0 := Matrix.trace_mul_cycle marginalKraus0 ρ marginalKraus0ᴴ
  have h1 := Matrix.trace_mul_cycle marginalKraus1 ρ marginalKraus1ᴴ
  rw [h0, h1, ← Matrix.trace_add, ← Matrix.add_mul, marginalKraus_complete]
  simp [Matrix.trace_smul]

/-- Twice the directional spin-3/2 matrix in the ordered Dicke basis. -/
def twiceSpin (v : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let w : ℂ := v 0 - Complex.I * v 1
  let z : ℂ := v 2
  !![3*z, (Real.sqrt 3 : ℂ)*w, 0, 0;
     (Real.sqrt 3 : ℂ)*star w, z, 2*w, 0;
     0, 2*star w, -z, (Real.sqrt 3 : ℂ)*w;
     0, 0, (Real.sqrt 3 : ℂ)*star w, -3*z]

def realProjector (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.vecMulVec (fun i => (v i : ℂ)) (fun i => (v i : ℂ))

set_option maxHeartbeats 2000000 in
lemma spinSquare_complement (v : Fin 3 → ℝ) :
    (twiceSpin v)ᴴ * twiceSpin v + (2 : ℂ) •
      (marginalKraus0ᴴ * realProjector v * marginalKraus0 +
       marginalKraus1ᴴ * realProjector v * marginalKraus1) =
    ((9 * ((v 0)^2+(v 1)^2+(v 2)^2) : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twiceSpin, marginalKraus0, marginalKraus1, realProjector, Matrix.vecMulVec,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.smul_apply, Complex.ext_iff, Complex.mul_re, Complex.mul_im] <;>
    constructor <;> ring_nf <;> simp [hs, ← Complex.ofReal_pow] <;> ring

lemma trace_realProjector (ρ : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℝ) :
    (ρ * realProjector v).trace =
      (fun i => (v i : ℂ)) ⬝ᵥ (ρ *ᵥ (fun i => (v i : ℂ))) := by
  rw [realProjector, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

lemma cartesianReal_quadratic (ρ : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (cartesianReal ρ *ᵥ v) = 2 * (ρ * realProjector v).trace.re := by
  rw [trace_realProjector]
  simp [cartesianReal, dotProduct, Matrix.mulVec, Fin.sum_univ_succ,
    Complex.mul_re]
  ring

lemma trace_conjugation_effect {m n : Type*} [Fintype m] [Fintype n]
    (ρ : Matrix n n ℂ) (P : Matrix m m ℂ) (B : Matrix m n ℂ) :
    (ρ * (Bᴴ * P * B)).trace = (B * ρ * Bᴴ * P).trace := by
  rw [Matrix.trace_mul_comm]
  simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle B ρ (Bᴴ * P)).symm

lemma threeToTwo_effect (ρ : Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 3) (Fin 3) ℂ) :
    6 * (threeToTwo ρ * P).trace =
      (ρ * (marginalKraus0ᴴ * P * marginalKraus0)).trace +
      (ρ * (marginalKraus1ᴴ * P * marginalKraus1)).trace := by
  rw [trace_conjugation_effect, trace_conjugation_effect]
  simp [threeToTwo, Matrix.trace_smul, Matrix.add_mul,
    Matrix.trace_add, Complex.real_smul]
  ring

lemma threeToTwo_quadratic_bound (ρ : Matrix (Fin 4) (Fin 4) ℂ)
    (hρ : ρ.PosSemidef) (ht : ρ.trace=1) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (cartesianReal (threeToTwo ρ) *ᵥ v) ≤
      (3/2)*((v 0)^2+(v 1)^2+(v 2)^2) := by
  have hcomp := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (ρ*M).trace)
    (spinSquare_complement v)
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.mul_one, ht] at hcomp
  rw [← threeToTwo_effect ρ (realProjector v)] at hcomp
  have hpos := (hρ.mul_mul_conjTranspose_same (twiceSpin v)).trace_nonneg
  have htrace : (twiceSpin v * ρ * (twiceSpin v)ᴴ).trace =
      (ρ * ((twiceSpin v)ᴴ * twiceSpin v)).trace := by
    have h := Matrix.trace_mul_cycle (twiceSpin v) ρ (twiceSpin v)ᴴ
    rw [Matrix.trace_mul_comm ((twiceSpin v)ᴴ * twiceSpin v) ρ] at h
    exact h
  rw [htrace] at hpos
  have hposre : 0 ≤ (ρ * ((twiceSpin v)ᴴ * twiceSpin v)).trace.re := hpos.1
  have he := congrArg Complex.re hcomp
  rw [cartesianReal_quadratic]
  simp [Complex.mul_re, -Complex.ofReal_pow] at he
  nlinarith

/-- The crucial physical bound, proved for the actual three-qubit marginal map. -/
lemma threeToTwo_upper (ρ : Matrix (Fin 4) (Fin 4) ℂ)
    (hρ : ρ.PosSemidef) (ht : ρ.trace=1) :
    ((3/2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
      cartesianReal (threeToTwo ρ)).PosSemidef := by
  have hA := cartesianReal_posSemidef (threeToTwo ρ) (threeToTwo_posSemidef ρ hρ)
  constructor
  · exact ((Matrix.PosSemidef.one : (1 : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef).smul
      (by norm_num : (0 : ℝ) ≤ 3/2)).isHermitian.sub hA.isHermitian
  · intro v
    have h := sub_nonneg.mpr (threeToTwo_quadratic_bound ρ hρ ht v)
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec,
      dotProduct, Fin.sum_univ_succ, pow_two] at h ⊢
    nlinarith

/-- All marginal constraints needed by the determinant argument, with no assumed
marginal bounds: they follow from positivity and normalization of the input. -/
theorem threeToTwo_physical_constraints (ρ : Matrix (Fin 4) (Fin 4) ℂ)
    (hρ : ρ.PosSemidef) (ht : ρ.trace=1) :
    (threeToTwo ρ).PosSemidef ∧ (threeToTwo ρ).trace=1 ∧
    (cartesianReal (threeToTwo ρ)).PosSemidef ∧
    (cartesianReal (threeToTwo ρ)).trace=2 ∧
    ((3/2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
      cartesianReal (threeToTwo ρ)).PosSemidef := by
  have hp := threeToTwo_posSemidef ρ hρ
  have htr : (threeToTwo ρ).trace=1 := (threeToTwo_trace ρ).trans ht
  exact ⟨hp, htr, cartesianReal_posSemidef _ hp,
    cartesianReal_trace _ htr, threeToTwo_upper ρ hρ ht⟩

end
end Physical
end SU2T2
