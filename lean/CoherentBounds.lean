import PhysicalNBody
import CartesianSpectral
import ChoiScalarBounds

/-! Multiplier inequalities from the actual coherent-state marginal. -/
namespace SU2T2.Physical
open Matrix
open scoped Matrix ComplexOrder
noncomputable section

def coherent (n : ℕ) : Matrix (Fin (n+4)) (Fin (n+4)) ℂ :=
  Matrix.single 0 0 1

def coherentTwo : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1/2,-Complex.I/2,0; Complex.I/2,1/2,0; 0,0,0]

lemma coherent_posSemidef (n : ℕ) : (coherent n).PosSemidef := by
  have he : coherent n = Matrix.diagonal (fun i => if i=0 then (1:ℂ) else 0) := by
    ext i j
    by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp [coherent, Matrix.single,
      Matrix.diagonal_apply, hi, hj, eq_comm]
  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro i
  dsimp
  split_ifs <;> norm_num

lemma coherent_trace (n : ℕ) : (coherent n).trace=1 := by
  simp [coherent]

lemma groupedDicke_zero (n : ℕ) (b : ThreeBits) (r : Dicke.Bits n) :
    groupedDicke n (b,r) 0 =
      if threeWeight b=0 ∧ Dicke.weight r=0 then 1 else 0 := by
  rw [groupedDicke_weight]
  simp [Nat.add_eq_zero_iff]

lemma coherent_grouped_entry (n : ℕ) (b c : ThreeBits) (r s : Dicke.Bits n) :
    (groupedDicke n * coherent n * (groupedDicke n)ᴴ) (b,r) (c,s) =
      (if threeWeight b=0 ∧ Dicke.weight r=0 then 1 else 0) *
      (if threeWeight c=0 ∧ Dicke.weight s=0 then 1 else 0) := by
  rw [Matrix.mul_apply]
  have he (x : Fin (n+4)) : (groupedDicke n * coherent n) (b,r) x =
      if x=0 then groupedDicke n (b,r) 0 else 0 := by
    by_cases hx : x=0
    · subst x; simp [coherent]
    · simp [coherent, Matrix.mul_single_apply_of_ne, hx]
  simp_rw [he]
  simp [Matrix.conjTranspose_apply, groupedDicke_zero]
  split_ifs <;> rfl

lemma coherent_three_entry (n : ℕ) (b c : ThreeBits) :
    partialTraceLast (groupedDicke n * coherent n * (groupedDicke n)ᴴ) b c =
      if threeWeight b=0 ∧ threeWeight c=0 then 1 else 0 := by
  simp only [partialTraceLast, coherent_grouped_entry]
  by_cases hb : threeWeight b=0 <;> by_cases hc : threeWeight c=0
  · simp only [hb,hc,true_and]
    simp_rw [ite_mul_ite, mul_one, mul_zero]
    simpa using Dicke.weightCount_complex n 0
  · simp [hb,hc]
  · simp [hb,hc]
  · simp [hb,hc]

set_option maxHeartbeats 1000000 in
lemma twoMarginal_coherent (n : ℕ) : twoMarginal n (coherent n)=coherentTwo := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have he : partialTraceLast (groupedDicke n * coherent n * (groupedDicke n)ᴴ) =
      (fun b c => if threeWeight b=0 ∧ threeWeight c=0 then (1:ℂ) else 0) := by
    ext b c
    exact coherent_three_entry n b c
  unfold twoMarginal
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
      partialTraceLast, cartesianTriplet, threeWeight,
      coherentTwo, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;>
    norm_num <;> ring_nf <;> simp [hs] <;> ring_nf <;> norm_num [hs, Finset.filter_eq']

lemma coherent_action_bounds (f g : ℝ)
    (h : (Cartesian.covarianceAction f g coherentTwo).PosSemidef) :
    0 ≤ (2+g)/3+f ∧ 0 ≤ (2+g)/3-f ∧ 0 ≤ 1-g := by
  have hplus := h.re_dotProduct_nonneg ![1,Complex.I,0]
  have hminus := h.re_dotProduct_nonneg ![1,-Complex.I,0]
  have hzero := h.re_dotProduct_nonneg ![0,0,1]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hplus hminus hzero
  simp [Cartesian.covarianceAction_apply, coherentTwo, Complex.mul_re,
    Complex.mul_im] at hplus hminus hzero
  exact ⟨by linarith, by linarith, by linarith⟩

end
end SU2T2.Physical
