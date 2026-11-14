import DickeSU2
import Mathlib.Algebra.Polynomial.Coeff

namespace SU2T2.Dicke
open Matrix Polynomial
noncomputable section

def rowPolynomial (U : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (b : Bits n) : Polynomial ℂ :=
  ∑ c, C (tensorPower U n b c) * X ^ weight c

lemma rowPolynomial_succ (U : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ)
    (i : Fin 2) (b : Bits n) :
    rowPolynomial U (n+1) (i,b) = (C (U i 0)+C (U i 1)*X)*rowPolynomial U n b := by
  unfold rowPolynomial
  change (∑ c : Fin 2 × Bits n, _) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [tensorPower, Matrix.kronecker, Matrix.kroneckerMap, weight, Fin.val_zero, Fin.val_one,
    zero_add, pow_add, pow_one, map_mul, Finset.mul_sum, add_mul, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro c hc <;> simp only [Matrix.of_apply, map_mul] <;> ring

lemma rowPolynomial_formula (U : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (b : Bits n) :
    rowPolynomial U n b = (C (U 0 0)+C (U 0 1)*X)^(n-weight b) *
      (C (U 1 0)+C (U 1 1)*X)^weight b := by
  induction n with
  | zero =>
    have hb : b = PUnit.unit := by cases b; rfl
    subst b
    simp [rowPolynomial, tensorPower, Bits, weight, Matrix.one_apply]
  | succ n ih =>
    rcases b with ⟨i,b⟩
    rw [rowPolynomial_succ, ih]
    have hw := weight_le b
    have hone (h : 1<2) : (⟨1,h⟩ : Fin 2)=1 := rfl
    fin_cases i
    · simp only [weight, Fin.val_zero, zero_add]
      rw [show n+1-weight b=(n-weight b)+1 by omega, pow_succ]
      simp only [Fin.mk_zero]
      ring
    · simp only [weight, Fin.val_one, hone]
      rw [show n+1-(1+weight b)=n-weight b by omega,
        show 1+weight b=weight b+1 by omega, pow_succ]
      ring

lemma tensor_unweighted_constant (U : Matrix (Fin 2) (Fin 2) ℂ) (n k : ℕ)
    (b c : Bits n) (h : weight b=weight c) :
    (tensorPower U n *ᵥ unweighted n k) b =
      (tensorPower U n *ᵥ unweighted n k) c := by
  have he : rowPolynomial U n b=rowPolynomial U n c := by
    rw [rowPolynomial_formula,rowPolynomial_formula,h]
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff k) he
  simpa [rowPolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Matrix.mulVec, dotProduct, unweighted, mul_ite, eq_comm] using hc

lemma tensor_embedding_constant (U : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ)
    (b c : Bits n) (h : weight b=weight c) (k : Fin (n+1)) :
    (tensorPower U n * embedding n) b k = (tensorPower U n * embedding n) c k := by
  change (tensorPower U n *ᵥ (fun d => embedding n d k)) b =
    (tensorPower U n *ᵥ (fun d => embedding n d k)) c
  rw [embedding_column, Matrix.mulVec_smul]
  simp only [Pi.smul_apply]
  rw [tensor_unweighted_constant U n k b c h]

lemma weight_constant_projection {a : Type*} (n : ℕ) (W : Matrix (Bits n) a ℂ)
    (hW : ∀ b c, weight b=weight c → ∀ j, W b j=W c j) :
    embedding n * ((embedding n)ᴴ * W)=W := by
  ext b j
  let k : Fin (n+1) := ⟨weight b, by have := weight_le b; omega⟩
  let s : ℂ := (Real.sqrt (n.choose (weight b) : ℝ) : ℂ)
  have hs : s ≠ 0 := by
    dsimp [s]
    have hp : (0:ℝ)<n.choose (weight b) := by exact_mod_cast Nat.choose_pos (weight_le b)
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hp))
  have hs2 : s^2=(n.choose (weight b):ℂ) := by
    dsimp [s]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_cast
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · have he (c : Bits n) : star (embedding n c k)*W c j =
        (if weight c=weight b then (1:ℂ) else 0)*(s⁻¹*W b j) := by
      by_cases hc : weight c=weight b
      · rw [hW c b hc]
        simp [embedding,k,s,hc]
      · simp [embedding,k,s,hc]
    have hb : embedding n b k=s⁻¹ := by simp [embedding,k,s]
    rw [hb, Matrix.mul_apply]
    change s⁻¹ * (∑ c, star (embedding n c k)*W c j)=W b j
    simp_rw [he]
    rw [← Finset.sum_mul, weightCount_complex, ← hs2]
    field_simp
  · intro l hl hne
    have hn : weight b ≠ l.val := by
      intro h
      apply hne
      exact Fin.ext h.symm
    simp [embedding, hn]
  · simp

/-- Every tensor power preserves the full normalized symmetric sector. -/
theorem action_intertwines (n : ℕ) (U : SU2) :
    tensorPower U.val n * embedding n = embedding n * action n U := by
  symm
  simpa only [action, Matrix.mul_assoc] using
    weight_constant_projection n (tensorPower U.val n * embedding n)
      (tensor_embedding_constant U.val n)

@[simp] theorem action_one (n : ℕ) : action n 1=1 := by
  simp [action, tensorPower_one, embedding_isometry]

@[simp] theorem action_mul (n : ℕ) (U V : SU2) :
    action n (U*V)=action n U * action n V := by
  change (embedding n)ᴴ * tensorPower (U.val*V.val) n * embedding n = _
  rw [tensorPower_mul]
  calc
    _ = (embedding n)ᴴ * tensorPower U.val n * (tensorPower V.val n * embedding n) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [action_intertwines]; simp only [action,Matrix.mul_assoc]

/-- The compressed action is unitary for every SU(2) element and every N. -/
theorem action_unitary (n : ℕ) (U : SU2) :
    action n U ∈ Matrix.unitaryGroup (Fin (n+1)) ℂ := by
  have hT : (tensorPower U.val n)ᴴ * tensorPower U.val n=1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp (tensorPower_unitary U n)
  have h : (embedding n * action n U)ᴴ * (embedding n * action n U)=1 := by
    rw [← action_intertwines]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (tensorPower U.val n)ᴴ, hT, Matrix.one_mul, embedding_isometry]
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (action n U)ᴴ * action n U=1
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (embedding n)ᴴ, embedding_isometry, Matrix.one_mul] using h

/-- The certified spin representation, including its unitary codomain. -/
def unitaryAction (n : ℕ) : SU2 →* Matrix.unitaryGroup (Fin (n+1)) ℂ where
  toFun U := ⟨action n U, action_unitary n U⟩
  map_one' := by apply Subtype.ext; exact action_one n
  map_mul' U V := by apply Subtype.ext; exact action_mul n U V

end
end SU2T2.Dicke

#print axioms SU2T2.Dicke.action_intertwines
#print axioms SU2T2.Dicke.action_mul
#print axioms SU2T2.Dicke.action_unitary

