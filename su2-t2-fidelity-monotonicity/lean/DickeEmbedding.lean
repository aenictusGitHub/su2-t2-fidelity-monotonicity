import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! The normalized Dicke embedding into a recursively indexed qubit tensor product. -/
namespace SU2T2.Dicke
open Matrix
noncomputable section

def Bits : ℕ → Type
  | 0 => Unit
  | n+1 => Fin 2 × Bits n

instance bitsFintype : (n : ℕ) → Fintype (Bits n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @instFintypeProd _ _ (inferInstanceAs (Fintype (Fin 2))) (bitsFintype n)

instance bitsDecidableEq : (n : ℕ) → DecidableEq (Bits n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 => @instDecidableEqProd _ _ (inferInstanceAs (DecidableEq (Fin 2))) (bitsDecidableEq n)

def weight : {n : ℕ} → Bits n → ℕ
  | 0, _ => 0
  | n+1, b => b.1.val + weight b.2

def weightCount (n k : ℕ) : ℕ := ∑ b : Bits n, if weight b = k then 1 else 0

lemma weightCount_succ_zero (n : ℕ) : weightCount (n+1) 0 = weightCount n 0 := by
  change (∑ b : Fin 2 × Bits n, if b.1.val + weight b.2 = 0 then 1 else 0) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [weightCount]

lemma weightCount_succ_succ (n k : ℕ) :
    weightCount (n+1) (k+1) = weightCount n (k+1) + weightCount n k := by
  change (∑ b : Fin 2 × Bits n, if b.1.val + weight b.2 = k+1 then 1 else 0) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, zero_add]
  change weightCount n (k+1) + (∑ b : Bits n, if 1+weight b=k+1 then 1 else 0) = _
  congr 1
  unfold weightCount
  apply Finset.sum_congr rfl
  intro b hb
  have h : (1+weight b=k+1) ↔ weight b=k := by omega
  simp only [h]

lemma weightCount_eq_choose (n k : ℕ) : weightCount n k = n.choose k := by
  induction n generalizing k with
  | zero =>
    cases k <;> simp [weightCount, Bits, weight]
  | succ n ih =>
    cases k with
    | zero => rw [weightCount_succ_zero, ih]; simp
    | succ k => rw [weightCount_succ_succ, ih, ih, Nat.choose_succ_succ]; simp only [Nat.succ_eq_add_one, add_comm]

/-- Normalized Dicke vectors, with k the number of one-bits. -/
def embedding (n : ℕ) : Matrix (Bits n) (Fin (n+1)) ℂ :=
  fun b k => if weight b=k.val then ((Real.sqrt (n.choose k.val : ℝ) : ℂ))⁻¹ else 0

lemma weightCount_complex (n k : ℕ) :
    (∑ b : Bits n, if weight b=k then (1:ℂ) else 0) = (n.choose k : ℂ) := by
  have h := weightCount_eq_choose n k
  unfold weightCount at h
  exact_mod_cast h

lemma embedding_isometry (n : ℕ) : (embedding n)ᴴ * embedding n = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  by_cases hkl : k=l
  · subst l
    rw [Matrix.one_apply_eq]
    let c : ℂ := (Real.sqrt (n.choose k.val : ℝ) : ℂ)
    have hc : c ≠ 0 := by
      dsimp [c]
      have hp : (0:ℝ) < n.choose k.val := by
        exact_mod_cast Nat.choose_pos (show k.val≤n by omega)
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hp))
    have hc2 : c^2 = (n.choose k.val : ℂ) := by
      dsimp [c]
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
      norm_cast
    have he (b : Bits n) :
        star (embedding n b k) * embedding n b k =
          (if weight b=k.val then (1:ℂ) else 0) * (c⁻¹*c⁻¹) := by
      by_cases hb : weight b=k.val <;> simp [embedding, hb, c]
    simp_rw [he]
    rw [← Finset.sum_mul, weightCount_complex, ← hc2]
    field_simp
  · have hval : k.val ≠ l.val := fun h => hkl (Fin.ext h)
    rw [Matrix.one_apply_ne hkl]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hk : weight b=k.val
    · have hl : weight b≠l.val := fun h => hval (hk.symm.trans h)
      simp [embedding, hk, hval]
    · simp [embedding, hk]

lemma weight_le : ∀ {n : ℕ} (b : Bits n), weight b ≤ n
  | 0, b => by simp [weight]
  | n+1, b => by
    have hb := b.1.isLt
    have ht := weight_le b.2
    simp only [weight]
    omega

def unweighted (n k : ℕ) : Bits n → ℂ := fun b => if weight b=k then 1 else 0

def qubitRaising : Matrix (Fin 2) (Fin 2) ℂ := !![0,0;1,0]

def totalRaising : (n : ℕ) → Matrix (Bits n) (Bits n) ℂ
  | 0 => 0
  | n+1 => Matrix.kronecker qubitRaising (1 : Matrix (Bits n) (Bits n) ℂ) +
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (totalRaising n)

lemma totalRaising_succ_apply (n : ℕ) (v : Bits (n+1) → ℂ) (i : Fin 2) (b : Bits n) :
    (totalRaising (n+1) *ᵥ v) (i,b) =
      (if i=1 then v (0,b) else 0) + (totalRaising n *ᵥ fun c => v (i,c)) b := by
  change (∑ c : Fin 2 × Bits n, totalRaising (n+1) (i,b) c * v c) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;>
    simp [totalRaising, qubitRaising, Matrix.mulVec, dotProduct,
      Matrix.one_apply, Finset.sum_add_distrib]

lemma totalRaising_unweighted (n k : ℕ) :
    totalRaising n *ᵥ unweighted n k = ((k+1 : ℕ):ℂ) • unweighted n (k+1) := by
  induction n generalizing k with
  | zero =>
    ext b
    simp [totalRaising, unweighted, weight]
  | succ n ih =>
    ext b
    rcases b with ⟨i,b⟩
    rw [totalRaising_succ_apply]
    fin_cases i
    · simpa [unweighted, weight] using congrFun (ih k) b
    · cases k with
      | zero =>
        simp [unweighted, weight, Matrix.mulVec, dotProduct]
      | succ k =>
        have h := congrFun (ih k) b
        simp only [unweighted, weight, Fin.val_one, Fin.val_zero, zero_add,
          Pi.smul_apply, smul_eq_mul] at h ⊢
        simp only [ite_true, Nat.add_comm 1, Nat.add_right_cancel_iff]
        change (if weight b=k+1 then (1:ℂ) else 0) +
            (totalRaising n *ᵥ unweighted n k) b =
            ((k+1+1 : ℕ):ℂ) * (if weight b=k+1 then (1:ℂ) else 0)
        rw [ih]
        simp [unweighted]
        split_ifs <;> ring

end
end SU2T2.Dicke
