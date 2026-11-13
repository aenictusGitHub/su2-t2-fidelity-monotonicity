import DickeEmbedding
import SpinGenerators
import Mathlib.Analysis.Matrix.Order

namespace SU2T2.Dicke
open Matrix
open scoped ComplexOrder
noncomputable section

lemma raising_normalization (n k : ℕ) (hk : k<n) :
    ((k+1 : ℝ) * Real.sqrt (n.choose (k+1) : ℝ)) =
      Spin.weight n k * Real.sqrt (n.choose k : ℝ) := by
  have hk' : k≤n := Nat.le_of_lt hk
  have hc : (n.choose (k+1) : ℝ)*(k+1) = (n.choose k : ℝ)*((n:ℝ)-k) := by
    exact_mod_cast (Nat.choose_succ_right_eq n k)
  have h0 : (0:ℝ) ≤ (k+1)*((n:ℝ)-k) := by
    have hkn : (k:ℝ)≤n := by exact_mod_cast hk'
    exact mul_nonneg (by positivity) (by linarith)
  have hs0 := Real.sq_sqrt h0
  have hs1 := Real.sq_sqrt (show (0:ℝ)≤(n.choose (k+1):ℝ) by positivity)
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤(n.choose k:ℝ) by positivity)
  have hmul := congrArg (fun x : ℝ => (k+1)*x) hc
  have he : ((k+1:ℝ)*Real.sqrt (n.choose (k+1):ℝ))^2 =
      (Spin.weight n k * Real.sqrt (n.choose k : ℝ))^2 := by
    dsimp [Spin.weight]
    rw [mul_pow, mul_pow, hs0, hs1, hs2]
    nlinarith [hmul]
  have hleft : 0≤(k+1:ℝ)*Real.sqrt (n.choose (k+1):ℝ) := by positivity
  have hright : 0≤Spin.weight n k * Real.sqrt (n.choose k:ℝ) := by
    dsimp [Spin.weight]; positivity
  nlinarith

lemma embedding_column (n : ℕ) (k : Fin (n+1)) :
    (fun b => embedding n b k) =
      ((Real.sqrt (n.choose k.val:ℝ):ℂ))⁻¹ • unweighted n k.val := by
  ext b
  by_cases h : weight b=k.val <;> simp [embedding, unweighted, h]

lemma totalRaising_embedding_apply (n : ℕ) (b : Bits n) (k : Fin (n+1)) :
    (totalRaising n * embedding n) b k =
      ((Real.sqrt (n.choose k.val:ℝ):ℂ))⁻¹ * (k.val+1:ℂ) *
        unweighted n (k.val+1) b := by
  change (totalRaising n *ᵥ (fun c => embedding n c k)) b = _
  rw [embedding_column, Matrix.mulVec_smul, totalRaising_unweighted]
  simp [smul_eq_mul, mul_assoc]

lemma mul_raising_castSucc {m : Type*} (n : ℕ) (D : Matrix m (Fin (n+1)) ℂ)
    (b : m) (k : Fin n) :
    (D * Spin.raising n) b k.castSucc = D b k.succ * (Spin.weight n k.val : ℂ) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single k.succ]
  · simp [Spin.raising]
  · intro j hj hne
    have hj' : j.val ≠ k.val+1 := fun h => hne (Fin.ext h)
    simp [Spin.raising, hj']
  · simp

lemma mul_raising_last {m : Type*} (n : ℕ) (D : Matrix m (Fin (n+1)) ℂ)
    (b : m) : (D * Spin.raising n) b (Fin.last n)=0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : j.val ≠ n+1 := by omega
  simp [Spin.raising, hj']

lemma totalRaising_intertwines (n : ℕ) :
    totalRaising n * embedding n = embedding n * Spin.raising n := by
  ext b k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · rw [mul_raising_last, totalRaising_embedding_apply]
    have h : weight b ≠ n+1 := by have hb := weight_le b; omega
    simp [unweighted, h]
  · rw [mul_raising_castSucc, totalRaising_embedding_apply]
    have hcR : Real.sqrt (n.choose k.val : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      exact_mod_cast Nat.choose_pos (show k.val≤n by omega)
    have hsR : Real.sqrt (n.choose (k.val+1) : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      exact_mod_cast Nat.choose_pos (show k.val+1≤n by omega)
    have hc : (Real.sqrt (n.choose k.val : ℝ):ℂ) ≠ 0 := by exact_mod_cast hcR
    have hs : (Real.sqrt (n.choose (k.val+1) : ℝ):ℂ) ≠ 0 := by exact_mod_cast hsR
    have hn : (k.val+1:ℂ)*(Real.sqrt (n.choose (k.val+1) : ℝ):ℂ) =
        (Spin.weight n k.val:ℂ)*(Real.sqrt (n.choose k.val : ℝ):ℂ) := by
      exact_mod_cast raising_normalization n k.val k.isLt
    have he : ((Real.sqrt (n.choose k.val : ℝ):ℂ))⁻¹*(k.val+1:ℂ) =
        ((Real.sqrt (n.choose (k.val+1) : ℝ):ℂ))⁻¹*(Spin.weight n k.val:ℂ) := by
      apply (mul_right_cancel₀ (mul_ne_zero hc hs))
      field_simp
      linear_combination hn
    by_cases hb : weight b=k.val+1
    · simp [embedding, unweighted, hb, he]
    · simp [embedding, unweighted, hb]

/-- Collective magnetic generator, before restricting to the symmetric subspace. -/
def totalZ (n : ℕ) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.diagonal (fun b => (weight b:ℂ)-(n:ℂ)/2)

lemma totalZ_intertwines (n : ℕ) : totalZ n * embedding n = embedding n * Spin.zAxis n := by
  ext b k
  simp only [totalZ, Spin.zAxis, Matrix.diagonal_mul, Matrix.mul_diagonal, Spin.magnetic]
  by_cases hb : weight b=k.val
  · simp [embedding, hb, mul_comm]
  · simp [embedding, hb]

lemma compressed_totalRaising (n : ℕ) :
    (embedding n)ᴴ * totalRaising n * embedding n = Spin.raising n := by
  rw [Matrix.mul_assoc, totalRaising_intertwines, ← Matrix.mul_assoc, embedding_isometry,
    Matrix.one_mul]

lemma compressed_totalZ (n : ℕ) :
    (embedding n)ᴴ * totalZ n * embedding n = Spin.zAxis n := by
  rw [Matrix.mul_assoc, totalZ_intertwines, ← Matrix.mul_assoc, embedding_isometry,
    Matrix.one_mul]


def qubitZ : Matrix (Fin 2) (Fin 2) ℂ := !![-1/2, 0; 0, 1/2]

lemma totalZ_succ (n : ℕ) : totalZ (n+1) =
    Matrix.kronecker qubitZ (1 : Matrix (Bits n) (Bits n) ℂ) +
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (totalZ n) := by
  change (Matrix.diagonal (fun b : Fin 2 × Bits n => ((b.1.val+weight b.2:ℕ):ℂ)-((n+1:ℕ):ℂ)/2)) = _
  ext ⟨i,b⟩ ⟨j,c⟩
  by_cases hbc : b=c
  · subst c
    fin_cases i <;> fin_cases j <;>
      simp [totalZ, qubitZ, Prod.mk.injEq] <;> ring
  · fin_cases i <;> fin_cases j <;>
      simp [totalZ, qubitZ, hbc, Prod.mk.injEq]

lemma qubitRaising_commutator : qubitRaising*qubitRaisingᴴ-
    qubitRaisingᴴ*qubitRaising = (2:ℂ) • qubitZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitRaising,qubitZ,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

lemma kronecker_sum_commutator {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    let T := Matrix.kronecker A (1 : Matrix n n ℂ) + Matrix.kronecker (1 : Matrix m m ℂ) B
    T*Tᴴ-Tᴴ*T = Matrix.kronecker (A*Aᴴ-Aᴴ*A) (1:Matrix n n ℂ) +
      Matrix.kronecker (1:Matrix m m ℂ) (B*Bᴴ-Bᴴ*B) := by
  dsimp
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, add_mul, mul_add, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  ext ⟨i,b⟩ ⟨j,c⟩
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.kronecker_apply]
  ring

lemma totalRaising_commutator (n : ℕ) :
    totalRaising n*(totalRaising n)ᴴ-(totalRaising n)ᴴ*totalRaising n =
      (2:ℂ) • totalZ n := by
  induction n with
  | zero => ext i j; cases i; cases j; simp [totalRaising,totalZ,weight]
  | succ n ih =>
    rw [totalRaising, kronecker_sum_commutator, qubitRaising_commutator, ih, totalZ_succ]
    change Matrix.kronecker ((2:ℂ) • qubitZ) (1:Matrix (Bits n) (Bits n) ℂ) +
      Matrix.kronecker (1:Matrix (Fin 2) (Fin 2) ℂ) ((2:ℂ) • totalZ n) = _
    ext i j
    simp [Matrix.kronecker, Matrix.kroneckerMap, smul_eq_mul, mul_add]
    ring

lemma lowering_intertwines_of_commutator {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (D : Matrix m n ℂ)
    (A Z : Matrix m m ℂ) (E H : Matrix n n ℂ)
    (hD : Dᴴ*D=1) (hA : A*D=D*E) (hZ : Z*D=D*H)
    (hcomm : A*Aᴴ-Aᴴ*A=(2:ℂ) • Z)
    (hecomm : E*Eᴴ-Eᴴ*E=(2:ℂ) • H) : Aᴴ*D=D*Eᴴ := by
  apply sub_eq_zero.mp
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  have ha : Dᴴ*Aᴴ=Eᴴ*Dᴴ := by
    simpa using congrArg Matrix.conjTranspose hA
  have hca : A*Aᴴ=Aᴴ*A+(2:ℂ) • Z := by
    exact (sub_eq_iff_eq_add.mp hcomm).trans (add_comm _ _)
  have hce : Eᴴ*E+(2:ℂ) • H=E*Eᴴ := by
    exact ((sub_eq_iff_eq_add.mp hecomm).trans (add_comm _ _)).symm
  have haa : Dᴴ*(A*Aᴴ)*D=E*Eᴴ := by
    rw [hca, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc Dᴴ Z D, hZ,
      ← Matrix.mul_assoc Dᴴ D H, hD, Matrix.one_mul]
    rw [Matrix.mul_assoc Dᴴ (Aᴴ*A) D, Matrix.mul_assoc Aᴴ A D, hA]
    simp only [← Matrix.mul_assoc]
    rw [ha]
    simp only [Matrix.mul_assoc, hD, Matrix.one_mul]
    exact hce
  have haD : Dᴴ*Aᴴ*D=Eᴴ := by rw [ha, Matrix.mul_assoc, hD, Matrix.mul_one]
  have hDA : Dᴴ*A*D=E := by rw [Matrix.mul_assoc,hA,← Matrix.mul_assoc,hD,Matrix.one_mul]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
  have haa' : Dᴴ*A*Aᴴ*D=E*Eᴴ := by simpa only [Matrix.mul_assoc] using haa
  simp only [← Matrix.mul_assoc]
  rw [haa', hDA]
  have h1 : E*Dᴴ*Aᴴ*D=E*Eᴴ := by
    simpa only [Matrix.mul_assoc] using congrArg (fun X => E*X) haD
  have h2 : E*Dᴴ*D*Eᴴ=E*Eᴴ := by
    rw [Matrix.mul_assoc E Dᴴ D,hD,Matrix.mul_one]
  rw [h1,h2]
  abel

lemma totalLowering_intertwines (n : ℕ) :
    (totalRaising n)ᴴ * embedding n = embedding n * Spin.lowering n := by
  exact lowering_intertwines_of_commutator (embedding n) (totalRaising n)
    (totalZ n) (Spin.raising n) (Spin.zAxis n) (embedding_isometry n)
    (totalRaising_intertwines n) (totalZ_intertwines n)
    (totalRaising_commutator n) (Spin.raising_lowering_commutator n)

end
end SU2T2.Dicke
