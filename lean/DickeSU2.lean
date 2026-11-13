import DickeGenerators
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The actual symmetric tensor SU(2) action and its infinitesimal generators. -/
namespace SU2T2.Dicke
open Matrix
noncomputable section

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

def tensorPower (U : Matrix (Fin 2) (Fin 2) ℂ) : (n : ℕ) → Matrix (Bits n) (Bits n) ℂ
  | 0 => 1
  | n+1 => Matrix.kronecker U (tensorPower U n)

def collective (G : Matrix (Fin 2) (Fin 2) ℂ) : (n : ℕ) → Matrix (Bits n) (Bits n) ℂ
  | 0 => 0
  | n+1 => Matrix.kronecker G (1:Matrix (Bits n) (Bits n) ℂ) +
      Matrix.kronecker (1:Matrix (Fin 2) (Fin 2) ℂ) (collective G n)

def action (n : ℕ) (U : SU2) : Spin.Mat n :=
  (embedding n)ᴴ * tensorPower U.val n * embedding n

lemma tensorPower_one (n : ℕ) : tensorPower 1 n=1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [tensorPower,ih] using Matrix.one_kronecker_one

lemma collective_raising (n : ℕ) : collective qubitRaising n=totalRaising n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [collective,totalRaising,ih]

lemma collective_z (n : ℕ) : collective qubitZ n=totalZ n := by
  induction n with
  | zero => ext i j; cases i; cases j; simp [collective,totalZ,weight]
  | succ n ih => simp only [collective,ih,totalZ_succ]

lemma collective_add (G H : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    collective (G+H) n=collective G n+collective H n := by
  induction n with
  | zero => simp [collective]
  | succ n ih =>
    simp only [collective, ih]
    ext i j
    simp [Matrix.kronecker, Matrix.kroneckerMap]
    ring

lemma collective_smul (c : ℂ) (G : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    collective (c • G) n=c • collective G n := by
  induction n with
  | zero => simp [collective]
  | succ n ih =>
    simp only [collective,ih]
    ext i j
    simp [Matrix.kronecker,Matrix.kroneckerMap,smul_eq_mul,mul_add]
    ring

lemma collective_star (G : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    collective Gᴴ n=(collective G n)ᴴ := by
  induction n with
  | zero => simp [collective]
  | succ n ih =>
    simp only [collective,ih]
    ext i j
    simp [Matrix.kronecker,Matrix.kroneckerMap,Matrix.conjTranspose_apply,Matrix.one_apply,eq_comm,mul_comm]
    split_ifs <;> simp_all

lemma tensorPower_deriv (U : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (G : Matrix (Fin 2) (Fin 2) ℂ) (hU : U 0=1) (hd : HasDerivAt U G 0) (n : ℕ) :
    HasDerivAt (fun t => tensorPower (U t) n) (collective G n) 0 := by
  induction n with
  | zero => simpa [tensorPower,collective] using (hasDerivAt_const (𝕜:=ℝ) (0:ℝ) (fun i j : Bits 0 => (1:Matrix (Bits 0) (Bits 0) ℂ) i j))
  | succ n ih =>
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    have h1 := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i.1) j.1)
    have h2 := (hasDerivAt_pi.mp (hasDerivAt_pi.mp ih i.2) j.2)
    simpa [tensorPower,collective,Matrix.kronecker,Matrix.kroneckerMap,hU,tensorPower_one]
      using h1.mul h2

lemma matrix_mul_deriv {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (A : ℝ → Matrix m n ℂ) (B : ℝ → Matrix n p ℂ)
    (A' : Matrix m n ℂ) (B' : Matrix n p ℂ) (t : ℝ)
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := HasDerivAt.fun_sum (u:=Finset.univ) (fun k hk =>
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB k) j))
  simpa [Matrix.mul_apply, Finset.sum_add_distrib, Finset.sum_apply, Pi.mul_apply] using h

lemma matrix_star_deriv {m n : Type*} [Fintype m] [Fintype n]
    (A : ℝ → Matrix m n ℂ) (A' : Matrix m n ℂ) (t : ℝ)
    (hA : HasDerivAt A A' t) : HasDerivAt (fun s => (A s)ᴴ) A'ᴴ t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA j) i).star

lemma compressed_deriv (n : ℕ) (U : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (G : Matrix (Fin 2) (Fin 2) ℂ) (hU : U 0=1) (hd : HasDerivAt U G 0) :
    HasDerivAt (fun t => (embedding n)ᴴ * tensorPower (U t) n * embedding n)
      ((embedding n)ᴴ * collective G n * embedding n) 0 := by
  have h1 := matrix_mul_deriv (fun _ : ℝ => (embedding n)ᴴ)
    (fun t => tensorPower (U t) n) 0 (collective G n) 0
    (hasDerivAt_const (𝕜:=ℝ) (0:ℝ) (fun i j => (embedding n)ᴴ i j)) (tensorPower_deriv U G hU hd n)
  have h2 := matrix_mul_deriv _ (fun _ : ℝ => embedding n) _ 0 0 h1 (hasDerivAt_const (𝕜:=ℝ) (0:ℝ) (fun i j => embedding n i j))
  simpa using h2

/-- Standard complex parametrization of an SU(2) matrix. -/
def quaternionMatrix (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a, -star b; b, star a]

lemma quaternionMatrix_mem (a b : ℂ) (h : a*star a+b*star b=1) :
    quaternionMatrix a b ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  change a*(starRingEnd ℂ) a+b*(starRingEnd ℂ) b=1 at h
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · change quaternionMatrix a b * (quaternionMatrix a b)ᴴ=1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quaternionMatrix,Matrix.mul_apply,Fin.sum_univ_two,
        Matrix.conjTranspose_apply]
    all_goals first | simpa only [mul_comm,add_comm] using h | simp [mul_comm]
  · simp [quaternionMatrix, Matrix.det_fin_two]
    linear_combination h

def rotationX (t : ℝ) : SU2 :=
  ⟨quaternionMatrix (Real.cos t) (Complex.I*Real.sin t), by
    apply quaternionMatrix_mem
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,-Complex.ofReal_cos,-Complex.ofReal_sin]
    all_goals nlinarith [Real.sin_sq_add_cos_sq t]⟩

def rotationY (t : ℝ) : SU2 :=
  ⟨quaternionMatrix (Real.cos t) (Real.sin t), by
    apply quaternionMatrix_mem
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,-Complex.ofReal_cos,-Complex.ofReal_sin]
    all_goals nlinarith [Real.sin_sq_add_cos_sq t]⟩

def rotationZ (t : ℝ) : SU2 :=
  ⟨quaternionMatrix ((Real.cos t:ℂ)-Complex.I*Real.sin t) 0, by
    apply quaternionMatrix_mem
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,-Complex.ofReal_cos,-Complex.ofReal_sin]
    all_goals nlinarith [Real.sin_sq_add_cos_sq t]⟩

lemma rotationX_zero : (rotationX 0).val=1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotationX,quaternionMatrix]
lemma rotationY_zero : (rotationY 0).val=1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotationY,quaternionMatrix]
lemma rotationZ_zero : (rotationZ 0).val=1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotationZ,quaternionMatrix]

lemma rotationX_deriv : HasDerivAt (fun t => (rotationX t).val)
    (Complex.I • (qubitRaising+qubitRaisingᴴ)) 0 := by
  have hc := (Real.hasDerivAt_cos (0:ℝ)).ofReal_comp
  have hs := (Real.hasDerivAt_sin (0:ℝ)).ofReal_comp
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [rotationX,quaternionMatrix,qubitRaising,Matrix.conjTranspose_apply,
      -Complex.ofReal_cos,-Complex.ofReal_sin] using hc
  · simpa [rotationX,quaternionMatrix,qubitRaising,Matrix.conjTranspose_apply,
      -Complex.ofReal_cos,-Complex.ofReal_sin] using hs.const_mul Complex.I
  · simpa [rotationX,quaternionMatrix,qubitRaising,Matrix.conjTranspose_apply,
      -Complex.ofReal_cos,-Complex.ofReal_sin] using hs.const_mul Complex.I
  · simpa [rotationX,quaternionMatrix,qubitRaising,Matrix.conjTranspose_apply,
      -Complex.ofReal_cos,-Complex.ofReal_sin] using hc

lemma rotationY_deriv : HasDerivAt (fun t => (rotationY t).val)
    (qubitRaising-qubitRaisingᴴ) 0 := by
  have hc := (Real.hasDerivAt_cos (0:ℝ)).ofReal_comp
  have hs := (Real.hasDerivAt_sin (0:ℝ)).ofReal_comp
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [rotationY,quaternionMatrix,qubitRaising,Matrix.conjTranspose_apply,
      -Complex.ofReal_cos,-Complex.ofReal_sin] using hc
  · simpa [rotationY,quaternionMatrix,qubitRaising,Matrix.conjTranspose_apply,
      -Complex.ofReal_cos,-Complex.ofReal_sin] using hs.neg
  · simpa [rotationY,quaternionMatrix,qubitRaising,Matrix.conjTranspose_apply,
      -Complex.ofReal_cos,-Complex.ofReal_sin] using hs
  · simpa [rotationY,quaternionMatrix,qubitRaising,Matrix.conjTranspose_apply,
      -Complex.ofReal_cos,-Complex.ofReal_sin] using hc

lemma rotationZ_deriv : HasDerivAt (fun t => (rotationZ t).val)
    ((2*Complex.I) • qubitZ) 0 := by
  have hc := (Real.hasDerivAt_cos (0:ℝ)).ofReal_comp
  have hs := (Real.hasDerivAt_sin (0:ℝ)).ofReal_comp
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · convert hc.fun_sub (hs.const_mul Complex.I) using 1
    norm_num [rotationZ,quaternionMatrix,qubitZ,-Complex.ofReal_cos,-Complex.ofReal_sin]
    ring
  · simpa [rotationZ,quaternionMatrix,qubitZ] using (hasDerivAt_const (𝕜:=ℝ) (0:ℝ) (0:ℂ))
  · simpa [rotationZ,quaternionMatrix,qubitZ] using (hasDerivAt_const (𝕜:=ℝ) (0:ℝ) (0:ℂ))
  · convert hc.fun_add (hs.const_mul Complex.I) using 1 <;>
      norm_num [rotationZ,quaternionMatrix,qubitZ,-Complex.ofReal_cos,-Complex.ofReal_sin]
    ring

lemma compressed_collective_x (n : ℕ) :
    (embedding n)ᴴ * collective (Complex.I • (qubitRaising+qubitRaisingᴴ)) n * embedding n =
      Complex.I • (Spin.raising n+Spin.lowering n) := by
  rw [collective_smul,collective_add,collective_star,collective_raising,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_add,Matrix.add_mul,compressed_totalRaising]
  congr 1
  rw [Matrix.mul_assoc,totalLowering_intertwines,←Matrix.mul_assoc,embedding_isometry,Matrix.one_mul]

lemma compressed_collective_y (n : ℕ) :
    (embedding n)ᴴ * collective (qubitRaising-qubitRaisingᴴ) n * embedding n =
      Spin.raising n-Spin.lowering n := by
  rw [sub_eq_add_neg, ←neg_one_smul ℂ qubitRaisingᴴ,collective_add,collective_smul,
    collective_star,collective_raising,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_smul,Matrix.smul_mul,compressed_totalRaising]
  rw [Matrix.mul_assoc (embedding n)ᴴ (totalRaising n)ᴴ (embedding n),
    totalLowering_intertwines,←Matrix.mul_assoc,embedding_isometry,Matrix.one_mul]
  simp only [neg_one_smul,sub_eq_add_neg]

lemma compressed_collective_z (n : ℕ) :
    (embedding n)ᴴ * collective ((2*Complex.I) • qubitZ) n * embedding n =
      (2*Complex.I) • Spin.zAxis n := by
  rw [collective_smul,collective_z,Matrix.mul_smul,Matrix.smul_mul,compressed_totalZ]

lemma tensorPower_mul (U V : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    tensorPower (U*V) n=tensorPower U n*tensorPower V n := by
  induction n with
  | zero => simp [tensorPower]
  | succ n ih =>
    simpa only [tensorPower,ih] using Matrix.mul_kronecker_mul U V (tensorPower U n) (tensorPower V n)

lemma tensorPower_conjTranspose (U : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    tensorPower Uᴴ n=(tensorPower U n)ᴴ := by
  induction n with
  | zero => simp [tensorPower]
  | succ n ih =>
    simpa only [tensorPower,ih] using (Matrix.conjTranspose_kronecker U (tensorPower U n)).symm

lemma tensorPower_unitary (U : SU2) (n : ℕ) :
    tensorPower U.val n ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  induction n with
  | zero => exact one_mem _
  | succ n ih =>
    exact Matrix.kronecker_mem_unitary
      (Matrix.specialUnitaryGroup_le_unitaryGroup U.property) ih


/-- Covariance under every actual fundamental SU(2) matrix, acting on the
normalized symmetric N-qubit sector. -/
def Covariant (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n) : Prop :=
  ∀ (U : SU2) (X : Spin.Mat n),
    φ (action n U * X * (action n U)ᴴ)=action n U * φ X * (action n U)ᴴ

def CommutesGenerator (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n) (G : Spin.Mat n) : Prop :=
  ∀ X, φ (G*X-X*G)=G*φ X-φ X*G

lemma covariance_differentiation (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n)
    (U : ℝ → Spin.Mat n) (G : Spin.Mat n)
    (h0 : U 0=1) (hd : HasDerivAt U G 0) (hstar : Gᴴ = -G)
    (hcov : ∀ t X, φ (U t*X*(U t)ᴴ)=U t*φ X*(U t)ᴴ) :
    CommutesGenerator n φ G := by
  intro X
  let φc : ((Fin (n+1) → Fin (n+1) → ℂ) →L[ℝ] (Fin (n+1) → Fin (n+1) → ℂ)) :=
    (φ.restrictScalars ℝ).toContinuousLinearMap
  have hconj (Y : Spin.Mat n) :
      HasDerivAt (fun t => U t*Y*(U t)ᴴ) (G*Y-Y*G) 0 := by
    have h1 := matrix_mul_deriv U (fun _ : ℝ => Y) G 0 0 hd
      (hasDerivAt_const (𝕜:=ℝ) (0:ℝ) (fun i j => Y i j))
    have h2 := matrix_mul_deriv _ (fun t => (U t)ᴴ) _ Gᴴ 0 h1
      (matrix_star_deriv U G 0 hd)
    simpa [h0,hstar,Matrix.mul_neg,sub_eq_add_neg] using h2
  have hleft := φc.hasFDerivAt.comp_hasDerivAt 0 (hconj X)
  change HasDerivAt (fun t => φ (U t*X*(U t)ᴴ)) (φ (G*X-X*G)) 0 at hleft
  have heq : (fun t => φ (U t*X*(U t)ᴴ))=(fun t => U t*φ X*(U t)ᴴ) := by
    funext t
    exact hcov t X
  rw [heq] at hleft
  ext i j
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hleft i) j).unique
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp (hconj (φ X)) i) j)

lemma commutesGenerator_add (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n)
    (G H : Spin.Mat n) (hG : CommutesGenerator n φ G) (hH : CommutesGenerator n φ H) :
    CommutesGenerator n φ (G+H) := by
  intro X
  have h : (G+H)*X-X*(G+H)=(G*X-X*G)+(H*X-X*H) := by noncomm_ring
  rw [h,map_add,hG,hH]
  noncomm_ring

lemma commutesGenerator_smul (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n)
    (c : ℂ) (G : Spin.Mat n) (hG : CommutesGenerator n φ G) :
    CommutesGenerator n φ (c • G) := by
  intro X
  simp only [Matrix.smul_mul,Matrix.mul_smul,←smul_sub,map_smul]
  rw [hG X]

lemma action_zero (n : ℕ) (U : SU2) (hU : U.val=1) : action n U=1 := by
  simp only [action,hU,tensorPower_one,Matrix.mul_one,embedding_isometry]

lemma covariant_generator_x (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n)
    (hcov : Covariant n φ) : CommutesGenerator n φ (Complex.I • (Spin.raising n+Spin.lowering n)) := by
  apply covariance_differentiation n φ (fun t => action n (rotationX t))
  · exact action_zero n (rotationX 0) rotationX_zero
  · simpa only [action,compressed_collective_x] using
      compressed_deriv n (fun t => (rotationX t).val) _ rotationX_zero rotationX_deriv
  · simp [Matrix.conjTranspose_smul,Matrix.conjTranspose_add,Spin.lowering,
      smul_add,neg_add_rev]
  · exact fun t X => hcov (rotationX t) X

lemma covariant_generator_y (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n)
    (hcov : Covariant n φ) : CommutesGenerator n φ (Spin.raising n-Spin.lowering n) := by
  apply covariance_differentiation n φ (fun t => action n (rotationY t))
  · exact action_zero n (rotationY 0) rotationY_zero
  · simpa only [action,compressed_collective_y] using
      compressed_deriv n (fun t => (rotationY t).val) _ rotationY_zero rotationY_deriv
  · simp [Spin.lowering,Matrix.conjTranspose_sub,neg_sub]
  · exact fun t X => hcov (rotationY t) X

lemma zAxis_hermitian (n : ℕ) : (Spin.zAxis n)ᴴ=Spin.zAxis n := by
  ext i j
  simp [Spin.zAxis,Spin.magnetic,Matrix.conjTranspose_apply,Matrix.diagonal_apply,eq_comm]
  split_ifs with h
  · subst j; norm_num
    have htwo : (starRingEnd ℂ) (2:ℂ)=2 := by exact map_ofNat (starRingEnd ℂ) 2
    rw [htwo]
  · simp

lemma covariant_generator_z (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n)
    (hcov : Covariant n φ) : CommutesGenerator n φ ((2*Complex.I) • Spin.zAxis n) := by
  apply covariance_differentiation n φ (fun t => action n (rotationZ t))
  · exact action_zero n (rotationZ 0) rotationZ_zero
  · simpa only [action,compressed_collective_z] using
      compressed_deriv n (fun t => (rotationZ t).val) _ rotationZ_zero rotationZ_deriv
  · simp [Matrix.conjTranspose_smul,zAxis_hermitian,neg_smul]
  · exact fun t X => hcov (rotationZ t) X

/-- All-group SU(2) covariance implies the concrete normalized Dicke raising,
lowering and magnetic commutator relations. -/
theorem covariant_generators (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n)
    (hcov : Covariant n φ) :
    CommutesGenerator n φ (Spin.raising n) ∧
    CommutesGenerator n φ (Spin.lowering n) ∧
    CommutesGenerator n φ (Spin.zAxis n) := by
  have hx := covariant_generator_x n φ hcov
  have hy := covariant_generator_y n φ hcov
  have hz := covariant_generator_z n φ hcov
  have he : (-Complex.I/2:ℂ) • (Complex.I • (Spin.raising n+Spin.lowering n)) +
      (1/2:ℂ) • (Spin.raising n-Spin.lowering n)=Spin.raising n := by
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
    linear_combination -(Spin.raising n i j+Spin.lowering n i j)/2*Complex.I_sq
  have hf : (-Complex.I/2:ℂ) • (Complex.I • (Spin.raising n+Spin.lowering n)) +
      (-1/2:ℂ) • (Spin.raising n-Spin.lowering n)=Spin.lowering n := by
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
    linear_combination -(Spin.raising n i j+Spin.lowering n i j)/2*Complex.I_sq
  have hh : (-Complex.I/2:ℂ) • ((2*Complex.I) • Spin.zAxis n)=Spin.zAxis n := by
    ext i j
    simp only [Matrix.smul_apply,smul_eq_mul]
    linear_combination -Spin.zAxis n i j*Complex.I_sq
  constructor
  · rw [←he]
    exact commutesGenerator_add n φ _ _ (commutesGenerator_smul n φ _ _ hx)
      (commutesGenerator_smul n φ _ _ hy)
  constructor
  · rw [←hf]
    exact commutesGenerator_add n φ _ _ (commutesGenerator_smul n φ _ _ hx)
      (commutesGenerator_smul n φ _ _ hy)
  · rw [←hh]
    exact commutesGenerator_smul n φ _ _ hz

end
end SU2T2.Dicke
