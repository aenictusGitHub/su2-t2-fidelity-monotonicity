import SpinHighestWeight
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Concrete normalized spin-N/2 generators in increasing magnetic order. -/
namespace SU2T2.Spin
open Matrix Module
noncomputable section

abbrev Space (N : ℕ) := Fin (N+1) → ℂ
abbrev Mat (N : ℕ) := Matrix (Fin (N+1)) (Fin (N+1)) ℂ

def weight (N k : ℕ) : ℝ := Real.sqrt ((k+1 : ℝ)*((N : ℝ)-k))
def raising (N : ℕ) : Mat N := fun i j => if i.val=j.val+1 then weight N j.val else 0
def magnetic (N : ℕ) (i : Fin (N+1)) : ℂ := (i.val : ℂ) - (N : ℂ)/2
def zAxis (N : ℕ) : Mat N := Matrix.diagonal (magnetic N)
def raisingEnd (N : ℕ) : Module.End ℂ (Space N) := Matrix.toLin' (raising N)
def zEnd (N : ℕ) : Module.End ℂ (Space N) := Matrix.toLin' (zAxis N)
def basis (N : ℕ) : Basis (Fin (N+1)) ℂ (Space N) := Pi.basisFun ℂ (Fin (N+1))

lemma weight_pos (N : ℕ) (k : Fin N) : 0 < weight N k.val := by
  apply Real.sqrt_pos.2
  have hk : (k.val : ℝ) < N := by exact_mod_cast k.isLt
  exact mul_pos (by positivity) (by linarith)

lemma weight_ne_zero (N : ℕ) (k : Fin N) : (weight N k.val : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (weight_pos N k))

lemma raising_basis (N : ℕ) (k : Fin N) :
    raisingEnd N (basis N k.castSucc) = (weight N k.val : ℂ) • basis N k.succ := by
  simp only [raisingEnd, Matrix.toLin'_apply, basis, Pi.basisFun_apply,
    Matrix.mulVec_single_one]
  ext i
  simp only [Matrix.col_apply, raising, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i=k.succ
  · subst i
    simp
  · have hh : i.val ≠ k.val+1 := by
      intro h
      exact hi (Fin.ext h)
    simp [hh, hi]

lemma zAxis_basis (N : ℕ) (k : Fin (N+1)) :
    zEnd N (basis N k) = magnetic N k • basis N k := by
  simp only [zEnd, Matrix.toLin'_apply, basis, Pi.basisFun_apply, zAxis,
    Matrix.diagonal_mulVec_single, mul_one]
  ext i
  by_cases h : i=k
  · subst i; simp
  · simp [h]

lemma magnetic_injective (N : ℕ) : Function.Injective (magnetic N) := by
  intro i j h
  apply Fin.ext
  have hh : (i.val : ℂ) = j.val := by simpa [magnetic] using h
  exact_mod_cast hh

lemma zAxis_raising (N : ℕ) :
    zAxis N * raising N - raising N * zAxis N = raising N := by
  ext i j
  simp only [Matrix.sub_apply, zAxis, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : i.val=j.val+1
  · simp only [raising, if_pos h, magnetic]
    have hc : (i.val : ℂ) = j.val+1 := by exact_mod_cast h
    rw [hc]
    ring
  · simp [raising, h]

lemma zEnd_raisingEnd (N : ℕ) :
    zEnd N * raisingEnd N - raisingEnd N * zEnd N = raisingEnd N := by
  have h := congrArg (fun M : Mat N => Matrix.toLin' M) (zAxis_raising N)
  simpa only [map_sub, Matrix.toLin'_mul, zEnd, raisingEnd,
    Module.End.mul_eq_comp] using h

lemma magnetic_step (N : ℕ) (k : Fin (N+1)) :
    magnetic N k - magnetic N 0 = (k.val : ℂ) := by
  simp [magnetic]

/-- Every infinitesimally covariant superoperator is scalar on the identity. -/
theorem scalar_on_identity (N : ℕ)
    (Φ : Module.End ℂ (Space N) →ₗ[ℂ] Module.End ℂ (Space N))
    (hcovE : ∀ T, Φ (raisingEnd N*T-T*raisingEnd N) =
      raisingEnd N*Φ T-Φ T*raisingEnd N)
    (hcovH : ∀ T, Φ (zEnd N*T-T*zEnd N) = zEnd N*Φ T-Φ T*zEnd N) :
    ∃ c : ℂ, Φ 1 = c • 1 := by
  apply SU2T2.equivariant_highest_weight_scalar (basis N) (raisingEnd N) (zEnd N) 1
    (fun k => (weight N k.val : ℂ)) (weight_ne_zero N) (raising_basis N)
    (magnetic N) (zAxis_basis N) (magnetic_injective N) 0 1 one_ne_zero
    (by simp) (by simp) (by simp) Φ hcovE hcovH

/-- The highest rank-one component is forced to be an eigenoperator. -/
theorem scalar_on_raising (N : ℕ) (hN : 1 ≤ N)
    (Φ : Module.End ℂ (Space N) →ₗ[ℂ] Module.End ℂ (Space N))
    (hcovE : ∀ T, Φ (raisingEnd N*T-T*raisingEnd N) =
      raisingEnd N*Φ T-Φ T*raisingEnd N)
    (hcovH : ∀ T, Φ (zEnd N*T-T*zEnd N) = zEnd N*Φ T-Φ T*zEnd N) :
    ∃ c : ℂ, Φ (raisingEnd N) = c • raisingEnd N := by
  let k : Fin (N+1) := ⟨1, by omega⟩
  let i : Fin N := ⟨0, by omega⟩
  have hzero : raisingEnd N (basis N 0) = (weight N 0 : ℂ) • basis N k := by
    simpa only [i, k] using raising_basis N i
  have hweight : zEnd N*raisingEnd N-raisingEnd N*zEnd N =
      (magnetic N k-magnetic N 0) • raisingEnd N := by
    rw [zEnd_raisingEnd, magnetic_step]
    simp [k]
  exact SU2T2.equivariant_highest_weight_scalar (basis N) (raisingEnd N) (zEnd N)
    (raisingEnd N) (fun i => (weight N i.val : ℂ)) (weight_ne_zero N) (raising_basis N)
    (magnetic N) (zAxis_basis N) (magnetic_injective N) k (weight N 0)
    (weight_ne_zero N i) hzero rfl hweight Φ hcovE hcovH

/-- The highest rank-two component is forced to be an eigenoperator. -/
theorem scalar_on_raising_sq (N : ℕ) (hN : 2 ≤ N)
    (Φ : Module.End ℂ (Space N) →ₗ[ℂ] Module.End ℂ (Space N))
    (hcovE : ∀ T, Φ (raisingEnd N*T-T*raisingEnd N) =
      raisingEnd N*Φ T-Φ T*raisingEnd N)
    (hcovH : ∀ T, Φ (zEnd N*T-T*zEnd N) = zEnd N*Φ T-Φ T*zEnd N) :
    ∃ c : ℂ, Φ (raisingEnd N ^ 2) = c • raisingEnd N ^ 2 := by
  let E := raisingEnd N
  let H := zEnd N
  let k : Fin (N+1) := ⟨2, by omega⟩
  let i₀ : Fin N := ⟨0, by omega⟩
  let i₁ : Fin N := ⟨1, by omega⟩
  have hzero : (E^2) (basis N 0) =
      ((weight N 0 : ℂ)*(weight N 1 : ℂ)) • basis N k := by
    change E (E (basis N 0)) = _
    have h₀ := raising_basis N i₀
    have h₁ := raising_basis N i₁
    change E (basis N 0) = (weight N 0 : ℂ) • basis N i₁.castSucc at h₀
    change E (basis N i₁.castSucc) = (weight N 1 : ℂ) • basis N k at h₁
    rw [h₀, map_smul, h₁, smul_smul]
  have hcomm : E*(E^2) = (E^2)*E := by noncomm_ring
  have hweight : H*(E^2)-(E^2)*H = (magnetic N k-magnetic N 0) • E^2 := by
    rw [magnetic_step]
    change H*E^2-E^2*H = (2 : ℂ) • E^2
    have h := zEnd_raisingEnd N
    change H*E-E*H=E at h
    calc
      H*E^2-E^2*H = (H*E-E*H)*E+E*(H*E-E*H) := by
        simp only [pow_two, sub_mul, mul_sub, mul_assoc]
        abel
      _ = E*E+E*E := by rw [h]
      _ = (2 : ℂ) • E^2 := by rw [two_smul]; noncomm_ring
  exact SU2T2.equivariant_highest_weight_scalar (basis N) E H (E^2)
    (fun i => (weight N i.val : ℂ)) (weight_ne_zero N) (raising_basis N)
    (magnetic N) (zAxis_basis N) (magnetic_injective N) k _
    (mul_ne_zero (weight_ne_zero N i₀) (weight_ne_zero N i₁)) hzero hcomm hweight
    Φ hcovE hcovH

def lowering (N : ℕ) : Mat N := (raising N)ᴴ

def loweringEnd (N : ℕ) : Module.End ℂ (Space N) := Matrix.toLin' (lowering N)

lemma weight_sq (N : ℕ) (k : Fin N) :
    (weight N k.val)^2 = (k.val+1 : ℝ)*((N : ℝ)-k.val) := by
  apply Real.sq_sqrt
  have hk : (k.val : ℝ) < N := by exact_mod_cast k.isLt
  exact mul_nonneg (by positivity) (by linarith)

lemma weight_sq_complex (N : ℕ) (k : Fin N) :
    (weight N k.val : ℂ)^2 = (k.val+1 : ℂ)*((N : ℂ)-k.val) := by
  exact_mod_cast weight_sq N k

lemma raising_col (N : ℕ) (k : Fin N) (i : Fin (N+1)) :
    raising N i k.castSucc = if i=k.succ then (weight N k.val : ℂ) else 0 := by
  by_cases h : i=k.succ
  · subst i; simp [raising]
  · have hh : i.val ≠ k.val+1 := by intro hh; exact h (Fin.ext hh)
    simp [raising, h, hh]

lemma raising_row (N : ℕ) (k : Fin N) (j : Fin (N+1)) :
    raising N k.succ j = if j=k.castSucc then (weight N k.val : ℂ) else 0 := by
  by_cases h : j=k.castSucc
  · subst j; simp [raising]
  · have hh : k.val ≠ j.val := by
      intro hh
      apply h
      apply Fin.ext
      change j.val = k.val
      omega
    simp [raising, h, hh]

lemma raising_first_row (N : ℕ) (j : Fin (N+1)) : raising N 0 j = 0 := by
  simp [raising]

lemma raising_last_col (N : ℕ) (i : Fin (N+1)) : raising N i (Fin.last N) = 0 := by
  have h : i.val ≠ N+1 := by omega
  simp [raising, h]

lemma raising_lowering (N : ℕ) :
    raising N*lowering N = Matrix.diagonal
      (fun i : Fin (N+1) => (i.val : ℂ)*((N : ℂ)+1-i.val)) := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [Matrix.mul_apply, raising_first_row, Matrix.diagonal_apply]
  · simp only [Matrix.mul_apply, raising_row, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [lowering, Matrix.conjTranspose_apply, raising_col]
    by_cases h : j=k.succ
    · subst j
      simp only [ite_true, Complex.star_def, Complex.conj_ofReal, Matrix.diagonal_apply_eq, Fin.val_succ]
      rw [← pow_two, weight_sq_complex]
      push_cast
      ring
    · have hh : k.succ ≠ j := Ne.symm h
      simp [h, hh, Matrix.diagonal_apply]

lemma lowering_raising (N : ℕ) :
    lowering N*raising N = Matrix.diagonal
      (fun i : Fin (N+1) => (i.val+1 : ℂ)*((N : ℂ)-i.val)) := by
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [Matrix.mul_apply, lowering, Matrix.conjTranspose_apply, raising_last_col,
      Matrix.diagonal_apply]
  · simp only [Matrix.mul_apply, lowering, Matrix.conjTranspose_apply, raising_col]
    simp only [apply_ite, star_zero, Complex.star_def, Complex.conj_ofReal, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [raising_row]
    by_cases h : j=k.castSucc
    · subst j
      simp only [ite_true, Matrix.diagonal_apply_eq]
      rw [← pow_two, weight_sq_complex]
      rfl
    · have hh : k.castSucc ≠ j := Ne.symm h
      simp [h, hh, Matrix.diagonal_apply]

lemma raising_lowering_commutator (N : ℕ) :
    raising N*lowering N-lowering N*raising N = (2 : ℂ) • zAxis N := by
  rw [raising_lowering, lowering_raising]
  ext i j
  by_cases h : i=j
  · subst j
    simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      zAxis, smul_eq_mul, magnetic]
    ring
  · simp [h, Matrix.diagonal_apply, zAxis]

def xAxis (N : ℕ) : Mat N := (1/2 : ℂ) • (raising N + lowering N)
def yAxis (N : ℕ) : Mat N := (-Complex.I/2 : ℂ) • (raising N - lowering N)
def casimir (N : ℕ) : ℝ := (N : ℝ)*((N : ℝ)+2)/4

lemma xAxis_yAxis (N : ℕ) :
    xAxis N*yAxis N-yAxis N*xAxis N = Complex.I • zAxis N := by
  have h := raising_lowering_commutator N
  calc
    xAxis N*yAxis N-yAxis N*xAxis N =
        (Complex.I/2 : ℂ) • (raising N*lowering N-lowering N*raising N) := by
      simp only [xAxis, yAxis, smul_mul_smul, add_mul, mul_add, sub_mul, mul_sub]
      module
    _ = _ := by rw [h, smul_smul]; congr 1; ring

lemma zAxis_lowering (N : ℕ) :
    zAxis N*lowering N-lowering N*zAxis N = -lowering N := by
  have h := congrArg Matrix.conjTranspose (zAxis_raising N)
  have hz : (zAxis N)ᴴ = zAxis N := by
    ext i j
    simp only [zAxis, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : i=j
    · subst j; simp [magnetic, Complex.star_def]
    · simp [h, Ne.symm h]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hz] at h
  change lowering N*zAxis N-zAxis N*lowering N=lowering N at h
  calc
    zAxis N*lowering N-lowering N*zAxis N = -(lowering N*zAxis N-zAxis N*lowering N) := by abel
    _ = _ := by rw [h]

lemma yAxis_zAxis (N : ℕ) :
    yAxis N*zAxis N-zAxis N*yAxis N = Complex.I • xAxis N := by
  have hE := zAxis_raising N
  have hF := zAxis_lowering N
  calc
    yAxis N*zAxis N-zAxis N*yAxis N =
        (Complex.I/2 : ℂ) • ((zAxis N*raising N-raising N*zAxis N)-
        (zAxis N*lowering N-lowering N*zAxis N)) := by
      simp only [yAxis, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub]
      module
    _ = _ := by rw [hE,hF]; simp only [xAxis]; module

lemma zAxis_xAxis (N : ℕ) :
    zAxis N*xAxis N-xAxis N*zAxis N = Complex.I • yAxis N := by
  have hE := zAxis_raising N
  have hF := zAxis_lowering N
  calc
    zAxis N*xAxis N-xAxis N*zAxis N =
        (1/2 : ℂ) • ((zAxis N*raising N-raising N*zAxis N)+
        (zAxis N*lowering N-lowering N*zAxis N)) := by
      simp only [xAxis, smul_mul_assoc, mul_smul_comm, add_mul, mul_add]
      module
    _ = _ := by
      rw [hE,hF]
      simp only [yAxis, smul_smul]
      match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

lemma xAxis_sq_add_yAxis_sq (N : ℕ) :
    xAxis N*xAxis N+yAxis N*yAxis N =
      (1/2 : ℂ) • (raising N*lowering N+lowering N*raising N) := by
  simp only [xAxis,yAxis,smul_mul_smul,add_mul,mul_add,sub_mul,mul_sub]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

lemma casimir_identity (N : ℕ) :
    xAxis N*xAxis N+yAxis N*yAxis N+zAxis N*zAxis N = (casimir N : ℂ) • 1 := by
  rw [xAxis_sq_add_yAxis_sq,raising_lowering,lowering_raising]
  ext i j
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,zAxis,
    Matrix.diagonal_mul_diagonal]
  by_cases h : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    simp only [magnetic,casimir]
    push_cast
    ring
  · simp [h,Matrix.diagonal_apply]

end
end SU2T2.Spin
