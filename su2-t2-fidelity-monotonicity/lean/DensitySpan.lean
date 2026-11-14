import DickeSU2

namespace SU2T2.Dicke
open Matrix
open scoped ComplexOrder
noncomputable section

/-- A complex-linear matrix map vanishing on density matrices vanishes on
all matrices. The proof uses normalization of positive matrices and a
four-term polarization identity. -/
lemma linearMap_zero_of_density {d : Type*} [Fintype d] [DecidableEq d]
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hL : ∀ ρ : Matrix d d ℂ, ρ.PosSemidef → ρ.trace=1 → L ρ=0) :
    ∀ X, L X=0 := by
  have hpos (A : Matrix d d ℂ) (hA : A.PosSemidef) : L A=0 := by
    by_cases hz : A.trace=0
    · rw [hA.trace_eq_zero_iff.mp hz,map_zero]
    have htr := Complex.nonneg_iff.mp hA.trace_nonneg
    have he : (A.trace.re:ℂ)=A.trace := by
      apply Complex.ext
      · rfl
      · simpa using htr.2
    have hr : A.trace.re≠0 := by
      intro h
      apply hz
      rw [←he,h,Complex.ofReal_zero]
    have hi : (0:ℂ)≤((A.trace.re)⁻¹:ℝ) := by
      exact_mod_cast (inv_nonneg.mpr htr.1)
    have hρ := hL ((((A.trace.re)⁻¹:ℝ):ℂ) • A) (hA.smul hi) (by
      rw [Matrix.trace_smul,smul_eq_mul,←he,Complex.ofReal_re,←Complex.ofReal_mul,inv_mul_cancel₀ hr]
      rfl)
    rw [map_smul] at hρ
    exact (smul_eq_zero.mp hρ).resolve_left (by exact_mod_cast inv_ne_zero hr)
  have hGram (A : Matrix d d ℂ) : L (A*Aᴴ)=0 :=
    hpos _ (Matrix.posSemidef_self_mul_conjTranspose A)
  intro X
  have hpol : (4:ℂ) • X =
      ((X+1)*(X+1)ᴴ-(X-1)*(X-1)ᴴ) +
      Complex.I • ((X+Complex.I • 1)*(X+Complex.I • 1)ᴴ-
        (X-Complex.I • 1)*(X-Complex.I • 1)ᴴ) := by
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one,Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_I]
    simp only [Matrix.add_mul,Matrix.sub_mul,Matrix.mul_add,Matrix.mul_sub,
      Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,
      smul_add,smul_sub,smul_smul]
    simp only [neg_mul,mul_neg,Complex.I_mul_I]
    module
  have h := congrArg L hpol
  simp only [map_smul,map_add,map_sub,hGram,sub_self,smul_zero,add_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

/-- The state-level covariance condition used in the manuscript. -/
def CovariantStates (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n) : Prop :=
  ∀ (U : SU2) (ρ : Spin.Mat n), ρ.PosSemidef → ρ.trace=1 →
    φ (action n U*ρ*(action n U)ᴴ)=action n U*φ ρ*(action n U)ᴴ

lemma covariant_of_covariantStates (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n)
    (hcov : CovariantStates n φ) : Covariant n φ := by
  intro U X
  let L : Spin.Mat n →ₗ[ℂ] Spin.Mat n := {
    toFun := fun Y => φ (action n U*Y*(action n U)ᴴ)-action n U*φ Y*(action n U)ᴴ
    map_add' := by
      intro Y Z
      simp only [Matrix.mul_add,Matrix.add_mul,map_add]
      abel
    map_smul' := by
      intro c Y
      simp only [Matrix.mul_smul,Matrix.smul_mul,map_smul,smul_sub,RingHom.id_apply] }
  exact sub_eq_zero.mp (linearMap_zero_of_density L (by
    intro ρ hρ htr
    exact sub_eq_zero.mpr (hcov U ρ hρ htr)) X)

lemma covariantStates_iff_covariant (n : ℕ) (φ : Spin.Mat n →ₗ[ℂ] Spin.Mat n) :
    CovariantStates n φ ↔ Covariant n φ :=
  ⟨covariant_of_covariantStates n φ,fun h U ρ _ _ => h U ρ⟩

end
end SU2T2.Dicke
