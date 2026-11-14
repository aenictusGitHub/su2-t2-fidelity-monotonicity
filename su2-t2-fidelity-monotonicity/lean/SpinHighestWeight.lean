import Mathlib.Tactic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Uniqueness of highest-weight operators

These algebraic lemmas provide a route from covariance with spin generators to
scalar action on the first two tensor ranks, without Clebsch–Gordan theory.
The concrete spin representation and the passage from group covariance to the
generator identities must be instantiated separately.
-/

namespace SU2T2
open Module
noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A map commuting with a nondegenerate ladder is determined by the lowest
basis vector. Every ladder coefficient is explicit in the hypothesis. -/
theorem eq_of_commute_ladder {N : ℕ} (b : Basis (Fin (N+1)) ℂ V)
    (E X Y : Module.End ℂ V) (w : Fin N → ℂ)
    (hw : ∀ i, w i ≠ 0)
    (hE : ∀ i : Fin N, E (b i.castSucc) = w i • b i.succ)
    (hX : ∀ v, E (X v) = X (E v))
    (hY : ∀ v, E (Y v) = Y (E v))
    (hzero : X (b 0) = Y (b 0)) : X = Y := by
  apply b.ext
  intro i
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact hzero
  | succ i ih =>
    have hiN : i < N := by omega
    let k : Fin N := ⟨i, hiN⟩
    have hprev : X (b k.castSucc) = Y (b k.castSucc) := ih (by omega)
    have heq := congrArg E hprev
    rw [hX, hY, hE, map_smul, map_smul] at heq
    exact (smul_right_injective V (hw k)) heq

/-- Coordinates of a diagonal operator in its given basis. -/
theorem repr_diagonal_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ V) (H : Module.End ℂ V) (μ : ι → ℂ)
    (hH : ∀ i, H (b i) = μ i • b i) (v : V) (i : ι) :
    b.repr (H v) i = μ i * b.repr v i := by
  have hv : H v = ∑ j, b.repr v j • (μ j • b j) := by
    calc
      H v = H (∑ j, b.repr v j • b j) := congrArg H (b.sum_repr v).symm
      _ = _ := by simp only [map_sum, map_smul, hH]
  rw [hv]
  simp [smul_smul, mul_comm, Finsupp.single_apply]

/-- A simple diagonal eigenvalue has a one-dimensional eigenspace. -/
theorem eigenvector_scalar_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ V) (H : Module.End ℂ V) (μ : ι → ℂ)
    (hH : ∀ i, H (b i) = μ i • b i) (hμ : Function.Injective μ)
    (k : ι) (v : V) (hv : H v = μ k • v) :
    v = (b.repr v k) • b k := by
  apply b.repr.injective
  ext i
  by_cases hik : i = k
  · subst i; simp
  · have hi : μ i ≠ μ k := fun h => hik (hμ h)
    have hh := congrArg (fun z => b.repr z i) hv
    change b.repr (H v) i = b.repr (μ k • v) i at hh
    rw [repr_diagonal_apply b H μ hH] at hh
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hh
    have hz : b.repr v i = 0 := by
      apply (mul_eq_zero.mp (show (μ i-μ k)*b.repr v i=0 by linear_combination hh)).resolve_left
      exact sub_ne_zero.mpr hi
    simp [hz, hik]

/-- Highest-weight uniqueness, stated for any comparison operator B with
nonzero action on the lowest vector. -/
theorem highest_weight_scalar {N : ℕ} (b : Basis (Fin (N+1)) ℂ V)
    (E H X B : Module.End ℂ V) (w : Fin N → ℂ)
    (hw : ∀ i, w i ≠ 0)
    (hE : ∀ i : Fin N, E (b i.castSucc) = w i • b i.succ)
    (μ : Fin (N+1) → ℂ) (hH : ∀ i, H (b i) = μ i • b i)
    (hμ : Function.Injective μ) (k : Fin (N+1)) (β : ℂ) (hβ : β ≠ 0)
    (hBzero : B (b 0) = β • b k)
    (hX : ∀ v, E (X v) = X (E v))
    (hB : ∀ v, E (B v) = B (E v))
    (hweight : ∀ v, H (X v) - X (H v) = (μ k - μ 0) • X v) :
    ∃ c : ℂ, X = c • B := by
  have heig : H (X (b 0)) = μ k • X (b 0) := by
    have h := hweight (b 0)
    rw [hH, map_smul] at h
    rw [sub_smul] at h
    exact (sub_left_inj).mp h
  have hxzero := eigenvector_scalar_basis b H μ hH hμ k (X (b 0)) heig
  let c := b.repr (X (b 0)) k / β
  refine ⟨c, eq_of_commute_ladder b E X (c • B) w hw hE hX ?_ ?_⟩
  · intro v
    simpa only [LinearMap.smul_apply, map_smul] using congrArg (fun z => c • z) (hB v)
  · simp only [LinearMap.smul_apply, hBzero, smul_smul]
    rw [hxzero]
    congr 1
    exact (div_mul_cancel₀ _ hβ).symm

/-- Intertwining the two infinitesimal spin actions forces scalar action on
any highest-weight operator in the nondegenerate ladder representation. -/
theorem equivariant_highest_weight_scalar {N : ℕ}
    (b : Basis (Fin (N+1)) ℂ V) (E H B : Module.End ℂ V)
    (w : Fin N → ℂ) (hw : ∀ i, w i ≠ 0)
    (hE : ∀ i : Fin N, E (b i.castSucc) = w i • b i.succ)
    (μ : Fin (N+1) → ℂ) (hH : ∀ i, H (b i) = μ i • b i)
    (hμ : Function.Injective μ) (k : Fin (N+1)) (β : ℂ) (hβ : β ≠ 0)
    (hBzero : B (b 0) = β • b k)
    (hEB : E * B = B * E)
    (hHB : H * B - B * H = (μ k - μ 0) • B)
    (Φ : Module.End ℂ V →ₗ[ℂ] Module.End ℂ V)
    (hcovE : ∀ T, Φ (E*T-T*E) = E*Φ T-Φ T*E)
    (hcovH : ∀ T, Φ (H*T-T*H) = H*Φ T-Φ T*H) :
    ∃ c : ℂ, Φ B = c • B := by
  apply highest_weight_scalar b E H (Φ B) B w hw hE μ hH hμ k β hβ hBzero
  · intro v
    have h := hcovE B
    rw [hEB, sub_self, map_zero] at h
    exact congrArg (fun T : Module.End ℂ V => T v) (sub_eq_zero.mp h.symm)
  · intro v
    exact congrArg (fun T : Module.End ℂ V => T v) hEB
  · intro v
    have h := hcovH B
    rw [hHB, map_smul] at h
    exact congrArg (fun T : Module.End ℂ V => T v) h.symm

end
end SU2T2
