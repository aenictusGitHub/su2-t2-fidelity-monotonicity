import SpinGenerators
import SU2Choi
import TraceDual

/-! Concrete consequences of infinitesimal covariance for the first two spin ranks. -/
namespace SU2T2.Spin
open Matrix Module
open scoped ComplexOrder
noncomputable section

/-- Covariance under the commutator with one specified generator. -/
def CommutesWithCommutator {N : ℕ} (φ : Mat N →ₗ[ℂ] Mat N) (G : Mat N) : Prop :=
  ∀ A, φ (G*A-A*G) = G*φ A-φ A*G

def endSuperoperator {N : ℕ} (φ : Mat N →ₗ[ℂ] Mat N) :
    Module.End ℂ (Space N) →ₗ[ℂ] Module.End ℂ (Space N) :=
  (Matrix.toLinAlgEquiv'.toLinearMap).comp
    (φ.comp Matrix.toLinAlgEquiv'.symm.toLinearMap)

lemma endSuperoperator_apply {N : ℕ} (φ : Mat N →ₗ[ℂ] Mat N) (A : Mat N) :
    endSuperoperator φ (Matrix.toLinAlgEquiv' A) = Matrix.toLinAlgEquiv' (φ A) := by
  simp [endSuperoperator]

lemma endSuperoperator_covariant {N : ℕ} (φ : Mat N →ₗ[ℂ] Mat N) (G : Mat N)
    (h : CommutesWithCommutator φ G) :
    ∀ T, endSuperoperator φ (Matrix.toLinAlgEquiv' G*T-T*Matrix.toLinAlgEquiv' G) =
      Matrix.toLinAlgEquiv' G*endSuperoperator φ T-
      endSuperoperator φ T*Matrix.toLinAlgEquiv' G := by
  intro T
  obtain ⟨A,rfl⟩ := Matrix.toLinAlgEquiv'.surjective T
  simp only [← map_mul, ← map_sub, endSuperoperator_apply]
  rw [h]

lemma scalar_identity_matrix (N : ℕ) (φ : Mat N →ₗ[ℂ] Mat N)
    (hE : CommutesWithCommutator φ (raising N))
    (hH : CommutesWithCommutator φ (zAxis N)) :
    ∃ c : ℂ, φ 1 = c • 1 := by
  obtain ⟨c,hc⟩ := scalar_on_identity N (endSuperoperator φ)
    (endSuperoperator_covariant φ (raising N) hE)
    (endSuperoperator_covariant φ (zAxis N) hH)
  refine ⟨c, ?_⟩
  apply Matrix.toLinAlgEquiv'.injective
  have heone : Matrix.toLinAlgEquiv' (1 : Mat N) = 1 := map_one _
  rw [map_smul, heone]
  have he : Matrix.toLinAlgEquiv' (φ (1 : Mat N)) = endSuperoperator φ 1 := by
    rw [← endSuperoperator_apply, heone]
  rw [he, hc]

lemma scalar_raising_matrix (N : ℕ) (hN : 1 ≤ N) (φ : Mat N →ₗ[ℂ] Mat N)
    (hE : CommutesWithCommutator φ (raising N))
    (hH : CommutesWithCommutator φ (zAxis N)) :
    ∃ c : ℂ, φ (raising N) = c • raising N := by
  obtain ⟨c,hc⟩ := scalar_on_raising N hN (endSuperoperator φ)
    (endSuperoperator_covariant φ (raising N) hE)
    (endSuperoperator_covariant φ (zAxis N) hH)
  refine ⟨c, ?_⟩
  apply Matrix.toLinAlgEquiv'.injective
  change endSuperoperator φ (Matrix.toLinAlgEquiv' (raising N)) =
    c • Matrix.toLinAlgEquiv' (raising N) at hc
  simpa only [endSuperoperator_apply, map_smul] using hc

lemma scalar_raising_sq_matrix (N : ℕ) (hN : 2 ≤ N) (φ : Mat N →ₗ[ℂ] Mat N)
    (hE : CommutesWithCommutator φ (raising N))
    (hH : CommutesWithCommutator φ (zAxis N)) :
    ∃ c : ℂ, φ (raising N * raising N) = c • (raising N * raising N) := by
  obtain ⟨c,hc⟩ := scalar_on_raising_sq N hN (endSuperoperator φ)
    (endSuperoperator_covariant φ (raising N) hE)
    (endSuperoperator_covariant φ (zAxis N) hH)
  refine ⟨c, ?_⟩
  apply Matrix.toLinAlgEquiv'.injective
  have he : Matrix.toLinAlgEquiv' (raising N * raising N) = raisingEnd N ^ 2 := by
    rw [map_mul, pow_two]
    rfl
  rw [← he, endSuperoperator_apply] at hc
  simpa only [map_smul] using hc

lemma hermitian_eigenvalue_real {n : ℕ} (φ : Choi.Mat n →ₗ[ℂ] Choi.Mat n)
    (hstar : ∀ X, φ Xᴴ = (φ X)ᴴ) (A : Choi.Mat n) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (c : ℂ) (heig : φ A = c • A) : ∃ r : ℝ, c = r := by
  have h : (φ A)ᴴ = φ A := by rw [← hstar, hA.eq]
  rw [heig, Matrix.conjTranspose_smul, hA.eq] at h
  have hc : star c = c := smul_left_injective ℂ hA0 h
  exact Complex.conj_eq_iff_real.mp hc

lemma zAxis_isHermitian (N : ℕ) : (zAxis N).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp only [zAxis, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst j; simp [magnetic]
  · simp [h, Ne.symm h]

lemma zAxis_ne_zero (N : ℕ) (hN : 1 ≤ N) : zAxis N ≠ 0 := by
  intro h
  have hh := congrArg (fun A : Mat N => A 0 0) h
  simp [zAxis, magnetic] at hh
  exact (by omega : N ≠ 0) hh

lemma eigen_commutator {N : ℕ} (φ : Mat N →ₗ[ℂ] Mat N) (G A : Mat N)
    (hG : CommutesWithCommutator φ G) (c : ℂ) (hA : φ A = c • A) :
    φ (G*A-A*G) = c • (G*A-A*G) := by
  rw [hG, hA]
  simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

lemma eigen_remove_smul {N : ℕ} (φ : Mat N →ₗ[ℂ] Mat N)
    (A : Mat N) (c d : ℂ) (hd : d ≠ 0)
    (h : φ (d • A) = c • (d • A)) : φ A = c • A := by
  rw [map_smul, smul_comm c d] at h
  exact (smul_right_injective _ hd) h

lemma lowering_raising_commutator (N : ℕ) :
    lowering N*raising N-raising N*lowering N = (-2 : ℂ) • zAxis N := by
  have h := raising_lowering_commutator N
  calc
    _ = -(raising N*lowering N-lowering N*raising N) := by abel
    _ = _ := by rw [h]; module

lemma dipole_scalar (N : ℕ) (hN : 1 ≤ N) (φ : Mat N →ₗ[ℂ] Mat N)
    (hE : CommutesWithCommutator φ (raising N))
    (hH : CommutesWithCommutator φ (zAxis N))
    (hF : CommutesWithCommutator φ (lowering N))
    (hstar : ∀ A, φ Aᴴ = (φ A)ᴴ) :
    ∃ f : ℝ, φ (xAxis N) = (f : ℂ) • xAxis N ∧
      φ (yAxis N) = (f : ℂ) • yAxis N ∧ φ (zAxis N) = (f : ℂ) • zAxis N := by
  obtain ⟨c, hc⟩ := scalar_raising_matrix N hN φ hE hH
  have hz := eigen_commutator φ (lowering N) (raising N) hF c hc
  rw [lowering_raising_commutator] at hz
  have hzc := eigen_remove_smul φ (zAxis N) c (-2) (by norm_num) hz
  obtain ⟨f, rfl⟩ := hermitian_eigenvalue_real φ hstar (zAxis N)
    (zAxis_isHermitian N) (zAxis_ne_zero N hN) c hzc
  have hf : φ (lowering N) = (f : ℂ) • lowering N := by
    rw [lowering, hstar, hc, Matrix.conjTranspose_smul]
    simp
  refine ⟨f, ?_, ?_, hzc⟩
  · simp only [xAxis, map_smul, map_add, hc, hf]
    module
  · simp only [yAxis, map_smul, map_sub, hc, hf]
    module

lemma unital_of_trace_preserving (N : ℕ) (φ : Mat N →ₗ[ℂ] Mat N)
    (hE : CommutesWithCommutator φ (raising N))
    (hH : CommutesWithCommutator φ (zAxis N))
    (hTP : ∀ A, (φ A).trace = A.trace) : φ 1 = 1 := by
  obtain ⟨c,hc⟩ := scalar_identity_matrix N φ hE hH
  have htr := hTP 1
  rw [hc, Matrix.trace_smul] at htr
  have hn : ((N+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : N+1 ≠ 0)
  have hc1 : c = 1 := by
    simp only [Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htr
    apply mul_right_cancel₀ hn
    simpa using htr
  simpa [hc1] using hc

def quadrupoleZ (N : ℕ) : Mat N :=
  zAxis N*zAxis N - ((casimir N : ℂ)/3) • 1

lemma quadrupoleZ_isHermitian (N : ℕ) : (quadrupoleZ N).IsHermitian := by
  unfold Matrix.IsHermitian quadrupoleZ
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    (zAxis_isHermitian N).eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

lemma quadrupoleZ_first_entry (N : ℕ) :
    quadrupoleZ N 0 0 = (N : ℂ)*((N : ℂ)-1)/6 := by
  simp only [quadrupoleZ, Matrix.sub_apply, zAxis, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one, magnetic, Fin.val_zero, Nat.cast_zero, zero_sub, casimir]
  push_cast
  ring

lemma quadrupoleZ_ne_zero (N : ℕ) (hN : 2 ≤ N) : quadrupoleZ N ≠ 0 := by
  intro h
  have hh := congrArg (fun A : Mat N => A 0 0) h
  change quadrupoleZ N 0 0 = 0 at hh
  rw [quadrupoleZ_first_entry] at hh
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hn1 : (N : ℂ)-1 ≠ 0 := by
    intro he
    have hn1 : (N : ℂ) = 1 := sub_eq_zero.mp he
    have : N = 1 := by exact_mod_cast hn1
    omega
  exact (div_ne_zero (mul_ne_zero hn hn1) (by norm_num)) hh

lemma lowering_zAxis_commutator (N : ℕ) :
    lowering N*zAxis N-zAxis N*lowering N = lowering N := by
  have h := zAxis_lowering N
  calc
    _ = -(zAxis N*lowering N-lowering N*zAxis N) := by abel
    _ = _ := by rw [h, neg_neg]

lemma lowering_raising_sq_commutator (N : ℕ) :
    lowering N*(raising N*raising N)-(raising N*raising N)*lowering N =
      (-2 : ℂ) • (zAxis N*raising N+raising N*zAxis N) := by
  calc
    _ = (lowering N*raising N-raising N*lowering N)*raising N+
        raising N*(lowering N*raising N-raising N*lowering N) := by noncomm_ring
    _ = _ := by
      rw [lowering_raising_commutator]
      simp only [smul_mul_assoc, mul_smul_comm, smul_add]

lemma raising_lowering_sum (N : ℕ) :
    lowering N*raising N+raising N*lowering N =
      (2 : ℂ) • ((casimir N : ℂ) • 1-zAxis N*zAxis N) := by
  calc
    _ = (2 : ℂ) • (((1/2 : ℂ) •
        (raising N*lowering N+lowering N*raising N)+zAxis N*zAxis N)-
        zAxis N*zAxis N) := by module
    _ = _ := by rw [← xAxis_sq_add_yAxis_sq, casimir_identity]

lemma lowering_zRaising_commutator (N : ℕ) :
    lowering N*(zAxis N*raising N+raising N*zAxis N)-
      (zAxis N*raising N+raising N*zAxis N)*lowering N =
      (-6 : ℂ) • quadrupoleZ N := by
  calc
    _ = (lowering N*zAxis N-zAxis N*lowering N)*raising N+
        zAxis N*(lowering N*raising N-raising N*lowering N)+
        (lowering N*raising N-raising N*lowering N)*zAxis N+
        raising N*(lowering N*zAxis N-zAxis N*lowering N) := by noncomm_ring
    _ = lowering N*raising N+raising N*lowering N-
        (4 : ℂ) • (zAxis N*zAxis N) := by
      rw [lowering_zAxis_commutator, lowering_raising_commutator]
      simp only [smul_mul_assoc, mul_smul_comm]
      module
    _ = _ := by
      rw [raising_lowering_sum]
      unfold quadrupoleZ
      module

lemma xAxis_isHermitian (N : ℕ) : (xAxis N).IsHermitian := by
  unfold Matrix.IsHermitian xAxis lowering
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose]
  norm_num
  module

lemma yAxis_isHermitian (N : ℕ) : (yAxis N).IsHermitian := by
  unfold Matrix.IsHermitian yAxis lowering
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  norm_num [Complex.star_def]
  module

lemma xAxis_sq_sub_yAxis_sq (N : ℕ) :
    xAxis N*xAxis N-yAxis N*yAxis N =
      (1/2 : ℂ) • (raising N*raising N+lowering N*lowering N) := by
  simp only [xAxis,yAxis,smul_mul_smul,add_mul,mul_add,sub_mul,mul_sub]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

lemma xy_anticommutator (N : ℕ) :
    xAxis N*yAxis N+yAxis N*xAxis N =
      (-Complex.I/2 : ℂ) • (raising N*raising N-lowering N*lowering N) := by
  simp only [xAxis,yAxis,smul_mul_smul,add_mul,mul_add,sub_mul,mul_sub]
  module

lemma yz_anticommutator (N : ℕ) :
    yAxis N*zAxis N+zAxis N*yAxis N =
      (-Complex.I/2 : ℂ) • ((zAxis N*raising N+raising N*zAxis N)-
        (zAxis N*lowering N+lowering N*zAxis N)) := by
  simp only [yAxis,smul_mul_assoc,mul_smul_comm,sub_mul,mul_sub]
  module

lemma zx_anticommutator (N : ℕ) :
    zAxis N*xAxis N+xAxis N*zAxis N =
      (1/2 : ℂ) • ((zAxis N*raising N+raising N*zAxis N)+
        (zAxis N*lowering N+lowering N*zAxis N)) := by
  simp only [xAxis,smul_mul_assoc,mul_smul_comm,add_mul,mul_add]
  module

lemma quadrupoleX_decomposition (N : ℕ) :
    xAxis N*xAxis N-((casimir N : ℂ)/3) • 1 =
      (1/2 : ℂ) • ((1/2 : ℂ) •
        (raising N*raising N+lowering N*lowering N)-quadrupoleZ N) := by
  calc
    _ = (1/2 : ℂ) • ((xAxis N*xAxis N-yAxis N*yAxis N)-quadrupoleZ N)+
        (1/2 : ℂ) • ((xAxis N*xAxis N+yAxis N*yAxis N+zAxis N*zAxis N)-
          (casimir N : ℂ) • 1) := by unfold quadrupoleZ; module
    _ = _ := by rw [casimir_identity,xAxis_sq_sub_yAxis_sq]; module

lemma quadrupoleY_decomposition (N : ℕ) :
    yAxis N*yAxis N-((casimir N : ℂ)/3) • 1 =
      (1/2 : ℂ) • (-(1/2 : ℂ) •
        (raising N*raising N+lowering N*lowering N)-quadrupoleZ N) := by
  calc
    _ = (1/2 : ℂ) • (-(xAxis N*xAxis N-yAxis N*yAxis N)-quadrupoleZ N)+
        (1/2 : ℂ) • ((xAxis N*xAxis N+yAxis N*yAxis N+zAxis N*zAxis N)-
          (casimir N : ℂ) • 1) := by unfold quadrupoleZ; module
    _ = _ := by rw [casimir_identity,xAxis_sq_sub_yAxis_sq]; module

lemma quadrupole_scalar (N : ℕ) (hN : 2 ≤ N) (φ : Mat N →ₗ[ℂ] Mat N)
    (hE : CommutesWithCommutator φ (raising N))
    (hH : CommutesWithCommutator φ (zAxis N))
    (hF : CommutesWithCommutator φ (lowering N))
    (hstar : ∀ A, φ Aᴴ = (φ A)ᴴ) :
    ∃ g : ℝ,
      φ (xAxis N*xAxis N-((casimir N : ℂ)/3) • 1) =
        (g : ℂ) • (xAxis N*xAxis N-((casimir N : ℂ)/3) • 1) ∧
      φ (yAxis N*yAxis N-((casimir N : ℂ)/3) • 1) =
        (g : ℂ) • (yAxis N*yAxis N-((casimir N : ℂ)/3) • 1) ∧
      φ (zAxis N*zAxis N-((casimir N : ℂ)/3) • 1) =
        (g : ℂ) • (zAxis N*zAxis N-((casimir N : ℂ)/3) • 1) ∧
      φ (xAxis N*yAxis N+yAxis N*xAxis N) =
        (g : ℂ) • (xAxis N*yAxis N+yAxis N*xAxis N) ∧
      φ (yAxis N*zAxis N+zAxis N*yAxis N) =
        (g : ℂ) • (yAxis N*zAxis N+zAxis N*yAxis N) ∧
      φ (zAxis N*xAxis N+xAxis N*zAxis N) =
        (g : ℂ) • (zAxis N*xAxis N+xAxis N*zAxis N) := by
  obtain ⟨c,hc⟩ := scalar_raising_sq_matrix N hN φ hE hH
  have hs := eigen_commutator φ (lowering N) (raising N*raising N) hF c hc
  rw [lowering_raising_sq_commutator] at hs
  have hsc := eigen_remove_smul φ _ c (-2) (by norm_num) hs
  have hz := eigen_commutator φ (lowering N) _ hF c hsc
  rw [lowering_zRaising_commutator] at hz
  have hzc := eigen_remove_smul φ _ c (-6) (by norm_num) hz
  obtain ⟨g,rfl⟩ := hermitian_eigenvalue_real φ hstar (quadrupoleZ N)
    (quadrupoleZ_isHermitian N) (quadrupoleZ_ne_zero N hN) c hzc
  have hff : φ (lowering N*lowering N) = (g : ℂ) • (lowering N*lowering N) := by
    have h := hstar (raising N*raising N)
    rw [hc,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul] at h
    simpa [lowering] using h
  have hsf : φ (zAxis N*lowering N+lowering N*zAxis N) =
      (g : ℂ) • (zAxis N*lowering N+lowering N*zAxis N) := by
    have h := hstar (zAxis N*raising N+raising N*zAxis N)
    rw [hsc,Matrix.conjTranspose_smul,Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,(zAxis_isHermitian N).eq] at h
    simpa only [lowering,add_comm,Complex.star_def,Complex.conj_ofReal] using h
  refine ⟨g, ?_, ?_, hzc, ?_, ?_, ?_⟩
  · rw [quadrupoleX_decomposition]
    simp only [map_smul,map_sub,map_add,hc,hff,hzc]
    module
  · rw [quadrupoleY_decomposition]
    simp only [map_smul,map_sub,map_add,hc,hff,hzc]
    module
  · rw [xy_anticommutator]
    simp only [map_smul,map_sub,hc,hff]
    module
  · rw [yz_anticommutator]
    simp only [map_smul,map_sub,hsc,hsf]
    module
  · rw [zx_anticommutator]
    simp only [map_smul,map_add,hsc,hsf]
    module

lemma traceDual_eigenvalue_eq {n : ℕ} (φ : Choi.Mat n →ₗ[ℂ] Choi.Mat n)
    (A : Choi.Mat n) (hA : A.IsHermitian) (hA0 : A ≠ 0) (c d : ℂ)
    (hc : φ A = c • A) (hd : Choi.traceDual φ A = d • A) : d = c := by
  have htr : (A*A).trace ≠ 0 := by
    rw [← hA.eq]
    simpa only [hA.eq] using
      (not_congr (Matrix.trace_conjTranspose_mul_self_eq_zero_iff (A := A))).mpr hA0
  have h := Choi.traceDual_pairing φ A A
  rw [hc,hd,smul_mul_assoc,mul_smul_comm,Matrix.trace_smul,Matrix.trace_smul] at h
  exact mul_right_cancel₀ htr h

lemma dual_dipole_action (N : ℕ) (hN : 1 ≤ N) (φ : Mat N →ₗ[ℂ] Mat N)
    (hE : CommutesWithCommutator φ (raising N))
    (hH : CommutesWithCommutator φ (zAxis N))
    (hF : CommutesWithCommutator φ (lowering N))
    (hstar : ∀ A, φ Aᴴ = (φ A)ᴴ) (f : ℝ)
    (hz : φ (zAxis N) = (f : ℂ) • zAxis N) :
    Choi.traceDual φ (xAxis N) = (f : ℂ) • xAxis N ∧
      Choi.traceDual φ (yAxis N) = (f : ℂ) • yAxis N ∧
      Choi.traceDual φ (zAxis N) = (f : ℂ) • zAxis N := by
  obtain ⟨d,hdx,hdy,hdz⟩ := dipole_scalar N hN (Choi.traceDual φ)
    (Choi.traceDual_commutator φ _ hE) (Choi.traceDual_commutator φ _ hH)
    (Choi.traceDual_commutator φ _ hF) (Choi.traceDual_conjTranspose φ hstar)
  have hd : (d : ℂ) = (f : ℂ) := traceDual_eigenvalue_eq φ (zAxis N)
    (zAxis_isHermitian N) (zAxis_ne_zero N hN) f d hz hdz
  simpa only [hd] using And.intro hdx (And.intro hdy hdz)

lemma dual_quadrupole_action (N : ℕ) (hN : 2 ≤ N) (φ : Mat N →ₗ[ℂ] Mat N)
    (hE : CommutesWithCommutator φ (raising N))
    (hH : CommutesWithCommutator φ (zAxis N))
    (hF : CommutesWithCommutator φ (lowering N))
    (hstar : ∀ A, φ Aᴴ = (φ A)ᴴ) (g : ℝ)
    (hz : φ (quadrupoleZ N) = (g : ℂ) • quadrupoleZ N) :
      Choi.traceDual φ (xAxis N*xAxis N-((casimir N : ℂ)/3) • 1) =
        (g : ℂ) • (xAxis N*xAxis N-((casimir N : ℂ)/3) • 1) ∧
      Choi.traceDual φ (yAxis N*yAxis N-((casimir N : ℂ)/3) • 1) =
        (g : ℂ) • (yAxis N*yAxis N-((casimir N : ℂ)/3) • 1) ∧
      Choi.traceDual φ (zAxis N*zAxis N-((casimir N : ℂ)/3) • 1) =
        (g : ℂ) • (zAxis N*zAxis N-((casimir N : ℂ)/3) • 1) ∧
      Choi.traceDual φ (xAxis N*yAxis N+yAxis N*xAxis N) =
        (g : ℂ) • (xAxis N*yAxis N+yAxis N*xAxis N) ∧
      Choi.traceDual φ (yAxis N*zAxis N+zAxis N*yAxis N) =
        (g : ℂ) • (yAxis N*zAxis N+zAxis N*yAxis N) ∧
      Choi.traceDual φ (zAxis N*xAxis N+xAxis N*zAxis N) =
        (g : ℂ) • (zAxis N*xAxis N+xAxis N*zAxis N) := by
  obtain ⟨d,hdx,hdy,hdz,hdxy,hdyz,hdzx⟩ := quadrupole_scalar N hN (Choi.traceDual φ)
    (Choi.traceDual_commutator φ _ hE) (Choi.traceDual_commutator φ _ hH)
    (Choi.traceDual_commutator φ _ hF) (Choi.traceDual_conjTranspose φ hstar)
  have hd : (d : ℂ) = (g : ℂ) := traceDual_eigenvalue_eq φ (quadrupoleZ N)
    (quadrupoleZ_isHermitian N) (quadrupoleZ_ne_zero N hN) g d hz hdz
  simpa only [hd] using And.intro hdx (And.intro hdy (And.intro hdz
    (And.intro hdxy (And.intro hdyz hdzx))))

/-- The nine concrete first and second moment identities. This is a conclusion
of covariance below, not an additional hypothesis on the physical channel. -/
structure LowRankAction (N : ℕ) (φ : Mat N →ₗ[ℂ] Mat N) (f g : ℝ) : Prop where
  x : φ (xAxis N) = (f : ℂ) • xAxis N
  y : φ (yAxis N) = (f : ℂ) • yAxis N
  z : φ (zAxis N) = (f : ℂ) • zAxis N
  xx : φ (xAxis N*xAxis N-((casimir N : ℂ)/3) • 1) =
    (g : ℂ) • (xAxis N*xAxis N-((casimir N : ℂ)/3) • 1)
  yy : φ (yAxis N*yAxis N-((casimir N : ℂ)/3) • 1) =
    (g : ℂ) • (yAxis N*yAxis N-((casimir N : ℂ)/3) • 1)
  zz : φ (zAxis N*zAxis N-((casimir N : ℂ)/3) • 1) =
    (g : ℂ) • (zAxis N*zAxis N-((casimir N : ℂ)/3) • 1)
  xy : φ (xAxis N*yAxis N+yAxis N*xAxis N) =
    (g : ℂ) • (xAxis N*yAxis N+yAxis N*xAxis N)
  yz : φ (yAxis N*zAxis N+zAxis N*yAxis N) =
    (g : ℂ) • (yAxis N*zAxis N+zAxis N*yAxis N)
  zx : φ (zAxis N*xAxis N+xAxis N*zAxis N) =
    (g : ℂ) • (zAxis N*xAxis N+xAxis N*zAxis N)

lemma raising_decomposition (N : ℕ) : raising N = xAxis N+Complex.I • yAxis N := by
  simp only [xAxis,yAxis,smul_smul]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

lemma raising_sq_decomposition (N : ℕ) :
    raising N*raising N =
      (xAxis N*xAxis N-((casimir N : ℂ)/3) • 1)-
      (yAxis N*yAxis N-((casimir N : ℂ)/3) • 1)+
      Complex.I • (xAxis N*yAxis N+yAxis N*xAxis N) := by
  calc
    _ = (xAxis N+Complex.I • yAxis N)*(xAxis N+Complex.I • yAxis N) := by
      rw [← raising_decomposition]
    _ = _ := by
      simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul]
      match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

lemma LowRankAction.raising {N : ℕ} {φ : Mat N →ₗ[ℂ] Mat N} {f g : ℝ}
    (h : LowRankAction N φ f g) : φ (Spin.raising N) = (f : ℂ) • Spin.raising N := by
  rw [raising_decomposition]
  simp only [map_add,map_smul,h.x,h.y]
  module

lemma LowRankAction.raising_sq {N : ℕ} {φ : Mat N →ₗ[ℂ] Mat N} {f g : ℝ}
    (h : LowRankAction N φ f g) :
    φ (Spin.raising N*Spin.raising N) = (g : ℂ) • (Spin.raising N*Spin.raising N) := by
  rw [raising_sq_decomposition]
  simp only [map_add,map_sub,map_smul,h.xx,h.yy,h.xy]
  module

/-- Actual complete positivity, trace preservation and commutator covariance
imply the real first/second-moment action of the channel and its trace dual,
unitality, and the Choi-variance restriction on the two multipliers. -/
theorem covariant_channel_reduction (N : ℕ) (hN : 2 ≤ N)
    (φ : Mat N →ₗ[ℂ] Mat N) (hCP : Choi.CompletelyPositive φ)
    (hTP : ∀ A, (φ A).trace = A.trace)
    (hE : CommutesWithCommutator φ (raising N))
    (hH : CommutesWithCommutator φ (zAxis N))
    (hF : CommutesWithCommutator φ (lowering N)) :
    ∃ f g : ℝ, φ 1 = 1 ∧ LowRankAction N φ f g ∧
      LowRankAction N (Choi.traceDual φ) f g ∧
      3*((N : ℝ)*(N+2))*f^2-6*f-(N : ℝ)*(N+2) ≤
        2*((N : ℝ)*(N+2)-3)*g := by
  have hstar := Choi.map_conjTranspose φ hCP
  obtain ⟨f,hx,hy,hz⟩ := dipole_scalar N (by omega) φ hE hH hF hstar
  obtain ⟨g,hxx,hyy,hzz,hxy,hyz,hzx⟩ := quadrupole_scalar N hN φ hE hH hF hstar
  obtain ⟨hdx,hdy,hdz⟩ := dual_dipole_action N (by omega) φ hE hH hF hstar f hz
  obtain ⟨hdxx,hdyy,hdzz,hdxy,hdyz,hdzx⟩ :=
    dual_quadrupole_action N hN φ hE hH hF hstar g hzz
  refine ⟨f,g,unital_of_trace_preserving N φ hE hH hTP,
    ⟨hx,hy,hz,hxx,hyy,hzz,hxy,hyz,hzx⟩,
    ⟨hdx,hdy,hdz,hdxx,hdyy,hdzz,hdxy,hdyz,hdzx⟩,?_⟩
  have hc : 0 < casimir N := by
    have hnR : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    unfold casimir
    positivity
  have hcurve := Choi.cp_multiplier_curve (by omega : 0 < N+1) φ hCP hTP
    (xAxis N) (yAxis N) (zAxis N) (casimir N) f g hc
    (xAxis_isHermitian N) (yAxis_isHermitian N) (zAxis_isHermitian N)
    (xAxis_yAxis N) (yAxis_zAxis N) (zAxis_xAxis N) (casimir_identity N)
    hx hy hz hxx hyy hzz hxy hyz hzx
  have hc4 : 4*casimir N = (N : ℝ)*(N+2) := by unfold casimir; ring
  simpa only [hc4] using hcurve

end
end SU2T2.Spin

#print axioms SU2T2.Spin.covariant_channel_reduction
