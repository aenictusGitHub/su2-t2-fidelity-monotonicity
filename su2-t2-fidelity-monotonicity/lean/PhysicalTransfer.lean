import SpinCovariance
import TraceDual

/-! Highest-weight transfer across an actual rectangular marginal map. -/
namespace SU2T2.Physical
open Matrix Module
noncomputable section

lemma highest_one_matrix (N : ℕ) (hN : 1 ≤ N) (X : Spin.Mat N)
    (hE : Spin.raising N*X=X*Spin.raising N)
    (hH : Spin.zAxis N*X-X*Spin.zAxis N=X) :
    ∃ c : ℂ, X=c • Spin.raising N := by
  let k : Fin (N+1) := ⟨1, by omega⟩
  let i : Fin N := ⟨0, by omega⟩
  have hzero : Spin.raisingEnd N (Spin.basis N 0) =
      (Spin.weight N 0 : ℂ) • Spin.basis N k := by
    simpa only [i,k] using Spin.raising_basis N i
  have he : Spin.raisingEnd N * Matrix.toLin' X =
      Matrix.toLin' X * Spin.raisingEnd N := by
    simpa only [Spin.raisingEnd, Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg Matrix.toLin' hE
  have hh : Spin.zEnd N * Matrix.toLin' X - Matrix.toLin' X * Spin.zEnd N =
      Matrix.toLin' X := by
    simpa only [Spin.zEnd, map_sub, Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg Matrix.toLin' hH
  obtain ⟨c,hc⟩ := highest_weight_scalar (Spin.basis N) (Spin.raisingEnd N)
    (Spin.zEnd N) (Matrix.toLin' X) (Spin.raisingEnd N)
    (fun j => (Spin.weight N j.val : ℂ)) (Spin.weight_ne_zero N) (Spin.raising_basis N)
    (Spin.magnetic N) (Spin.zAxis_basis N) (Spin.magnetic_injective N)
    k (Spin.weight N 0) (Spin.weight_ne_zero N i) hzero
    (fun v => congrArg (fun T : Module.End ℂ (Spin.Space N) => T v) he)
    (fun _ => rfl) (fun v => by
      have h := congrArg (fun T : Module.End ℂ (Spin.Space N) => T v) hh
      simpa [Spin.magnetic_step, k] using h)
  refine ⟨c, ?_⟩
  apply Matrix.toLinAlgEquiv'.injective
  simpa [Spin.raisingEnd] using hc

lemma highest_two_matrix (N : ℕ) (hN : 2 ≤ N) (X : Spin.Mat N)
    (hE : Spin.raising N*X=X*Spin.raising N)
    (hH : Spin.zAxis N*X-X*Spin.zAxis N=(2:ℂ) • X) :
    ∃ c : ℂ, X=c • (Spin.raising N*Spin.raising N) := by
  let E := Spin.raisingEnd N
  let H := Spin.zEnd N
  let k : Fin (N+1) := ⟨2, by omega⟩
  let i₀ : Fin N := ⟨0, by omega⟩
  let i₁ : Fin N := ⟨1, by omega⟩
  have hzero : (E^2) (Spin.basis N 0) =
      ((Spin.weight N 0 : ℂ)*(Spin.weight N 1 : ℂ)) • Spin.basis N k := by
    change E (E (Spin.basis N 0)) = _
    have h₀ := Spin.raising_basis N i₀
    have h₁ := Spin.raising_basis N i₁
    change E (Spin.basis N 0) = (Spin.weight N 0 : ℂ) • Spin.basis N i₁.castSucc at h₀
    change E (Spin.basis N i₁.castSucc) = (Spin.weight N 1 : ℂ) • Spin.basis N k at h₁
    rw [h₀, map_smul, h₁, smul_smul]
  have he : E * Matrix.toLin' X = Matrix.toLin' X * E := by
    simpa only [E, Spin.raisingEnd, Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg Matrix.toLin' hE
  have hh : H * Matrix.toLin' X - Matrix.toLin' X * H =
      (2:ℂ) • Matrix.toLin' X := by
    simpa only [H, Spin.zEnd, map_sub, map_smul, Matrix.toLin'_mul,
      Module.End.mul_eq_comp] using congrArg Matrix.toLin' hH
  have hEB : E*(E^2)=(E^2)*E := by noncomm_ring
  obtain ⟨c,hc⟩ := highest_weight_scalar (Spin.basis N) E H (Matrix.toLin' X) (E^2)
    (fun j => (Spin.weight N j.val : ℂ)) (Spin.weight_ne_zero N) (Spin.raising_basis N)
    (Spin.magnetic N) (Spin.zAxis_basis N) (Spin.magnetic_injective N)
    k _ (mul_ne_zero (Spin.weight_ne_zero N i₀) (Spin.weight_ne_zero N i₁)) hzero
    (fun v => congrArg (fun T : Module.End ℂ (Spin.Space N) => T v) he)
    (fun v => congrArg (fun T : Module.End ℂ (Spin.Space N) => T v) hEB)
    (fun v => by
      have h := congrArg (fun T : Module.End ℂ (Spin.Space N) => T v) hh
      simpa [Spin.magnetic_step, k] using h)
  refine ⟨c, ?_⟩
  apply Matrix.toLinAlgEquiv'.injective
  simpa [E, Spin.raisingEnd, pow_two, Matrix.toLin'_mul] using hc

lemma highest_transfer (N : ℕ) (hN : 2 ≤ N)
    (ψ : Spin.Mat 2 →ₗ[ℂ] Spin.Mat N)
    (hE : ∀ B, ψ (Spin.raising 2*B-B*Spin.raising 2)=
      Spin.raising N*ψ B-ψ B*Spin.raising N)
    (hH : ∀ B, ψ (Spin.zAxis 2*B-B*Spin.zAxis 2)=
      Spin.zAxis N*ψ B-ψ B*Spin.zAxis N) :
    (∃ c : ℂ, ψ (Spin.raising 2)=c • Spin.raising N) ∧
    (∃ c : ℂ, ψ (Spin.raising 2*Spin.raising 2)=c • (Spin.raising N*Spin.raising N)) := by
  constructor
  · apply highest_one_matrix N (by omega)
    · apply sub_eq_zero.mp
      rw [← hE]
      simp
    · rw [← hH, Spin.zAxis_raising]
  · apply highest_two_matrix N hN
    · apply sub_eq_zero.mp
      rw [← hE]
      have he : Spin.raising 2*(Spin.raising 2*Spin.raising 2)-
          (Spin.raising 2*Spin.raising 2)*Spin.raising 2=0 := by noncomm_ring
      rw [he, map_zero]
    · rw [← hH]
      have he : Spin.zAxis 2*(Spin.raising 2*Spin.raising 2)-
          (Spin.raising 2*Spin.raising 2)*Spin.zAxis 2 =
          (2:ℂ) • (Spin.raising 2*Spin.raising 2) := by
        calc
          _ = (Spin.zAxis 2*Spin.raising 2-Spin.raising 2*Spin.zAxis 2)*Spin.raising 2+
            Spin.raising 2*(Spin.zAxis 2*Spin.raising 2-Spin.raising 2*Spin.zAxis 2) := by noncomm_ring
          _ = _ := by rw [Spin.zAxis_raising]; module
      rw [he, map_smul]

lemma transferred_highest_eigenvectors (N : ℕ) (hN : 2 ≤ N)
    (ψ : Spin.Mat 2 →ₗ[ℂ] Spin.Mat N) (Φ : Spin.Mat N →ₗ[ℂ] Spin.Mat N)
    (hE : ∀ B, ψ (Spin.raising 2*B-B*Spin.raising 2)=
      Spin.raising N*ψ B-ψ B*Spin.raising N)
    (hH : ∀ B, ψ (Spin.zAxis 2*B-B*Spin.zAxis 2)=
      Spin.zAxis N*ψ B-ψ B*Spin.zAxis N)
    (f g : ℂ) (hf : Φ (Spin.raising N)=f • Spin.raising N)
    (hg : Φ (Spin.raising N*Spin.raising N)=g • (Spin.raising N*Spin.raising N)) :
    Φ (ψ (Spin.raising 2))=f • ψ (Spin.raising 2) ∧
    Φ (ψ (Spin.raising 2*Spin.raising 2))=g • ψ (Spin.raising 2*Spin.raising 2) := by
  obtain ⟨⟨c,hc⟩,⟨d,hd⟩⟩ := highest_transfer N hN ψ hE hH
  constructor
  · rw [hc,map_smul,hf,smul_comm]
  · rw [hd,map_smul,hg,smul_comm]

end
end SU2T2.Physical
