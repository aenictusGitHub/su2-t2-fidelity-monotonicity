import Determinant
import Qutrit
import Multipliers

/-!
# Combined scalar certificate

The theorem `fidelity_monotone_from_scalar_reduction` checks the complete
real-algebra argument once the SU(2) channel and its marginal have been reduced
to the scalar data displayed in its hypotheses.  The PDF proves that physical
data satisfy these hypotheses.  The representation-theoretic and matrix-spectral
reduction itself is not formalized here.
-/

namespace SU2T2

noncomputable section

def purity4 (a b c r s t : ℝ) : ℝ := a^2+b^2+c^2+2*(r^2+s^2+t^2)

theorem purity_monotone (a b c r s t f g : ℝ)
    (hs : a+b+c=2) (hf : f^2 ≤ 1) (hg : g^2 ≤ 1) :
    purity4 (affine g a) (affine g b) (affine g c) (f*r) (f*s) (f*t)
      ≤ purity4 a b c r s t := by
  have h₁ := mul_nonneg (show 0 ≤ 1-g^2 by linarith)
    (show 0 ≤ (a-2/3)^2+(b-2/3)^2+(c-2/3)^2 by positivity)
  have h₂ := mul_nonneg (show 0 ≤ 1-f^2 by linarith)
    (show 0 ≤ r^2+s^2+t^2 by positivity)
  have hid : purity4 a b c r s t -
      purity4 (affine g a) (affine g b) (affine g c) (f*r) (f*s) (f*t) =
      (1-g^2)*((a-2/3)^2+(b-2/3)^2+(c-2/3)^2)+
        2*(1-f^2)*(r^2+s^2+t^2) := by
    have hc : c=2-a-b := by linarith
    dsimp [purity4, affine]
    rw [hc]
    ring
  linarith

theorem fidelity_monotone_from_scalar_reduction
    (a b c r s t M f g x y z X Y Z : ℝ)
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c)
    (ha₁ : a ≤ 3/2) (hb₁ : b ≤ 3/2) (hc₁ : c ≤ 3/2)
    (hs : a+b+c=2) (hM : 15 ≤ M)
    (hg₀ : -(3/5) ≤ g) (hg₁ : g ≤ 1)
    (hflo : -(2+g) ≤ 3*f) (hfhi : 3*f ≤ 2+g)
    (hcurve : 3*M*f^2-6*f-M ≤ 2*(M-3)*g)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hnorm : x^2+y^2+z^2=1) (hNorm : X^2+Y^2+Z^2=1)
    (hpur : 4*(x^4+y^4+z^4)=purity4 a b c r s t)
    (hPur : 4*(X^4+Y^4+Z^4)=
      purity4 (affine g a) (affine g b) (affine g c) (f*r) (f*s) (f*t))
    (hdet : 8*(x^2*y^2*z^2)=det8 a b c r s t)
    (hDet : 8*(X^2*Y^2*Z^2)=
      det8 (affine g a) (affine g b) (affine g c) (f*r) (f*s) (f*t)) :
    ((x+y+z)^2-1)/2 ≤ ((X+Y+Z)^2-1)/2 := by
  have hf : f^2 ≤ 1 := by
    have h := mul_nonneg (show 0 ≤ 1-f by linarith) (show 0 ≤ 1+f by linarith)
    nlinarith
  have hg : g^2 ≤ 1 := by
    have h := mul_nonneg (show 0 ≤ 1-g by linarith) (show 0 ≤ 1+g by linarith)
    nlinarith
  have hpm := purity_monotone a b c r s t f g hs hf hg
  have hp : X^4+Y^4+Z^4 ≤ x^4+y^4+z^4 := by linarith
  have hdm := determinant_monotone a b c r s t M f g ha₀ hb₀ hc₀ ha₁ hb₁ hc₁
    hs hM hg₀ hg₁ hflo hfhi hcurve (by rw [←hdet]; positivity) (by rw [←hDet]; positivity)
  have hd : x^2*y^2*z^2 ≤ X^2*Y^2*Z^2 := by linarith
  exact qutrit_fidelity_mono_of_purity x y z X Y Z hx hy hz hX hY hZ hnorm hNorm hp hd

/-- Main scalar certificate, including the arbitrary finite-N channel mixture.

The four equations `hpur`, `hPur`, `hdet`, `hDet` are the ordinary spectral
identities for the input and output marginal, expressed using their nonnegative
eigenvalue square roots. They are explicit hypotheses, not hidden axioms.
-/
theorem channel_fidelity_monotone_from_scalar_reduction
    (N : ℕ) (hN : 3 ≤ N) (p : Fin (N+1) → ℝ)
    (hp : ∀ K, 0 ≤ p K) (hpsum : ∑ K, p K = 1)
    (a b c r s t f g x y z X Y Z : ℝ)
    (hfdef : f = ∑ K, p K * vertexF (spinSize N) (choiCasimir K.val))
    (hgdef : g = ∑ K, p K * vertexG (spinSize N) (choiCasimir K.val))
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c)
    (ha₁ : a ≤ 3/2) (hb₁ : b ≤ 3/2) (hc₁ : c ≤ 3/2)
    (hs : a+b+c=2)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hnorm : x^2+y^2+z^2=1) (hNorm : X^2+Y^2+Z^2=1)
    (hpur : 4*(x^4+y^4+z^4)=purity4 a b c r s t)
    (hPur : 4*(X^4+Y^4+Z^4)=
      purity4 (affine g a) (affine g b) (affine g c) (f*r) (f*s) (f*t))
    (hdet : 8*(x^2*y^2*z^2)=det8 a b c r s t)
    (hDet : 8*(X^2*Y^2*Z^2)=
      det8 (affine g a) (affine g b) (affine g c) (f*r) (f*s) (f*t)) :
    ((x+y+z)^2-1)/2 ≤ ((X+Y+Z)^2-1)/2 := by
  have hregion := channel_region N hN p hp hpsum
  dsimp only at hregion
  rw [←hfdef, ←hgdef] at hregion
  rcases hregion with ⟨hg₀,hg₁,hfabs,hcurve⟩
  have hM : 15 ≤ spinSize N := by
    have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [spinSize]
    nlinarith
  have hflo : -(2+g) ≤ 3*f := by nlinarith [neg_le_abs f]
  have hfhi : 3*f ≤ 2+g := by nlinarith [le_abs_self f]
  exact fidelity_monotone_from_scalar_reduction a b c r s t (spinSize N) f g x y z X Y Z
    ha₀ hb₀ hc₀ ha₁ hb₁ hc₁ hs hM hg₀ hg₁ hflo hfhi hcurve
    hx hy hz hX hY hZ hnorm hNorm hpur hPur hdet hDet

end
end SU2T2

#print axioms SU2T2.determinant_monotone
#print axioms SU2T2.qutrit_fidelity_mono
#print axioms SU2T2.fidelity_monotone_from_scalar_reduction
#print axioms SU2T2.channel_fidelity_monotone_from_scalar_reduction
