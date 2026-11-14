import Mathlib.Tactic

/-!
# A larger admissible multiplier region

This strengthens the original certificate by allowing g ≥ -2/3.
All results in this file are real-algebra theorems.  The final theorem
has precisely the scalar hypotheses supplied by the physical reduction in the PDF.
It does not itself formalize SU(2), partial trace, or complete positivity.
-/

namespace SU2T2.Broad

noncomputable section

def affine (g a : ℝ) : ℝ := 2 * (1 - g) / 3 + g * a

lemma schur_ordered (x y z : ℝ) (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
    x^3 + y^3 + z^3 + 3*x*y*z -
      (x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) ≥ 0 := by
  have h₁ := mul_nonneg (sq_nonneg (x-y)) (show 0 ≤ x+y-z by linarith)
  have h₂ := mul_nonneg (mul_nonneg hz (show 0 ≤ x-z by linarith))
    (show 0 ≤ y-z by linarith)
  nlinarith

lemma schur_three (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x^3 + y^3 + z^3 + 3*x*y*z -
      (x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) ≥ 0 := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · nlinarith [schur_ordered z y x hx hxy hyz]
    · rcases le_total x z with hxz | hzx
      · nlinarith [schur_ordered y z x hx hxz hzy]
      · nlinarith [schur_ordered y x z hz hzx hxy]
  · rcases le_total x z with hxz | hzx
    · nlinarith [schur_ordered z x y hy hyx hxz]
    · rcases le_total y z with hyz | hzy
      · nlinarith [schur_ordered x z y hy hyz hzx]
      · nlinarith [schur_ordered x y z hz hzy hyx]

lemma deviation_bound (x y z : ℝ) (hx : x ≤ 5/6) (hy : y ≤ 5/6)
    (hz : z ≤ 5/6) (hs : x+y+z = 0) :
    6*x*y*z ≤ (5/6)*(x^2+y^2+z^2) := by
  have h := schur_three (5/6-x) (5/6-y) (5/6-z)
    (by linarith) (by linarith) (by linarith)
  have he : z = -x-y := by linarith
  rw [he] at h ⊢
  nlinarith

lemma multiplier_quadratic_positive (g : ℝ) (hg₀ : -(2/3) ≤ g) (hg₁ : g ≤ 1) :
    0 ≤ 7+7*g-5*g^2 := by
  have h := mul_nonneg (show 0 ≤ g+2/3 by linarith) (show 0 ≤ 1-g by linarith)
  nlinarith

theorem unpolarized_determinant (a b c g : ℝ)
    (ha : a ≤ 3/2) (hb : b ≤ 3/2) (hc : c ≤ 3/2) (hs : a+b+c=2)
    (hg₀ : -(2/3) ≤ g) (hg₁ : g ≤ 1) :
    a*b*c ≤ affine g a * affine g b * affine g c := by
  let x := a-2/3
  let y := b-2/3
  let z := c-2/3
  let S := x^2+y^2+z^2
  let P := x*y*z
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hP : 36*P ≤ 5*S := by
    have h := deviation_bound x y z (by dsimp [x]; linarith)
      (by dsimp [y]; linarith) (by dsimp [z]; linarith)
      (by dsimp [x,y,z]; linarith)
    dsimp [P,S]; nlinarith
  have hgg : 0 ≤ 1+g+g^2 := by nlinarith [sq_nonneg (g+1/2)]
  have hcube : 0 ≤ 1-g^3 := by
    have h := mul_nonneg (show 0 ≤ 1-g by linarith) hgg
    nlinarith
  have h₁ := mul_nonneg hcube (show 0 ≤ 5*S-36*P by linarith)
  have h₂ := mul_nonneg (mul_nonneg (show 0 ≤ 1-g by linarith) hS)
    (multiplier_quadratic_positive g hg₀ hg₁)
  have he : affine g a * affine g b * affine g c - a*b*c =
      (1-g^2)/3*S-(1-g^3)*P := by
    have hec : c = 2-a-b := by linarith
    dsimp [affine,S,P,x,y,z]
    rw [hec]
    ring
  nlinarith

lemma affine_nonnegative (g a : ℝ) (hg₀ : -(2/3) ≤ g) (hg₁ : g ≤ 1)
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 3/2) : 0 ≤ affine g a := by
  dsimp [affine]
  by_cases hg : 0 ≤ g
  · have h := mul_nonneg hg ha₀
    linarith
  · have h := mul_nonneg (show 0 ≤ -g by linarith) (show 0 ≤ 3/2-a by linarith)
    nlinarith

lemma small_f_squared (M f g : ℝ) (hM : 15 ≤ M) (hg : g ≤ -(1/2))
    (hcurve : 3*M*f^2-6*f-M ≤ 2*(M-3)*g) : f^2 ≤ 1/9 := by
  have hf2 := sq_nonneg f
  have hg' := mul_nonneg (show 0 ≤ M-3 by linarith) (show 0 ≤ -(1/2)-g by linarith)
  have hM' := mul_nonneg (show 0 ≤ M-15 by linarith) hf2
  have hpoly : 15*f^2-2*f-1 ≤ 0 := by nlinarith
  have hflo : -(1/3) ≤ f := by
    by_contra h
    have hh : f < -(1/3) := by linarith
    have hprod := mul_nonneg (show 0 ≤ -f-1/3 by linarith)
      (show 0 ≤ -f+1/3 by linarith)
    nlinarith
  have hfhi : f ≤ 1/3 := by
    by_contra h
    have hh : 1/3 < f := by linarith
    have hprod := mul_pos (show 0 < f-1/3 by linarith)
      (show 0 < 15*f+3 by linarith)
    nlinarith
  nlinarith [mul_nonneg (show 0 ≤ f+1/3 by linarith) (show 0 ≤ 1/3-f by linarith)]

theorem cofactor (M f g b c : ℝ) (hM : 15 ≤ M)
    (hg₀ : -(2/3) ≤ g) (hg₁ : g ≤ 1)
    (hflo : -(2+g) ≤ 3*f) (hfhi : 3*f ≤ 2+g)
    (hcurve : 3*M*f^2-6*f-M ≤ 2*(M-3)*g)
    (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c)
    (hb₁ : b ≤ 3/2) (hc₁ : c ≤ 3/2) (hs : b+c ≤ 2) :
    f^2*b*c ≤ affine g b * affine g c := by
  have hp : 0 ≤ b*c := mul_nonneg hb₀ hc₀
  let α := 2*(1-g)/3
  have hα : 0 ≤ α := by dsimp [α]; linarith
  by_cases hg : -(1/2) ≤ g
  · have hq : 0 ≤ 2*g+α := by dsimp [α]; linarith
    have hf : f^2 ≤ (g+α)^2 := by
      have h := mul_nonneg (show 0 ≤ 2+g-3*f by linarith)
        (show 0 ≤ 2+g+3*f by linarith)
      dsimp [α]; nlinarith
    have h₁ := mul_nonneg hq (sq_nonneg (b-c))
    have h₂ := mul_nonneg (show 0 ≤ 2-b-c by linarith)
      (show 0 ≤ 2*α+(2*g+α)*(b+c) by positivity)
    have h₃ := mul_nonneg hα (add_nonneg h₁ h₂)
    have h₄ := mul_nonneg (show 0 ≤ (g+α)^2-f^2 by linarith) hp
    change f^2*b*c ≤ (α+g*b)*(α+g*c)
    nlinarith
  · have hg' : g ≤ -(1/2) := by linarith
    have hf := small_f_squared M f g hM hg' hcurve
    have hq : 0 ≤ g^2-1/9 := by nlinarith [sq_nonneg (g+1/2)]
    have hrect := mul_nonneg (show 0 ≤ 3/2-b by linarith)
      (show 0 ≤ 3/2-c by linarith)
    have h₁ := mul_nonneg hq hrect
    have hcoef : α*g+3/2*(g^2-1/9) ≤ 0 := by
      have h := mul_nonneg (show 0 ≤ 1-5*g by linarith) (show 0 ≤ g+1 by linarith)
      dsimp [α]; nlinarith
    have h₂ := mul_nonneg (show 0 ≤ -(α*g+3/2*(g^2-1/9)) by linarith)
      (show 0 ≤ 2-b-c by linarith)
    have hmin : 0 ≤ 13+16*g-5*g^2 := by
      have h := mul_nonneg (show 0 ≤ g+2/3 by linarith) (show 0 ≤ 1-g by linarith)
      nlinarith
    have h₃ := mul_nonneg (show 0 ≤ 1/9-f^2 by linarith) hp
    change f^2*b*c ≤ (α+g*b)*(α+g*c)
    dsimp [α] at *
    nlinarith

/-- The determinant, multiplied by eight, in a real eigenbasis of A. -/
def det8 (a b c r s t : ℝ) : ℝ := a*b*c-a*r^2-b*s^2-c*t^2

theorem determinant_monotone (a b c r s t M f g : ℝ)
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c)
    (ha₁ : a ≤ 3/2) (hb₁ : b ≤ 3/2) (hc₁ : c ≤ 3/2)
    (hs : a+b+c=2) (hM : 15 ≤ M)
    (hg₀ : -(2/3) ≤ g) (hg₁ : g ≤ 1)
    (hflo : -(2+g) ≤ 3*f) (hfhi : 3*f ≤ 2+g)
    (hcurve : 3*M*f^2-6*f-M ≤ 2*(M-3)*g)
    (hin : 0 ≤ det8 a b c r s t)
    (hout : 0 ≤ det8 (affine g a) (affine g b) (affine g c) (f*r) (f*s) (f*t)) :
    det8 a b c r s t ≤
      det8 (affine g a) (affine g b) (affine g c) (f*r) (f*s) (f*t) := by
  have hA := affine_nonnegative g a hg₀ hg₁ ha₀ ha₁
  have hB := affine_nonnegative g b hg₀ hg₁ hb₀ hb₁
  have hC := affine_nonnegative g c hg₀ hg₁ hc₀ hc₁
  have hvol := unpolarized_determinant a b c g ha₁ hb₁ hc₁ hs hg₀ hg₁
  have hbc := cofactor M f g b c hM hg₀ hg₁ hflo hfhi hcurve hb₀ hc₀ hb₁ hc₁ (by linarith)
  have hac := cofactor M f g a c hM hg₀ hg₁ hflo hfhi hcurve ha₀ hc₀ ha₁ hc₁ (by linarith)
  have hab := cofactor M f g a b hM hg₀ hg₁ hflo hfhi hcurve ha₀ hb₀ ha₁ hb₁ (by linarith)
  have hD : 0 ≤ a*b*c := by positivity
  by_cases hzero : a*b*c=0
  · have hv : 0 ≤ a*r^2+b*s^2+c*t^2 := by positivity
    dsimp [det8] at hin hout ⊢
    linarith
  · have hpos : 0 < a*b*c := lt_of_le_of_ne hD (Ne.symm hzero)
    have h₁ := mul_nonneg (show 0 ≤ a*affine g a*r^2 by positivity)
      (show 0 ≤ affine g b*affine g c-f^2*b*c by linarith)
    have h₂ := mul_nonneg (show 0 ≤ b*affine g b*s^2 by positivity)
      (show 0 ≤ affine g a*affine g c-f^2*a*c by linarith)
    have h₃ := mul_nonneg (show 0 ≤ c*affine g c*t^2 by positivity)
      (show 0 ≤ affine g a*affine g b-f^2*a*b by linarith)
    have h₄ := mul_nonneg (show 0 ≤ affine g a*affine g b*affine g c-a*b*c by linarith) hin
    have hid : a*b*c *
        (det8 (affine g a) (affine g b) (affine g c) (f*r) (f*s) (f*t) - det8 a b c r s t) =
        (affine g a*affine g b*affine g c-a*b*c)*det8 a b c r s t +
        a*affine g a*r^2*(affine g b*affine g c-f^2*b*c) +
        b*affine g b*s^2*(affine g a*affine g c-f^2*a*c) +
        c*affine g c*t^2*(affine g a*affine g b-f^2*a*b) := by
      dsimp [det8]; ring
    have hprod : 0 ≤ a*b*c *
        (det8 (affine g a) (affine g b) (affine g c) (f*r) (f*s) (f*t) - det8 a b c r s t) := by
      rw [hid]; positivity
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hpos).mp hprod)

end
end SU2T2.Broad
