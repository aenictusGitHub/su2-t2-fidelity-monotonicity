import Mathlib.Tactic

/-!
An elementary scalar certificate for the last step of the qutrit argument.
The variables are the nonnegative square roots of two triples of eigenvalues.
All assumptions are displayed: normalization, increasing second elementary
symmetric polynomial, and increasing determinant. No matrix or channel claims
are hidden in these hypotheses.
-/

namespace SU2T2

theorem qutrit_root_sum_mono
    (x y z X Y Z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hin : x ^ 2 + y ^ 2 + z ^ 2 = 1)
    (hout : X ^ 2 + Y ^ 2 + Z ^ 2 = 1)
    (he₂ : x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2 ≤
      X ^ 2 * Y ^ 2 + X ^ 2 * Z ^ 2 + Y ^ 2 * Z ^ 2)
    (hdet : x ^ 2 * y ^ 2 * z ^ 2 ≤ X ^ 2 * Y ^ 2 * Z ^ 2) :
    x + y + z ≤ X + Y + Z := by
  let s := x + y + z
  let t := X + Y + Z
  let d := x * y * z
  let D := X * Y * Z
  let e := x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2
  let E := X ^ 2 * Y ^ 2 + X ^ 2 * Z ^ 2 + Y ^ 2 * Z ^ 2
  have hd₀ : 0 ≤ d := by dsimp [d]; positivity
  have hD₀ : 0 ≤ D := by dsimp [D]; positivity
  have hd : d ≤ D := by
    by_contra h
    have hlt : D < d := lt_of_not_ge h
    have hp : 0 < (d - D) * (d + D) :=
      mul_pos (by linarith) (by linarith)
    have hsq : d ^ 2 ≤ D ^ 2 := by dsimp [d, D]; nlinarith only [hdet]
    nlinarith only [hp, hsq]
  have he : e ≤ E := he₂
  have hs₀ : 0 ≤ s := by dsimp [s]; positivity
  have ht₀ : 0 ≤ t := by dsimp [t]; positivity
  have hs₂ : 1 ≤ s ^ 2 := by
    dsimp [s]
    nlinarith only [hin, mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
  have ht₂ : 1 ≤ t ^ 2 := by
    dsimp [t]
    nlinarith only [hout, mul_nonneg hX hY, mul_nonneg hX hZ, mul_nonneg hY hZ]
  have hs : 1 ≤ s := by nlinarith only [hs₂, hs₀]
  have ht : 1 ≤ t := by nlinarith only [ht₂, ht₀]
  have hid : (s ^ 2 - 1) ^ 2 = 4 * e + 8 * d * s := by
    calc
      (s ^ 2 - 1) ^ 2 = (s ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2)) ^ 2 := by rw [hin]
      _ = 4 * e + 8 * d * s := by dsimp [s, e, d]; ring
  have hid' : (t ^ 2 - 1) ^ 2 = 4 * E + 8 * D * t := by
    calc
      (t ^ 2 - 1) ^ 2 = (t ^ 2 - (X ^ 2 + Y ^ 2 + Z ^ 2)) ^ 2 := by rw [hout]
      _ = 4 * E + 8 * D * t := by dsimp [t, E, D]; ring
  have hschur_id : s * (s ^ 2 - 1) - 18 * d =
      2 * (z * (x - y) ^ 2 + x * (y - z) ^ 2 + y * (z - x) ^ 2) := by
    calc
      s * (s ^ 2 - 1) - 18 * d =
          s * (s ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2)) - 18 * d := by rw [hin]
      _ = _ := by dsimp [s, d]; ring
  have hschur : 18 * d ≤ s * (s ^ 2 - 1) := by
    have hnn : 0 ≤ 2 * (z * (x - y) ^ 2 + x * (y - z) ^ 2 +
        y * (z - x) ^ 2) := by positivity
    linarith
  change s ≤ t
  by_contra h
  have hst : t < s := lt_of_not_ge h
  have hdiff : (s - t) * ((s + t) * (s ^ 2 + t ^ 2 - 2) - 8 * d) =
      4 * (e - E) - 8 * (D - d) * t := by nlinarith only [hid, hid']
  have hnonpos : (s - t) * ((s + t) * (s ^ 2 + t ^ 2 - 2) - 8 * d) ≤ 0 := by
    rw [hdiff]
    have hnn : 0 ≤ (D - d) * t := mul_nonneg (by linarith) ht₀
    linarith
  have hbound : (s + t) * (s ^ 2 + t ^ 2 - 2) ≤ 8 * d := by
    by_contra hbad
    have hp : 0 < (s - t) * ((s + t) * (s ^ 2 + t ^ 2 - 2) - 8 * d) :=
      mul_pos (by linarith) (by linarith)
    linarith
  have hs_strict : 0 < s ^ 2 - 1 := by nlinarith only [hst, ht]
  have hpos : 0 < t * (s ^ 2 - 1) := mul_pos (by linarith) hs_strict
  have hnn : 0 ≤ (s + t) * (t ^ 2 - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hlower : s * (s ^ 2 - 1) < (s + t) * (s ^ 2 + t ^ 2 - 2) := by
    nlinarith only [hpos, hnn]
  linarith

theorem qutrit_fidelity_mono
    (x y z X Y Z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hin : x ^ 2 + y ^ 2 + z ^ 2 = 1)
    (hout : X ^ 2 + Y ^ 2 + Z ^ 2 = 1)
    (he₂ : x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2 ≤
      X ^ 2 * Y ^ 2 + X ^ 2 * Z ^ 2 + Y ^ 2 * Z ^ 2)
    (hdet : x ^ 2 * y ^ 2 * z ^ 2 ≤ X ^ 2 * Y ^ 2 * Z ^ 2) :
    ((x + y + z) ^ 2 - 1) / 2 ≤ ((X + Y + Z) ^ 2 - 1) / 2 := by
  have hm := qutrit_root_sum_mono x y z X Y Z hx hy hz hX hY hZ hin hout he₂ hdet
  have hp : 0 ≤ ((X + Y + Z) - (x + y + z)) * ((X + Y + Z) + (x + y + z)) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith only [hp]

theorem qutrit_fidelity_mono_of_purity
    (x y z X Y Z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hin : x ^ 2 + y ^ 2 + z ^ 2 = 1)
    (hout : X ^ 2 + Y ^ 2 + Z ^ 2 = 1)
    (hpurity : X ^ 4 + Y ^ 4 + Z ^ 4 ≤ x ^ 4 + y ^ 4 + z ^ 4)
    (hdet : x ^ 2 * y ^ 2 * z ^ 2 ≤ X ^ 2 * Y ^ 2 * Z ^ 2) :
    ((x + y + z) ^ 2 - 1) / 2 ≤ ((X + Y + Z) ^ 2 - 1) / 2 := by
  have hin₂ : x ^ 4 + y ^ 4 + z ^ 4 +
      2 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) = 1 := by
    calc
      _ = (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hin]; norm_num
  have hout₂ : X ^ 4 + Y ^ 4 + Z ^ 4 +
      2 * (X ^ 2 * Y ^ 2 + X ^ 2 * Z ^ 2 + Y ^ 2 * Z ^ 2) = 1 := by
    calc
      _ = (X ^ 2 + Y ^ 2 + Z ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hout]; norm_num
  have he₂ : x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2 ≤
      X ^ 2 * Y ^ 2 + X ^ 2 * Z ^ 2 + Y ^ 2 * Z ^ 2 := by
    linarith only [hin₂, hout₂, hpurity]
  exact qutrit_fidelity_mono x y z X Y Z hx hy hz hX hY hZ hin hout he₂ hdet

end SU2T2
