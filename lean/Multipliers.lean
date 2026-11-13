import Mathlib.Tactic

/-!
# Low-rank multipliers of SU(2)-covariant channels

This file checks the real-algebra inequalities used after the Choi/Casimir
calculation in the accompanying proof. The representation-theoretic calculation
identifying channel multipliers with the formulas below is not formalized here.
-/

namespace SU2T2

noncomputable section

/-- Rank-one multiplier of a Choi block. -/
def vertexF (S χ : ℝ) : ℝ := 1 - 2 * χ / S

/-- Rank-two multiplier of a Choi block. -/
def vertexG (S χ : ℝ) : ℝ :=
  1 + 6 * χ * (χ - S + 1) / (S * (S - 3))

/-- Four times the spin Casimir, in the normalization used in the proof. -/
def spinSize (N : ℕ) : ℝ := (N : ℝ) * ((N : ℝ) + 2)

/-- Casimir label of the spin-K Choi block. -/
def choiCasimir (K : ℕ) : ℝ := (K : ℝ) * ((K : ℝ) + 1)

theorem vertex_linear_minus (S χ : ℝ) (hS : S ≠ 0) (hS3 : S - 3 ≠ 0) :
    S * (S - 3) * (2 + vertexG S χ - 3 * vertexF S χ) =
      6 * χ * (χ - 2) := by
  unfold vertexF vertexG
  field_simp
  ring

theorem vertex_linear_plus (S χ : ℝ) (hS : S ≠ 0) (hS3 : S - 3 ≠ 0) :
    S * (S - 3) * (2 + vertexG S χ + 3 * vertexF S χ) =
      6 * ((χ - S + 2) ^ 2 + S - 4) := by
  unfold vertexF vertexG
  field_simp
  ring

theorem vertex_quadratic (S χ : ℝ) (hS : S ≠ 0) (hS3 : S - 3 ≠ 0) :
    2 * (S - 3) * vertexG S χ =
      3 * S * (vertexF S χ) ^ 2 - 6 * vertexF S χ - S := by
  unfold vertexF vertexG
  field_simp
  ring

theorem vertex_lower_identity (S χ : ℝ) (hS : S ≠ 0) (hS3 : S - 3 ≠ 0) :
    10 * (S * (S - 3)) * (vertexG S χ + 3 / 5) =
      60 * (χ - (S - 1) / 2) ^ 2 + (S - 24) * (S + 6) + 129 := by
  unfold vertexG
  field_simp
  ring

theorem vertex_basic_region (S χ : ℝ) (hS : 15 ≤ S)
    (hχ : 0 ≤ χ) (hχupper : χ ≤ S - 1)
    (hχdiscrete : χ = 0 ∨ 2 ≤ χ) :
    vertexG S χ ≤ 1 ∧ 3 * |vertexF S χ| ≤ 2 + vertexG S χ := by
  have hSpos : 0 < S := by linarith
  have hS3pos : 0 < S - 3 := by linarith
  have hDpos : 0 < S * (S - 3) := mul_pos hSpos hS3pos
  have hnum : 6 * χ * (χ - S + 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hgupper : vertexG S χ ≤ 1 := by
    unfold vertexG
    have := div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hDpos)
    linarith
  have hm := vertex_linear_minus S χ (ne_of_gt hSpos) (ne_of_gt hS3pos)
  have hp := vertex_linear_plus S χ (ne_of_gt hSpos) (ne_of_gt hS3pos)
  have hχprod : 0 ≤ χ * (χ - 2) := by
    rcases hχdiscrete with hzero | htwo
    · rw [hzero]
      norm_num
    · exact mul_nonneg hχ (by linarith)
  have hminus : 0 ≤ 2 + vertexG S χ - 3 * vertexF S χ := by
    apply nonneg_of_mul_nonneg_left _ hDpos
    nlinarith
  have hplus : 0 ≤ 2 + vertexG S χ + 3 * vertexF S χ := by
    apply nonneg_of_mul_nonneg_left _ hDpos
    nlinarith [sq_nonneg (χ - S + 2)]
  refine ⟨hgupper, ?_⟩
  rcases le_total 0 (vertexF S χ) with hpos | hneg
  · rw [abs_of_nonneg hpos]
    linarith
  · rw [abs_of_nonpos hneg]
    linarith

theorem vertex_lower_large (S χ : ℝ) (hS : 24 ≤ S) :
    -(3 / 5 : ℝ) ≤ vertexG S χ := by
  have hSpos : 0 < S := by linarith
  have hS3pos : 0 < S - 3 := by linarith
  have hDpos : 0 < 10 * (S * (S - 3)) := by positivity
  have hprod : 0 ≤ (S - 24) * (S + 6) :=
    mul_nonneg (by linarith) (by linarith)
  have hid := vertex_lower_identity S χ (ne_of_gt hSpos) (ne_of_gt hS3pos)
  have hnonneg : 0 ≤ vertexG S χ + 3 / 5 := by
    apply nonneg_of_mul_nonneg_left _ hDpos
    nlinarith [sq_nonneg (χ - (S - 1) / 2)]
  linarith

/-- All three scalar restrictions for every physical spin and Choi block. -/
theorem vertex_region (N K : ℕ) (hN : 3 ≤ N) (hK : K ≤ N) :
    -(3 / 5 : ℝ) ≤ vertexG (spinSize N) (choiCasimir K) ∧
    vertexG (spinSize N) (choiCasimir K) ≤ 1 ∧
    3 * |vertexF (spinSize N) (choiCasimir K)| ≤
      2 + vertexG (spinSize N) (choiCasimir K) ∧
    2 * (spinSize N - 3) * vertexG (spinSize N) (choiCasimir K) =
      3 * spinSize N * (vertexF (spinSize N) (choiCasimir K)) ^ 2 -
      6 * vertexF (spinSize N) (choiCasimir K) - spinSize N := by
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hk : (K : ℝ) ≤ N := by exact_mod_cast hK
  have hk0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hS : 15 ≤ spinSize N := by
    unfold spinSize
    nlinarith
  have hχ : 0 ≤ choiCasimir K := by
    unfold choiCasimir
    positivity
  have hχupper : choiCasimir K ≤ spinSize N - 1 := by
    unfold choiCasimir spinSize
    have hprod := mul_nonneg (sub_nonneg.mpr hk)
      (show 0 ≤ (N : ℝ) + (K : ℝ) + 1 by positivity)
    nlinarith
  have hχdiscrete : choiCasimir K = 0 ∨ 2 ≤ choiCasimir K := by
    by_cases hzero : K = 0
    · left
      simp [choiCasimir, hzero]
    · right
      have hk1 : 1 ≤ K := by omega
      have hk1r : (1 : ℝ) ≤ K := by exact_mod_cast hk1
      unfold choiCasimir
      nlinarith
  have hbasic := vertex_basic_region (spinSize N) (choiCasimir K)
    hS hχ hχupper hχdiscrete
  have hlower : -(3 / 5 : ℝ) ≤ vertexG (spinSize N) (choiCasimir K) := by
    by_cases hthree : N = 3
    · subst N
      interval_cases K <;> norm_num [vertexG, spinSize, choiCasimir]
    · have hfour : 4 ≤ N := by omega
      have hfourr : (4 : ℝ) ≤ N := by exact_mod_cast hfour
      apply vertex_lower_large
      unfold spinSize
      nlinarith
  exact ⟨hlower, hbasic.1, hbasic.2,
    vertex_quadratic _ _ (by linarith) (by linarith)⟩


open scoped BigOperators

/-- Weighted sums commute with affine functions. -/
theorem weighted_affine {ι : Type*} [Fintype ι] (p x : ι → ℝ)
    (hsum : ∑ i, p i = 1) (a b : ℝ) :
    ∑ i, p i * (a * x i + b) = a * (∑ i, p i * x i) + b := by
  simp_rw [mul_add, mul_left_comm (p _) a]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hsum]
  ring

/-- The elementary weighted-variance inequality, with a finite probability law. -/
theorem weighted_square {ι : Type*} [Fintype ι] (p x : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, p i * x i) ^ 2 ≤ ∑ i, p i * (x i) ^ 2 := by
  let m : ℝ := ∑ i, p i * x i
  have hvar : 0 ≤ ∑ i, p i * (x i - m) ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))
  have heq : (∑ i, p i * (x i - m) ^ 2) =
      (∑ i, p i * (x i) ^ 2) - m ^ 2 := by
    calc
      _ = ∑ i, (p i * (x i) ^ 2 + p i * ((-2 * m) * x i + m ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, p i * (x i) ^ 2) + ((-2 * m) * m + m ^ 2) := by
        rw [Finset.sum_add_distrib, weighted_affine p x hsum]
      _ = _ := by ring
  dsimp [m] at heq
  linarith

/-- The multiplier region is preserved by arbitrary finite convex mixtures. -/
theorem mixture_region {ι : Type*} [Fintype ι]
    (S : ℝ) (hS : 15 ≤ S) (p fv gv : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hlower : ∀ i, -(3 / 5 : ℝ) ≤ gv i)
    (hupper : ∀ i, gv i ≤ 1)
    (hlinear : ∀ i, 3 * |fv i| ≤ 2 + gv i)
    (hquad : ∀ i, 2 * (S - 3) * gv i =
      3 * S * (fv i) ^ 2 - 6 * fv i - S) :
    -(3 / 5 : ℝ) ≤ (∑ i, p i * gv i) ∧
    (∑ i, p i * gv i) ≤ 1 ∧
    3 * |∑ i, p i * fv i| ≤ 2 + (∑ i, p i * gv i) ∧
    3 * S * (∑ i, p i * fv i) ^ 2 - 6 * (∑ i, p i * fv i) - S ≤
      2 * (S - 3) * (∑ i, p i * gv i) := by
  let f := ∑ i, p i * fv i
  let g := ∑ i, p i * gv i
  have hlo : -(3 / 5 : ℝ) ≤ g := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_left (hlower i) (hp i))
    simpa [g, ← Finset.sum_mul, hsum] using h
  have hup : g ≤ 1 := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_left (hupper i) (hp i))
    simpa [g, ← Finset.sum_mul, hsum] using h
  have hpos : 3 * f ≤ 2 + g := by
    have hpoint : ∀ i, 3 * fv i ≤ 2 + gv i := by
      intro i
      nlinarith [hlinear i, le_abs_self (fv i)]
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hp i))
    have hleft := weighted_affine p fv hsum 3 0
    have hright := weighted_affine p gv hsum 1 2
    simp only [one_mul, add_zero] at hleft hright
    have hcomm : (∑ i, p i * (2 + gv i)) = ∑ i, p i * (gv i + 2) := by
      congr 1
      funext i
      ring
    rw [hleft, hcomm, hright] at h
    simpa [f, g, add_comm] using h
  have hneg : -3 * f ≤ 2 + g := by
    have hpoint : ∀ i, -3 * fv i ≤ 2 + gv i := by
      intro i
      nlinarith [hlinear i, neg_le_abs (fv i)]
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hp i))
    have hleft := weighted_affine p fv hsum (-3) 0
    have hright := weighted_affine p gv hsum 1 2
    simp only [one_mul, add_zero] at hleft hright
    have hcomm : (∑ i, p i * (2 + gv i)) = ∑ i, p i * (gv i + 2) := by
      congr 1
      funext i
      ring
    rw [hleft, hcomm, hright] at h
    simpa [f, g, add_comm] using h
  have habs : 3 * |f| ≤ 2 + g := by
    rcases le_total 0 f with hf | hf
    · rw [abs_of_nonneg hf]
      exact hpos
    · rw [abs_of_nonpos hf]
      linarith
  have hsq := weighted_square p fv hp hsum
  have hquadratic : 2 * (S - 3) * g =
      3 * S * (∑ i, p i * (fv i) ^ 2) - 6 * f - S := by
    calc
      _ = ∑ i, p i * (2 * (S - 3) * gv i) := by
        have h := weighted_affine p gv hsum (2 * (S - 3)) 0
        simpa [g] using h.symm
      _ = ∑ i, p i * (3 * S * (fv i) ^ 2 - 6 * fv i - S) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hquad i]
      _ = ∑ i, (p i * ((3 * S) * (fv i) ^ 2 + 0) +
          p i * ((-6) * fv i + (-S))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, weighted_affine p (fun i => (fv i) ^ 2) hsum,
          weighted_affine p fv hsum]
        dsimp [f]
        ring
  refine ⟨hlo, hup, habs, ?_⟩
  have hmul : 0 ≤ 3 * S * ((∑ i, p i * (fv i) ^ 2) - f ^ 2) :=
    mul_nonneg (by linarith) (by dsimp [f]; linarith)
  dsimp [f, g] at hquadratic hmul
  nlinarith


/-- Multiplier restrictions for every probability distribution on the N+1 Choi blocks.

The analytic bridge from SU(2)-covariant CPTP maps to this finite probability
law is the Choi/Casimir calculation in the companion mathematical proof.
-/
theorem channel_region (N : ℕ) (hN : 3 ≤ N) (p : Fin (N + 1) → ℝ)
    (hp : ∀ K, 0 ≤ p K) (hsum : ∑ K, p K = 1) :
    let f := ∑ K, p K * vertexF (spinSize N) (choiCasimir K.val);
    let g := ∑ K, p K * vertexG (spinSize N) (choiCasimir K.val);
    -(3 / 5 : ℝ) ≤ g ∧ g ≤ 1 ∧ 3 * |f| ≤ 2 + g ∧
      3 * spinSize N * f ^ 2 - 6 * f - spinSize N ≤
        2 * (spinSize N - 3) * g := by
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hS : 15 ≤ spinSize N := by
    unfold spinSize
    nlinarith
  have hv (K : Fin (N + 1)) :=
    vertex_region N K.val hN (Nat.le_of_lt_succ K.isLt)
  exact mixture_region (spinSize N) hS p
    (fun K => vertexF (spinSize N) (choiCasimir K.val))
    (fun K => vertexG (spinSize N) (choiCasimir K.val)) hp hsum
    (fun K => (hv K).1) (fun K => (hv K).2.1)
    (fun K => (hv K).2.2.1) (fun K => (hv K).2.2.2)

#print axioms channel_region

end

end SU2T2
