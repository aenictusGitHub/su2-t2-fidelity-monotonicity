import PhysicalTwoCovariance
import PhysicalTransfer

/-! Trace preservation and low-rank transfer for the physical marginal. -/
namespace SU2T2.Physical
open Matrix
noncomputable section

lemma dicke2_projector_fixes_weight (F : ℕ → ℂ) :
    (dicke2*dicke2ᴴ) *ᵥ (fun b => F (b.1.val+b.2.val)) = fun b => F (b.1.val+b.2.val) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hsi : ((Real.sqrt 2)⁻¹)^2=(1/2:ℝ) := by rw [inv_pow,hs]; norm_num
  have hsC : ((Real.sqrt 2:ℝ):ℂ)^2=2 := by exact_mod_cast hs
  have hsiC : (((Real.sqrt 2:ℝ):ℂ)⁻¹)^2=(1/2:ℂ) := by rw [inv_pow,hsC]; norm_num
  rw [← Matrix.mulVec_mulVec]
  ext ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, dicke2, twoBitsEquiv,
      Dicke.embedding,Dicke.weight,Fintype.sum_prod_type,Fin.sum_univ_succ] <;>
    norm_num <;> ring_nf <;> norm_num [hs,hsi,hsiC,map_ofNat] <;> ring

lemma groupedTwoDicke_weight (n : ℕ) (b : TwoBits) (r : Dicke.Bits (n+1))
    (k : Fin (n+4)) :
    groupedTwoDicke n (b,r) k =
      if b.1.val+b.2.val+Dicke.weight r=k.val then
        ((Real.sqrt ((n+3).choose k.val : ℝ) : ℂ))⁻¹ else 0 := by
  simp [groupedTwoDicke,Dicke.embedding,splitTwo,Dicke.weight,add_assoc]

lemma two_support (n : ℕ) (ρ : Spin.Mat (n+3)) :
    (dicke2*dicke2ᴴ)*partialTraceLast (groupedTwoDicke n*ρ*(groupedTwoDicke n)ᴴ)=
      partialTraceLast (groupedTwoDicke n*ρ*(groupedTwoDicke n)ᴴ) := by
  have hslice (r : Dicke.Bits (n+1)) :
      (dicke2*dicke2ᴴ)*(groupedTwoDicke n).submatrix (fun b => (b,r)) id =
        (groupedTwoDicke n).submatrix (fun b => (b,r)) id := by
    ext b k
    have h := congrFun (dicke2_projector_fixes_weight (fun s =>
      if s+Dicke.weight r=k.val then
        ((Real.sqrt ((n+3).choose k.val : ℝ) : ℂ))⁻¹ else 0)) b
    simpa [Matrix.mul_apply,Matrix.mulVec,dotProduct,groupedTwoDicke_weight] using h
  rw [partialTraceLast_embedding,Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [← Matrix.mul_assoc,hslice]

lemma spinOneMarginal_trace (n : ℕ) (ρ : Spin.Mat (n+3)) :
    (spinOneMarginal n ρ).trace=ρ.trace := by
  change (dicke2ᴴ * partialTraceLast
    (groupedTwoDicke n*ρ*(groupedTwoDicke n)ᴴ) * dicke2).trace=ρ.trace
  rw [Matrix.trace_mul_cycle,two_support,
    partialTraceLast_trace,Matrix.trace_mul_cycle,groupedTwoDicke_isometry,Matrix.one_mul]

lemma partialTraceLast_conjTranspose {m n : Type*} [Fintype n]
    (R : Matrix (m×n) (m×n) ℂ) : partialTraceLast Rᴴ=(partialTraceLast R)ᴴ := by
  ext i j
  simp [partialTraceLast,Matrix.conjTranspose_apply,map_sum]

lemma spinOneMarginal_conjTranspose (n : ℕ) (ρ : Spin.Mat (n+3)) :
    spinOneMarginal n ρᴴ=(spinOneMarginal n ρ)ᴴ := by
  change dicke2ᴴ * partialTraceLast
    (groupedTwoDicke n*ρᴴ*(groupedTwoDicke n)ᴴ) * dicke2 =
      (dicke2ᴴ * partialTraceLast (groupedTwoDicke n*ρ*(groupedTwoDicke n)ᴴ) * dicke2)ᴴ
  simp [Matrix.conjTranspose_mul,Matrix.mul_assoc,← partialTraceLast_conjTranspose]

lemma marginalDual_identity (n : ℕ) : Choi.traceDual (spinOneMarginal n) 1=1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro ρ
  rw [Choi.traceDual_pairing]
  simp [spinOneMarginal_trace]

lemma marginalDual_raising (n : ℕ) (B : Spin.Mat 2) :
    Choi.traceDual (spinOneMarginal n) (Spin.raising 2*B-B*Spin.raising 2)=
      Spin.raising (n+3)*Choi.traceDual (spinOneMarginal n) B-
      Choi.traceDual (spinOneMarginal n) B*Spin.raising (n+3) :=
  Choi.traceDual_intertwiner _ _ _ (spinOneMarginal_raising n) B

lemma marginalDual_z (n : ℕ) (B : Spin.Mat 2) :
    Choi.traceDual (spinOneMarginal n) (Spin.zAxis 2*B-B*Spin.zAxis 2)=
      Spin.zAxis (n+3)*Choi.traceDual (spinOneMarginal n) B-
      Choi.traceDual (spinOneMarginal n) B*Spin.zAxis (n+3) :=
  Choi.traceDual_intertwiner _ _ _ (spinOneMarginal_z n) B

lemma marginalDual_lowering (n : ℕ) (B : Spin.Mat 2) :
    Choi.traceDual (spinOneMarginal n) (Spin.lowering 2*B-B*Spin.lowering 2)=
      Spin.lowering (n+3)*Choi.traceDual (spinOneMarginal n) B-
      Choi.traceDual (spinOneMarginal n) B*Spin.lowering (n+3) :=
  Choi.traceDual_intertwiner _ _ _ (spinOneMarginal_lowering n) B

lemma marginalDual_highest_eigenvectors (n : ℕ)
    (Φ : Spin.Mat (n+3) →ₗ[ℂ] Spin.Mat (n+3))
    (f g : ℂ) (hf : Φ (Spin.raising (n+3))=f • Spin.raising (n+3))
    (hg : Φ (Spin.raising (n+3)*Spin.raising (n+3))=
      g • (Spin.raising (n+3)*Spin.raising (n+3))) :
    Φ (Choi.traceDual (spinOneMarginal n) (Spin.raising 2))=
      f • Choi.traceDual (spinOneMarginal n) (Spin.raising 2) ∧
    Φ (Choi.traceDual (spinOneMarginal n) (Spin.raising 2*Spin.raising 2))=
      g • Choi.traceDual (spinOneMarginal n) (Spin.raising 2*Spin.raising 2) :=
  transferred_highest_eigenvectors (n+3) (by omega) _ Φ
    (marginalDual_raising n) (marginalDual_z n) f g hf hg

lemma cartesianTriplet_eq_dicke2_explicit :
    cartesianTriplet = dicke2 *
      !![-(Real.sqrt 2 : ℂ)/2,Complex.I*(Real.sqrt 2 : ℂ)/2,0;
          0,0,1;
          (Real.sqrt 2 : ℂ)/2,Complex.I*(Real.sqrt 2 : ℂ)/2,0] := by
  have hs : (Real.sqrt 2:ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hn : (Real.sqrt 2:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)))
  have hi : (Real.sqrt 2:ℂ)⁻¹=(Real.sqrt 2:ℂ)/2 := by
    apply (mul_left_cancel₀ hn)
    rw [mul_inv_cancel₀ hn]
    linear_combination -hs/2
  ext ⟨a,b⟩ k
  fin_cases a <;> fin_cases b <;> fin_cases k <;>
    simp [cartesianTriplet,dicke2,twoBitsEquiv,Dicke.embedding,Dicke.weight,
      Matrix.mul_apply,Fin.sum_univ_succ] <;> norm_num [hi]

end
end SU2T2.Physical
