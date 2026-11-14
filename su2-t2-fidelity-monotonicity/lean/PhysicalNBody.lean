import PhysicalEmbedding
import DickeEmbedding

/-! Physical symmetric marginals for every N≥3, using the normalized Dicke embedding. -/
namespace SU2T2.Physical
open Matrix
open scoped Matrix ComplexOrder
noncomputable section

/-- Reassociation of the first three qubits. -/
def splitThree (n : ℕ) : (ThreeBits × Dicke.Bits n) ≃ Dicke.Bits (n+3) where
  toFun x := (x.1.1.1,(x.1.1.2,(x.1.2,x.2)))
  invFun x := (((x.1,x.2.1),x.2.2.1),x.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

lemma weight_splitThree (n : ℕ) (b : ThreeBits) (r : Dicke.Bits n) :
    Dicke.weight (splitThree n (b,r))=threeWeight b+Dicke.weight r := by
  simp [splitThree, Dicke.weight, threeWeight, add_assoc]

/-- The Dicke embedding, with qubits grouped as 3 plus N−3. -/
def groupedDicke (n : ℕ) : Matrix (ThreeBits × Dicke.Bits n) (Fin (n+4)) ℂ :=
  (Dicke.embedding (n+3)).submatrix (splitThree n) id

lemma groupedDicke_isometry (n : ℕ) : (groupedDicke n)ᴴ*groupedDicke n=1 := by
  simp [groupedDicke, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Dicke.embedding_isometry]

lemma groupedDicke_weight (n : ℕ) (b : ThreeBits) (r : Dicke.Bits n)
    (k : Fin (n+4)) :
    groupedDicke n (b,r) k =
      if threeWeight b+Dicke.weight r=k.val then
        ((Real.sqrt ((n+3).choose k.val : ℝ) : ℂ))⁻¹ else 0 := by
  simp [groupedDicke, Dicke.embedding, weight_splitThree]

lemma groupedDicke_density (n : ℕ) (ρ : Matrix (Fin (n+4)) (Fin (n+4)) ℂ) :
    groupedDicke n*ρ*(groupedDicke n)ᴴ =
      ((Dicke.embedding (n+3))*ρ*(Dicke.embedding (n+3))ᴴ).submatrix
        (splitThree n) (splitThree n) := by
  simp only [groupedDicke, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul _ _ (splitThree n) id (splitThree n) Function.bijective_id,
    Matrix.submatrix_mul _ _ (splitThree n) id id Function.bijective_id]
  rfl

/-- The physical symmetric two-body marginal of a spin-(n+3)/2 state, in the
Cartesian spin-one basis. It is an actual qubit partial trace of the normalized
Dicke embedding, as `groupedDicke_density` makes explicit. -/
def twoMarginal (n : ℕ) (ρ : Matrix (Fin (n+4)) (Fin (n+4)) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  cartesianTripletᴴ * partialTraceLast
    (partialTraceLast (groupedDicke n*ρ*(groupedDicke n)ᴴ)) * cartesianTriplet

/-- Canonical symmetric N→3→2 reduction for every N=n+3. -/
theorem twoMarginal_has_three_extension (n : ℕ)
    (ρ : Matrix (Fin (n+4)) (Fin (n+4)) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace=1) :
    ∃ ρ3 : Matrix (Fin 4) (Fin 4) ℂ, ρ3.PosSemidef ∧ ρ3.trace=1 ∧
      threeToTwo ρ3=twoMarginal n ρ := by
  apply exists_three_state_of_weight_embedding (groupedDicke n)
    (fun s r k => if s+Dicke.weight r=k.val then
      ((Real.sqrt ((n+3).choose k.val : ℝ) : ℂ))⁻¹ else 0)
  · exact groupedDicke_weight n
  · exact groupedDicke_isometry n
  · exact hρ
  · exact ht

/-- The full physical marginal constraints for arbitrary N≥3. These are proved
from positivity and trace one of the global spin state, not assumed of its reduction. -/
theorem twoMarginal_physical_constraints (n : ℕ)
    (ρ : Matrix (Fin (n+4)) (Fin (n+4)) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace=1) :
    (twoMarginal n ρ).PosSemidef ∧ (twoMarginal n ρ).trace=1 ∧
    (cartesianReal (twoMarginal n ρ)).PosSemidef ∧
    (cartesianReal (twoMarginal n ρ)).trace=2 ∧
    ((3/2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
      cartesianReal (twoMarginal n ρ)).PosSemidef := by
  obtain ⟨ρ3,h3,ht3,hm⟩ := twoMarginal_has_three_extension n ρ hρ ht
  rw [← hm]
  exact threeToTwo_physical_constraints ρ3 h3 ht3

end
end SU2T2.Physical
