import PhysicalCovariance
import DickeGenerators
import TraceDual
import SpinCovariance

/-! Covariance of the actual two-body marginal in the standard spin-one basis. -/
namespace SU2T2.Physical
open Matrix
open scoped Matrix Kronecker
noncomputable section

def splitTwo (n : ℕ) : (TwoBits × Dicke.Bits (n+1)) ≃ Dicke.Bits (n+3) where
  toFun x := (x.1.1,(x.1.2,x.2))
  invFun x := ((x.1,x.2.1),x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def twoBitsEquiv : TwoBits ≃ Dicke.Bits 2 where
  toFun x := (x.1,(x.2,()))
  invFun x := (x.1,x.2.1)
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨a,b,u⟩; cases u; rfl

def dicke2 : Matrix TwoBits (Fin 3) ℂ :=
  (Dicke.embedding 2).submatrix twoBitsEquiv id

def groupedTwoDicke (n : ℕ) : Matrix (TwoBits × Dicke.Bits (n+1)) (Fin (n+4)) ℂ :=
  (Dicke.embedding (n+3)).submatrix (splitTwo n) id

def spinOneMarginal (n : ℕ) : Spin.Mat (n+3) →ₗ[ℂ] Spin.Mat 2 where
  toFun ρ := dicke2ᴴ * partialTraceLast
    (groupedTwoDicke n*ρ*(groupedTwoDicke n)ᴴ) * dicke2
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul, partialTraceLast_add]
  map_smul' c A := by
    ext i j
    simp [partialTraceLast, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm]

lemma groupedTwoDicke_isometry (n : ℕ) :
    (groupedTwoDicke n)ᴴ*groupedTwoDicke n=1 := by
  simp [groupedTwoDicke, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Dicke.embedding_isometry]

lemma dicke2_isometry : dicke2ᴴ*dicke2=1 := by
  simp [dicke2, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Dicke.embedding_isometry]

lemma reindex_intertwiner {m m' d : Type*} [Fintype m] [Fintype m'] [Fintype d]
    (e : m' ≃ m) (D : Matrix m d ℂ) (G : Matrix m m ℂ) (J : Matrix d d ℂ)
    (h : G*D=D*J) : G.submatrix e e*D.submatrix e id=D.submatrix e id*J := by
  rw [Matrix.submatrix_mul_equiv]
  simpa only [Matrix.submatrix_mul, Matrix.submatrix_id_id] using
    congrArg (fun M => M.submatrix e id) h

lemma reindex_intertwiner_right {m m' d : Type*} [Fintype m] [Fintype m'] [Fintype d]
    (e : m' ≃ m) (D : Matrix m d ℂ) (G : Matrix m m ℂ) (J : Matrix d d ℂ)
    (h : Dᴴ*G=J*Dᴴ) : (D.submatrix e id)ᴴ*G.submatrix e e=J*(D.submatrix e id)ᴴ := by
  simp only [Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv]
  simpa only [Matrix.submatrix_mul, Matrix.submatrix_id_id] using
    congrArg (fun M => M.submatrix id e) h

def twoRaising : Matrix TwoBits TwoBits ℂ :=
  (Dicke.totalRaising 2).submatrix twoBitsEquiv twoBitsEquiv

def twoZ : Matrix TwoBits TwoBits ℂ :=
  (Dicke.totalZ 2).submatrix twoBitsEquiv twoBitsEquiv

lemma grouped_raising (n : ℕ) :
    (Dicke.totalRaising (n+3)).submatrix (splitTwo n) (splitTwo n) =
      twoRaising ⊗ₖ (1 : Matrix (Dicke.Bits (n+1)) (Dicke.Bits (n+1)) ℂ) +
      (1 : Matrix TwoBits TwoBits ℂ) ⊗ₖ Dicke.totalRaising (n+1) := by
  ext ⟨⟨a,b⟩,⟨r₀,r₁⟩⟩ ⟨⟨c,d⟩,⟨s₀,s₁⟩⟩
  dsimp [Matrix.submatrix, splitTwo, twoRaising, twoBitsEquiv]
  simp only [Dicke.totalRaising, Matrix.add_apply, Matrix.kronecker_apply]
  simp only [Matrix.one_apply, Prod.ext_iff]
  by_cases h₁ : a=c <;> by_cases h₂ : b=d <;> by_cases h₃ : r₀=s₀ <;> by_cases h₄ : r₁=s₁ <;>
    simp_all [Dicke.Bits, Dicke.qubitRaising, Matrix.one_apply, Prod.ext_iff] <;> ring

lemma grouped_z (n : ℕ) :
    (Dicke.totalZ (n+3)).submatrix (splitTwo n) (splitTwo n) =
      twoZ ⊗ₖ (1 : Matrix (Dicke.Bits (n+1)) (Dicke.Bits (n+1)) ℂ) +
      (1 : Matrix TwoBits TwoBits ℂ) ⊗ₖ Dicke.totalZ (n+1) := by
  ext ⟨⟨a,b⟩,⟨r₀,r₁⟩⟩ ⟨⟨c,d⟩,⟨s₀,s₁⟩⟩
  dsimp [Matrix.submatrix, splitTwo, twoZ, twoBitsEquiv]
  simp only [Dicke.totalZ, Matrix.diagonal_apply, Matrix.add_apply, Matrix.kronecker_apply]
  simp only [Matrix.one_apply, Prod.ext_iff, Dicke.weight]
  by_cases h₁ : a=c <;> by_cases h₂ : b=d <;> by_cases h₃ : r₀=s₀ <;> by_cases h₄ : r₁=s₁ <;>
    simp_all [Dicke.Bits, Prod.ext_iff] <;> push_cast <;> ring

lemma grouped_lowering (n : ℕ) :
    ((Dicke.totalRaising (n+3))ᴴ).submatrix (splitTwo n) (splitTwo n) =
      twoRaisingᴴ ⊗ₖ (1 : Matrix (Dicke.Bits (n+1)) (Dicke.Bits (n+1)) ℂ) +
      (1 : Matrix TwoBits TwoBits ℂ) ⊗ₖ (Dicke.totalRaising (n+1))ᴴ := by
  rw [← Matrix.conjTranspose_submatrix, grouped_raising]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

lemma twoMarginal_eq_grouped (n : ℕ) (ρ : Spin.Mat (n+3)) :
    twoMarginal n ρ = cartesianTripletᴴ * partialTraceLast
      (groupedTwoDicke n*ρ*(groupedTwoDicke n)ᴴ) * cartesianTriplet := by
  unfold twoMarginal
  congr 2
  rw [partialTraceLast_assoc]
  congr 1

lemma spinOneMarginal_intertwines (n : ℕ)
    (G : Matrix (Dicke.Bits (n+3)) (Dicke.Bits (n+3)) ℂ)
    (A : Matrix (Dicke.Bits 2) (Dicke.Bits 2) ℂ)
    (B : Matrix (Dicke.Bits (n+1)) (Dicke.Bits (n+1)) ℂ)
    (J : Spin.Mat (n+3)) (K : Spin.Mat 2)
    (hG : G.submatrix (splitTwo n) (splitTwo n) =
      A.submatrix twoBitsEquiv twoBitsEquiv ⊗ₖ (1 : Matrix _ _ ℂ) +
      (1 : Matrix TwoBits TwoBits ℂ) ⊗ₖ B)
    (hJL : G*Dicke.embedding (n+3)=Dicke.embedding (n+3)*J)
    (hJR : (Dicke.embedding (n+3))ᴴ*G=J*(Dicke.embedding (n+3))ᴴ)
    (hKL : A*Dicke.embedding 2=Dicke.embedding 2*K)
    (hKR : (Dicke.embedding 2)ᴴ*A=K*(Dicke.embedding 2)ᴴ)
    (ρ : Spin.Mat (n+3)) :
    spinOneMarginal n (J*ρ-ρ*J)=K*spinOneMarginal n ρ-spinOneMarginal n ρ*K := by
  change dicke2ᴴ * partialTraceLast
    (groupedTwoDicke n*(J*ρ-ρ*J)*(groupedTwoDicke n)ᴴ) * dicke2 = _
  dsimp only [groupedTwoDicke]
  rw [embed_commutator _ (G.submatrix (splitTwo n) (splitTwo n)) _ _
    (reindex_intertwiner (splitTwo n) _ _ _ hJL)
    (reindex_intertwiner_right (splitTwo n) _ _ _ hJR), hG,
    partialTraceLast_commutator]
  exact compress_commutator dicke2 (A.submatrix twoBitsEquiv twoBitsEquiv) _ K
    (reindex_intertwiner twoBitsEquiv _ _ _ hKL)
    (reindex_intertwiner_right twoBitsEquiv _ _ _ hKR)

lemma raising_right (N : ℕ) :
    (Dicke.embedding N)ᴴ*Dicke.totalRaising N=Spin.raising N*(Dicke.embedding N)ᴴ := by
  simpa [Spin.lowering] using
    congrArg Matrix.conjTranspose (Dicke.totalLowering_intertwines N)

lemma lowering_right (N : ℕ) :
    (Dicke.embedding N)ᴴ*(Dicke.totalRaising N)ᴴ=Spin.lowering N*(Dicke.embedding N)ᴴ := by
  simpa [Spin.lowering] using
    congrArg Matrix.conjTranspose (Dicke.totalRaising_intertwines N)

lemma totalZ_hermitian (N : ℕ) : (Dicke.totalZ N).IsHermitian := by
  unfold Matrix.IsHermitian Dicke.totalZ
  simp [Matrix.diagonal_conjTranspose]

lemma z_right (N : ℕ) :
    (Dicke.embedding N)ᴴ*Dicke.totalZ N=Spin.zAxis N*(Dicke.embedding N)ᴴ := by
  have h := congrArg Matrix.conjTranspose (Dicke.totalZ_intertwines N)
  simpa only [Matrix.conjTranspose_mul, (totalZ_hermitian N).eq,
    (Spin.zAxis_isHermitian N).eq] using h

lemma spinOneMarginal_raising (n : ℕ) (ρ : Spin.Mat (n+3)) :
    spinOneMarginal n (Spin.raising (n+3)*ρ-ρ*Spin.raising (n+3)) =
      Spin.raising 2*spinOneMarginal n ρ-spinOneMarginal n ρ*Spin.raising 2 := by
  exact spinOneMarginal_intertwines n (Dicke.totalRaising (n+3)) (Dicke.totalRaising 2)
    (Dicke.totalRaising (n+1)) _ _ (grouped_raising n)
    (Dicke.totalRaising_intertwines _) (raising_right _)
    (Dicke.totalRaising_intertwines _) (raising_right _) ρ

lemma spinOneMarginal_lowering (n : ℕ) (ρ : Spin.Mat (n+3)) :
    spinOneMarginal n (Spin.lowering (n+3)*ρ-ρ*Spin.lowering (n+3)) =
      Spin.lowering 2*spinOneMarginal n ρ-spinOneMarginal n ρ*Spin.lowering 2 := by
  apply spinOneMarginal_intertwines n (Dicke.totalRaising (n+3))ᴴ (Dicke.totalRaising 2)ᴴ
    (Dicke.totalRaising (n+1))ᴴ _ _ _
    (Dicke.totalLowering_intertwines _) (lowering_right _)
    (Dicke.totalLowering_intertwines _) (lowering_right _) ρ
  simpa [twoRaising, Matrix.conjTranspose_submatrix] using grouped_lowering n

lemma spinOneMarginal_z (n : ℕ) (ρ : Spin.Mat (n+3)) :
    spinOneMarginal n (Spin.zAxis (n+3)*ρ-ρ*Spin.zAxis (n+3)) =
      Spin.zAxis 2*spinOneMarginal n ρ-spinOneMarginal n ρ*Spin.zAxis 2 := by
  exact spinOneMarginal_intertwines n (Dicke.totalZ (n+3)) (Dicke.totalZ 2)
    (Dicke.totalZ (n+1)) _ _ (grouped_z n)
    (Dicke.totalZ_intertwines _) (z_right _)
    (Dicke.totalZ_intertwines _) (z_right _) ρ

end
end SU2T2.Physical
