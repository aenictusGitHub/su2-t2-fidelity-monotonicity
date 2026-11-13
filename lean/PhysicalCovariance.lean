import PhysicalNBody
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Actual partial traces intertwine local commutator actions. -/
namespace SU2T2.Physical
open Matrix
open scoped Matrix Kronecker ComplexOrder
noncomputable section

lemma partialTraceLast_sub {m n : Type*} [Fintype n]
    (A B : Matrix (m × n) (m × n) ℂ) :
    partialTraceLast (A-B)=partialTraceLast A-partialTraceLast B := by
  ext i j
  simp [partialTraceLast, Finset.sum_sub_distrib]

lemma partialTraceLast_add {m n : Type*} [Fintype n]
    (A B : Matrix (m × n) (m × n) ℂ) :
    partialTraceLast (A+B)=partialTraceLast A+partialTraceLast B := by
  ext i j
  simp [partialTraceLast, Finset.sum_add_distrib]

lemma partialTraceLast_left_mul {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (R : Matrix (m × n) (m × n) ℂ) :
    partialTraceLast ((A ⊗ₖ (1 : Matrix n n ℂ))*R)=A*partialTraceLast R := by
  ext i j
  simp [partialTraceLast, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma partialTraceLast_mul_left {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (R : Matrix (m × n) (m × n) ℂ) :
    partialTraceLast (R*(A ⊗ₖ (1 : Matrix n n ℂ)))=partialTraceLast R*A := by
  ext i j
  simp [partialTraceLast, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma partialTraceLast_right_cycle {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (B : Matrix n n ℂ) (R : Matrix (m × n) (m × n) ℂ) :
    partialTraceLast (((1 : Matrix m m ℂ) ⊗ₖ B)*R)=
      partialTraceLast (R*((1 : Matrix m m ℂ) ⊗ₖ B)) := by
  ext i j
  simp [partialTraceLast, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_comm]
  rw [Finset.sum_comm]

lemma partialTraceLast_commutator {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (R : Matrix (m × n) (m × n) ℂ) :
    partialTraceLast
      (((A ⊗ₖ (1 : Matrix n n ℂ)) + ((1 : Matrix m m ℂ) ⊗ₖ B))*R-
        R*((A ⊗ₖ (1 : Matrix n n ℂ)) + ((1 : Matrix m m ℂ) ⊗ₖ B))) =
      A*partialTraceLast R-partialTraceLast R*A := by
  simp only [Matrix.add_mul, Matrix.mul_add, partialTraceLast_sub, partialTraceLast_add,
    partialTraceLast_left_mul, partialTraceLast_mul_left, partialTraceLast_right_cycle]
  abel

lemma embed_commutator {m n : Type*} [Fintype m] [Fintype n]
    (V : Matrix m n ℂ) (G : Matrix m m ℂ) (J ρ : Matrix n n ℂ)
    (hL : G*V=V*J) (hR : Vᴴ*G=J*Vᴴ) :
    V*(J*ρ-ρ*J)*Vᴴ = G*(V*ρ*Vᴴ)-(V*ρ*Vᴴ)*G := by
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · calc
      V*(J*ρ)*Vᴴ=(V*J)*ρ*Vᴴ := by simp [Matrix.mul_assoc]
      _=(G*V)*ρ*Vᴴ := by rw [hL]
      _=G*(V*ρ*Vᴴ) := by simp [Matrix.mul_assoc]
  · calc
      V*(ρ*J)*Vᴴ=V*ρ*(J*Vᴴ) := by simp [Matrix.mul_assoc]
      _=V*ρ*(Vᴴ*G) := by rw [hR]
      _=V*ρ*Vᴴ*G := by simp [Matrix.mul_assoc]

lemma compress_commutator {m n : Type*} [Fintype m] [Fintype n]
    (V : Matrix m n ℂ) (G R : Matrix m m ℂ) (J : Matrix n n ℂ)
    (hL : G*V=V*J) (hR : Vᴴ*G=J*Vᴴ) :
    Vᴴ*(G*R-R*G)*V=J*(Vᴴ*R*V)-(Vᴴ*R*V)*J := by
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · calc
      Vᴴ*(G*R)*V=(Vᴴ*G)*R*V := by simp [Matrix.mul_assoc]
      _=(J*Vᴴ)*R*V := by rw [hR]
      _=J*(Vᴴ*R*V) := by simp [Matrix.mul_assoc]
  · calc
      Vᴴ*(R*G)*V=Vᴴ*R*(G*V) := by simp [Matrix.mul_assoc]
      _=Vᴴ*R*(V*J) := by rw [hL]
      _=Vᴴ*R*V*J := by simp [Matrix.mul_assoc]

end
end SU2T2.Physical
