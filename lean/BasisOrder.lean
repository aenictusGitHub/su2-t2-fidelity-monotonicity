import SpinGenerators

/-! Conversion between the manuscript numerical arrays (descending m) and
Lean coordinates (ascending m). Both conversions are their own inverses. -/
namespace SU2T2.Spin
noncomputable section

def reverseVector (N : ℕ) (v : Space N) : Space N := fun k => v k.rev

def reverseMatrix (N : ℕ) (A : Mat N) : Mat N := A.submatrix Fin.rev Fin.rev

@[simp] theorem reverseVector_involutive (N : ℕ) (v : Space N) :
    reverseVector N (reverseVector N v)=v := by
  funext k
  simp [reverseVector]

@[simp] theorem reverseMatrix_involutive (N : ℕ) (A : Mat N) :
    reverseMatrix N (reverseMatrix N A)=A := by
  ext k l
  simp [reverseMatrix, Matrix.submatrix]

/-- Coordinate conversion of a linear channel: reverse both input and output. -/
def reverseChannel (N : ℕ) (Φ : Mat N →ₗ[ℂ] Mat N) (A : Mat N) : Mat N :=
  reverseMatrix N (Φ (reverseMatrix N A))

end
end SU2T2.Spin
