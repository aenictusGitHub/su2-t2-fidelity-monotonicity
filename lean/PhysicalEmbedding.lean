import PhysicalMarginal

/-! Identification of the concrete marginal map with an actual qubit partial trace. -/
namespace SU2T2.Physical
open Matrix
open scoped ComplexOrder Matrix
noncomputable section

/-- Three ordered qubits, with the last qubit traced out. -/
abbrev ThreeBits := (Fin 2 × Fin 2) × Fin 2
abbrev TwoBits := Fin 2 × Fin 2

def dicke3 : Matrix ThreeBits (Fin 4) ℂ := fun b k =>
  if b.1.1.val + b.1.2.val + b.2.val = k.val then
    if k.val=0 ∨ k.val=3 then 1 else (Real.sqrt 3 : ℂ)/3
  else 0

/-- The Cartesian triplet basis in two physical qubits. -/
def cartesianTriplet : Matrix TwoBits (Fin 3) ℂ := fun b =>
  if b=(0,0) then ![-(Real.sqrt 2 : ℂ)/2, Complex.I*(Real.sqrt 2 : ℂ)/2,0]
  else if b=(1,1) then ![(Real.sqrt 2 : ℂ)/2, Complex.I*(Real.sqrt 2 : ℂ)/2,0]
  else ![0,0,(Real.sqrt 2 : ℂ)/2]

/-- A genuine partial trace, defined by its standard matrix-entry sum. -/
def partialTraceLast {m n : Type*} [Fintype n]
    (R : Matrix (m × n) (m × n) ℂ) : Matrix m m ℂ :=
  fun i j => ∑ k, R (i,k) (j,k)

lemma partialTraceLast_embedding {m n d : Type*} [Fintype n] [Fintype d]
    (V : Matrix (m × n) d ℂ) (ρ : Matrix d d ℂ) :
    partialTraceLast (V * ρ * Vᴴ) =
      ∑ k, (V.submatrix (fun i => (i,k)) id) * ρ *
        (V.submatrix (fun i => (i,k)) id)ᴴ := by
  ext i j
  simp [partialTraceLast, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply]

set_option maxHeartbeats 1000000 in
lemma dicke3_isometry : dicke3ᴴ * dicke3 = 1 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [dicke3, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Complex.ext_iff, Complex.mul_re, Complex.mul_im] <;>
    norm_num <;> ring_nf <;> simp [hs] <;> ring_nf <;> norm_num [hs]

set_option maxHeartbeats 1000000 in
lemma cartesianTriplet_isometry : cartesianTripletᴴ * cartesianTriplet = 1 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [cartesianTriplet, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im] <;>
    norm_num <;> ring_nf <;> simp [hs] <;> ring_nf <;> norm_num [hs]

set_option maxHeartbeats 1000000 in
lemma cartesian_dicke_kraus (k : Fin 2) :
    cartesianTripletᴴ * (dicke3.submatrix (fun i => (i,k)) id) =
      (((Real.sqrt 2 * Real.sqrt 3)/6 : ℝ) : ℂ) •
        (if k=0 then marginalKraus0 else marginalKraus1) := by
  have hs3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [cartesianTriplet, dicke3, marginalKraus0, marginalKraus1,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
      Matrix.smul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im] <;>
    norm_num <;> ring_nf <;> simp [hs3, hs2] <;> ring_nf <;> norm_num [hs3, hs2]

lemma threeToTwo_eq_partialTrace (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    threeToTwo ρ =
      cartesianTripletᴴ * partialTraceLast (dicke3 * ρ * dicke3ᴴ) * cartesianTriplet := by
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  let q : ℂ := ((Real.sqrt 2 * Real.sqrt 3)/6 : ℝ)
  have hq : star q * q = (1/6 : ℝ) := by
    dsimp [q]
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;>
      ring_nf <;> simp [hs2, hs3] <;> norm_num <;> ring_nf <;> norm_num [hs2, hs3]
  have h : cartesianTripletᴴ * partialTraceLast (dicke3 * ρ * dicke3ᴴ) *
      cartesianTriplet =
      ∑ k : Fin 2, (cartesianTripletᴴ * dicke3.submatrix (fun i => (i,k)) id) * ρ *
        (cartesianTripletᴴ * dicke3.submatrix (fun i => (i,k)) id)ᴴ := by
    rw [partialTraceLast_embedding, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [h]
  simp_rw [cartesian_dicke_kraus]
  simp only [Fin.sum_univ_two, ↓reduceIte, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num only [Fin.reduceEq, if_false]
  change (1/6 : ℝ) • (marginalKraus0 * ρ * marginalKraus0ᴴ +
      marginalKraus1 * ρ * marginalKraus1ᴴ) =
    (star q * q) • (marginalKraus0 * ρ * marginalKraus0ᴴ) +
    (star q * q) • (marginalKraus1 * ρ * marginalKraus1ᴴ)
  rw [hq]
  ext i j
  simp [smul_add, Matrix.smul_apply, Complex.real_smul]

lemma partialTraceLast_posSemidef {m n : Type*} [Fintype m] [Fintype n]
    (R : Matrix (m × n) (m × n) ℂ) (hR : R.PosSemidef) :
    (partialTraceLast R).PosSemidef := by
  have he : partialTraceLast R = ∑ k : n, R.submatrix (fun i => (i,k)) (fun i => (i,k)) := by
    ext i j
    simp [partialTraceLast, Matrix.sum_apply]
  rw [he]
  have hsum (s : Finset n) :
      (∑ k ∈ s, R.submatrix (fun i => (i,k)) (fun i => (i,k))).PosSemidef := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Matrix.PosSemidef.zero]
    | @insert k s hk ih =>
      simpa [Finset.sum_insert hk] using (hR.submatrix (fun i => (i,k))).add ih
  simpa using hsum Finset.univ

lemma partialTraceLast_trace {m n : Type*} [Fintype m] [Fintype n]
    (R : Matrix (m × n) (m × n) ℂ) : (partialTraceLast R).trace=R.trace := by
  simp [partialTraceLast, Matrix.trace, Fintype.sum_prod_type]

/-- Density matrix on the spin-3/2 sector obtained by compressing a supported
three-qubit density matrix. -/
def compressThree (R : Matrix ThreeBits ThreeBits ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  dicke3ᴴ * R * dicke3

lemma supported_reconstruction (R : Matrix ThreeBits ThreeBits ℂ)
    (hR : R.PosSemidef) (hsupport : (dicke3 * dicke3ᴴ) * R=R) :
    dicke3 * compressThree R * dicke3ᴴ=R := by
  have hr : R * (dicke3 * dicke3ᴴ)=R := by
    have h := congrArg Matrix.conjTranspose hsupport
    simpa [Matrix.conjTranspose_mul, hR.isHermitian.eq, Matrix.mul_assoc] using h
  calc
    dicke3 * compressThree R * dicke3ᴴ =
        ((dicke3*dicke3ᴴ)*R)*(dicke3*dicke3ᴴ) := by
          simp [compressThree, Matrix.mul_assoc]
    _ = R := by rw [hsupport, hr]

lemma compressThree_density (R : Matrix ThreeBits ThreeBits ℂ)
    (hR : R.PosSemidef) (ht : R.trace=1)
    (hsupport : (dicke3 * dicke3ᴴ) * R=R) :
    (compressThree R).PosSemidef ∧ (compressThree R).trace=1 := by
  constructor
  · exact hR.conjTranspose_mul_mul_same dicke3
  · unfold compressThree
    rw [Matrix.trace_mul_cycle, hsupport, ht]

/-- Every density matrix supported on the actual symmetric three-qubit subspace
has a two-qubit Cartesian marginal obeying the bound needed in the proof. -/
theorem supported_three_marginal_upper (R : Matrix ThreeBits ThreeBits ℂ)
    (hR : R.PosSemidef) (ht : R.trace=1)
    (hsupport : (dicke3 * dicke3ᴴ) * R=R) :
    ((3/2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
      cartesianReal (cartesianTripletᴴ * partialTraceLast R * cartesianTriplet)).PosSemidef := by
  have hd := compressThree_density R hR ht hsupport
  have hm := threeToTwo_upper (compressThree R) hd.1 hd.2
  rw [threeToTwo_eq_partialTrace, supported_reconstruction R hR hsupport] at hm
  exact hm

def threeWeight (b : ThreeBits) : ℕ := b.1.1.val+b.1.2.val+b.2.val

set_option maxHeartbeats 2000000 in
lemma dicke3_projector_fixes_weight (F : ℕ → ℂ) :
    (dicke3*dicke3ᴴ) *ᵥ (fun b => F (threeWeight b)) =
      fun b => F (threeWeight b) := by
  have hs : ((Real.sqrt 3 : ℝ) : ℂ)^2=3 := by
    exact_mod_cast (Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num))
  rw [← Matrix.mulVec_mulVec]
  ext b
  rcases b with ⟨⟨b0,b1⟩,b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, dicke3, threeWeight,
      Fintype.sum_prod_type, Fin.sum_univ_succ] <;>
    norm_num <;> ring_nf <;> norm_num [hs, map_ofNat] <;> ring

/-- Associativity of the partial trace, including the explicit product reassociation. -/
lemma partialTraceLast_assoc {m n p : Type*} [Fintype n] [Fintype p]
    (R : Matrix ((m × n) × p) ((m × n) × p) ℂ) :
    partialTraceLast (partialTraceLast R) =
      partialTraceLast (R.submatrix (fun x : m × (n × p) => ((x.1,x.2.1),x.2.2))
        (fun x : m × (n × p) => ((x.1,x.2.1),x.2.2))) := by
  ext i j
  simp [partialTraceLast, Fintype.sum_prod_type]

/-- Every Dicke-type embedding is constant on the first-three-qubit weight
classes. This gives symmetric support after reduction to three qubits. -/
lemma weight_embedding_three_support {r d : Type*} [Fintype r] [Fintype d]
    (V : Matrix (ThreeBits × r) d ℂ) (F : ℕ → r → d → ℂ)
    (hweight : ∀ b a k, V (b,a) k=F (threeWeight b) a k)
    (ρ : Matrix d d ℂ) :
    (dicke3*dicke3ᴴ) * partialTraceLast (V*ρ*Vᴴ) = partialTraceLast (V*ρ*Vᴴ) := by
  have hslice (a : r) :
      (dicke3*dicke3ᴴ) * V.submatrix (fun b => (b,a)) id =
        V.submatrix (fun b => (b,a)) id := by
    ext b k
    have h := congrFun (dicke3_projector_fixes_weight (fun s => F s a k)) b
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hweight] using h
  rw [partialTraceLast_embedding, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [← Matrix.mul_assoc, hslice]

/-- Canonical reduction from any isometric Dicke-type embedding to a genuine
spin-3/2 density matrix. No bound on the resulting two-body marginal is assumed. -/
theorem exists_three_state_of_weight_embedding {r d : Type*}
    [Fintype r] [Fintype d] [DecidableEq d]
    (V : Matrix (ThreeBits × r) d ℂ) (F : ℕ → r → d → ℂ)
    (hweight : ∀ b a k, V (b,a) k=F (threeWeight b) a k)
    (hisometry : Vᴴ*V=1) (ρ : Matrix d d ℂ)
    (hρ : ρ.PosSemidef) (ht : ρ.trace=1) :
    ∃ ρ3 : Matrix (Fin 4) (Fin 4) ℂ, ρ3.PosSemidef ∧ ρ3.trace=1 ∧
      threeToTwo ρ3 = cartesianTripletᴴ *
        partialTraceLast (partialTraceLast (V*ρ*Vᴴ)) * cartesianTriplet := by
  let R := partialTraceLast (V*ρ*Vᴴ)
  have hR : R.PosSemidef := partialTraceLast_posSemidef _ (hρ.mul_mul_conjTranspose_same V)
  have htR : R.trace=1 := by
    dsimp [R]
    rw [partialTraceLast_trace, Matrix.trace_mul_cycle, hisometry, Matrix.one_mul, ht]
  have hsR : (dicke3*dicke3ᴴ)*R=R := weight_embedding_three_support V F hweight ρ
  have hd := compressThree_density R hR htR hsR
  refine ⟨compressThree R, hd.1, hd.2, ?_⟩
  rw [threeToTwo_eq_partialTrace, supported_reconstruction R hR hsR]

end
end SU2T2.Physical
