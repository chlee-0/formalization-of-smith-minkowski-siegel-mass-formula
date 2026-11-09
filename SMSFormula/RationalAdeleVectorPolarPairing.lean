import SMSFormula.RationalAdeleCoordinateElementaryFourier
import SMSFormula.RationalSpecialOrthogonalTamagawa

/-!
# Rational-adelic vector polar pairing

This file fixes the matrix convention needed for vector Fourier analysis.  A
`RationalQuadraticSpaceMatrix` stores the symmetric matrix `F` of
`q(x) = x^T F x`; the matrix of the polar form is therefore `C = 2F`.

We define the exact full-adelic polar character

`(x,y) |-> psi (x^T C y)`

and prove its relation to the already certified coordinate Fourier character,
its triviality on rational diagonals, and its covariance under the existing
full-adelic orthogonal carrier.  No Fourier integral, change of measure, dual
lattice, shell decomposition, or Tamagawa-number assertion is made here.
-/

noncomputable section

open Matrix
open PositiveDefiniteIntegralLattice
open scoped BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Matrix of the polar form `q(x+y)-q(x)-q(y)`.  The factor two is literal
and must be retained at the dyadic places. -/
def polarMatrix (V : RationalQuadraticSpaceMatrix n) :
    Matrix (Fin n) (Fin n) ℚ :=
  (2 : ℚ) • V.pairingMatrix

theorem polarMatrix_isSymm (V : RationalQuadraticSpaceMatrix n) :
    V.polarMatrix.IsSymm :=
  V.form_symm.smul _

/-- Diagonal scalar extension of the exact polar matrix to the full adeles. -/
def fullAdelicPolarMatrix (V : RationalQuadraticSpaceMatrix n) :
    Matrix (Fin n) (Fin n) RationalAdele :=
  V.polarMatrix.map (algebraMap ℚ RationalAdele)

theorem fullAdelicPolarMatrix_eq_two_smul
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicPolarMatrix = (2 : RationalAdele) • V.fullAdelicFormMatrix := by
  ext i j
  change algebraMap ℚ RationalAdele ((2 : ℚ) * V.pairingMatrix i j) =
    (2 : RationalAdele) * algebraMap ℚ RationalAdele (V.pairingMatrix i j)
  rw [map_mul, map_ofNat]

theorem fullAdelicPolarMatrix_isSymm
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicPolarMatrix.IsSymm :=
  V.polarMatrix_isSymm.map _

/-- The exact polar additive character on two adelic vectors. -/
def rationalAdeleVectorPolarChar
    (V : RationalQuadraticSpaceMatrix n)
    (x y : Fin n → RationalAdele) : Circle :=
  rationalAdeleFourierChar
    (dotProduct x (V.fullAdelicPolarMatrix.mulVec y))

/-- Applying the product coordinate character to a pointwise product is the
scalar character of the coordinate dot product. -/
theorem rationalAdeleCoordinateFourierChar_mul_eq_dotProduct
    (x y : Fin n → RationalAdele) :
    rationalAdeleCoordinateFourierChar n (x * y) =
      rationalAdeleFourierChar (dotProduct x y) := by
  simp only [rationalAdeleCoordinateFourierChar_apply, Pi.mul_apply,
    dotProduct]
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        AddChar.map_add_eq_mul, ih]

/-- The polar character is the already certified coordinate Fourier character
evaluated at the polar-matrix frequency. -/
theorem rationalAdeleVectorPolarChar_eq_coordinate
    (V : RationalQuadraticSpaceMatrix n)
    (x y : Fin n → RationalAdele) :
    V.rationalAdeleVectorPolarChar x y =
      rationalAdeleCoordinateFourierChar n
        (x * V.fullAdelicPolarMatrix.mulVec y) := by
  rw [rationalAdeleCoordinateFourierChar_mul_eq_dotProduct]
  rfl

/-- The rational matrix-vector value embeds diagonally into the full adeles. -/
theorem fullAdelicPolarMatrix_mulVec_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n) (y : Fin n → ℚ) :
    V.fullAdelicPolarMatrix.mulVec
        (fun i => algebraMap ℚ RationalAdele (y i)) =
      fun i => algebraMap ℚ RationalAdele (V.polarMatrix.mulVec y i) := by
  ext i
  simp [fullAdelicPolarMatrix, Matrix.mulVec, dotProduct, map_sum]

/-- The polar character is literally one on two rational diagonal vectors. -/
@[simp]
theorem rationalAdeleVectorPolarChar_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n) (x y : Fin n → ℚ) :
    V.rationalAdeleVectorPolarChar
        (fun i => algebraMap ℚ RationalAdele (x i))
        (fun i => algebraMap ℚ RationalAdele (y i)) = 1 := by
  rw [rationalAdeleVectorPolarChar,
    V.fullAdelicPolarMatrix_mulVec_rationalDiagonal]
  rw [show dotProduct
      (fun i => algebraMap ℚ RationalAdele (x i))
      (fun i => algebraMap ℚ RationalAdele (V.polarMatrix.mulVec y i)) =
      algebraMap ℚ RationalAdele
        (dotProduct x (V.polarMatrix.mulVec y)) by
    simp [dotProduct, map_sum]]
  exact rationalAdeleFourierChar_algebraMap _

/-- Orthogonal matrices preserve the exact polar matrix, not merely the stored
quadratic-form matrix. -/
theorem fullAdelicPolarMatrix_conj
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicSpecialOrthogonalGroup) :
    g.1.1.1ᵀ * V.fullAdelicPolarMatrix * g.1.1.1 =
      V.fullAdelicPolarMatrix := by
  rw [V.fullAdelicPolarMatrix_eq_two_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [g.1.2]

/-- Exact intertwining of the polar identification with the contragredient:
`A^T C = C A^{-1}`.  No lift of the contragredient matrix is chosen. -/
theorem polar_contragredient_intertwining
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicSpecialOrthogonalGroup) :
    g.1.1.1ᵀ * V.fullAdelicPolarMatrix =
      V.fullAdelicPolarMatrix * (↑(g.1.1⁻¹) :
        Matrix (Fin n) (Fin n) RationalAdele) := by
  have hmul :
      g.1.1.1 * (↑(g.1.1⁻¹) : Matrix (Fin n) (Fin n) RationalAdele) = 1 :=
    congrArg Units.val (mul_inv_cancel g.1.1)
  calc
    g.1.1.1ᵀ * V.fullAdelicPolarMatrix =
        (g.1.1.1ᵀ * V.fullAdelicPolarMatrix) * 1 := by simp
    _ = (g.1.1.1ᵀ * V.fullAdelicPolarMatrix) *
        (g.1.1.1 * (↑(g.1.1⁻¹) :
          Matrix (Fin n) (Fin n) RationalAdele)) := by
      rw [hmul]
    _ = (g.1.1.1ᵀ * V.fullAdelicPolarMatrix * g.1.1.1) *
        (↑(g.1.1⁻¹) : Matrix (Fin n) (Fin n) RationalAdele) := by
      simp only [Matrix.mul_assoc]
    _ = V.fullAdelicPolarMatrix * (↑(g.1.1⁻¹) :
        Matrix (Fin n) (Fin n) RationalAdele) := by
      rw [V.fullAdelicPolarMatrix_conj g]

/-- Transporting the first variable by an orthogonal matrix transports the
second variable by its inverse.  This is the character-level contragredient
covariance needed by the polar Fourier transform. -/
theorem rationalAdeleVectorPolarChar_contragredient
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicSpecialOrthogonalGroup)
    (x y : Fin n → RationalAdele) :
    V.rationalAdeleVectorPolarChar (g.1.1.1.mulVec x) y =
      V.rationalAdeleVectorPolarChar x
        ((↑(g.1.1⁻¹) : Matrix (Fin n) (Fin n) RationalAdele).mulVec y) := by
  have hmul :
      g.1.1.1 * (↑(g.1.1⁻¹) : Matrix (Fin n) (Fin n) RationalAdele) = 1 :=
    congrArg Units.val (mul_inv_cancel g.1.1)
  have hpair := dotProduct_mulVec_eq_of_matrix_conj
    (V.fullAdelicPolarMatrix_conj g) x
      ((↑(g.1.1⁻¹) : Matrix (Fin n) (Fin n) RationalAdele).mulVec y)
  have hcancel :
      g.1.1.1.mulVec
          ((↑(g.1.1⁻¹) : Matrix (Fin n) (Fin n) RationalAdele).mulVec y) = y := by
    have := congrArg (fun A : Matrix (Fin n) (Fin n) RationalAdele =>
      A.mulVec y) hmul
    simpa only [Matrix.mulVec_mulVec, Matrix.one_mulVec] using this
  rw [hcancel] at hpair
  exact congrArg rationalAdeleFourierChar hpair

/-- Simultaneous orthogonal transport preserves the exact polar character. -/
theorem rationalAdeleVectorPolarChar_orthogonal
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicSpecialOrthogonalGroup)
    (x y : Fin n → RationalAdele) :
    V.rationalAdeleVectorPolarChar (g.1.1.1.mulVec x) (g.1.1.1.mulVec y) =
      V.rationalAdeleVectorPolarChar x y := by
  unfold rationalAdeleVectorPolarChar
  rw [dotProduct_mulVec_eq_of_matrix_conj
    (V.fullAdelicPolarMatrix_conj g)]

end RationalQuadraticSpaceMatrix
