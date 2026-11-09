import SMSFormula.RationalFiniteAdeleVectorPolarDualLattice
import SMSFormula.SpecialOrthogonalConcreteRationalQuotientCarrier
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Determinant normalization for the rational-adelic polar matrix

This file isolates the determinant calculation needed before changing the
real Gaussian from the standard coordinate pairing to the exact polar pairing
`C = 2F`.  It proves the rational and real determinant formulas, specializes
positivity to the lattice-backed carrier, and records the exact Lebesgue
measure transport under `x |-> Cx`.

The positive square-root determinant scale and its reciprocal are packaged
without asserting a Gaussian Fourier formula.  No new coordinate chart,
shell decomposition, orbital distribution, or Tamagawa-number statement is
introduced.
-/

noncomputable section

open Matrix
open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Scalar extension of the exact polar matrix to the real coordinate
carrier. -/
def realPolarMatrix (V : RationalQuadraticSpaceMatrix n) :
    Matrix (Fin n) (Fin n) ℝ :=
  V.polarMatrix.map (Rat.castHom ℝ)

theorem realPolarMatrix_isSymm
    (V : RationalQuadraticSpaceMatrix n) :
    V.realPolarMatrix.IsSymm :=
  V.polarMatrix_isSymm.map _

/-- The dyadic factor contributes exactly `2^n` to the polar determinant. -/
theorem polarMatrix_det
    (V : RationalQuadraticSpaceMatrix n) :
    V.polarMatrix.det = (2 : ℚ) ^ n * V.pairingMatrix.det := by
  rw [polarMatrix, Matrix.det_smul]
  simp

theorem polarMatrix_det_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.polarMatrix.det ≠ 0 := by
  rw [V.polarMatrix_det]
  exact mul_ne_zero (pow_ne_zero n (by norm_num)) V.form_det_ne_zero

/-- The exact polar matrix as a canonical rational general-linear element. -/
def polarMatrixGeneralLinear
    (V : RationalQuadraticSpaceMatrix n) : GL (Fin n) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero V.polarMatrix
    V.polarMatrix_det_ne_zero

@[simp]
theorem polarMatrixGeneralLinear_coe
    (V : RationalQuadraticSpaceMatrix n) :
    (V.polarMatrixGeneralLinear : Matrix (Fin n) (Fin n) ℚ) =
      V.polarMatrix :=
  rfl

/-- Real scalar extension commutes with the determinant. -/
theorem realPolarMatrix_det
    (V : RationalQuadraticSpaceMatrix n) :
    V.realPolarMatrix.det = (V.polarMatrix.det : ℝ) := by
  simpa [realPolarMatrix] using
    (RingHom.map_det (Rat.castHom ℝ) V.polarMatrix).symm

theorem realPolarMatrix_det_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.realPolarMatrix.det ≠ 0 := by
  rw [V.realPolarMatrix_det]
  exact_mod_cast V.polarMatrix_det_ne_zero

/-- Exact real change of variables under the polar matrix for the standard
coordinate Lebesgue measure. -/
theorem map_realPolarMatrix_volume
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.map (Matrix.toLin' V.realPolarMatrix)
        (volume : Measure (Fin n → ℝ)) =
      ENNReal.ofReal |V.realPolarMatrix.det⁻¹| •
        (volume : Measure (Fin n → ℝ)) := by
  exact Real.map_matrix_volume_pi_eq_smul_volume_pi
    V.realPolarMatrix_det_ne_zero

/-! ## Positive lattice-backed normalization -/

/-- On the lattice-backed carrier, the real polar matrix is literally the
real scalar extension of the integral polar Gram matrix. -/
theorem _root_.PositiveDefiniteIntegralLattice.rationalQuadraticSpaceMatrix_realPolarMatrix
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.realPolarMatrix =
      L.polarGramMatrix.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp [realPolarMatrix, polarMatrix,
    PositiveDefiniteIntegralLattice.rationalQuadraticSpaceMatrix,
    PositiveDefiniteIntegralLattice.rationalFormMatrix, PositiveDefiniteIntegralLattice.polarGramMatrix,
    Matrix.transpose_apply, L.form_symm.apply, two_mul]

/-- Positive definiteness of the lattice form makes its exact real polar
matrix positive definite. -/
theorem _root_.PositiveDefiniteIntegralLattice.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.realPolarMatrix.PosDef := by
  rw [L.rationalQuadraticSpaceMatrix_realPolarMatrix,
    show L.polarGramMatrix.map (Int.cast : ℤ → ℝ) =
        (2 : ℝ) • L.pairingMatrix.map (Int.cast : ℤ → ℝ) by
      ext i j
      simp [PositiveDefiniteIntegralLattice.polarGramMatrix, Matrix.transpose_apply,
        L.form_symm.apply, two_mul]]
  exact L.form_posDef.smul (by norm_num : (0 : ℝ) < 2)

/-- The real polar determinant is the cast of the integral bilinear
discriminant. -/
theorem _root_.PositiveDefiniteIntegralLattice.rationalQuadraticSpaceMatrix_realPolarMatrix_det
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.realPolarMatrix.det = (L.polarDeterminant : ℝ) := by
  rw [L.rationalQuadraticSpaceMatrix_realPolarMatrix]
  simpa [PositiveDefiniteIntegralLattice.polarDeterminant] using
    (Int.cast_det L.polarGramMatrix).symm

theorem _root_.PositiveDefiniteIntegralLattice.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos
    (L : PositiveDefiniteIntegralLattice n) :
    0 < L.rationalQuadraticSpaceMatrix.realPolarMatrix.det := by
  rw [L.rationalQuadraticSpaceMatrix_realPolarMatrix_det]
  exact_mod_cast L.polarDeterminant_pos

/-- The positive real square-root determinant scale. -/
def _root_.PositiveDefiniteIntegralLattice.polarRealDeterminantScale
    (L : PositiveDefiniteIntegralLattice n) : NNReal :=
  ⟨Real.sqrt L.rationalQuadraticSpaceMatrix.realPolarMatrix.det,
    Real.sqrt_nonneg _⟩

@[simp, norm_cast]
theorem _root_.PositiveDefiniteIntegralLattice.coe_polarRealDeterminantScale
    (L : PositiveDefiniteIntegralLattice n) :
    (L.polarRealDeterminantScale : ℝ) =
      Real.sqrt L.rationalQuadraticSpaceMatrix.realPolarMatrix.det :=
  rfl

theorem _root_.PositiveDefiniteIntegralLattice.polarRealDeterminantScale_pos
    (L : PositiveDefiniteIntegralLattice n) :
    0 < L.polarRealDeterminantScale := by
  change 0 < Real.sqrt
    L.rationalQuadraticSpaceMatrix.realPolarMatrix.det
  exact Real.sqrt_pos.2
    L.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos

theorem _root_.PositiveDefiniteIntegralLattice.polarRealDeterminantScale_ne_zero
    (L : PositiveDefiniteIntegralLattice n) :
    L.polarRealDeterminantScale ≠ 0 :=
  ne_of_gt L.polarRealDeterminantScale_pos

/-- Squaring the positive scale recovers the exact real polar determinant. -/
theorem _root_.PositiveDefiniteIntegralLattice.polarRealDeterminantScale_sq
    (L : PositiveDefiniteIntegralLattice n) :
    (L.polarRealDeterminantScale : ℝ) ^ 2 =
      L.rationalQuadraticSpaceMatrix.realPolarMatrix.det := by
  exact Real.sq_sqrt
    (le_of_lt L.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos)

/-- The reciprocal determinant scale assigned to the finite factor. -/
def _root_.PositiveDefiniteIntegralLattice.polarFiniteReciprocalDeterminantScale
    (L : PositiveDefiniteIntegralLattice n) : NNReal :=
  L.polarRealDeterminantScale⁻¹

/-- The real and finite determinant scales cancel literally. -/
@[simp]
theorem _root_.PositiveDefiniteIntegralLattice.polarReal_mul_finiteDeterminantScale
    (L : PositiveDefiniteIntegralLattice n) :
    L.polarRealDeterminantScale *
        L.polarFiniteReciprocalDeterminantScale = 1 := by
  exact mul_inv_cancel₀ L.polarRealDeterminantScale_ne_zero

/-- On a positive lattice-backed form, the absolute determinant in the real
change-of-variables theorem is the determinant itself. -/
theorem _root_.PositiveDefiniteIntegralLattice.map_rationalQuadraticSpaceMatrix_realPolarMatrix_volume
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.map
        (Matrix.toLin' L.rationalQuadraticSpaceMatrix.realPolarMatrix)
        (volume : Measure (Fin n → ℝ)) =
      ENNReal.ofReal
          L.rationalQuadraticSpaceMatrix.realPolarMatrix.det⁻¹ •
        (volume : Measure (Fin n → ℝ)) := by
  rw [L.rationalQuadraticSpaceMatrix.map_realPolarMatrix_volume,
    abs_of_pos (inv_pos.mpr
      L.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos)]

end RationalQuadraticSpaceMatrix
