import SMSFormula.RationalQuadraticIsometrySpinCandidateRepresentedNormCoefficient
import SMSFormula.RationalAdeleVectorPolarPoissonReduction

/-!
# The all-rational Spin-weighted theta expansion

The ordinary adelic theta summand at a rational vector is the value of a
nonnegative test function at the rational diagonal after applying the inverse
of the represented special-orthogonal matrix of an intrinsic full-adelic
`GSpin` point.  This file packages that ambient summand, which needs no
witness, and specializes the represented-norm Tonelli theorem to it.

In rank at least four, the resulting weighted theta function has coefficient
one at the zero vector and the unique local one-shell Spin Tamagawa
coefficient on every represented nonzero norm fiber.  No vector,
complement-lattice witness, presentation, or raw lower datum is selected.

This is the calibrated nonnegative all-shell expansion on the adelic group.
It does not identify its left-quotient integral with the
probability-normalized theta average; that analytic comparison is not proved
here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The inverse represented orthogonal action of a full-adelic intrinsic
`GSpin` point on the rational diagonal of a vector. -/
def fullAdelicCliffordGeneralSpinRationalVectorAction
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicCliffordGeneralSpinGroup)
    (x : Fin n → ℚ) : Fin n → RationalAdele :=
  Matrix.mulVec (g.matrixGroup⁻¹).1.1.1
    (rationalAdeleVectorDiagonal n x)

@[simp]
theorem fullAdelicCliffordGeneralSpinRationalVectorAction_zero
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinRationalVectorAction g 0 = 0 := by
  ext i
  simp [fullAdelicCliffordGeneralSpinRationalVectorAction,
    Matrix.mulVec, dotProduct, rationalAdeleVectorDiagonal]

/-- For a fixed rational vector, the full-adelic inverse orthogonal action is
continuous in the intrinsic `GSpin` point. -/
theorem continuous_fullAdelicCliffordGeneralSpinRationalVectorAction
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ) :
    Continuous
      (fun g : V.FullAdelicCliffordGeneralSpinGroup ↦
        V.fullAdelicCliffordGeneralSpinRationalVectorAction g x) := by
  apply continuous_pi
  intro i
  simp only [fullAdelicCliffordGeneralSpinRationalVectorAction,
    Matrix.mulVec, dotProduct]
  apply continuous_finset_sum
  intro j _
  exact
    (V.continuous_cliffordGeneralSpinInvMatrixCoordinate
      RationalAdele i j).mul continuous_const

/-- The ambient nonnegative theta summand at one rational vector. -/
def fullAdelicCliffordGeneralSpinRationalVectorThetaSummand
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicCliffordGeneralSpinGroup)
    (x : Fin n → ℚ) : ℝ≥0∞ :=
  Phi (V.fullAdelicCliffordGeneralSpinRationalVectorAction g x)

theorem measurable_fullAdelicCliffordGeneralSpinRationalVectorThetaSummand
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi) (x : Fin n → ℚ) :
    Measurable
      (fun g : V.FullAdelicCliffordGeneralSpinGroup ↦
        V.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand Phi g x) :=
  hPhi.comp
    (V.continuous_fullAdelicCliffordGeneralSpinRationalVectorAction x).measurable

/-- The witness-free all-rational theta function weighted by the normalized
one-shell Spin Tamagawa coefficient. -/
def fullAdelicCliffordGeneralSpinOneShellWeightedTheta
    (V : RationalQuadraticSpaceMatrix n)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hLocal : V.OneShellSpinCoefficientLocallyNonempty)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicCliffordGeneralSpinGroup) : ℝ≥0∞ :=
  ∑' x : Fin n → ℚ,
    V.rationalVectorOneShellSpinTamagawaWeight DAmbient hLocal x *
      V.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand Phi g x

/-- A measurable nonnegative test function gives a measurable weighted theta
function on the full-adelic intrinsic `GSpin` group. -/
theorem measurable_fullAdelicCliffordGeneralSpinOneShellWeightedTheta
    (V : RationalQuadraticSpaceMatrix n)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hLocal : V.OneShellSpinCoefficientLocallyNonempty)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    Measurable
      (V.fullAdelicCliffordGeneralSpinOneShellWeightedTheta
        DAmbient hLocal Phi) := by
  unfold fullAdelicCliffordGeneralSpinOneShellWeightedTheta
  exact Measurable.ennreal_tsum fun x ↦
    measurable_const.mul
      (V.measurable_fullAdelicCliffordGeneralSpinRationalVectorThetaSummand
        Phi hPhi x)

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {n : ℕ}

end PositiveDefiniteIntegralLattice

end
