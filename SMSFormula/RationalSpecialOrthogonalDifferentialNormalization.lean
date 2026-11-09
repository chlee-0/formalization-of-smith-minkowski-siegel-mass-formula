import SMSFormula.RationalAdeleAdditiveMeasure
import SMSFormula.RationalSpecialOrthogonalTamagawa

/-!
# Rational differential coordinate normalization

This file joins the canonical additive adelic coordinate scale to the fixed
rational skew-adjoint basis used to define the invariant top differential of
a rational quadratic space.  It is the coordinate-level normalization
certificate needed before a group Haar measure can be declared
differential-induced.

The certificate does not construct a measure on the adelic special
orthogonal group and does not state a Tamagawa-number theorem.
-/

open MeasureTheory Set

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The coordinate index of the fixed rational skew-adjoint basis underlying
the invariant top differential. -/
abbrev InvariantDifferentialCoordinateIndex
    (V : RationalQuadraticSpaceMatrix n) :=
  Fin (Module.finrank ℚ V.skewAdjointTangent)

/-- The standard full-adelic parallelotope in the coordinates of the fixed
rational skew-adjoint basis. -/
noncomputable def invariantDifferentialAdeleStandardParallelotope
    (V : RationalQuadraticSpaceMatrix n) :
    Set (V.InvariantDifferentialCoordinateIndex → PositiveDefiniteIntegralLattice.RationalAdele) :=
  PositiveDefiniteIntegralLattice.rationalAdeleCoordinateStandardBlock
    (Module.finrank ℚ V.skewAdjointTangent)

/-- A non-circular coordinate-level normalization certificate for the
rational invariant differential.

The measure must be additive Haar and must give the standard adelic
parallelotope in the differential's fixed rational basis volume one. -/
structure InvariantDifferentialAdeleCoordinateNormalization
    (V : RationalQuadraticSpaceMatrix n) where
  measure :
    Measure (V.InvariantDifferentialCoordinateIndex →
      PositiveDefiniteIntegralLattice.RationalAdele)
  isAddHaarMeasure : measure.IsAddHaarMeasure
  standardParallelotope_eq_one :
    measure V.invariantDifferentialAdeleStandardParallelotope = 1

namespace InvariantDifferentialAdeleCoordinateNormalization

variable {V : RationalQuadraticSpaceMatrix n}

noncomputable instance (D : InvariantDifferentialAdeleCoordinateNormalization V) :
    D.measure.IsAddHaarMeasure :=
  D.isAddHaarMeasure

theorem measure_ne_zero
    (D : InvariantDifferentialAdeleCoordinateNormalization V) :
    D.measure ≠ 0 := by
  intro hzero
  have h : (1 : ENNReal) = 0 := calc
    1 = D.measure V.invariantDifferentialAdeleStandardParallelotope :=
      D.standardParallelotope_eq_one.symm
    _ = 0 := by rw [hzero]; rfl
  exact one_ne_zero h

end InvariantDifferentialAdeleCoordinateNormalization

/-- The rational invariant differential evaluates to one on its
defining skew-adjoint basis.  This is the algebraic half of the coordinate
normalization certificate. -/
@[simp]
theorem invariantTopDifferential_apply_fixedBasis
    (V : RationalQuadraticSpaceMatrix n) :
    V.invariantTopDifferential
      (Matrix.skewAdjointFinBasis V.pairingMatrix) = 1 := by
  exact (Matrix.skewAdjointFinBasis V.pairingMatrix).det_self

/-- The canonical additive adelic coordinate measure attached to the fixed
rational invariant differential. -/
noncomputable def invariantDifferentialAdeleCoordinateNormalization
    (V : RationalQuadraticSpaceMatrix n) :
    InvariantDifferentialAdeleCoordinateNormalization V where
  measure :=
    PositiveDefiniteIntegralLattice.rationalAdeleCoordinateAddHaarMeasure
      (Module.finrank ℚ V.skewAdjointTangent)
  isAddHaarMeasure := inferInstance
  standardParallelotope_eq_one :=
    PositiveDefiniteIntegralLattice.rationalAdeleCoordinateAddHaarMeasure_standardBlock
      (Module.finrank ℚ V.skewAdjointTangent)

@[simp]
theorem invariantDifferentialAdeleCoordinateNormalization_measure
    (V : RationalQuadraticSpaceMatrix n) :
    V.invariantDifferentialAdeleCoordinateNormalization.measure =
      PositiveDefiniteIntegralLattice.rationalAdeleCoordinateAddHaarMeasure
        (Module.finrank ℚ V.skewAdjointTangent) :=
  rfl

/-- Unit parallelotope normalization rules out every nontrivial common
rescaling of the canonical differential coordinate measure. -/
theorem invariantDifferentialAdeleCoordinateMeasure_smul_normalized_iff
    (V : RationalQuadraticSpaceMatrix n) (c : ENNReal) :
    (c • V.invariantDifferentialAdeleCoordinateNormalization.measure)
        V.invariantDifferentialAdeleStandardParallelotope = 1 ↔
      c = 1 :=
  PositiveDefiniteIntegralLattice.rationalAdeleCoordinateAddHaarMeasure_smul_normalized_iff
    (Module.finrank ℚ V.skewAdjointTangent) c

end RationalQuadraticSpaceMatrix
