import SMSFormula.SpecialOrthogonalConcreteRationalQuotientCarrier

/-!
# Differential Haar on the rational quadratic-space adelic carrier

This module transports the internally constructed full-adelic differential
Haar measure from the lattice carrier to the general
`RationalQuadraticSpaceMatrix` carrier instantiated by the lattice rational
form matrix.  It also records the corresponding neutral transport operation
for arbitrary measures on the rational diagonal left quotient.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The internally normalized differential Haar transported from the concrete
lattice full-adelic carrier to the general rational quadratic-space carrier. -/
def rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  Measure.map
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm.toHomeomorph
    (L.fullAdelicSpecialOrthogonalDifferentialMeasure P)

/-- Forward transport across the carrier equivalence recovers the concrete
ambient differential measure exactly. -/
theorem map_rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    Measure.map
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).toHomeomorph
        (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P) =
      L.fullAdelicSpecialOrthogonalDifferentialMeasure P := by
  rw [rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure]
  exact
    MeasurableEquiv.map_map_symm
      (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).toMeasurableEquiv

/-- Mapping the concrete differential measure through the inverse carrier
identification is the named general-carrier differential measure. -/
theorem map_fullAdelicSpecialOrthogonalDifferentialMeasure_to_rationalCarrier
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    Measure.map
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm.toHomeomorph
        (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) =
      L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P :=
  rfl

/-- The transported general-carrier differential measure is nonzero. -/
theorem rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P ≠ 0 := by
  intro hzero
  have hmap := congrArg
    (Measure.map
      (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).toHomeomorph)
    hzero
  rw [L.map_rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P,
    Measure.map_zero] at hmap
  exact
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_ne_zero hP hmap

/-- The transported general-carrier differential measure is sigma-finite. -/
theorem rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_sigmaFinite
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    SigmaFinite
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P) := by
  letI : SigmaFinite
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) :=
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_sigmaFinite hP
  unfold rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure
  exact
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm.toHomeomorph.toMeasurableEquiv.sigmaFinite_map

/-- The general-carrier differential measure is Haar at exactly the scale
fixed by the internally constructed rational differential. -/
theorem
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_isHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    Measure.IsHaarMeasure
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P) := by
  letI : Measure.IsHaarMeasure
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) :=
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_isHaarMeasure hP
  exact
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm.toMulEquiv.isHaarMeasure_map
        (L.fullAdelicSpecialOrthogonalDifferentialMeasure P)
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm.continuous
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).continuous

/-- The transported measure is left invariant on the general carrier. -/
theorem
    rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    Measure.IsMulLeftInvariant
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P) := by
  letI : Measure.IsHaarMeasure
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P) :=
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_isHaarMeasure
      hP
  infer_instance

/-- The transported differential Haar measure remains regular. -/
theorem rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure_regular
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    Measure.Regular
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P) := by
  letI : Measure.Regular
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) :=
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_regular hP
  unfold rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure
  exact
    Measure.Regular.map
      (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm.toHomeomorph

/-- Transport an arbitrary measure on the concrete lattice quotient to the
general rational quadratic-space quotient.  This operation carries no Weil
normalization assertion. -/
def rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure
    (L : PositiveDefiniteIntegralLattice n)
    (μ :
      Measure L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient) :
    Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient :=
  Measure.map
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv.symm μ

/-- Forward transport recovers the original arbitrary concrete quotient
measure. -/
theorem map_rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure
    (L : PositiveDefiniteIntegralLattice n)
    (μ :
      Measure L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient) :
    Measure.map
        L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv
        (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μ) =
      μ := by
  rw [rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure]
  exact
    MeasurableEquiv.map_map_symm
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv

/-- The defining inverse transport of an arbitrary concrete quotient
measure. -/
theorem map_concreteFullAdelicLeftQuotientMeasure_to_rationalCarrier
    (L : PositiveDefiniteIntegralLattice n)
    (μ :
      Measure L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient) :
    Measure.map
        L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv.symm
        μ =
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μ :=
  rfl

end PositiveDefiniteIntegralLattice
