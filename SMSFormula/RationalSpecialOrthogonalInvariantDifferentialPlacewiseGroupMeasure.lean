import SMSFormula.SpecialOrthogonalAdelicAmbientDifferentialNormalization
import SMSFormula.RationalSpecialOrthogonalDifferentialNormalization
import SMSFormula.SpecialOrthogonalRealChartMeasure
import SMSFormula.PadicCayleyHomeomorph
import SMSFormula.PadicCayleyCoordinateJacobianDensityENNRealPositive
import SMSFormula.PadicCayleyDomainOpenness
import SMSFormula.SkewSymmetricPadicGeneralCongruenceCharacter
import SMSFormula.PadicCayleyLeftTrivializedInversePowerDeterminant
import SMSFormula.SkewAdjointPadicMeasureGeneralTransport
import SMSFormula.PadicCayleyLeftTrivializedInverseModulus
import SMSFormula.PadicCayleyTangentModulus
import SMSFormula.SpecialOrthogonalRealDifferentialHaar
import SMSFormula.PadicCayleyTranslatedChartDifferentialHaar

/-!
# General placewise group measures induced by the invariant differential

The rational invariant top differential already supplies canonical identity
chart normalizations at the real and every p-adic place.  The completed
translated-chart developments independently glue those local densities to
full local group measures.

This module bundles both layers for an arbitrary
`RationalQuadraticSpaceMatrix`, including exact identity-centered chart
restriction and Haar certification.  It deliberately does not claim that a
measure on the full adelic group is the restricted product of these local
measures: the repository does not have a carrier-independent restricted
product of the local special-orthogonal groups, its cylinder measure, or an
equivalence with the matrix group over the rational adeles.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance invariantDifferentialPlacewiseRealModelMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance invariantDifferentialPlacewiseRealModelBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance invariantDifferentialPlacewiseRealGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  borel _

local instance invariantDifferentialPlacewiseRealGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance invariantDifferentialPlacewisePadicModelMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance invariantDifferentialPlacewisePadicModelBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance invariantDifferentialPlacewisePadicGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance invariantDifferentialPlacewisePadicGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The canonical full real group measure obtained by gluing the translated
charts carrying the scalar extension of `V.invariantTopDifferential`. -/
def realInvariantDifferentialGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  specialFormPreservingSmoothRealDifferentialMeasure
    V.pairingMatrix V.form_symm V.form_det_ne_zero

/-- The canonical full p-adic group measure obtained by gluing the corrected
translated Cayley charts carrying the scalar extension of
`V.invariantTopDifferential`. -/
def padicInvariantDifferentialGroupMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  padicCayleySpecialOrthogonalDifferentialMeasure
    p n V.pairingMatrix V.form_det_ne_zero

/-- The real invariant-differential group measure is Haar. -/
theorem realInvariantDifferentialGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure := by
  exact
    specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
      V.pairingMatrix V.form_symm V.form_det_ne_zero

/-- Every p-adic invariant-differential group measure is Haar. -/
theorem padicInvariantDifferentialGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsHaarMeasure (V.padicInvariantDifferentialGroupMeasure p) := by
  exact
    padicCayleySpecialOrthogonalDifferentialMeasure_isHaarMeasure
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero

/-- On the identity-centered real chart, the full group measure is exactly
the chart measure carrying the invariant differential density. -/
theorem restrict_realInvariantDifferentialGroupMeasure_identityChart
    (V : RationalQuadraticSpaceMatrix n) :
    V.realInvariantDifferentialGroupMeasure.restrict
        (specialFormPreservingSmoothRealChart
          V.pairingMatrix V.form_symm V.form_det_ne_zero 1).source =
      specialFormPreservingSmoothRealChartAmbientDensityMeasure
        V.pairingMatrix V.form_symm V.form_det_ne_zero 1 := by
  exact
    restrict_specialFormPreservingSmoothRealDifferentialMeasure_source
      V.pairingMatrix V.form_symm V.form_det_ne_zero 1

/-- On the identity-centered p-adic Cayley chart, the full group measure is
exactly the corrected chart measure carrying the invariant differential
density. -/
theorem restrict_padicInvariantDifferentialGroupMeasure_identityChart
    (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.padicInvariantDifferentialGroupMeasure p).restrict
        (padicCayleySpecialOrthogonalTranslatedTarget
          V.pairingMatrix p 1) =
      padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n V.pairingMatrix V.form_det_ne_zero 1 := by
  exact
    restrict_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero 1

end RationalQuadraticSpaceMatrix
