import SMSFormula.RationalCliffordSpinCandidateFullAdelicUnimodular
import SMSFormula.AdelicWeilQuotient
import Mathlib.MeasureTheory.Group.Measure
import SMSFormula.SpecialOrthogonalFullAdelicDifferentialMeasurableWeilQuotient
import SMSFormula.RationalCliffordSpinCandidateOnoRelativeTamagawaData

/-!
# The raw Clifford--Spin datum in the right quotient convention

Every raw Spin ambient measure is a finite scalar multiple of the coherent
full-adelic measure.  The completed coherent inversion theorem therefore
passes directly to the raw scale.  Consequently the actual raw Ono Spin
datum satisfies the right Weil identity for the same ambient measure used in
its left-quotient construction.

This does not identify that measure with a sourced canonical Tamagawa
normalization or evaluate its quotient mass.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} {V : RationalQuadraticSpaceMatrix n}

/-- Every proposed raw full-adelic Spin differential measure is invariant
under inversion. -/
theorem fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) (finiteScale : ℝ≥0) :
    Measure.IsInvInvariant
      (V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
        finiteScale) := by
  unfold fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
  exact Measure.isInvInvariant_smul
    (finiteScale : ℝ≥0∞)
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure

namespace IsRawCliffordSpinCandidateDifferentialMeasurableWeilDataWithScale

/-- The ambient measure of every scale-explicit raw Spin measurable-Weil
datum is invariant under inversion. -/
theorem adelicMeasure_isInvInvariant
    {finiteScale : ℝ≥0}
    {D : V.CliffordSpinCandidateMeasurableWeilMeasureData}
    (C : V.IsRawCliffordSpinCandidateDifferentialMeasurableWeilDataWithScale
      finiteScale D) :
    Measure.IsInvInvariant D.adelicMeasure := by
  rw [C.adelicMeasure_eq]
  exact
    V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_isInvInvariant
      finiteScale

end IsRawCliffordSpinCandidateDifferentialMeasurableWeilDataWithScale

namespace CliffordSpinCandidateRawOnoTamagawaData

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
