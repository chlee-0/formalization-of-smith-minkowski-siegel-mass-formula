import SMSFormula.HaarMeasureUnimodularInversion
import SMSFormula.PadicCayleyTranslatedChartDifferentialHaar
import SMSFormula.PadicCayleyTranslatedChartDifferentialRightInvariance

/-!
# Unimodularity of the corrected p-adic special-orthogonal differential

The corrected differential measure is already a regular left Haar measure.
The chartwise adjoint calculation and atlas gluing additionally make it right
invariant.  The generic two-sided-Haar bridge therefore proves invariance
under inversion at the same invariant-differential scale.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyDifferentialUnimodularGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyDifferentialUnimodularGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The corrected p-adic special-orthogonal differential measure is invariant
under inversion. -/
theorem padicCayleySpecialOrthogonalDifferentialMeasure_isInvInvariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    Measure.IsInvInvariant
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) := by
  let μ := padicCayleySpecialOrthogonalDifferentialMeasure p n F hF
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
    padicCayleySpecialOrthogonalGroup_locallyCompact p n F hF
  letI : Measure.IsHaarMeasure μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isHaarMeasure
      p n F hFsymm hF
  letI : Measure.IsMulRightInvariant μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isMulRightInvariant
      p n F hFsymm hF
  letI : Measure.Regular μ :=
    padicCayleySpecialOrthogonalDifferentialMeasure_regular
      p n F hFsymm hF
  exact Measure.isInvInvariant_of_isMulRightInvariant_of_regular μ

/-- Inversion invariance is installed at the actual corrected differential
scale for subsequent quotient-convention transport. -/
instance padicCayleySpecialOrthogonalDifferentialMeasure_instInvInvariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    Measure.IsInvInvariant
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) :=
  padicCayleySpecialOrthogonalDifferentialMeasure_isInvInvariant
    p n F hFsymm hF

end PositiveDefiniteIntegralLattice
