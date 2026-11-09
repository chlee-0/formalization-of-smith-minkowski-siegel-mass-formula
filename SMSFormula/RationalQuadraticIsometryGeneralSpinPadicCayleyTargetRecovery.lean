import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCayleyTargetDifferentialTransport
import SMSFormula.RationalSpecialOrthogonalInvariantDifferentialPlacewiseGroupMeasure

/-!
# Recovery of the glued p-adic SO measure on the canonical Cayley target

The canonical units-valued identity Cayley target measure introduced for
cross-presentation transport is the literal restriction of the repository's
globally glued invariant-differential `SO(ℚ_p)` measure.  This is the bridge
from the exact Cayley presentation square to the independently selected
general-Spin charts.

No selected chart domain, general-Spin group measure, or finite cylinder is
transported here.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {m : ℕ}

local instance padicCayleyTargetRecoveryModelMeasurableSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyTargetRecoveryModelBorelSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyTargetRecoveryGroupMeasurableSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTargetRecoveryGroupBorelSpace
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace
      (specialFormPreservingMatrixSubgroup
        (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The identity translation identifies the newly named canonical target
measure with the target restriction recovered from the glued `SO(ℚ_p)`
measure. -/
theorem map_padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure_oneTranslate
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (padicCayleySpecialOrthogonalLeftTranslateHomeomorph W.pairingMatrix p 1)
        (W.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p) =
      Measure.comap Subtype.val
        (W.padicInvariantDifferentialGroupMeasure p) := by
  calc
    Measure.map
        (padicCayleySpecialOrthogonalLeftTranslateHomeomorph W.pairingMatrix p 1)
        (W.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p) =
        padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
          p (m + 1) W.pairingMatrix W.form_det_ne_zero 1 := by
      unfold padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure
      unfold padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
      rw [Measure.map_map
        (padicCayleySpecialOrthogonalLeftTranslateHomeomorph
          W.pairingMatrix p 1).measurable
        (AnisotropicComplementPresentation.padicCayleySpecialOrthogonalIdentityHomeomorph
          W p).measurable]
      apply Measure.map_congr
      filter_upwards with X
      rfl
    _ = Measure.comap Subtype.val
        (W.padicInvariantDifferentialGroupMeasure p) := by
      symm
      simpa [padicInvariantDifferentialGroupMeasure] using
        (comap_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
          p (m + 1) W.pairingMatrix W.form_symm W.form_det_ne_zero 1)

/-- Including the canonical identity Cayley target into `SO(ℚ_p)` recovers
the exact restriction of the globally glued invariant-differential measure. -/
theorem map_padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure_subtypeVal
    (W : RationalQuadraticSpaceMatrix (m + 1))
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map Subtype.val
        (W.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p) =
      (W.padicInvariantDifferentialGroupMeasure p).restrict
        (padicCayleySpecialOrthogonalSubgroupInverseDomain W.pairingMatrix p) := by
  let e := padicCayleySpecialOrthogonalLeftTranslateHomeomorph W.pairingMatrix p 1
  let μ := W.padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure p
  have hmap :=
    W.map_padicCayleySpecialOrthogonalIdentityTargetDifferentialMeasure_oneTranslate p
  calc
    Measure.map Subtype.val μ =
        Measure.map Subtype.val (Measure.map e μ) := by
      rw [Measure.map_map continuous_subtype_val.measurable e.measurable]
      apply Measure.map_congr
      filter_upwards with g
      simp [e]
    _ = Measure.map Subtype.val
        (Measure.comap Subtype.val
          (W.padicInvariantDifferentialGroupMeasure p)) := by rw [hmap]
    _ = (W.padicInvariantDifferentialGroupMeasure p).restrict
        (padicCayleySpecialOrthogonalTranslatedTarget W.pairingMatrix p 1) :=
      map_comap_subtype_coe
        (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
          W.pairingMatrix p 1).measurableSet _
    _ = (W.padicInvariantDifferentialGroupMeasure p).restrict
        (padicCayleySpecialOrthogonalSubgroupInverseDomain W.pairingMatrix p) := by
      congr 1
      simp [padicCayleySpecialOrthogonalTranslatedTarget]

end RationalQuadraticSpaceMatrix
