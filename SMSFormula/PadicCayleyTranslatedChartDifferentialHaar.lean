import SMSFormula.PadicCayleyTranslatedChartDifferentialInvariance
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar properties of the corrected p-adic differential

The corrected reciprocal Cayley density is pointwise positive.  Absolute
continuity therefore transports open positivity from the source coordinate
measure to the corrected source differential.  Translated Cayley
homeomorphisms and arbitrary chart recovery then give open positivity of the
globally glued differential.

One exact Cayley chart also proves local compactness of the p-adic
special-orthogonal group.  Together with local
finiteness and left invariance, this packages the corrected differential as a
Haar measure at the scale fixed by the rational invariant differential.  No
Haar uniqueness scalar or stabilizer volume is evaluated here.
-/

noncomputable section

open MeasureTheory
open TopologicalSpace
open Topology
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyDifferentialHaarSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyDifferentialHaarSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The corrected differential measure on the exact Cayley source is positive
on every nonempty open set. -/
theorem
    skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_isOpenPosMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Measure.IsOpenPosMeasure
      (skewAdjointPadicCayleySourceDifferentialSubtypeMeasure p n F) := by
  let μ := skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F
  let f := skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F
  letI : Measure.IsOpenPosMeasure μ :=
    skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_isOpenPosMeasure
      p n F
  have hf : AEMeasurable f μ :=
    (measurable_skewAdjointPadicCayleySourceDifferentialDensityENNReal
      p n F).aemeasurable
  have hf0 : ∀ᵐ X ∂μ, f X ≠ 0 := Filter.Eventually.of_forall fun X => by
    change
      skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F X ≠ 0
    rw [skewAdjointPadicCayleySourceDifferentialDensityENNReal_eq_coe]
    exact ENNReal.coe_ne_zero.mpr <| inv_ne_zero <|
      (skewAdjointPadicCayleyCoordinateJacobianDensity_pos
        p n F X.1 X.2).ne'
  exact (withDensity_absolutelyContinuous' hf hf0).isOpenPosMeasure

end Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyDifferentialHaarSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyDifferentialHaarSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicCayleyDifferentialHaarGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyDifferentialHaarGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The corrected differential measure on every exact translated Cayley
target is positive on every nonempty open set. -/
theorem
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_isOpenPosMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.IsOpenPosMeasure
      (padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
        p n F hF c) := by
  let μ :=
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure p n F
  letI : Measure.IsOpenPosMeasure μ :=
    Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_isOpenPosMeasure
      p n F
  rw [padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure]
  exact
    (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c).continuous
      |>.isOpenPosMeasure_map
        (skewAdjointPadicCayleyTranslatedHomeomorph F p hF c).surjective

/-- The p-adic special-orthogonal group is locally compact. This is obtained
from one exact translated Cayley chart and does not use a measure. -/
theorem padicCayleySpecialOrthogonalGroup_locallyCompact
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0) :
    LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) := by
  let g :
      specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p])) := 1
  let e := skewAdjointPadicCayleyTranslatedHomeomorph F p hF g
  let proper : ProperSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    FiniteDimensional.proper ℚ_[p]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
  let ambientCompact : LocallyCompactSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    @locallyCompact_of_proper _ _ proper
  letI : LocallyCompactSpace (Matrix.skewAdjointPadicCayleySource F p) :=
    @IsOpen.locallyCompactSpace _ _ ambientCompact _
      (Matrix.isOpen_skewAdjointPadicCayleySource F p)
  letI : LocallyCompactSpace
      (padicCayleySpecialOrthogonalTranslatedTarget F p g) :=
    e.symm.isOpenEmbedding.locallyCompactSpace
  let x : padicCayleySpecialOrthogonalTranslatedTarget F p g :=
    ⟨g, self_mem_padicCayleySpecialOrthogonalTranslatedTarget F p g⟩
  rcases exists_compact_mem_nhds x with ⟨K, hK, hxK⟩
  let j :
      padicCayleySpecialOrthogonalTranslatedTarget F p g →
        specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ ℚ_[p])) :=
    Subtype.val
  have hj : IsOpenEmbedding j :=
    (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
      F p g).isOpenEmbedding_subtypeVal
  exact (hK.image hj.continuous).locallyCompactSpace_of_mem_nhds_of_group
    (hj.image_mem_nhds.mpr hxK)

/-- The globally glued corrected p-adic differential is positive on every
nonempty open group set. -/
theorem
    padicCayleySpecialOrthogonalDifferentialMeasure_isOpenPosMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    Measure.IsOpenPosMeasure
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) := by
  refine ⟨fun U hU hUne ↦ ?_⟩
  rcases hUne with ⟨x, hxU⟩
  let T := padicCayleySpecialOrthogonalTranslatedTarget F p x
  let ν :=
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
      p n F hF x
  letI : Measure.IsOpenPosMeasure ν :=
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_isOpenPosMeasure
      p n F hF x
  let W : Set T := Subtype.val ⁻¹' U
  have hW : IsOpen W := hU.preimage continuous_subtype_val
  have hWne : W.Nonempty :=
    ⟨⟨x, self_mem_padicCayleySpecialOrthogonalTranslatedTarget F p x⟩,
      hxU⟩
  exact ne_of_gt <| calc
    0 < ν W := hW.measure_pos ν hWne
    _ = padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF x U := by
      rw [
        padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure,
        Measure.map_apply continuous_subtype_val.measurable
          hU.measurableSet]
    _ = (padicCayleySpecialOrthogonalDifferentialMeasure
        p n F hF).restrict T U := by
      rw [
        restrict_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
          p n F hFsymm hF x]
    _ ≤ padicCayleySpecialOrthogonalDifferentialMeasure p n F hF U :=
      Measure.restrict_apply_le T U

/-- The corrected p-adic differential is finite on compact sets. -/
theorem
    padicCayleySpecialOrthogonalDifferentialMeasure_isFiniteOnCompacts
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    IsFiniteMeasureOnCompacts
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) := by
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
    padicCayleySpecialOrthogonalGroup_locallyCompact p n F hF
  letI : IsLocallyFiniteMeasure
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isLocallyFinite
      p n F hFsymm hF
  set_option synthInstance.maxHeartbeats 200000 in
    infer_instance

instance padicCayleySpecialOrthogonalDifferentialMeasure_instFiniteOnCompacts
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    IsFiniteMeasureOnCompacts
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) :=
  padicCayleySpecialOrthogonalDifferentialMeasure_isFiniteOnCompacts
    p n F hFsymm hF

instance padicCayleySpecialOrthogonalDifferentialMeasure_instOpenPosMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    Measure.IsOpenPosMeasure
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) :=
  padicCayleySpecialOrthogonalDifferentialMeasure_isOpenPosMeasure
    p n F hFsymm hF

/-- The corrected p-adic differential is a Haar measure at the scale fixed by
the rational invariant differential. -/
theorem padicCayleySpecialOrthogonalDifferentialMeasure_isHaarMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    Measure.IsHaarMeasure
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) where
  toIsFiniteMeasureOnCompacts :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isFiniteOnCompacts
      p n F hFsymm hF
  toIsMulLeftInvariant :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isMulLeftInvariant
      p n F hFsymm hF
  toIsOpenPosMeasure :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isOpenPosMeasure
      p n F hFsymm hF

instance padicCayleySpecialOrthogonalDifferentialMeasure_instHaarMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    Measure.IsHaarMeasure
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) :=
  padicCayleySpecialOrthogonalDifferentialMeasure_isHaarMeasure
    p n F hFsymm hF

/-- The corrected p-adic differential is regular. -/
theorem padicCayleySpecialOrthogonalDifferentialMeasure_regular
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    Measure.Regular
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) := by
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
    padicCayleySpecialOrthogonalGroup_locallyCompact p n F hF
  letI : SecondCountableTopology
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
    padicCayleySpecialOrthogonalGroup_secondCountable F p
  letI : IsLocallyFiniteMeasure
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isLocallyFinite
      p n F hFsymm hF
  infer_instance

end PositiveDefiniteIntegralLattice
