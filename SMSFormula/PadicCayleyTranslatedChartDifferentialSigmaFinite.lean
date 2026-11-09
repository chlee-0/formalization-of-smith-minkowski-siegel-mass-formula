import SMSFormula.PadicCayleyTranslatedChartDifferentialRegularity

/-!
# Local finiteness and sigma-finiteness of the corrected p-adic differential

At every point of the p-adic special-orthogonal group, use the translated
Cayley chart centered at that same point.  A finite-measure open neighborhood
in the exact target subtype maps through its open embedding to an open group
neighborhood.  Arbitrary chart recovery identifies the glued differential
measure there with the corrected target differential measure.

This proves local finiteness of the glued measure without extending one chart
measure by zero across its boundary.  Second countability of the topology
then yields sigma-finiteness.
-/

noncomputable section

open MeasureTheory
open TopologicalSpace
open Topology
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyDifferentialSigmaFiniteGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyDifferentialSigmaFiniteGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The corrected p-adic differential measure glued from translated Cayley
charts is locally finite. -/
theorem padicCayleySpecialOrthogonalDifferentialMeasure_isLocallyFinite
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    IsLocallyFiniteMeasure
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) := by
  refine ⟨fun x ↦ ?_⟩
  let T :=
    padicCayleySpecialOrthogonalTranslatedTarget F p x
  let ν :=
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure
      p n F hF x
  letI : IsLocallyFiniteMeasure ν :=
    padicCayleySpecialOrthogonalTranslatedTargetDifferentialMeasure_isLocallyFinite
      p n F hF x
  let xt : T :=
    ⟨x, self_mem_padicCayleySpecialOrthogonalTranslatedTarget F p x⟩
  rcases ν.exists_isOpen_measure_lt_top xt with ⟨U, hxU, hU, hνU⟩
  let j :
      T →
        specialFormPreservingMatrixSubgroup
          (F.map (algebraMap ℚ ℚ_[p])) :=
    Subtype.val
  let W := j '' U
  have hj : IsOpenEmbedding j :=
    (isOpen_padicCayleySpecialOrthogonalTranslatedTarget
      F p x).isOpenEmbedding_subtypeVal
  have hW : IsOpen W := hj.isOpenMap U hU
  have hxW : x ∈ W := ⟨xt, hxU, rfl⟩
  refine ⟨W, hW.mem_nhds hxW, ?_⟩
  have hWT :
      W ⊆ padicCayleySpecialOrthogonalTranslatedTarget F p x := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  calc
    padicCayleySpecialOrthogonalDifferentialMeasure p n F hF W =
        (padicCayleySpecialOrthogonalDifferentialMeasure
          p n F hF).restrict
            (padicCayleySpecialOrthogonalTranslatedTarget F p x) W := by
      rw [Measure.restrict_apply hW.measurableSet,
        Set.inter_eq_left.mpr hWT]
    _ = padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure
        p n F hF x W := by
      rw [
        restrict_padicCayleySpecialOrthogonalDifferentialMeasure_translatedTarget
          p n F hFsymm hF x]
    _ = ν U := by
      rw [padicCayleySpecialOrthogonalTranslatedAmbientDifferentialMeasure,
        Measure.map_apply continuous_subtype_val.measurable
          hW.measurableSet]
      congr 1
      exact Set.preimage_image_eq U hj.injective
    _ < (⊤ : ENNReal) := hνU

/-- The corrected p-adic differential measure glued from translated Cayley
charts is sigma-finite. -/
theorem padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0) :
    SigmaFinite
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) := by
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
