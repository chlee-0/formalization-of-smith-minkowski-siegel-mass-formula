import SMSFormula.AdelicWeilQuotient
import Mathlib.MeasureTheory.Group.Measure
import SMSFormula.SpecialOrthogonalFullAdelicDifferentialMeasurableWeilQuotient
import SMSFormula.RationalCliffordSpinCandidateOnoRelativeTamagawaData
import SMSFormula.RationalSpecialOrthogonalFullAdelicDifferentialUnimodular

/-!
# The raw special-orthogonal datum in the right quotient convention

Every scale-explicit raw `SO` normalization pushes forward under the verified
real--finite splitting to the product of the real differential measure and a
scalar multiple of the finite-adelic differential measure.  The completed
real and finite inversion theorems therefore make that product inversion
invariant.  Inversion invariance descends through the splitting equivalence,
so the actual raw Ono `SO` datum satisfies the right Weil identity for the
identical ambient measure rather than merely its inverse.

This does not assert the corresponding Spin endpoint or identify either
measure with a sourced canonical Tamagawa normalization.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} {V : RationalQuadraticSpaceMatrix n}

set_option synthInstance.maxHeartbeats 200000

local instance rawRightQuotientRealUnderlyingMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  borel _

local instance rawRightQuotientRealUnderlyingBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance rawRightQuotientRealMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.RealSpecialOrthogonalGroup :=
  borel _

local instance rawRightQuotientRealBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.RealSpecialOrthogonalGroup :=
  ⟨rfl⟩

local instance rawRightQuotientFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  borel _

local instance rawRightQuotientFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

namespace IsRawInvariantDifferentialFullAdelicGroupMeasureWithScale

/-- Every scale-explicit raw `SO` ambient measure is invariant under
inversion. -/
theorem isInvInvariant
    {finiteScale : ℝ≥0∞}
    {mu : Measure V.FullAdelicSpecialOrthogonalGroup}
    (C : V.IsRawInvariantDifferentialFullAdelicGroupMeasureWithScale
      finiteScale mu) :
    Measure.IsInvInvariant mu := by
  let E := V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite V.finiteAdelicInvariantDifferentialGroupMeasure :=
    finiteAdelicInvariantDifferentialGroupMeasure_isSigmaFinite V
  letI : SFinite V.realInvariantDifferentialGroupMeasure := by
    infer_instance
  letI : SFinite V.finiteAdelicInvariantDifferentialGroupMeasure := by
    infer_instance
  letI : Measure.IsInvInvariant
      (finiteScale • V.finiteAdelicInvariantDifferentialGroupMeasure) :=
    Measure.isInvInvariant_smul finiteScale
      V.finiteAdelicInvariantDifferentialGroupMeasure
  have hprod : Measure.IsInvInvariant
      (V.realInvariantDifferentialGroupMeasure.prod
        (finiteScale • V.finiteAdelicInvariantDifferentialGroupMeasure)) :=
    Measure.isInvInvariant_prod
      V.realInvariantDifferentialGroupMeasure
      (finiteScale • V.finiteAdelicInvariantDifferentialGroupMeasure)
  have hmap : Measure.IsInvInvariant
      (Measure.map E.toHomeomorph mu) := by
    exact C.map_realFinite_eq.symm ▸ hprod
  exact Measure.isInvInvariant_of_map_of_commutes
    (mu := mu) (f := E.toHomeomorph)
    E.toHomeomorph.measurableEmbedding
    (fun x => E.map_inv x) hmap

end IsRawInvariantDifferentialFullAdelicGroupMeasureWithScale

namespace IsRawInvariantDifferentialFullAdelicGroupMeasure

/-- The existential raw `SO` normalization also forces inversion
invariance. -/
theorem isInvInvariant
    {mu : Measure V.FullAdelicSpecialOrthogonalGroup}
    (C : V.IsRawInvariantDifferentialFullAdelicGroupMeasure mu) :
    Measure.IsInvInvariant mu := by
  obtain ⟨finiteScale, C⟩ := C
  exact C.isInvInvariant

end IsRawInvariantDifferentialFullAdelicGroupMeasure

namespace IsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale

/-- The ambient measure of scale-explicit raw `SO` measurable-Weil data is
inversion invariant. -/
theorem adelicMeasure_isInvInvariant
    {finiteScale : ℝ≥0∞}
    {D : SpecialOrthogonalAdelicMeasurableWeilMeasureData V}
    (C : V.IsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale
      finiteScale D) :
    Measure.IsInvInvariant D.adelicMeasure :=
  C.adelicMeasure_normalized.isInvInvariant

end IsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale

namespace CliffordSpinCandidateRawOnoTamagawaData

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
