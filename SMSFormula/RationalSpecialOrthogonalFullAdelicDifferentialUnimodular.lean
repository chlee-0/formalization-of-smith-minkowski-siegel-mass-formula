import SMSFormula.MeasureInversionTransport
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicDifferentialUnimodular
import SMSFormula.RationalSpecialOrthogonalFullAdelicDifferentialMeasure
import SMSFormula.SpecialOrthogonalRealDifferentialUnimodular

/-!
# Unimodularity of the full-adelic special-orthogonal differential measure

The fixed-scale real and finite-adelic invariant-differential measures are
invariant under inversion.  Their product is therefore inversion invariant,
and this property transports through the verified real--finite continuous
multiplicative equivalence defining the full-adelic measure.  Left invariance
then gives right invariance at the same differential scale.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance fullAdelicUnimodularRawRealMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  borel _

local instance fullAdelicUnimodularRawRealBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance fullAdelicUnimodularRealMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.RealSpecialOrthogonalGroup :=
  borel _

local instance fullAdelicUnimodularRealBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.RealSpecialOrthogonalGroup :=
  ⟨rfl⟩

local instance fullAdelicUnimodularFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  borel _

local instance fullAdelicUnimodularFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

/-- The actual real invariant-differential measure exposes the completed
fixed-scale real inversion theorem. -/
instance realInvariantDifferentialGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsInvInvariant V.realInvariantDifferentialGroupMeasure := by
  unfold realInvariantDifferentialGroupMeasure
  exact
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_isInvInvariant
      V.pairingMatrix V.form_symm V.form_det_ne_zero

/-- The literal real--finite product is inversion invariant. -/
instance realFiniteInvariantDifferentialGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsInvInvariant V.realFiniteInvariantDifferentialGroupMeasure := by
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite V.finiteAdelicInvariantDifferentialGroupMeasure :=
    finiteAdelicInvariantDifferentialGroupMeasure_isSigmaFinite V
  letI : SFinite V.realInvariantDifferentialGroupMeasure := by
    infer_instance
  letI : SFinite V.finiteAdelicInvariantDifferentialGroupMeasure := by
    infer_instance
  unfold realFiniteInvariantDifferentialGroupMeasure
  exact Measure.isInvInvariant_prod
    V.realInvariantDifferentialGroupMeasure
    V.finiteAdelicInvariantDifferentialGroupMeasure

/-- The actual full-adelic invariant-differential measure is invariant under
inversion at its constructed scale. -/
instance fullAdelicInvariantDifferentialGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsInvInvariant V.fullAdelicInvariantDifferentialGroupMeasure := by
  unfold fullAdelicInvariantDifferentialGroupMeasure
  exact Measure.isInvInvariant_map_of_commutes
    V.realFiniteInvariantDifferentialGroupMeasure
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.continuous.measurable
    (fun x =>
      V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.map_inv x)

/-- Consequently the full-adelic invariant-differential measure is globally
right invariant. -/
theorem fullAdelicInvariantDifferentialGroupMeasure_isMulRightInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulRightInvariant
      V.fullAdelicInvariantDifferentialGroupMeasure := by
  letI : Measure.IsMulLeftInvariant
      V.fullAdelicInvariantDifferentialGroupMeasure :=
    V.fullAdelicInvariantDifferentialGroupMeasure_isMulLeftInvariant
  exact Measure.isMulRightInvariant_of_isInvInvariant
    V.fullAdelicInvariantDifferentialGroupMeasure

end RationalQuadraticSpaceMatrix
