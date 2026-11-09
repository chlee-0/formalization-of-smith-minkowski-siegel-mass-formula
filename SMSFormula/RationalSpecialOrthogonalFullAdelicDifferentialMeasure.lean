import SMSFormula.RationalSpecialOrthogonalFiniteAdelicDifferentialMeasureRegularity
import SMSFormula.RationalSpecialOrthogonalFullAdelicRealFiniteCarrier
import Mathlib.MeasureTheory.Measure.Regular

/-!
# General full-adelic invariant-differential measure

For an arbitrary rational quadratic-space matrix `V`, this module takes the
product of the real invariant-differential group measure and the finite-adelic
invariant-differential group measure.  It maps that product through the
inverse of the real/finite carrier splitting.

The exact map-back formula keeps both differential factors.  Nonzeroness,
sigma-finiteness, left invariance, Haar certification, and regularity are
transported from the two factors through the continuous multiplicative
equivalence.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 400000

local instance fullAdelicDifferentialProductRealMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  borel _

local instance fullAdelicDifferentialProductRealBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance fullAdelicDifferentialProductRealCarrierMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.RealSpecialOrthogonalGroup :=
  borel _

local instance fullAdelicDifferentialProductRealCarrierBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.RealSpecialOrthogonalGroup :=
  ⟨rfl⟩

local instance fullAdelicDifferentialProductFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  borel _

local instance fullAdelicDifferentialProductFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

/-! ## The literal real/finite product -/

/-- The direct product of the real and finite invariant-differential group
measures induced by the rational invariant top differential. -/
def realFiniteInvariantDifferentialGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure
      (V.RealSpecialOrthogonalGroup ×
        V.FiniteAdelicSpecialOrthogonalGroup) :=
  V.realInvariantDifferentialGroupMeasure.prod
    V.finiteAdelicInvariantDifferentialGroupMeasure

set_option backward.isDefEq.respectTransparency false in
/-- The literal real/finite differential product is sigma-finite. -/
theorem realFiniteInvariantDifferentialGroupMeasure_sigmaFinite
    (V : RationalQuadraticSpaceMatrix n) :
    SigmaFinite V.realFiniteInvariantDifferentialGroupMeasure := by
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite V.finiteAdelicInvariantDifferentialGroupMeasure :=
    finiteAdelicInvariantDifferentialGroupMeasure_isSigmaFinite V
  unfold realFiniteInvariantDifferentialGroupMeasure
  exact Measure.prod.instSigmaFinite
    (μ := V.realInvariantDifferentialGroupMeasure)
    (ν := V.finiteAdelicInvariantDifferentialGroupMeasure)

/-- The literal real/finite differential product is Haar. -/
theorem realFiniteInvariantDifferentialGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsHaarMeasure
      V.realFiniteInvariantDifferentialGroupMeasure := by
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite V.finiteAdelicInvariantDifferentialGroupMeasure :=
    finiteAdelicInvariantDifferentialGroupMeasure_isSigmaFinite V
  letI : SFinite V.realInvariantDifferentialGroupMeasure := by
    infer_instance
  letI : SFinite V.finiteAdelicInvariantDifferentialGroupMeasure := by
    infer_instance
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  letI : Measure.IsHaarMeasure
      V.finiteAdelicInvariantDifferentialGroupMeasure :=
    V.finiteAdelicInvariantDifferentialGroupMeasure_isHaarMeasure
  unfold realFiniteInvariantDifferentialGroupMeasure
  exact Measure.prod.instIsHaarMeasure
    V.realInvariantDifferentialGroupMeasure
    V.finiteAdelicInvariantDifferentialGroupMeasure

/-- The literal real/finite differential product is nonzero. -/
theorem realFiniteInvariantDifferentialGroupMeasure_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.realFiniteInvariantDifferentialGroupMeasure ≠ 0 := by
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite V.finiteAdelicInvariantDifferentialGroupMeasure :=
    finiteAdelicInvariantDifferentialGroupMeasure_isSigmaFinite V
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  letI : Measure.IsHaarMeasure
      V.finiteAdelicInvariantDifferentialGroupMeasure :=
    V.finiteAdelicInvariantDifferentialGroupMeasure_isHaarMeasure
  have hreal : V.realInvariantDifferentialGroupMeasure Set.univ ≠ 0 :=
    isOpen_univ.measure_ne_zero
      V.realInvariantDifferentialGroupMeasure Set.univ_nonempty
  have hfinite :
      V.finiteAdelicInvariantDifferentialGroupMeasure Set.univ ≠ 0 :=
    isOpen_univ.measure_ne_zero
      V.finiteAdelicInvariantDifferentialGroupMeasure Set.univ_nonempty
  intro hzero
  have huniv := congrArg (fun μ : Measure
      (V.RealSpecialOrthogonalGroup ×
        V.FiniteAdelicSpecialOrthogonalGroup) => μ Set.univ) hzero
  change
    (V.realInvariantDifferentialGroupMeasure.prod
        V.finiteAdelicInvariantDifferentialGroupMeasure) Set.univ =
      (0 : Measure
        (V.RealSpecialOrthogonalGroup ×
          V.FiniteAdelicSpecialOrthogonalGroup)) Set.univ at huniv
  rw [Measure.prod_apply MeasurableSet.univ] at huniv
  simp only [Set.preimage_univ, lintegral_const, Measure.coe_zero,
    Pi.zero_apply] at huniv
  exact (mul_ne_zero hfinite hreal) huniv

/-- Left invariance of the literal real/finite differential product. -/
theorem realFiniteInvariantDifferentialGroupMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulLeftInvariant
      V.realFiniteInvariantDifferentialGroupMeasure := by
  letI : Measure.IsHaarMeasure
      V.realFiniteInvariantDifferentialGroupMeasure :=
    V.realFiniteInvariantDifferentialGroupMeasure_isHaarMeasure
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The literal real/finite differential product is regular. -/
theorem realFiniteInvariantDifferentialGroupMeasure_regular
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.Regular V.realFiniteInvariantDifferentialGroupMeasure := by
  letI : LocallyCompactSpace V.RealSpecialOrthogonalGroup :=
    specialFormPreservingRealGroup_locallyCompact
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SecondCountableTopology V.RealSpecialOrthogonalGroup :=
    specialFormPreservingRealGroup_secondCountable V.pairingMatrix
  letI : IsLocallyFiniteMeasure V.realInvariantDifferentialGroupMeasure :=
    specialFormPreservingSmoothRealDifferentialMeasure_isLocallyFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : IsLocallyFiniteMeasure
      V.finiteAdelicInvariantDifferentialGroupMeasure :=
    finiteAdelicInvariantDifferentialGroupMeasure_isLocallyFinite V
  letI : IsLocallyFiniteMeasure
      V.realFiniteInvariantDifferentialGroupMeasure := by
    unfold realFiniteInvariantDifferentialGroupMeasure
    exact Measure.prod.instIsLocallyFiniteMeasure
      (μ := V.realInvariantDifferentialGroupMeasure)
      (ν := V.finiteAdelicInvariantDifferentialGroupMeasure)
  letI : RegularSpace
      (V.RealSpecialOrthogonalGroup ×
        V.FiniteAdelicSpecialOrthogonalGroup) :=
    IsTopologicalGroup.regularSpace _
  letI : TopologicalSpace.PseudoMetrizableSpace
      (V.RealSpecialOrthogonalGroup ×
        V.FiniteAdelicSpecialOrthogonalGroup) :=
    TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology
      _
  exact
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure
      V.realFiniteInvariantDifferentialGroupMeasure

/-! ## Transport to the full-adelic carrier -/

/-- The general full-adelic invariant-differential group measure, obtained by
mapping the literal real/finite product through the inverse carrier split. -/
def fullAdelicInvariantDifferentialGroupMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure V.FullAdelicSpecialOrthogonalGroup :=
  Measure.map
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.toHomeomorph
    V.realFiniteInvariantDifferentialGroupMeasure

/-- Mapping the full-adelic differential measure back through the verified
real/finite split recovers the literal product. -/
theorem map_fullAdelicInvariantDifferentialGroupMeasure_realFinite
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.map
        V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toHomeomorph
        V.fullAdelicInvariantDifferentialGroupMeasure =
      V.realInvariantDifferentialGroupMeasure.prod
        V.finiteAdelicInvariantDifferentialGroupMeasure := by
  rw [fullAdelicInvariantDifferentialGroupMeasure]
  exact
    MeasurableEquiv.map_map_symm
      V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toMeasurableEquiv

/-- The general full-adelic invariant-differential measure is nonzero. -/
theorem fullAdelicInvariantDifferentialGroupMeasure_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicInvariantDifferentialGroupMeasure ≠ 0 := by
  intro hzero
  have hmap := congrArg
    (Measure.map
      V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.toHomeomorph)
    hzero
  rw [V.map_fullAdelicInvariantDifferentialGroupMeasure_realFinite,
    Measure.map_zero] at hmap
  exact V.realFiniteInvariantDifferentialGroupMeasure_ne_zero hmap

/-- The general full-adelic invariant-differential measure is sigma-finite. -/
theorem fullAdelicInvariantDifferentialGroupMeasure_sigmaFinite
    (V : RationalQuadraticSpaceMatrix n) :
    SigmaFinite V.fullAdelicInvariantDifferentialGroupMeasure := by
  letI : SigmaFinite V.realFiniteInvariantDifferentialGroupMeasure :=
    V.realFiniteInvariantDifferentialGroupMeasure_sigmaFinite
  unfold fullAdelicInvariantDifferentialGroupMeasure
  exact
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.toHomeomorph.toMeasurableEquiv.sigmaFinite_map

/-- The general full-adelic invariant-differential measure is Haar. -/
theorem fullAdelicInvariantDifferentialGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsHaarMeasure
      V.fullAdelicInvariantDifferentialGroupMeasure := by
  letI : Measure.IsHaarMeasure V.realFiniteInvariantDifferentialGroupMeasure :=
    V.realFiniteInvariantDifferentialGroupMeasure_isHaarMeasure
  unfold fullAdelicInvariantDifferentialGroupMeasure
  exact
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.toMulEquiv.isHaarMeasure_map
      V.realFiniteInvariantDifferentialGroupMeasure
      V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.continuous
      V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.continuous

/-- Left invariance of the general full-adelic differential measure. -/
theorem fullAdelicInvariantDifferentialGroupMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulLeftInvariant
      V.fullAdelicInvariantDifferentialGroupMeasure := by
  letI : Measure.IsHaarMeasure V.fullAdelicInvariantDifferentialGroupMeasure :=
    V.fullAdelicInvariantDifferentialGroupMeasure_isHaarMeasure
  infer_instance

/-- The general full-adelic invariant-differential measure is regular. -/
theorem fullAdelicInvariantDifferentialGroupMeasure_regular
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.Regular V.fullAdelicInvariantDifferentialGroupMeasure := by
  letI : Measure.Regular V.realFiniteInvariantDifferentialGroupMeasure :=
    V.realFiniteInvariantDifferentialGroupMeasure_regular
  unfold fullAdelicInvariantDifferentialGroupMeasure
  exact
    Measure.Regular.map
      V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.toHomeomorph

end RationalQuadraticSpaceMatrix
