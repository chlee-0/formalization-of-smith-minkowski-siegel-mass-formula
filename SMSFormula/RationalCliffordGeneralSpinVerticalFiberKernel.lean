import SMSFormula.RationalCliffordGeneralSpinRawVerticalCrossedCutoff
import SMSFormula.RationalCliffordGeneralSpinAdelicFundamentalDomainSection
import SMSFormula.RationalCliffordSpinCandidateCanonicalRightQuotient

/-!
# A measurable source kernel for translated vertical Spin fibers

Right translation of the neutral raw Spin quotient measure is jointly
measurable when the translating adelic `GSpin` point varies.  This module
packages those translates as an s-finite kernel indexed by ambient adelic
`GSpin`, and identifies its values with the already established translated
vertical fibers whenever a representative of an idele class is inserted.

This is the source kernel needed for the vertical common-quotient
construction.  It does not descend the kernel to rational idele classes:
that descent additionally requires representative-independence under the
rational `GSpin` diagonal.  No comparison with the singular raw `SO`
quotient measure, measurable similitude section, Cartesian extension, or
volume finiteness is asserted here.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance verticalFiberKernelFullGSpinSecondCountableTopology :
    SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
  V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

local instance verticalFiberKernelGSpinQuotientSecondCountableTopology :
    SecondCountableTopology
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  V.fullAdelicCliffordGeneralSpinLeftQuotientSecondCountableTopology

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1800000

/-! ## Joint right translation on the rational GSpin quotient -/

/-- Joint right translation, with the ambient translating point first and
the rational left-quotient point second. -/
def fullAdelicCliffordGeneralSpinVerticalJointRightOrbit :
    V.FullAdelicCliffordGeneralSpinGroup ×
        V.FullAdelicCliffordGeneralSpinLeftQuotient →
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  fun p => V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul p.1 p.2

/-- Right translation is jointly continuous in the ambient translating point
and the rational left-quotient point. -/
theorem continuous_fullAdelicCliffordGeneralSpinVerticalJointRightOrbit :
    Continuous V.fullAdelicCliffordGeneralSpinVerticalJointRightOrbit := by
  let Q : IsOpenQuotientMap
      (Prod.map
        (id : V.FullAdelicCliffordGeneralSpinGroup →
          V.FullAdelicCliffordGeneralSpinGroup)
        V.fullAdelicCliffordGeneralSpinLeftQuotientMap) :=
    IsOpenQuotientMap.id.prodMap
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isOpenQuotientMap
  apply Q.isQuotientMap.continuous_iff.mpr
  have hrep : Continuous (fun p :
      V.FullAdelicCliffordGeneralSpinGroup ×
        V.FullAdelicCliffordGeneralSpinGroup =>
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap (p.2 * p.1)) :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap.continuous.comp
      (continuous_snd.mul continuous_fst)
  simpa [Q, Prod.map,
    fullAdelicCliffordGeneralSpinVerticalJointRightOrbit,
    fullAdelicCliffordGeneralSpinLeftQuotientRightMul]
    using hrep

end RationalQuadraticSpaceMatrix

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ} {V : RationalQuadraticSpaceMatrix n}

local instance verticalFiberKernelDataFullGSpinSecondCountableTopology :
    SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
  V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

local instance verticalFiberKernelDataGSpinQuotientSecondCountableTopology :
    SecondCountableTopology
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  V.fullAdelicCliffordGeneralSpinLeftQuotientSecondCountableTopology

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1800000

/-! ## S-finiteness of the neutral translated source -/

/-- The raw Spin quotient measure is s-finite independently of whether its
total Tamagawa mass is finite.  It is the pushforward of the restriction of
the s-finite raw ambient Haar measure to the exact Spin fundamental domain. -/
instance spinGeneralSpinQuotientPushforwardMeasure_sFinite
    (D : V.CliffordSpinCandidateRawOnoTamagawaData) :
    SFinite (spinGeneralSpinQuotientPushforwardMeasure V D) := by
  rw [spinGeneralSpinQuotientPushforwardMeasure,
    fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpinPushforward,
    D.spinData.quotientMeasure_eq_fundamentalDomain]
  letI : SFinite D.spinData.adelicMeasure := by
    rw [D.spinRaw.adelicMeasure_eq]
    unfold fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
    letI : SigmaFinite
        V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_sigmaFinite
    letI : SFinite
      V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure := by
      infer_instance
    infer_instance
  unfold leftQuotientFundamentalDomainMeasure
  infer_instance

/-! ## The ambient-source translated Spin kernel -/

/-- The neutral raw Spin quotient translated jointly through every ambient
adelic `GSpin` origin. -/
noncomputable def verticalSpinFiberKernelAtAmbient
    (D : V.CliffordSpinCandidateRawOnoTamagawaData) :
    ProbabilityTheory.Kernel
      V.FullAdelicCliffordGeneralSpinGroup
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  ProbabilityTheory.Kernel.map
    (ProbabilityTheory.Kernel.id ×ₖ
      ProbabilityTheory.Kernel.const
        V.FullAdelicCliffordGeneralSpinGroup
        (spinGeneralSpinQuotientPushforwardMeasure V D))
    V.fullAdelicCliffordGeneralSpinVerticalJointRightOrbit

instance verticalSpinFiberKernelAtAmbient_isSFinite
      (D : V.CliffordSpinCandidateRawOnoTamagawaData) :
    ProbabilityTheory.IsSFiniteKernel
      (D.verticalSpinFiberKernelAtAmbient (V := V)) := by
  unfold verticalSpinFiberKernelAtAmbient
  infer_instance

/-- The ambient-source kernel value is the literal right translate of the
neutral raw Spin quotient pushforward. -/
theorem verticalSpinFiberKernelAtAmbient_apply
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    D.verticalSpinFiberKernelAtAmbient (V := V) x =
      Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)
        (spinGeneralSpinQuotientPushforwardMeasure V D) := by
  ext A hA
  rw [verticalSpinFiberKernelAtAmbient,
    ProbabilityTheory.Kernel.map_apply'
      _ V.continuous_fullAdelicCliffordGeneralSpinVerticalJointRightOrbit.measurable
      _ hA,
    ProbabilityTheory.Kernel.id_prod_apply' _ x
      (V.continuous_fullAdelicCliffordGeneralSpinVerticalJointRightOrbit.measurable
        hA),
    ProbabilityTheory.Kernel.const_apply]
  change spinGeneralSpinQuotientPushforwardMeasure V D
      ((V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) ⁻¹' A) =
    Measure.map
      (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x)
      (spinGeneralSpinQuotientPushforwardMeasure V D) A
  exact (Measure.map_apply
    (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) hA).symm

/-- Inserting the existing chosen representative of an idele class recovers
the translated vertical Spin fiber. -/
theorem verticalSpinFiberKernelAtAmbient_verticalRepresentative
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    D.verticalSpinFiberKernelAtAmbient (V := V)
        (V.verticalGeneralSpinRepresentative hsurj c) =
      D.verticalSpinFiberMeasure V hsurj c := by
  rw [D.verticalSpinFiberKernelAtAmbient_apply]
  rfl

/-- Every ambient-source translated Spin fiber remains s-finite. -/
instance verticalSpinFiberKernelAtAmbient_apply_sFinite
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    SFinite (D.verticalSpinFiberKernelAtAmbient (V := V) x) := by
  rw [D.verticalSpinFiberKernelAtAmbient_apply]
  infer_instance

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
