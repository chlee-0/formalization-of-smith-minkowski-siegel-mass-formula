import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteExceptionalOverlapRecovery
import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderHaarRestriction

/-!
# Coherent finite-adelic Haar restricted to a presentation overlap

The recovered unweighted exceptional/tail overlap source is pushed through
the repository's existing identity-chart assembly.  Restricting the fixed
finite-adelic horizontal Haar to its actual image gives the assembled overlap
cylinder multiplied by the already defined coherent restricted-block weight.

The weight remains explicit.  No block/ambient weight comparison or
evaluation of the finite presentation scalar is made here.
-/

noncomputable section

open MeasureTheory
open Topology

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance coherentOverlapRestrictionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance coherentOverlapRestrictionFiniteMeasurableSpace :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance coherentOverlapRestrictionFiniteBorelSpace :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance coherentOverlapRestrictionExceptionalSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance coherentOverlapRestrictionExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance coherentOverlapRestrictionIntegralFactorSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance coherentOverlapRestrictionIntegralFactorBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance coherentOverlapRestrictionTailSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance coherentOverlapRestrictionTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

/-- The actual finite-adelic image of the common presentation overlap inside
the already selected ambient identity-chart cylinder. -/
def ambientFiniteAdelicPresentationOverlapCylinderCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set V.FiniteAdelicCliffordGeneralSpinGroup :=
  V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S ''
    P.ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S

theorem measurableSet_ambientFiniteAdelicPresentationOverlapCylinderCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet
      (P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S) :=
  (V.measurableEmbedding_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S)
    |>.measurableSet_image.mpr
      (P.measurableSet_ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S)

/-- Restricting the coherent finite-adelic horizontal Haar cylinder to the
common presentation overlap leaves the repository's ambient block weight
explicit and multiplies the assembled unweighted overlap-cylinder measure by
that weight. -/
theorem finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_presentationOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
        (P.ambientFiniteAdelicPresentationOverlapCylinderCarrier hx S) =
      V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
        P.ambientFiniteAdelicPresentationOverlapCylinderMeasure hx hS := by
  let f := V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
  let C := P.ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S
  let I : Set (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S) :=
    V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S ×ˢ Set.univ
  let μ := V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S
  let μI := V.cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure S
  let w := V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S
  let j := P.ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS
  let ν := P.ambientFiniteAdelicPresentationOverlapCylinderSourceMeasure S hx
  have hf : MeasurableEmbedding f :=
    V.measurableEmbedding_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
  have hC : MeasurableSet C :=
    P.measurableSet_ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S
  have hFC : MeasurableSet (f '' C) := hf.measurableSet_image.mpr hC
  have hsub : C ⊆ I := by
    rintro g ⟨hg, _⟩
    constructor
    · intro v _
      exact (hg v (Set.mem_univ v)).2
    · exact Set.mem_univ _
  have hsubImage : f '' C ⊆ f '' I := Set.image_mono hsub
  have hcoherent :
      V.cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure S =
        Measure.map f (w • μI) := by
    have hi : Measurable
        (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S) :=
      (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S).measurable
    have he : Measurable
        (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm :=
      (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm.measurable
    have hh : Measurable
        (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S) :=
      (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S).measurable
    dsimp only [f, w, μI]
    unfold cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure
      cliffordGeneralSpinHorizontalCoherentIdentityChartGenuinePrincipalBlockMeasure
      cliffordGeneralSpinHorizontalCoherentIdentityChartRestrictedPrincipalBlockMeasure
      cliffordGeneralSpinHorizontalIdentityChartRestrictedPrincipalBlockMeasure
      cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
    simp_rw [Measure.map_smul]
    congr 1
    rw [Measure.map_map hi he, Measure.map_map (hi.comp he) hh]
    rfl
  have hsource : (w • μI).restrict C = w • μ.restrict C := by
    rw [Measure.restrict_smul]
    congr 1
    change
      (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure S).restrict C =
        (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S).restrict C
    rw [← V.restrict_cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_identityChart S]
    rw [Measure.restrict_restrict hC]
    congr 1
    exact Set.inter_eq_left.mpr hsub
  have hj : Measurable j :=
    P.measurable_ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS
  have hjmap : Measure.map j ν = μ.restrict C :=
    P.map_ambientFiniteAdelicPresentationOverlapCylinderSourceMeasure_eq_restrict hx hS
  have hcylinder : Measure.map f (μ.restrict C) =
      P.ambientFiniteAdelicPresentationOverlapCylinderMeasure hx hS := by
    rw [← hjmap]
    rw [Measure.map_map hf.measurable hj]
    unfold ambientFiniteAdelicPresentationOverlapCylinderMeasure
    congr 1
  unfold ambientFiniteAdelicPresentationOverlapCylinderCarrier
  change V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict (f '' C) = _
  calc
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict (f '' C) =
        (V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
          (f '' I)).restrict (f '' C) := by
      rw [Measure.restrict_restrict hFC]
      congr 1
      exact (Set.inter_eq_left.mpr hsubImage).symm
    _ = (V.cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure S).restrict
          (f '' C) := by
      change
        (V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
          (V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S)).restrict
            (f '' C) = _
      rw [V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_identityChart S]
    _ = (Measure.map f (w • μI)).restrict (f '' C) := by rw [hcoherent]
    _ = Measure.map f ((w • μI).restrict C) := by
      rw [Measure.restrict_map hf.measurable hFC]
      congr 2
      exact Set.preimage_image_eq C hf.injective
    _ = Measure.map f (w • μ.restrict C) := by rw [hsource]
    _ = w • Measure.map f (μ.restrict C) := by rw [Measure.map_smul]
    _ = w • P.ambientFiniteAdelicPresentationOverlapCylinderMeasure hx hS := by
      rw [hcylinder]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
