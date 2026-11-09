import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteBlockOverlapRecovery
import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicCoherentOverlapRestriction

/-!
# Block coherent finite-adelic Haar restricted to a presentation overlap

The recovered native block exceptional/tail overlap source is pushed through
the repository's existing block identity-chart assembly.  Restricting the
fixed block finite-adelic horizontal Haar to its actual image gives the
transported overlap cylinder multiplied by the already defined block
restricted-block weight.

No chart domain is identified with an ambient chart domain, and no comparison
of the block and ambient coherent weights is made here.
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

local instance blockCoherentOverlapRestrictionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance blockCoherentOverlapRestrictionFiniteMeasurableSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    MeasurableSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance blockCoherentOverlapRestrictionFiniteBorelSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    BorelSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance blockCoherentOverlapRestrictionExceptionalSecondCountable
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (W.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance blockCoherentOverlapRestrictionExceptionalBorelSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (W.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance blockCoherentOverlapRestrictionIntegralFactorSecondCountable
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : W.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (W.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance blockCoherentOverlapRestrictionIntegralFactorBorelSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : W.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (W.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance blockCoherentOverlapRestrictionTailSecondCountable
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (W.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance blockCoherentOverlapRestrictionTailBorelSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (W.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

/-- The actual finite-adelic image of the pulled-back common overlap inside
the already selected native block identity-chart cylinder. -/
def blockFiniteAdelicPresentationOverlapCylinderCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (P.blockSpace hx).FiniteAdelicCliffordGeneralSpinGroup :=
  (P.blockSpace hx).cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S ''
    P.blockFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S

theorem measurableSet_blockFiniteAdelicPresentationOverlapCylinderCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet
      (P.blockFiniteAdelicPresentationOverlapCylinderCarrier hx S) :=
  ((P.blockSpace hx)
    |>.measurableEmbedding_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S)
    |>.measurableSet_image.mpr
      (P.measurableSet_blockFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S)

/-- Restricting the coherent block finite-adelic horizontal Haar cylinder to
the pulled-back common presentation overlap leaves the repository's native
block weight explicit and multiplies the assembled transported overlap
cylinder measure by that weight. -/
theorem blockFiniteAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_presentationOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    ((P.blockSpace hx)
      |>.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure).restrict
        (P.blockFiniteAdelicPresentationOverlapCylinderCarrier hx S) =
      (P.blockSpace hx).cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
        P.transportedFiniteAdelicPresentationOverlapCylinderMeasure hx hS := by
  let W := P.blockSpace hx
  let f := W.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
  let C := P.blockFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S
  let I : Set (W.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      W.CliffordGeneralSpinHorizontalIntegralTail S) :=
    W.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S ×ˢ Set.univ
  let μ := W.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S
  let μI := W.cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure S
  let w := W.cliffordGeneralSpinHorizontalRestrictedBlockWeight S
  let j := P.blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS
  let ν := P.transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure S hx
  have hf : MeasurableEmbedding f :=
    W.measurableEmbedding_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
  have hC : MeasurableSet C :=
    P.measurableSet_blockFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S
  have hFC : MeasurableSet (f '' C) := hf.measurableSet_image.mpr hC
  have hsub : C ⊆ I := by
    rintro g ⟨hg, _⟩
    constructor
    · intro v _
      have hcommon := hg v (Set.mem_univ v)
      change
        P.blockToAmbientGeneralSpinIntrinsicPoint
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] hx (g.1 v) ∈
          P.transportedAmbientPadicCentralFiberSourceOverlap
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx at hcommon
      have htransported := hcommon.1
      rw [P.mem_blockToAmbientTransportedPadicCentralFiberIdentityChart_source_iff
        hx (Rat.HeightOneSpectrum.primesEquiv v.1).1] at htransported
      simpa only [P.ambientToBlockGeneralSpinIntrinsicPoint_blockToAmbient] using
        htransported
    · exact Set.mem_univ _
  have hsubImage : f '' C ⊆ f '' I := Set.image_mono hsub
  have hcoherent :
      W.cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure S =
        Measure.map f (w • μI) := by
    have hi : Measurable
        (W.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S) :=
      (W.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S)
        |>.measurable
    have he : Measurable
        (W.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm :=
      (W.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm.measurable
    have hh : Measurable
        (W.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S) :=
      (W.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S)
        |>.measurable
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
      (W.cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure S).restrict C =
        (W.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S).restrict C
    rw [← W.restrict_cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_identityChart S]
    rw [Measure.restrict_restrict hC]
    congr 1
    exact Set.inter_eq_left.mpr hsub
  have hj : Measurable j :=
    P.measurable_blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS
  have hjmap : Measure.map j ν = μ.restrict C :=
    P.map_transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure_eq_restrict hx hS
  have hcylinder : Measure.map f (μ.restrict C) =
      P.transportedFiniteAdelicPresentationOverlapCylinderMeasure hx hS := by
    rw [← hjmap]
    rw [Measure.map_map hf.measurable hj]
    unfold transportedFiniteAdelicPresentationOverlapCylinderMeasure
    congr 1
  unfold blockFiniteAdelicPresentationOverlapCylinderCarrier
  change W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict (f '' C) = _
  calc
    W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict (f '' C) =
        (W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
          (f '' I)).restrict (f '' C) := by
      rw [Measure.restrict_restrict hFC]
      congr 1
      exact (Set.inter_eq_left.mpr hsubImage).symm
    _ = (W.cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure S).restrict
          (f '' C) := by
      change
        (W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
          (W.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S)).restrict
            (f '' C) = _
      rw [W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_identityChart S]
    _ = (Measure.map f (w • μI)).restrict (f '' C) := by rw [hcoherent]
    _ = Measure.map f ((w • μI).restrict C) := by
      rw [Measure.restrict_map hf.measurable hFC]
      congr 2
      exact Set.preimage_image_eq C hf.injective
    _ = Measure.map f (w • μ.restrict C) := by rw [hsource]
    _ = w • Measure.map f (μ.restrict C) := by rw [Measure.map_smul]
    _ = w • P.transportedFiniteAdelicPresentationOverlapCylinderMeasure hx hS := by
      rw [hcylinder]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
