import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiberBind

/-!
# Horizontal Haar restricted to the calibrated identity-chart cylinders

The coherent identity-chart measures used to calibrate the ambient central
fiber are literal restrictions of the already fixed horizontal Haar measure.
This file records that fact first on the finite-adelic carrier and then after
adjoining the real identity chart and transporting to full adeles.

The carrier is an actual image of the exceptional identity chart times the
complete normalized good tail.  No directed supremum of chart cylinders is
used: exceptional-set enlargement does not make these carriers monotone.
-/

noncomputable section

open MeasureTheory
open Topology

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalCylinderHaarRestrictionPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalCylinderHaarRestrictionFiniteMeasurableSpace :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalCylinderHaarRestrictionFiniteBorelSpace :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalCylinderHaarRestrictionFullMeasurableSpace :
    MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalCylinderHaarRestrictionFullBorelSpace :
    BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalCylinderHaarRestrictionExceptionalSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalCylinderHaarRestrictionExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance horizontalCylinderHaarRestrictionIntegralFactorSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalCylinderHaarRestrictionIntegralFactorBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance horizontalCylinderHaarRestrictionTailSecondCountable
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalCylinderHaarRestrictionTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

/-! ## Finite-adelic carrier -/

/-- The actual finite-adelic image of the exceptional identity chart times
the complete normalized integral tail. -/
def cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set V.FiniteAdelicCliffordGeneralSpinGroup :=
  V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S ''
    ((V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S) ×ˢ
      Set.univ)

theorem measurableEmbedding_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableEmbedding
      (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S) := by
  unfold cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
  exact
    (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
      S).comp
      ((V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm
        |>.measurableEmbedding.comp
        (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S
          |>.measurableEmbedding))

theorem measurableSet_cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet (V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S) := by
  let f := V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
  let C : Set (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S) :=
    (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S) ×ˢ Set.univ
  have hf : MeasurableEmbedding f :=
    V.measurableEmbedding_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
  have hC : MeasurableSet C :=
    (V.measurableSet_cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S).prod
      MeasurableSet.univ
  exact hf.measurableSet_image.mpr hC

/-- Restricting the fixed finite-adelic horizontal Haar to the literal
identity-chart carrier gives exactly the coherent finite cylinder. -/
theorem finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_identityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
        (V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S) =
      V.cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure S := by
  let f := V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
  let C : Set (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S) :=
    (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S) ×ˢ Set.univ
  let B := Set.range
    (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S)
  have hf : MeasurableEmbedding f :=
    V.measurableEmbedding_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
  have hC : MeasurableSet C :=
    (V.measurableSet_cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S).prod
      MeasurableSet.univ
  have hFC : MeasurableSet (f '' C) := hf.measurableSet_image.mpr hC
  have hsub : f '' C ⊆ B := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨_, rfl⟩
  have hsource :
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure S =
        Measure.map f
          (V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
            V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S) := by
    have hi : Measurable
        (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S) :=
      (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S).measurable
    have he : Measurable
        (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm :=
      (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm.measurable
    have hh : Measurable
        (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S) :=
      (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S).measurable
    dsimp only [f]
    unfold cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure
      cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure
      cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure
      cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure
      cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
    simp_rw [Measure.map_smul]
    congr 1
    rw [Measure.map_map hi he, Measure.map_map (hi.comp he) hh]
    simp only [Function.comp_def]
  calc
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict (f '' C) =
        (V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict B).restrict
          (f '' C) := by
      rw [Measure.restrict_restrict]
      · congr 1
        exact (Set.inter_eq_left.mpr hsub).symm
      · exact hFC
    _ = (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure S).restrict
          (f '' C) := by
      rw [V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_genuineBlock S]
    _ = (Measure.map f
          (V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
            V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S)).restrict
          (f '' C) := by rw [hsource]
    _ = Measure.map f
          ((V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
            V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S).restrict C) := by
      rw [Measure.restrict_map hf.measurable (hf.measurableSet_image.mpr hC)]
      congr 2
      exact Set.preimage_image_eq C hf.injective
    _ = Measure.map f
          (V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S •
            V.cliffordGeneralSpinHorizontalExceptionalIdentityChartTailSourceMeasure S) := by
      rw [Measure.restrict_smul,
        V.restrict_cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_identityChart S]
    _ = V.cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure S := by
      have hi : Measurable
          (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S) :=
        (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S).measurable
      have he : Measurable
          (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm :=
        (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm.measurable
      have hh : Measurable
          (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S) :=
        (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S).measurable
      dsimp only [f]
      unfold cliffordGeneralSpinHorizontalCoherentIdentityChartAmbientMeasure
        cliffordGeneralSpinHorizontalCoherentIdentityChartGenuinePrincipalBlockMeasure
        cliffordGeneralSpinHorizontalCoherentIdentityChartRestrictedPrincipalBlockMeasure
        cliffordGeneralSpinHorizontalIdentityChartRestrictedPrincipalBlockMeasure
        cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
      simp_rw [Measure.map_smul]
      congr 1
      rw [Measure.map_map hi he, Measure.map_map (hi.comp he) hh]
      simp only [Function.comp_def]

/-! ## Real--finite and full-adelic carriers -/

/-- The literal real identity chart times the finite coherent carrier. -/
def cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (V.RealCliffordGeneralSpinGroup ×
      V.FiniteAdelicCliffordGeneralSpinGroup) :=
  V.realCliffordGeneralSpinCentralFiberIdentityChart.source ×ˢ
    V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S

theorem measurableSet_cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet
      (V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S) := by
  exact V.realCliffordGeneralSpinCentralFiberIdentityChart.open_source.measurableSet.prod
    (V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S)

theorem realFiniteCliffordGeneralSpinHorizontalGroupMeasure_restrict_identityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.realFiniteCliffordGeneralSpinHorizontalGroupMeasure.restrict
        (V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S) =
      V.cliffordGeneralSpinHorizontalCoherentIdentityChartRealFiniteMeasure S := by
  letI : Measure.IsHaarMeasure
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
  letI : SigmaFinite
      V.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    Measure.IsHaarMeasure.sigmaFinite _
  unfold realFiniteCliffordGeneralSpinHorizontalGroupMeasure
    cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier
    cliffordGeneralSpinHorizontalCoherentIdentityChartRealFiniteMeasure
    realCliffordGeneralSpinHorizontalIdentityChartAmbientMeasure
  rw [← Measure.prod_restrict,
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_identityChart S]

/-- The calibrated full-adelic cylinder carrier obtained through the exact
real--finite equivalence. -/
def cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set V.FullAdelicCliffordGeneralSpinGroup :=
  V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm ''
    V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S

theorem measurableSet_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    MeasurableSet
      (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S) := by
  exact
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.measurableEmbedding
      |>.measurableSet_image.mpr
        (V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S)

/-- The calibrated full-adelic identity carrier is open.  This is the
topological input needed to choose a compact calibration neighborhood inside
the already constructed cylinder; it introduces no new chart. -/
theorem isOpen_cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S) := by
  let exceptionalCarrier :=
    V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S
  let finiteSourceCarrier : Set
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
        V.CliffordGeneralSpinHorizontalIntegralTail S) :=
    exceptionalCarrier ×ˢ Set.univ
  have hexceptional : IsOpen exceptionalCarrier := by
    unfold exceptionalCarrier
      cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier
    apply isOpen_set_pi Set.finite_univ
    intro v _hv
    exact
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).open_source
  have hfiniteSource : IsOpen finiteSourceCarrier :=
    hexceptional.prod isOpen_univ
  have hfiniteMap : IsOpenEmbedding
      (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S) := by
    unfold cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient
    exact
      (V.isOpen_cliffordGeneralSpinHorizontalGenuinePrincipalBlock S
        |>.isOpenEmbedding_subtypeVal).comp
        ((V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph S).symm
          |>.isOpenEmbedding.comp
          (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph S
            |>.isOpenEmbedding))
  have hfinite : IsOpen
      (V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S) := by
    unfold cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier
    exact hfiniteMap.isOpenMap finiteSourceCarrier hfiniteSource
  have hrealFinite : IsOpen
      (V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S) := by
    exact V.realCliffordGeneralSpinCentralFiberIdentityChart.open_source.prod hfinite
  unfold cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
  exact
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.toHomeomorph
      |>.isOpen_image.mpr hrealFinite

/-- The calibrated full-adelic identity carrier is nonempty. -/
theorem cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier_nonempty
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S).Nonempty := by
  let exceptional : V.CliffordGeneralSpinHorizontalExceptionalProduct S :=
    fun _v ↦ 1
  let tail : V.CliffordGeneralSpinHorizontalIntegralTail S := fun _v ↦ 1
  let finitePoint :=
    V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S (exceptional, tail)
  have hexceptional : exceptional ∈
      V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S := by
    intro v _hv
    exact
      V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source
        (Rat.HeightOneSpectrum.primesEquiv v.1).1
  have hfinite : finitePoint ∈
      V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S := by
    exact ⟨(exceptional, tail), ⟨hexceptional, Set.mem_univ tail⟩, rfl⟩
  let realFinitePoint :
      V.RealCliffordGeneralSpinGroup × V.FiniteAdelicCliffordGeneralSpinGroup :=
    (1, finitePoint)
  refine ⟨V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm realFinitePoint, ?_⟩
  exact ⟨realFinitePoint, ⟨
    V.one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source, hfinite⟩, rfl⟩

/-- The coherent full-adelic identity-chart cylinder is exactly the
restriction of the fixed horizontal adelic Haar to its literal carrier. -/
theorem fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_restrict_identityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.restrict
        (V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S) =
      V.cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure S := by
  let e :=
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm.toHomeomorph
  let C := V.cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S
  have hC : MeasurableSet C :=
    V.measurableSet_cliffordGeneralSpinHorizontalIdentityChartRealFiniteCarrier S
  have heC : MeasurableSet (e '' C) :=
    e.measurableEmbedding.measurableSet_image.mpr hC
  unfold fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
    cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier
    cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure
  change (Measure.map e V.realFiniteCliffordGeneralSpinHorizontalGroupMeasure).restrict
      (e '' C) =
    Measure.map e
      (V.cliffordGeneralSpinHorizontalCoherentIdentityChartRealFiniteMeasure S)
  rw [Measure.restrict_map e.measurable heC]
  rw [Set.preimage_image_eq C e.injective]
  rw [V.realFiniteCliffordGeneralSpinHorizontalGroupMeasure_restrict_identityChart S]

end RationalQuadraticSpaceMatrix
