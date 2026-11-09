import SMSFormula.RationalIdeleDifferentialBlockHaar
import SMSFormula.RationalIdeleDifferentialHaar
import SMSFormula.RationalAdeleAdditiveMeasure

/-!
# Haar regularity and exact normalization of differential finite ideles

Exact recovery on the open genuine Haar blocks makes the directed measure
locally finite and positive on nonempty opens.  The empty exceptional block is
literally the everywhere-integral finite-idele subgroup and has probability
mass one.  Haar uniqueness at that positive compact therefore identifies the
directed measure exactly with the pre-existing compact-normalized Haar measure,
with no Euler-product scalar.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Topology

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2400000

local instance rationalIdeleFiniteRegularityAmbientMeasurableSpace :
    MeasurableSpace RationalFiniteAdeleˣ :=
  borel _

local instance rationalIdeleFiniteRegularityAmbientBorelSpace :
    BorelSpace RationalFiniteAdeleˣ :=
  ⟨rfl⟩

local instance rationalIdeleFiniteRegularityFiniteAdeleT2 :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance rationalIdeleFiniteRegularityAmbientLocallyCompact :
    LocallyCompactSpace RationalFiniteAdeleˣ := by
  infer_instance

local instance rationalIdeleFiniteRegularityBlockBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

local instance rationalIdeleFiniteRegularityPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance rationalIdeleFiniteRegularityLocalMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance rationalIdeleFiniteRegularityLocalBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

local instance rationalIdeleFiniteRegularityLocalSecondCountable
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ := by
  letI : SecondCountableTopology
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology
      (ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] ×
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ᵐᵒᵖ) :=
    inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

local instance rationalIdeleFiniteRegularityIntegralSecondCountable
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance rationalIdeleFiniteRegularityIntegralBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  Subtype.borelSpace _

local instance rationalIdeleFiniteRegularityExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialExceptionalProduct S) :=
  Pi.borelSpace

local instance rationalIdeleFiniteRegularityTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialIntegralTail S) :=
  Pi.borelSpace

/-- Rational finite ideles are second countable through their value--inverse
embedding into the finite adele ring and its multiplicative opposite. -/
noncomputable instance rationalFiniteIdeleSecondCountableTopology_differential :
    SecondCountableTopology RationalFiniteAdeleˣ := by
  letI : SecondCountableTopology RationalFiniteAdeleᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology
      (RationalFiniteAdele × RationalFiniteAdeleᵐᵒᵖ) :=
    inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/-- Exact recovery on the open Haar blocks makes the directed differential
measure locally finite. -/
instance rationalFiniteIdeleDifferentialDirectedMeasure_isLocallyFinite :
    IsLocallyFiniteMeasure rationalFiniteIdeleDifferentialDirectedMeasure := by
  constructor
  intro x
  obtain ⟨S, hxS⟩ :=
    exists_mem_rationalIdeleDifferentialGenuinePrincipalBlock x
  let iS := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S
  let xS : RationalIdeleDifferentialGenuinePrincipalBlock S := ⟨x, hxS⟩
  let muS := rationalIdeleDifferentialGenuinePrincipalBlockMeasure S
  letI : LocallyCompactSpace
      (RationalIdeleDifferentialGenuinePrincipalBlock S) :=
    (isOpen_isRationalIdeleDifferentialGenuinePrincipalBlock S)
      |>.locallyCompactSpace
  letI : Measure.IsHaarMeasure muS :=
    rationalIdeleDifferentialGenuinePrincipalBlockMeasure_isHaarMeasure S
  letI : IsLocallyFiniteMeasure muS := by infer_instance
  obtain ⟨U, hxU, hUopen, hUfinite⟩ := muS.exists_isOpen_measure_lt_top xS
  refine ⟨iS '' U, ?_, ?_⟩
  · have hiSOpen : IsOpenEmbedding iS :=
      (isOpen_isRationalIdeleDifferentialGenuinePrincipalBlock S)
        |>.isOpenEmbedding_subtypeVal
    exact (hiSOpen.isOpenMap U hUopen).mem_nhds ⟨xS, hxU, rfl⟩
  · rw [←
      (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
        S).comap_apply,
      rationalFiniteIdeleDifferentialDirectedMeasure_comap_genuineBlock]
    exact hUfinite

/-- The directed differential measure is positive on every nonempty open
set. -/
theorem rationalFiniteIdeleDifferentialDirectedMeasure_isOpenPosMeasure :
    Measure.IsOpenPosMeasure rationalFiniteIdeleDifferentialDirectedMeasure := by
  constructor
  intro U hU hUne
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨S, hxS⟩ :=
    exists_mem_rationalIdeleDifferentialGenuinePrincipalBlock x
  let iS := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion S
  let muS := rationalIdeleDifferentialGenuinePrincipalBlockMeasure S
  letI : Measure.IsHaarMeasure muS :=
    rationalIdeleDifferentialGenuinePrincipalBlockMeasure_isHaarMeasure S
  let W : Set (RationalIdeleDifferentialGenuinePrincipalBlock S) := iS ⁻¹' U
  have hWopen : IsOpen W := hU.preimage continuous_subtype_val
  have hWne : W.Nonempty := ⟨⟨x, hxS⟩, hxU⟩
  have hWsub : iS '' W ⊆ U := Set.image_preimage_subset iS U
  exact ne_of_gt <| calc
    0 < muS W := hWopen.measure_pos muS hWne
    _ = rationalFiniteIdeleDifferentialDirectedMeasure (iS '' W) := by
      rw [←
        (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
          S).comap_apply,
        rationalFiniteIdeleDifferentialDirectedMeasure_comap_genuineBlock]
    _ ≤ rationalFiniteIdeleDifferentialDirectedMeasure U :=
      measure_mono hWsub

/-- The directed differential finite-idele measure is Haar at its coherent
cylinder scale. -/
theorem rationalFiniteIdeleDifferentialDirectedMeasure_isHaarMeasure :
    Measure.IsHaarMeasure rationalFiniteIdeleDifferentialDirectedMeasure := by
  letI : IsLocallyFiniteMeasure rationalFiniteIdeleDifferentialDirectedMeasure :=
    rationalFiniteIdeleDifferentialDirectedMeasure_isLocallyFinite
  refine
    { toIsMulLeftInvariant :=
        rationalFiniteIdeleDifferentialDirectedMeasure_isMulLeftInvariant
      toIsOpenPosMeasure :=
        rationalFiniteIdeleDifferentialDirectedMeasure_isOpenPosMeasure
      lt_top_of_isCompact := fun _K hK ↦
        hK.measure_lt_top_of_nhdsWithin fun _ _ ↦
          rationalFiniteIdeleDifferentialDirectedMeasure.finiteAt_nhdsWithin
            _ _ }

instance rationalFiniteIdeleDifferentialDirectedMeasure_isSigmaFinite :
    SigmaFinite rationalFiniteIdeleDifferentialDirectedMeasure :=
  sigmaFinite_of_locallyFinite

/-! ## The empty block fixes the scalar -/

/-- The empty exceptional block is literally the subgroup of everywhere
integral finite ideles with integral inverse. -/
theorem range_rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_empty :
    Set.range
        (rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion ∅) =
      integralFiniteIdeleUnits := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    constructor
    · rw [mem_integralFiniteAdeleSubring_iff]
      intro v
      have hv := x.2 v (by simp)
      rw [mem_padicIntegralUnitsSubgroup_iff] at hv
      exact (mem_adicCompletionIntegers_iff_padic v _).2 hv.1
    · rw [mem_integralFiniteAdeleSubring_iff]
      intro v
      have hv := x.2 v (by simp)
      rw [mem_padicIntegralUnitsSubgroup_iff] at hv
      exact (mem_adicCompletionIntegers_iff_padic v _).2 hv.2
  · intro ha
    refine ⟨⟨a, ?_⟩, rfl⟩
    intro v _hv
    rw [mem_padicIntegralUnitsSubgroup_iff]
    exact ⟨(mem_adicCompletionIntegers_iff_padic v _).1 (ha.1 v),
      (mem_adicCompletionIntegers_iff_padic v _).1 (ha.2 v)⟩

/-- With no exceptional coordinates the direct source is a literal
probability measure. -/
noncomputable instance
    rationalIdeleDifferentialExceptionalTailSourceMeasure_empty_isProbability :
    IsProbabilityMeasure
      (rationalIdeleDifferentialExceptionalTailSourceMeasure ∅) := by
  letI : IsProbabilityMeasure
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure ∅) :=
    rationalIdeleDifferentialNormalizedIntegralTailMeasure_isProbability ∅
  letI : IsProbabilityMeasure
      (rationalIdeleDifferentialExceptionalProductMeasure ∅) := by
    constructor
    have h := rationalIdeleDifferentialExceptionalProductMeasure_pi
      ∅ (fun _ ↦ Set.univ)
    simpa using h
  unfold rationalIdeleDifferentialExceptionalTailSourceMeasure
  infer_instance

/-- The coherent measure on the empty genuine block has total mass one. -/
theorem rationalIdeleDifferentialGenuinePrincipalBlockMeasure_empty_univ :
    rationalIdeleDifferentialGenuinePrincipalBlockMeasure ∅ Set.univ = 1 := by
  letI : IsProbabilityMeasure
      (rationalIdeleDifferentialExceptionalTailSourceMeasure ∅) :=
    rationalIdeleDifferentialExceptionalTailSourceMeasure_empty_isProbability
  unfold rationalIdeleDifferentialGenuinePrincipalBlockMeasure
  rw [Measure.map_apply
    (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockHomeomorph ∅
      |>.continuous.measurable)
    MeasurableSet.univ]
  simp

/-- Exact empty-block recovery gives the directed measure literal mass one on
the everywhere-integral subgroup. -/
theorem rationalFiniteIdeleDifferentialDirectedMeasure_integralUnits :
    rationalFiniteIdeleDifferentialDirectedMeasure integralFiniteIdeleUnits = 1 := by
  let i := rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion ∅
  have hi : MeasurableEmbedding i :=
    rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_measurableEmbedding ∅
  calc
    rationalFiniteIdeleDifferentialDirectedMeasure integralFiniteIdeleUnits =
        rationalFiniteIdeleDifferentialDirectedMeasure (Set.range i) := by
      rw [range_rationalIdeleDifferentialGenuinePrincipalBlockAmbientInclusion_empty]
    _ = rationalIdeleDifferentialGenuinePrincipalBlockMeasure ∅ Set.univ := by
      rw [← Set.image_univ]
      rw [← hi.comap_apply,
        rationalFiniteIdeleDifferentialDirectedMeasure_comap_genuineBlock]
    _ = 1 :=
      rationalIdeleDifferentialGenuinePrincipalBlockMeasure_empty_univ

/-- The glued cylinder measure is exactly the compact-normalized finite-idele
Haar measure.  In particular no Euler-product scalar survives the gluing. -/
theorem rationalFiniteIdeleDifferentialDirectedMeasure_eq_haar :
    rationalFiniteIdeleDifferentialDirectedMeasure =
      rationalFiniteIdeleDifferentialHaarMeasure := by
  letI : SigmaFinite rationalFiniteIdeleDifferentialDirectedMeasure :=
    rationalFiniteIdeleDifferentialDirectedMeasure_isSigmaFinite
  letI : Measure.IsMulLeftInvariant
      rationalFiniteIdeleDifferentialDirectedMeasure :=
    rationalFiniteIdeleDifferentialDirectedMeasure_isMulLeftInvariant
  apply Eq.symm
  unfold rationalFiniteIdeleDifferentialHaarMeasure
  apply (Measure.haarMeasure_eq_iff
    rationalFiniteIdeleIntegralPositiveCompacts
    rationalFiniteIdeleDifferentialDirectedMeasure).2
  exact rationalFiniteIdeleDifferentialDirectedMeasure_integralUnits

end RationalQuadraticSpaceMatrix
