import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicDirectedMeasure
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Haar packaging for the directed finite-adelic Clifford--Spin measure

The normalized good-place tail is a finite left-invariant measure on a compact
group, hence Haar.  The exceptional finite product is a product of the
completed local Spin Haar measures.  Product and continuous multiplicative-
equivalence transport therefore show that every coherent genuine block
measure is Haar.

Exact recovery on the open genuine blocks then proves that the directed
finite-adelic measure is locally finite and positive on every nonempty open
set.  Together with its completed global left invariance, this packages the
measure as Haar, sigma-finite, and regular.  No empty-block mass-one formula,
analytic top-form identification, or Tamagawa normalization is asserted.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open Topology
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2000000

local instance finiteAdelicSpinHaarPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicSpinHaarGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance finiteAdelicSpinHaarGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

local instance finiteAdelicSpinHaarGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicCliffordSpinCandidateGroup v) := by
  infer_instance

local instance finiteAdelicSpinHaarIntegralFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  Subtype.borelSpace _

local instance finiteAdelicSpinHaarIntegralFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicSpinHaarLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicSpinHaarExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinHaarExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  Pi.borelSpace

local instance finiteAdelicSpinHaarTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  Pi.borelSpace

local instance finiteAdelicSpinHaarTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinHaarMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance finiteAdelicSpinHaarMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinHaarFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance finiteAdelicSpinHaarFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance finiteAdelicSpinHaarGenuineBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
  Subtype.borelSpace _

/-! ## Haar measures on the explicit block factors -/

/-- The finite exceptional product is Haar for the componentwise group law. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
        S) := by
  letI (v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S}) :
      Measure.IsHaarMeasure
        (V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1) :=
    V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure_isHaarMeasure
      v.1
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
  exact Measure.pi.isHaarMeasure _

/-- The normalized integral tail is Haar on its compact product group. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) := by
  letI (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
      CompactSpace
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
    V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorCompactSpace
      S v.1 v.2
  letI : CompactSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) := by
    infer_instance
  letI : Measure.IsMulLeftInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isMulLeftInvariant
      S
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior
    (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
      S) Set.univ
  · exact isCompact_univ
  · rw [interior_univ]
    exact Set.univ_nonempty
  · simp
  · simp

/-- The exceptional Haar product times the compact normalized tail is Haar. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
        S) := by
  letI : Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
        S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isHaarMeasure
      S
  letI : Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isHaarMeasure
      S
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
        S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite
      S
  letI : SFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
        S) := by
    infer_instance
  letI : IsProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability
      S
  letI : IsFiniteMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) := by
    infer_instance
  letI : SFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) := by
    infer_instance
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
  exact Measure.prod.instIsHaarMeasure
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure S)

/-- The raw mixed-block cylinder is Haar after multiplicative homeomorphic
transport. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
        S) := by
  letI : Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
        S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_isHaarMeasure
      S
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
  change Measure.IsHaarMeasure
    (Measure.map
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
        S)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
        S))
  infer_instance

/-- Every coherently scaled genuine block measure is Haar. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        S) := by
  letI : Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
        S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure_isHaarMeasure
      S
  have hraw : Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
        S) := by
    unfold
      finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
    change Measure.IsHaarMeasure
      (Measure.map
        (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
          S).symm
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
          S))
    infer_instance
  letI : Measure.IsHaarMeasure
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockMeasure
        S) := hraw
  rw [
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_eq_weight_smul]
  exact Measure.IsHaarMeasure.smul _
    (V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_zero S)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_top S)

/-! ## The full directed measure -/

/-- The finite-adelic Spin-candidate carrier is second countable through its
finite coordinate embedding. -/
noncomputable instance
    finiteAdelicCliffordSpinCandidateGroupSecondCountableTopology
    (V : RationalQuadraticSpaceMatrix n) :
    SecondCountableTopology V.FiniteAdelicCliffordSpinCandidateGroup := by
  letI : SecondCountableTopology (Finset (Fin n) → RationalFiniteAdele) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) RationalFiniteAdele) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact
    (V.cliffordSpinCandidatePointCoordinateMap_isEmbedding RationalFiniteAdele)
      |>.secondCountableTopology

/-- Exact recovery on the open Haar blocks makes the directed full measure
locally finite. -/
instance finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isLocallyFinite
    (V : RationalQuadraticSpaceMatrix n) :
    IsLocallyFiniteMeasure
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  constructor
  intro x
  obtain ⟨S, hxS⟩ :=
    V.exists_mem_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock
      x
  let iS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S
  let xS :
      V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S :=
    ⟨x, hxS⟩
  let μS :=
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
      S
  letI : LocallyCompactSpace
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockLocallyCompactSpace
      S
  letI : Measure.IsHaarMeasure μS :=
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_isHaarMeasure
      S
  letI : IsLocallyFiniteMeasure μS := by infer_instance
  obtain ⟨U, hxU, hUopen, hUfinite⟩ := μS.exists_isOpen_measure_lt_top xS
  refine ⟨iS '' U, ?_, ?_⟩
  · have hiSOpen : IsOpenEmbedding iS :=
      (V.isOpen_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock
        S).isOpenEmbedding_subtypeVal
    exact (hiSOpen.isOpenMap U hUopen).mem_nhds ⟨xS, hxU, rfl⟩
  · rw [←
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
        S).comap_apply,
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_comap_genuineBlock]
    exact hUfinite

/-- The directed full measure is positive on every nonempty open set. -/
theorem finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isOpenPosMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsOpenPosMeasure
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  constructor
  intro U hU hUne
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨S, hxS⟩ :=
    V.exists_mem_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock
      x
  let iS :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S
  let μS :=
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
      S
  letI : Measure.IsHaarMeasure μS :=
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_isHaarMeasure
      S
  let W : Set
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
    iS ⁻¹' U
  have hWopen : IsOpen W := hU.preimage continuous_subtype_val
  have hWne : W.Nonempty := ⟨⟨x, hxS⟩, hxU⟩
  have hWsub : iS '' W ⊆ U := Set.image_preimage_subset iS U
  exact ne_of_gt <| calc
      0 < μS W := hWopen.measure_pos μS hWne
      _ = V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure (iS '' W) := by
        rw [←
          (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusion_measurableEmbedding
            S).comap_apply,
          V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_comap_genuineBlock]
      _ ≤ V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure U :=
        measure_mono hWsub

/-- The directed finite-adelic Spin measure is a genuine Haar measure at its
explicit coherent block scale. -/
theorem finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsHaarMeasure
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  letI : IsLocallyFiniteMeasure
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isLocallyFinite
  refine
    { toIsMulLeftInvariant :=
        V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isMulLeftInvariant
      toIsOpenPosMeasure :=
        V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isOpenPosMeasure
      lt_top_of_isCompact := fun _K hK =>
        hK.measure_lt_top_of_nhdsWithin fun _ _ =>
          V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure.finiteAt_nhdsWithin
            _ _ }

/-- Second countability and local finiteness make the directed measure
sigma-finite. -/
instance finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n) :
    SigmaFinite V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  exact sigmaFinite_of_locallyFinite

/-- The directed finite-adelic Spin Haar measure is regular. -/
theorem finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_regular
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.Regular V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  letI : RegularSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
    IsTopologicalGroup.regularSpace V.FiniteAdelicCliffordSpinCandidateGroup
  letI : TopologicalSpace.PseudoMetrizableSpace
      V.FiniteAdelicCliffordSpinCandidateGroup :=
    TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology
      V.FiniteAdelicCliffordSpinCandidateGroup
  exact
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure

end RationalQuadraticSpaceMatrix
