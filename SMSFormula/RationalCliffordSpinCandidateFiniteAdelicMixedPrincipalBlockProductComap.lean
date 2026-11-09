import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicMixedPrincipalBlockEmbedding
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Finite product comap for mixed principal-block transitions

For finite exceptional sets `S ⊆ T`, the new unrestricted coordinates in the
difference of the two normalized exceptional sets carry the finite product of
the unnormalized local chart-glued p-adic Spin Haar measures.  This module
proves that comapping that finite product along the literal componentwise
inclusion of the integral local subgroups gives exactly the already
constructed finite product of the
comapped integral measures.

The proof uses only measurable rectangles, `Set.piMap_image_univ_pi`, and
`Measure.pi_eq`.  No topology or measure is transported through the
restricted-family block equivalence, and no global finite-adelic measure is
constructed.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicCliffordSpinCandidateGroup v) := by
  infer_instance

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∈
      (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S
        ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∈
      (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \
        (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S
        ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
  Subtype.borelSpace _

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapTailFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapTailFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  Subtype.borelSpace _

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapNewExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapNewExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T) :=
  Pi.borelSpace

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapNewIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapNewIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T) :=
  Pi.borelSpace

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  Pi.borelSpace

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance cliffordSpinCandidateMixedPrincipalBlockProductComapTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  Pi.borelSpace

/-! ## The unrestricted finite new-coordinate product -/

/-- The finite product of the unnormalized local differential Haar measures
on the unrestricted new coordinates `(V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)`. -/
def finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T) :=
  Measure.pi fun v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)} ↦
    V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1

/-- The unrestricted new-coordinate finite product is sigma-finite. -/
instance finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure S T) := by
  unfold finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure
  infer_instance

/-- Comapping the unrestricted finite new-coordinate product along the
componentwise integral-subgroup inclusion gives exactly the finite product of
the comapped integral measures. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure_comap_integralInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure S T).comap
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusionHom
          S T) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralProductMeasure S T := by
  letI (v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
      SigmaFinite
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
          S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
    IsFiniteMeasure.toSigmaFinite _
  rw [finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralProductMeasure]
  symm
  apply Measure.pi_eq
  intro s hs
  rw [
    (V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusion_measurableEmbedding
      S T).comap_apply]
  change
    V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure S T
        (Pi.map
          (fun v
            (g :
              V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor
                S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) =>
              (g : V.HeightOnePadicCliffordSpinCandidateGroup v.1)) ''
          Set.pi Set.univ s) =
      _
  rw [Set.piMap_image_univ_pi]
  unfold finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure
  rw [Measure.pi_pi]
  congr 1
  funext v
  unfold
    heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
  exact
    (((V.isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v.1 (Finset.mem_sdiff.mp v.2).2)
      |>.isOpenEmbedding_subtypeVal.measurableEmbedding).comap_apply
        (V.padicCliffordSpinCandidateChartGluedMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1)
        (s v)).symm

/-! ## Exact nested source-product comparison -/

/-- The direct source-coordinate inclusion fixes the old exceptional
coordinates and common tail and includes only the new integral coordinates
into the unrestricted local groups. -/
def finiteAdelicCliffordSpinCandidateAdmissibleTransitionSourceInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewIntegralProduct S T ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T)) →
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        (V.FiniteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProduct S T ×
          V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail T)) :=
  Prod.map (fun g => g)
    (Prod.map
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusionHom S T)
      (fun g => g))

/-- Exact nested source-product comparison. Comapping the product with
unrestricted new-coordinate Haar factors along the direct transition source
inclusion gives the literal transition volume times the product with
normalized new integral factors. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleTransitionSourceProduct_comap_eq_volume_smul
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S).prod
        ((V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure S T).prod
          (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T))).comap
        (V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionSourceInclusion S T) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T •
        ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S).prod
          ((V.finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure
              S T).prod
            (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T))) := by
  letI (v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
      SigmaFinite
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
          S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
    IsFiniteMeasure.toSigmaFinite _
  letI (v : {v // v ∈ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces T) \ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S)}) :
      SigmaFinite
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S ⟨v.1, (Finset.mem_sdiff.mp v.2).2⟩) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : IsProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) :=
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability
      V T
  letI : IsZeroOrProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure
        S T) := by
    unfold finiteAdelicCliffordSpinCandidateAdmissibleNewNormalizedIntegralProductMeasure
    infer_instance
  letI : SigmaFinite
      ((V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure S T).comap
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusionHom
          S T)) := by
    rw [
      V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure_comap_integralInclusion
        S T]
    unfold finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralProductMeasure
    infer_instance
  unfold finiteAdelicCliffordSpinCandidateAdmissibleTransitionSourceInclusion
  rw [
    Measure.comap_id_prodMap_id_cliffordSpinCandidate
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralExceptionalInclusion_measurableEmbedding
        S T)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure S T)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure T),
    V.finiteAdelicCliffordSpinCandidateAdmissibleNewExceptionalProductMeasure_comap_integralInclusion
      S T,
    V.finiteAdelicCliffordSpinCandidateAdmissibleNewIntegralProductMeasure_eq_transitionVolume_smul
      S T,
    Measure.prod_smul_left,
    Measure.prod_smul_right]

end RationalQuadraticSpaceMatrix
