import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockEmbedding
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Finite product comap for mixed principal-block transitions

For finite exceptional sets `S ⊆ T`, the new unrestricted coordinates in
`T \ S` carry the finite product of the unnormalized local
invariant-differential Haar measures.  This module proves that comapping that
finite product along the literal componentwise inclusion of the integral
local subgroups gives exactly the already constructed finite product of the
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

local instance mixedPrincipalBlockProductComapDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance mixedPrincipalBlockProductComapPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance mixedPrincipalBlockProductComapGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance mixedPrincipalBlockProductComapGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

local instance mixedPrincipalBlockProductComapGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    V.pairingMatrix (Rat.HeightOneSpectrum.primesEquiv v).1

local instance mixedPrincipalBlockProductComapIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance mixedPrincipalBlockProductComapIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  Subtype.borelSpace _

local instance mixedPrincipalBlockProductComapNewExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockProductComapNewExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T) :=
  Pi.borelSpace

local instance mixedPrincipalBlockProductComapNewIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockProductComapNewIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T) :=
  Pi.borelSpace

local instance mixedPrincipalBlockProductComapExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockProductComapExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S) :=
  Pi.borelSpace

local instance mixedPrincipalBlockProductComapTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance mixedPrincipalBlockProductComapTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  Pi.borelSpace

/-! ## The unrestricted finite new-coordinate product -/

/-- The finite product of the unnormalized local differential Haar measures
on the unrestricted new coordinates `T \ S`. -/
def finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T) :=
  Measure.pi fun v : {v // v ∈ T \ S} ↦
    V.heightOnePadicInvariantDifferentialGroupMeasure v.1

/-- The unrestricted new-coordinate finite product is sigma-finite. -/
instance finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure S T) := by
  unfold finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure
  infer_instance

/-- Comapping the unrestricted finite new-coordinate product along the
componentwise integral-subgroup inclusion gives exactly the finite product of
the comapped integral measures. -/
theorem
    finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure_comap_integralInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure S T).comap
        (V.finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusionHom
          S T) =
      V.finiteAdelicSpecialOrthogonalNewIntegralProductMeasure S T := by
  letI (v : {v // v ∈ T \ S}) :
      SigmaFinite
        (V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1) :=
    IsFiniteMeasure.toSigmaFinite _
  rw [finiteAdelicSpecialOrthogonalNewIntegralProductMeasure]
  symm
  apply Measure.pi_eq
  intro s hs
  rw [
    (V.finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusion_measurableEmbedding
      S T).comap_apply]
  change
    V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure S T
        (Pi.map
          (fun v
            (g : V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) =>
              (g : V.HeightOnePadicSpecialOrthogonalGroup v.1)) ''
          Set.pi Set.univ s) =
      _
  rw [Set.piMap_image_univ_pi]
  unfold finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure
  rw [Measure.pi_pi]
  congr 1
  funext v
  unfold
    heightOnePadicInvariantDifferentialGroupMeasure
    heightOnePadicSpecialOrthogonalIntegralMeasure
  exact
    (((V.isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup v.1)
      |>.isOpenEmbedding_subtypeVal.measurableEmbedding).comap_apply
        (V.padicInvariantDifferentialGroupMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1)
        (s v)).symm

/-! ## Exact nested source-product comparison -/

/-- The direct source-coordinate inclusion fixes the old exceptional
coordinates and common tail and includes only the new integral coordinates
into the unrestricted local groups. -/
def finiteAdelicSpecialOrthogonalTransitionSourceInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        (V.FiniteAdelicSpecialOrthogonalNewIntegralProduct S T ×
          V.FiniteAdelicSpecialOrthogonalIntegralTail T)) →
      (V.FiniteAdelicSpecialOrthogonalExceptionalProduct S ×
        (V.FiniteAdelicSpecialOrthogonalNewExceptionalProduct S T ×
          V.FiniteAdelicSpecialOrthogonalIntegralTail T)) :=
  Prod.map (fun g => g)
    (Prod.map
      (V.finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusionHom S T)
      (fun g => g))

/-- Exact nested source-product comparison. Comapping the product with
unrestricted new-coordinate Haar factors along the direct transition source
inclusion gives the literal transition volume times the product with
normalized new integral factors. -/
theorem
    finiteAdelicSpecialOrthogonalTransitionSourceProduct_comap_eq_volume_smul
    (V : RationalQuadraticSpaceMatrix n)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ((V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).prod
        ((V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure S T).prod
          (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T))).comap
        (V.finiteAdelicSpecialOrthogonalTransitionSourceInclusion S T) =
      V.finiteAdelicSpecialOrthogonalTransitionVolume S T •
        ((V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S).prod
          ((V.finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure
              S T).prod
            (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T))) := by
  letI (v : {v // v ∈ T \ S}) :
      SigmaFinite
        (V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1) :=
    IsFiniteMeasure.toSigmaFinite _
  letI (v : {v // v ∈ T \ S}) :
      SigmaFinite
        (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : IsProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T) :=
    finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure_isProbability
      V T
  letI : IsZeroOrProbabilityMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T) :=
    IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite
      (V.finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure
        S T) := by
    unfold finiteAdelicSpecialOrthogonalNewNormalizedIntegralProductMeasure
    infer_instance
  letI : SigmaFinite
      ((V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure S T).comap
        (V.finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusionHom
          S T)) := by
    rw [
      V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure_comap_integralInclusion
        S T]
    unfold finiteAdelicSpecialOrthogonalNewIntegralProductMeasure
    infer_instance
  unfold finiteAdelicSpecialOrthogonalTransitionSourceInclusion
  rw [
    Measure.comap_id_prodMap_id
      (V.finiteAdelicSpecialOrthogonalNewIntegralExceptionalInclusion_measurableEmbedding
        S T)
      (V.finiteAdelicSpecialOrthogonalExceptionalProductMeasure S)
      (V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure S T)
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure T),
    V.finiteAdelicSpecialOrthogonalNewExceptionalProductMeasure_comap_integralInclusion
      S T,
    V.finiteAdelicSpecialOrthogonalNewIntegralProductMeasure_eq_transitionVolume_smul
      S T,
    Measure.prod_smul_left,
    Measure.prod_smul_right]

end RationalQuadraticSpaceMatrix
