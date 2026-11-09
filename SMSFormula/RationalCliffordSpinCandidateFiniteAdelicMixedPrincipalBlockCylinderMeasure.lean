import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicIntegralTailMeasure
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Cylinder measures on admissible Clifford--Spin mixed blocks

For a finite set `S`, the admissible mixed local carrier uses the unrestricted
p-adic Clifford--Spin candidate group at the normalized exceptional places and
the integral local subgroup elsewhere.  The preceding layer continuously
split this carrier into the finite exceptional product and the normalized
integral tail.

This file puts the unnormalized chart-glued p-adic Spin Haar measure on each
exceptional factor, takes their finite dependent product, and multiplies it by
the normalized integral-tail probability measure.  Mapping that source product
through the exceptional/tail homeomorphism defines a measure on the mixed
block.  Its total mass is the literal product of exceptional local total
masses and it is left invariant.

No measure is transported to the genuine finite-adelic block, no compatibility
between exceptional sets is proved, and no analytic identification with the
rational Spin top form or comparison with the full-adelic reference Haar scale
is asserted.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance finiteAdelicSpinMixedCylinderPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicSpinMixedCylinderGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance finiteAdelicSpinMixedCylinderGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

local instance finiteAdelicSpinMixedCylinderGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicCliffordSpinCandidateGroup v) := by
  infer_instance

local instance finiteAdelicSpinMixedCylinderIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicSpinMixedCylinderIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  Subtype.borelSpace _

local instance finiteAdelicSpinMixedCylinderLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicSpinMixedCylinderLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  Subtype.borelSpace _

local instance finiteAdelicSpinMixedCylinderExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinMixedCylinderExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  Pi.borelSpace

local instance finiteAdelicSpinMixedCylinderTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinMixedCylinderTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  Pi.borelSpace

local instance finiteAdelicSpinMixedCylinderMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinMixedCylinderMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  Pi.borelSpace

/-! ## Exceptional local and finite-product measures -/

/-- The chart-glued p-adic Spin Haar measure on the exact height-one local
carrier used by an exceptional factor. -/
def heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  V.padicCliffordSpinCandidateChartGluedMeasure
    (Rat.HeightOneSpectrum.primesEquiv v).1

/-- The height-one chart-glued local Spin measure is Haar. -/
theorem heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsHaarMeasure
      (V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v) :=
  V.padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure
    (Rat.HeightOneSpectrum.primesEquiv v).1

/-- Every exceptional chart-glued local Spin Haar measure is sigma-finite. -/
instance
    heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SigmaFinite
      (V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v) := by
  letI : Measure.IsHaarMeasure
      (V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v) :=
    V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure_isHaarMeasure v
  infer_instance

/-- Every exceptional chart-glued local Spin Haar measure is left invariant. -/
instance
    heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsMulLeftInvariant
      (V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v) :=
  (V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure_isHaarMeasure v)
    |>.toIsMulLeftInvariant

/-- The finite dependent product of unnormalized chart-glued p-adic Spin Haar
measures at the normalized exceptional places. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  Measure.pi fun
      v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} =>
    V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1

/-- The exceptional finite product has its literal rectangle formula. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_pi
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : forall
      v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S},
      Set (V.HeightOnePadicCliffordSpinCandidateGroup v.1)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S
        (Set.pi Set.univ s) =
      ∏ v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S},
        V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1
          (s v) := by
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
  exact Measure.pi_pi _ s

/-- The exceptional finite product has the literal product of local total
masses. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_univ
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S
        Set.univ =
      ∏ v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S},
        V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1
          Set.univ := by
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
  exact Measure.pi_univ _

/-- The finite exceptional product is sigma-finite. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
        S) := by
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
  infer_instance

/-- The finite exceptional product is invariant under componentwise left
multiplication. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
        S) := by
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
  exact Measure.pi.isMulLeftInvariant _

/-! ## Source product and mixed-block cylinder -/

/-- The cylinder source measure: unnormalized exceptional Haar product times
the normalized integral-tail probability measure. -/
def
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
    S).prod
    (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
      S)

/-- The exceptional/tail source product is left invariant. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
        S) := by
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
  letI : IsZeroOrProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) :=
    IsFiniteMeasure.toSigmaFinite _
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
  exact Measure.prod.instIsMulLeftInvariant

/-- Map the direct exceptional/tail source product through the splitting
homeomorphism to obtain the mixed-block cylinder measure. -/
def finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  Measure.map
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
      S)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
      S)

/-- Mapping the mixed-block cylinder back through the split recovers the
literal exceptional/tail source product. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure_map_symm
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
          S).symm
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
          S) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
        S := by
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
  exact MeasurableEquiv.map_symm_map
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
      S |>.toMeasurableEquiv)

/-- The mixed-block cylinder has the literal product of exceptional local
total masses; the normalized tail contributes one. -/
@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure_univ
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
        S Set.univ =
      ∏ v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S},
        V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1
          Set.univ := by
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
  letI : IsZeroOrProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) :=
    IsFiniteMeasure.toSigmaFinite _
  rw [
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure,
    Measure.map_apply
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
        S |>.continuous.measurable)
      MeasurableSet.univ]
  change
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
        S Set.univ = _
  rw [
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure,
    ← Set.univ_prod_univ,
    Measure.prod_prod,
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_univ,
    measure_univ,
    mul_one]

/-- The direct mixed-block cylinder measure is left invariant. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
        S) := by
  letI : Measure.IsMulLeftInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
        S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_isMulLeftInvariant
      S
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
  exact isMulLeftInvariant_map
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
      S |>.toMulHom)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
      S |>.continuous.measurable)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
      S |>.surjective)

end RationalQuadraticSpaceMatrix
