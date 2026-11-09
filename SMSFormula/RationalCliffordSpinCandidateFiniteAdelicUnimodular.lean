import SMSFormula.MeasureInversionTransport
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicHaar
import SMSFormula.RationalCliffordSpinCandidatePlacewiseUnimodular

/-!
# Finite-adelic unimodularity of the Clifford--Spin differential measure

The placewise glued Spin measures are inversion invariant. This module
propagates that property directly through the normalized integral factors,
infinite tail, exceptional product, mixed and genuine block equivalences,
ambient inclusions, and the directed supremum defining the coherent
finite-adelic Spin measure.

Supported ambient block measures are not asserted to be right invariant under
arbitrary ambient translations.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

local instance finiteAdelicSpinUnimodularPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicSpinUnimodularGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) := borel _

local instance finiteAdelicSpinUnimodularGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) := ⟨rfl⟩

local instance finiteAdelicSpinUnimodularIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicSpinUnimodularIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  Subtype.borelSpace _

local instance finiteAdelicSpinUnimodularExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinUnimodularExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  Pi.borelSpace

local instance finiteAdelicSpinUnimodularTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinUnimodularTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  Pi.borelSpace

local instance finiteAdelicSpinUnimodularLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicSpinUnimodularLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  Subtype.borelSpace _

local instance finiteAdelicSpinUnimodularMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinUnimodularMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance finiteAdelicSpinUnimodularFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup := borel _

local instance finiteAdelicSpinUnimodularFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup := ⟨rfl⟩

local instance finiteAdelicSpinUnimodularGenuineBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
  Subtype.borelSpace _

/-! ## Local factors -/

/-- The height-one chart-glued Spin measure is inversion invariant. -/
instance heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsInvInvariant
      (V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v) := by
  unfold heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure
  exact V.padicCliffordSpinCandidateChartGluedMeasure_isInvInvariant
    (Rat.HeightOneSpectrum.primesEquiv v).1

/-- Comapping to a good integral factor preserves inversion invariance. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure.IsInvInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
        S v) := by
  letI : Measure.IsInvInvariant
      (V.padicCliffordSpinCandidateChartGluedMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
    V.padicCliffordSpinCandidateChartGluedMeasure_isInvInvariant
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  unfold finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
  exact Measure.subgroup_comap_measure_isInvInvariant_of_subtype_mspace
    (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
      S v.1)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasurableSpace_eq
      S v)
    (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
      S v.1 v.2).measurableSet

/-- Normalization preserves good-factor inversion invariance. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure.IsInvInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S v) := by
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
  exact Measure.isInvInvariant_smul _ _

/-! ## Tail and exceptional products -/

/-- The normalized integral tail is inversion invariant. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) := by
  letI (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
      IsProbabilityMeasure
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      S v
  letI (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
      Measure.IsInvInvariant
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isInvInvariant
      S v
  constructor
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
  change
    Measure.map (fun x v ↦ (x v)⁻¹)
        (Measure.infinitePi fun v :
          V.CliffordSpinCandidateAdmissibleIntegralPlace S ↦
          V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
            S v) =
      Measure.infinitePi fun v :
        V.CliffordSpinCandidateAdmissibleIntegralPlace S ↦
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v
  rw [Measure.infinitePi_map_pi
    (μ := fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace S ↦
      V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S v)
    (f := fun _ x ↦ x⁻¹)
    (fun _ ↦ measurable_inv)]
  congr 1
  funext v
  exact Measure.map_inv_eq_self
    (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S v)

/-- The exceptional finite product is inversion invariant. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
        S) := by
  unfold finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
  exact Measure.pi.isInvInvariant _

/-- The exceptional/tail source product is inversion invariant. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
        S) := by
  letI : SigmaFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
        S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite
      S
  letI : SFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
        S) := by infer_instance
  letI : IsProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability
      S
  letI : IsFiniteMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) := by infer_instance
  letI : SFinite
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) := by infer_instance
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
  exact Measure.isInvInvariant_prod _ _

/-! ## Mixed, genuine, and ambient blocks -/

/-- The mixed admissible cylinder is inversion invariant. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
        S) := by
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure
  exact Measure.isInvInvariant_map_of_commutes _ _
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
      S |>.continuous.measurable)
    (fun x ↦
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
        S |>.map_inv x))

/-- Coherent scalar normalization preserves mixed-block inversion
invariance. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
        S) := by
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
  exact Measure.isInvInvariant_smul _ _

/-- The coherent genuine admissible block measure is inversion invariant. -/
instance
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
        S) := by
  unfold
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure
  exact Measure.isInvInvariant_map_of_commutes _ _
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S
      |>.symm.continuous.measurable)
    (fun x ↦
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
        S |>.symm.map_inv x))

/-- Mapping a genuine block into the ambient finite-adelic group preserves
inversion invariance. -/
instance
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        S) := by
  unfold
    finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
  exact Measure.isInvInvariant_map_of_commutes _ _
    (V.continuous_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
      S).measurable
    (fun x ↦
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup
        S |>.subtype.map_inv x))

/-! ## Directed global finite-adelic measure -/

/-- The actual coherent finite-adelic Spin measure is inversion invariant. -/
instance finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsInvInvariant
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  unfold finiteAdelicCliffordSpinCandidateCoherentGroupMeasure
  exact Measure.directedSup_isInvInvariant
    V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
    (fun _ _ hST ↦
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_mono
        hST)
    (fun S ↦
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_isInvInvariant
        S)

/-- Consequently the finite-adelic Spin measure is globally right invariant. -/
theorem finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isMulRightInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulRightInvariant
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  letI : Measure.IsHaarMeasure
      V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_isHaarMeasure
  exact Measure.isMulRightInvariant_of_isInvInvariant
    V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure

end RationalQuadraticSpaceMatrix
