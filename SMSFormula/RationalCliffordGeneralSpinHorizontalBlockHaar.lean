import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteAdelicHaar
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Horizontal Haar measures on general Spin principal blocks

The coherent finite-adelic cylinders are Haar on every genuine open block at
their literal normalized local-factor scale.

No ambient directed measure, real factor, Haar-uniqueness scalar, quotient
disintegration, vertical comparison, or Tamagawa-volume identity is asserted
here.
-/

noncomputable section

open MeasureTheory
open Topology
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2400000

local instance horizontalAdelicHaarDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalAdelicHaarPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalAdelicHaarLocalMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance horizontalAdelicHaarLocalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

local instance horizontalAdelicHaarExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalAdelicHaarExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance horizontalAdelicHaarIntegralFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalAdelicHaarIntegralFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance horizontalAdelicHaarTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalAdelicHaarTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance horizontalAdelicHaarFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalAdelicHaarFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalAdelicHaarGenuineBlockBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-- The restricted-family block group law transported from its exact
exceptional/tail product is a topological group law, including inversion. -/
noncomputable instance
    cliffordGeneralSpinHorizontalRestrictedPrincipalBlockIsTopologicalGroup
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsTopologicalGroup
      (V.CliffordGeneralSpinHorizontalRestrictedPrincipalBlock S) where
  continuous_mul := continuous_mul
  continuous_inv := by
    let e :=
      V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockContinuousMulEquiv
        S
    change Continuous (fun x ↦ e ((e.symm x)⁻¹))
    exact e.continuous.comp (continuous_inv.comp e.symm.continuous)

/-- The genuine block group law transported from the restricted-family block
is a topological group law. -/
noncomputable instance
    cliffordGeneralSpinHorizontalGenuinePrincipalBlockIsTopologicalGroup
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsTopologicalGroup
      (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) where
  continuous_mul := continuous_mul
  continuous_inv := by
    let e :=
      V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockContinuousMulEquiv S
    change Continuous (fun x ↦ e.symm ((e x)⁻¹))
    exact e.symm.continuous.comp (continuous_inv.comp e.continuous)

/-! ## Haar measures on every explicit block -/

/-- The finite exceptional product retains the literal fixed local horizontal
Haar scales and is Haar for componentwise multiplication. -/
theorem cliffordGeneralSpinHorizontalExceptionalProductMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := by
  letI (v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
      Measure.IsHaarMeasure
        (V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1) :=
    V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure_isHaarMeasure v.1
  unfold cliffordGeneralSpinHorizontalExceptionalProductMeasure
  exact Measure.pi.isHaarMeasure _

/-- The normalized good-place tail is Haar on its compact product group. -/
theorem cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) := by
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      CompactSpace
        (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
    isCompact_iff_compactSpace.mp
      (V.isCompact_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
  letI : CompactSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) := by
    infer_instance
  letI : Measure.IsMulLeftInvariant
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isMulLeftInvariant S
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior
    (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) Set.univ
  · exact isCompact_univ
  · rw [interior_univ]
    exact Set.univ_nonempty
  · simp
  · simp

/-- The unnormalized exceptional product times the normalized compact tail is
Haar at the literal horizontal local scales. -/
theorem cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S) := by
  letI : Measure.IsHaarMeasure
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) :=
    V.cliffordGeneralSpinHorizontalExceptionalProductMeasure_isHaarMeasure S
  letI : Measure.IsHaarMeasure
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isHaarMeasure S
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) :=
    V.cliffordGeneralSpinHorizontalExceptionalProductMeasure_isSigmaFinite S
  letI : SFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := by
    infer_instance
  letI : IsProbabilityMeasure
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isProbability S
  letI : IsFiniteMeasure
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) := by
    infer_instance
  letI : SFinite
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) := by
    infer_instance
  unfold cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure
  exact Measure.prod.instIsHaarMeasure
    (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S)
    (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)

/-- The first transported restricted-family block measure is Haar. -/
theorem cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure S) := by
  letI : Measure.IsHaarMeasure
      (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S) :=
    V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_isHaarMeasure S
  unfold cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure
  exact
    (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockContinuousMulEquiv
      S).toMulEquiv.isHaarMeasure_map
        (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S)
        (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockContinuousMulEquiv
          S).continuous
        (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockContinuousMulEquiv
          S).symm.continuous

/-- The globally weighted restricted-family block measure is Haar; the weight
is a literal positive finite product. -/
theorem
    cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S) := by
  letI : Measure.IsHaarMeasure
      (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure S) :=
    V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure_isHaarMeasure S
  unfold cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure
  exact Measure.IsHaarMeasure.smul _
    (V.cliffordGeneralSpinHorizontalRestrictedBlockWeight_ne_zero S)
    (V.cliffordGeneralSpinHorizontalRestrictedBlockWeight_ne_top S)

/-- Every coherent genuine intrinsic finite-adelic block measure is Haar. -/
theorem
    cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S) := by
  letI : Measure.IsHaarMeasure
      (V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S) :=
    V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure_isHaarMeasure S
  unfold cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure
  exact
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockContinuousMulEquiv
      S).symm.toMulEquiv.isHaarMeasure_map
        (V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S)
        (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockContinuousMulEquiv
          S).symm.continuous
        (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockContinuousMulEquiv
          S).continuous

end RationalQuadraticSpaceMatrix
