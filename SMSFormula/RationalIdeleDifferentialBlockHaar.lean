import SMSFormula.RationalIdeleDifferentialFiniteIdeleHaar
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Haar measures on differential finite-idele principal blocks

The literal exceptional Haar product and normalized compact tail are Haar.
Transport through the multiplicative fixed-block homeomorphism therefore makes
every coherent genuine finite-idele block measure Haar at its exact local
normalization.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Topology

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2400000

local instance rationalIdeleBlockHaarDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance rationalIdeleBlockHaarPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance rationalIdeleBlockHaarLocalMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance rationalIdeleBlockHaarLocalBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

local instance rationalIdeleBlockHaarLocalSecondCountable
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

local instance rationalIdeleBlockHaarIntegralSecondCountable
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance rationalIdeleBlockHaarIntegralBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  Subtype.borelSpace _

local instance rationalIdeleBlockHaarExceptionalBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialExceptionalProduct S) :=
  Pi.borelSpace

local instance rationalIdeleBlockHaarTailBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialIntegralTail S) :=
  Pi.borelSpace

local instance rationalIdeleBlockHaarAmbientMeasurableSpace :
    MeasurableSpace RationalFiniteAdeleˣ :=
  borel _

local instance rationalIdeleBlockHaarAmbientBorelSpace :
    BorelSpace RationalFiniteAdeleˣ :=
  ⟨rfl⟩

local instance rationalIdeleBlockHaarBlockBorelSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (RationalIdeleDifferentialGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-- The genuine transported block law is a topological group law. -/
noncomputable instance rationalIdeleDifferentialGenuinePrincipalBlockIsTopologicalGroup
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsTopologicalGroup (RationalIdeleDifferentialGenuinePrincipalBlock S) where
  continuous_mul := continuous_mul
  continuous_inv := by
    let e :=
      rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockContinuousMulEquiv S
    change Continuous (fun x ↦ e ((e.symm x)⁻¹))
    exact e.continuous.comp (continuous_inv.comp e.symm.continuous)

/-- The finite exceptional product of the local differential Haar measures is a
Haar measure. -/
theorem rationalIdeleDifferentialExceptionalProductMeasure_isHaarMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (rationalIdeleDifferentialExceptionalProductMeasure S) := by
  letI (v : {v // v ∈ S}) :
      Measure.IsHaarMeasure
        (rationalPadicIdeleDifferentialHaarMeasure v.1) :=
    rationalPadicIdeleDifferentialHaarMeasure_isHaarMeasure v.1
  unfold rationalIdeleDifferentialExceptionalProductMeasure
  exact Measure.pi.isHaarMeasure _

/-- The normalized integral tail is Haar on its compact product group. -/
theorem rationalIdeleDifferentialNormalizedIntegralTailMeasure_isHaarMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) := by
  letI (v : {v // v ∉ S}) : CompactSpace
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
    isCompact_iff_compactSpace.mp
      (isCompact_padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)
  letI : CompactSpace (RationalIdeleDifferentialIntegralTail S) := by
    infer_instance
  letI : Measure.IsMulLeftInvariant
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) :=
    rationalIdeleDifferentialNormalizedIntegralTailMeasure_isMulLeftInvariant S
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior
    (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) Set.univ
  · exact isCompact_univ
  · rw [interior_univ]
    exact Set.univ_nonempty
  · simp
  · simp

/-- The unrestricted exceptional product times normalized compact tail is
Haar at the literal local scales. -/
theorem rationalIdeleDifferentialExceptionalTailSourceMeasure_isHaarMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (rationalIdeleDifferentialExceptionalTailSourceMeasure S) := by
  letI : Measure.IsHaarMeasure
      (rationalIdeleDifferentialExceptionalProductMeasure S) :=
    rationalIdeleDifferentialExceptionalProductMeasure_isHaarMeasure S
  letI : Measure.IsHaarMeasure
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) :=
    rationalIdeleDifferentialNormalizedIntegralTailMeasure_isHaarMeasure S
  letI : SigmaFinite
      (rationalIdeleDifferentialExceptionalProductMeasure S) :=
    rationalIdeleDifferentialExceptionalProductMeasure_isSigmaFinite S
  letI : SFinite
      (rationalIdeleDifferentialExceptionalProductMeasure S) := by
    infer_instance
  letI : IsProbabilityMeasure
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) :=
    rationalIdeleDifferentialNormalizedIntegralTailMeasure_isProbability S
  letI : IsFiniteMeasure
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) := by
    infer_instance
  letI : SFinite
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) := by
    infer_instance
  unfold rationalIdeleDifferentialExceptionalTailSourceMeasure
  exact Measure.prod.instIsHaarMeasure
    (rationalIdeleDifferentialExceptionalProductMeasure S)
    (rationalIdeleDifferentialNormalizedIntegralTailMeasure S)

/-- Every coherent genuine differential finite-idele block measure is Haar. -/
theorem rationalIdeleDifferentialGenuinePrincipalBlockMeasure_isHaarMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsHaarMeasure
      (rationalIdeleDifferentialGenuinePrincipalBlockMeasure S) := by
  letI : Measure.IsHaarMeasure
      (rationalIdeleDifferentialExceptionalTailSourceMeasure S) :=
    rationalIdeleDifferentialExceptionalTailSourceMeasure_isHaarMeasure S
  unfold rationalIdeleDifferentialGenuinePrincipalBlockMeasure
  exact
    (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockContinuousMulEquiv
      S).toMulEquiv.isHaarMeasure_map
        (rationalIdeleDifferentialExceptionalTailSourceMeasure S)
        (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockContinuousMulEquiv
          S).continuous
        (rationalIdeleDifferentialExceptionalTailGenuinePrincipalBlockContinuousMulEquiv
          S).symm.continuous

end RationalQuadraticSpaceMatrix
