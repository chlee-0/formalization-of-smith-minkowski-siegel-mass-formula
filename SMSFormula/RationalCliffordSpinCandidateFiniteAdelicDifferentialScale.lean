import SMSFormula.RationalCliffordSpinCandidateDifferentialCoordinateHaar
import SMSFormula.PadicCayleyTranslatedChartOverlapStrictDifferential
import SMSFormula.PadicCayleyLeftTrivializedDeterminantModulus
import SMSFormula.SpecialOrthogonalRealTransitionConjugationDifferential
import SMSFormula.SpecialOrthogonalRealDifferentialInvariance
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicDirectedMeasure

/-!
# Finite-adelic differential scale of the Clifford--Spin candidate

The completed p-adic chart-glued Haar measures have been identified, in
every translated differential chart, with the density obtained by evaluating
the chosen rational Spin top form on its explicit nonlinear frame.  This file
records how those same local measures occur in the coherent finite-adelic
construction.

On every admissible block, mapping the directed global measure back through
genuine local evaluation and the exceptional/tail splitting gives exactly the
finite product of unrestricted exceptional differential measures times the
inverse-integral-volume-normalized probability tail.  Pushing the tail into
the unrestricted local groups makes every good-place restriction and scalar
literal.

The normalization is relative to the fixed empty-block exceptional set.  No
empty-block mass-one statement is made.  Recovering the unnormalized product
of the rational local differential measures still requires convergence of the
infinite product of the good integral volumes; no such convergence or
Tamagawa-volume statement is asserted here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

local instance finiteAdelicSpinDifferentialScaleDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteAdelicSpinDifferentialScalePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicSpinDifferentialScaleGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance finiteAdelicSpinDifferentialScaleGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

local instance finiteAdelicSpinDifferentialScaleGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.HeightOnePadicCliffordSpinCandidateGroup v) := by
  infer_instance

local instance finiteAdelicSpinDifferentialScaleIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicSpinDifferentialScaleIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v) :=
  Subtype.borelSpace _

local instance finiteAdelicSpinDifferentialScaleLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance finiteAdelicSpinDifferentialScaleLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  Subtype.borelSpace _

local instance finiteAdelicSpinDifferentialScaleExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinDifferentialScaleExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  Pi.borelSpace

local instance finiteAdelicSpinDifferentialScaleTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinDifferentialScaleTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  Pi.borelSpace

local instance finiteAdelicSpinDifferentialScaleUnrestrictedTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleUnrestrictedGoodTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinDifferentialScaleUnrestrictedTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleUnrestrictedGoodTail S) :=
  Pi.borelSpace

local instance finiteAdelicSpinDifferentialScaleMixedSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance finiteAdelicSpinDifferentialScaleMixedBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
  Pi.borelSpace

local instance finiteAdelicSpinDifferentialScaleFiniteGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance finiteAdelicSpinDifferentialScaleFiniteGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance finiteAdelicSpinDifferentialScaleGenuineBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) :=
  Subtype.borelSpace _

/-! ## The placewise differential scale used by the products -/

/-- The coherent scalar is the product of reciprocal integral differential
volumes precisely at the user-supplied places outside the fixed coordinate
bad set.  In particular, the fixed empty-block exceptional places are not
silently normalized away. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_eq_prod_sdiff_badPlaces
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S =
      ∏ v ∈ S \ V.cliffordSpinCandidateAdmissibleBadPlaces,
        (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹ := by
  classical
  unfold finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight
  change
    (∏ v ∈
        V.cliffordSpinCandidateAdmissibleExceptionalPlaces S \
          V.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅,
      (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) = _
  congr 1
  ext v
  simp only [cliffordSpinCandidateAdmissibleExceptionalPlaces,
    Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hSB, hnotUnion⟩
    have hnotB : v ∉ V.cliffordSpinCandidateAdmissibleBadPlaces :=
      fun hv => hnotUnion (Or.inr hv)
    exact ⟨hSB.resolve_right hnotB, hnotB⟩
  · rintro ⟨hS, hnotB⟩
    refine ⟨Or.inl hS, ?_⟩
    rintro (hEmpty | hBad)
    · simp at hEmpty
    · exact hnotB hBad

/-! ## Explicit source and unrestricted-tail formulas -/

/-- Simultaneously include every normalized integral-tail coordinate into its
unrestricted local Spin group, leaving the exceptional coordinates fixed. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailAmbientInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) →
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleUnrestrictedGoodTail S) :=
  Prod.map id
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailInclusion S)

/-- The source product maps to the unrestricted local products with every
good-place inverse integral volume and ambient differential restriction
visible literally. -/
theorem
    map_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_ambientInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailAmbientInclusion
          S)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
          S) =
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
        S).prod
        (Measure.infinitePi fun
            v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
          (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume
            v.1)⁻¹ •
            (V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure
              v.1).restrict
                {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 g}) := by
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
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailAmbientInclusion
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
  rw [← Measure.map_prod_map _ _ measurable_id
      (V.continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailInclusion
        S).measurable,
    Measure.map_id,
    V.map_finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
      S]
  rfl

/-! ## Coherent block recovery -/

/-- Mapping a coherent mixed block back to its direct source retains the
baseline-relative inverse-volume weight, the unnormalized exceptional
differential product, and the normalized integral tail exactly. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure_map_symm
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
          S).symm
        (V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure
          S) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
        ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
          S).prod
          (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
            S)) := by
  rw [finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure,
    Measure.map_smul,
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockCylinderMeasure_map_symm]
  rfl

/-- The comap of the directed global finite-adelic measure to any genuine
block, followed by genuine local evaluation and exceptional/tail splitting,
is the literal baseline-weighted differential source product. -/
theorem finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_block_source
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
          S).symm
        (Measure.map
          (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph
            S)
          (V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure.comap
            (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
              S))) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
        ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
          S).prod
          (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
            S)) := by
  rw [V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_comap_genuineBlock S]
  rw [V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockMeasure_map
    S]
  exact
    V.finiteAdelicCliffordSpinCandidateAdmissibleCoherentMixedPrincipalBlockCylinderMeasure_map_symm
      S

/-- After the same block recovery, simultaneous inclusion of the normalized
tail into the unrestricted good local groups exposes the finite exceptional
differential product and every inverse-volume-scaled ambient integral
restriction exactly. -/
theorem
    finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_block_ambientDifferentialSource
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailAmbientInclusion
          S)
        (Measure.map
          (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
            S).symm
          (Measure.map
            (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph
              S)
            (V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure.comap
              (V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockInclusionHom
                S)))) =
      V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
        ((V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
          S).prod
          (Measure.infinitePi fun
              v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
            (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume
              v.1)⁻¹ •
              (V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure
                v.1).restrict
                  {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral
                    v.1 g})) := by
  rw [V.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure_block_source S,
    Measure.map_smul]
  rw [show
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure
          S).prod
          (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
            S) =
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
          S by rfl,
    V.map_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure_ambientInclusion
      S]

end RationalQuadraticSpaceMatrix
