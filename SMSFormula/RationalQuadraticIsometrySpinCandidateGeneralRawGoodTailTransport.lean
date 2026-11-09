import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralIntegralSupport
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicHaar

/-!
# Canonical raw good Spin tails under an arbitrary rational isometry

The native normalized Spin tails are indexed by proof-carrying complements of
`S ∪ bad(V)`.  Comparing those two dependent index types directly across two
quadratic matrices makes Lean unfold both coordinate presentations at once.
This file instead inserts the canonical raw index `{v // v ∉ S}`.

Each native tail is first reindexed, for its own matrix only, to the raw
index.  The arbitrary-isometry equivalence is then applied fiberwise over the
literal same raw prime.  This separates reindexing from cross-matrix transport
and proves exact preservation of the normalized infinite-product probability.
No exceptional factor, finite carrier, quotient measure, or Tamagawa value is
introduced here.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 500000

variable {m : ℕ}
variable (W Z : RationalQuadraticSpaceMatrix (m + 1))
variable (e : W.quadraticForm.IsometryEquiv Z.quadraticForm)

/-- The canonical proof-carrying set of literal height-one places outside
`S`, independent of a quadratic-space coordinate presentation. -/
abbrev SpinCandidateRawGoodPlace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  {v : IsDedekindDomain.HeightOneSpectrum ℤ // v ∉ S}

/-- The principal integral Spin factor at a canonical raw good place. -/
abbrev SpinCandidateRawGoodLocalFactor
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : SpinCandidateRawGoodPlace S) :=
  V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor S v.1

/-- The canonical raw good-prime product for one rational quadratic matrix. -/
abbrev SpinCandidateRawGoodTail
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : SpinCandidateRawGoodPlace S) → V.SpinCandidateRawGoodLocalFactor S v

local instance rawGoodLocalFactorBorelSpace
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : SpinCandidateRawGoodPlace S) :
    BorelSpace (V.SpinCandidateRawGoodLocalFactor S v) :=
  Subtype.borelSpace _

local instance rawGoodLocalFactorSecondCountable
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : SpinCandidateRawGoodPlace S) :
    SecondCountableTopology (V.SpinCandidateRawGoodLocalFactor S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance rawGoodTailBorelSpace
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.SpinCandidateRawGoodTail S) :=
  Pi.borelSpace

local instance rawGoodTailSecondCountable
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (V.SpinCandidateRawGoodTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

/-- Outside a support containing the native admissible bad set, a raw good
place is also good for the native normalized tail. -/
theorem spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (v : SpinCandidateRawGoodPlace S) :
    v.1 ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S := by
  simp only [cliffordSpinCandidateAdmissibleExceptionalPlaces,
    Finset.mem_union]
  exact not_or_intro v.2 (fun hv ↦ v.2 (hV hv))

/-- The native proof-carrying good-place index is canonically the raw
complement of `S` once its native bad set is contained in `S`. -/
def cliffordSpinCandidateAdmissibleIntegralPlaceEquivRawGood
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    V.CliffordSpinCandidateAdmissibleIntegralPlace S ≃
      SpinCandidateRawGoodPlace S where
  toFun v := ⟨v.1, fun hv ↦ v.2 (by
    simp only [cliffordSpinCandidateAdmissibleExceptionalPlaces,
      Finset.mem_union]
    exact Or.inl hv)⟩
  invFun v := ⟨v.1,
    spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces V hV v⟩
  left_inv v := Subtype.ext rfl
  right_inv v := Subtype.ext rfl

/-- Reindex one native normalized tail to the canonical raw complement of
`S`.  This equivalence never mentions a second quadratic matrix. -/
def cliffordSpinCandidateAdmissibleIntegralTailRawGoodMeasurableEquiv
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S ≃ᵐ
      V.SpinCandidateRawGoodTail S :=
  let ι := V.cliffordSpinCandidateAdmissibleIntegralPlaceEquivRawGood hV
  (MeasurableEquiv.piCongrLeft
    (fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace S ↦
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v)
    ι.symm).symm

/-- The normalized infinite-product probability on the canonical raw good
tail, using the native normalized local factors with their canonically
derived goodness proofs. -/
def spinCandidateRawGoodNormalizedTailMeasure
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measure (V.SpinCandidateRawGoodTail S) :=
  Measure.infinitePi fun v : SpinCandidateRawGoodPlace S ↦
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S ⟨v.1,
        spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces V hV v⟩

/-- Same-matrix reindexing from the native good tail to the raw good tail
preserves the normalized infinite-product probability. -/
theorem cliffordSpinCandidateAdmissibleIntegralTailRawGood_measurePreserving
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    MeasurePreserving
      (V.cliffordSpinCandidateAdmissibleIntegralTailRawGoodMeasurableEquiv hV)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure S)
      (V.spinCandidateRawGoodNormalizedTailMeasure hV) := by
  let ι := V.cliffordSpinCandidateAdmissibleIntegralPlaceEquivRawGood hV
  let μ := fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace S ↦
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S v
  let reindex :=
    (MeasurableEquiv.piCongrLeft
      (fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace S ↦
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v)
      ι.symm).symm
  letI (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
      IsProbabilityMeasure (μ v) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      S v
  have hBack : MeasurePreserving reindex.symm
      (Measure.infinitePi fun w : SpinCandidateRawGoodPlace S ↦ μ (ι.symm w))
      (Measure.infinitePi μ) := by
    refine ⟨reindex.symm.measurable, ?_⟩
    exact Measure.infinitePi_map_piCongrLeft (μ := μ) ι.symm
  have hForward : MeasurePreserving reindex
      (Measure.infinitePi μ)
      (Measure.infinitePi fun w : SpinCandidateRawGoodPlace S ↦ μ (ι.symm w)) :=
    MeasurePreserving.symm reindex.symm hBack
  simpa only [
    cliffordSpinCandidateAdmissibleIntegralTailRawGoodMeasurableEquiv,
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure,
    spinCandidateRawGoodNormalizedTailMeasure, ι, μ, reindex] using hForward

/-- Fiberwise arbitrary-isometry transport over the literal raw good-prime
index.  There is no index reindexing in this map. -/
def rationalIsometrySpinCandidateRawGoodTailMeasurableEquiv
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    W.SpinCandidateRawGoodTail S ≃ᵐ Z.SpinCandidateRawGoodTail S :=
  MeasurableEquiv.piCongrRight fun v : SpinCandidateRawGoodPlace S ↦
    (rationalIsometrySpinCandidateIntegralPrincipalLocalContinuousMulEquiv
      W Z e hS v.1 v.2
        (spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces W hW v)
        (spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces Z hZ v))
      |>.toMeasurableEquiv

/-- The fiberwise arbitrary-isometry equivalence preserves the canonical raw
good infinite-product probability. -/
theorem rationalIsometrySpinCandidateRawGoodTail_measurePreserving
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    MeasurePreserving
      (rationalIsometrySpinCandidateRawGoodTailMeasurableEquiv W Z e hS hW hZ)
      (W.spinCandidateRawGoodNormalizedTailMeasure hW)
      (Z.spinCandidateRawGoodNormalizedTailMeasure hZ) := by
  let μ := fun v : SpinCandidateRawGoodPlace S ↦
    W.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S ⟨v.1,
        spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces W hW v⟩
  let ν := fun v : SpinCandidateRawGoodPlace S ↦
    Z.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S ⟨v.1,
        spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces Z hZ v⟩
  let fiber := rationalIsometrySpinCandidateRawGoodTailMeasurableEquiv
    W Z e hS hW hZ
  letI (v : SpinCandidateRawGoodPlace S) : IsProbabilityMeasure (μ v) :=
    W.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      S ⟨v.1,
        spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces W hW v⟩
  letI (v : SpinCandidateRawGoodPlace S) : IsProbabilityMeasure (ν v) :=
    Z.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      S ⟨v.1,
        spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces Z hZ v⟩
  refine ⟨fiber.measurable, ?_⟩
  change Measure.map
      (fun g v ↦
        rationalIsometrySpinCandidateIntegralPrincipalLocalContinuousMulEquiv
          W Z e hS v.1 v.2
            (spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces W hW v)
            (spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces Z hZ v)
          (g v))
      (Measure.infinitePi μ) = Measure.infinitePi ν
  rw [Measure.infinitePi_map_pi
    (μ := μ)
    (f := fun v g ↦
      rationalIsometrySpinCandidateIntegralPrincipalLocalContinuousMulEquiv
        W Z e hS v.1 v.2
          (spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces W hW v)
          (spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces Z hZ v) g)
    (fun v ↦
      (rationalIsometrySpinCandidateIntegralPrincipalLocalContinuousMulEquiv
        W Z e hS v.1 v.2
          (spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces W hW v)
          (spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces Z hZ v)).measurable)]
  congr 1
  funext v
  exact (rationalIsometrySpinCandidateIntegralPrincipalLocal_measurePreserving
    W Z e hS v.1 v.2
      (spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces W hW v)
      (spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces Z hZ v)).map_eq

/-- The complete native normalized tails are compared by the canonical raw
middle product, avoiding a direct cross-matrix dependent-index equivalence. -/
def rationalIsometrySpinCandidateIntegralTailViaRawGoodMeasurableEquiv
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    W.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S ≃ᵐ
      Z.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S :=
  (W.cliffordSpinCandidateAdmissibleIntegralTailRawGoodMeasurableEquiv hW).trans
    ((rationalIsometrySpinCandidateRawGoodTailMeasurableEquiv
      W Z e hS hW hZ).trans
      (Z.cliffordSpinCandidateAdmissibleIntegralTailRawGoodMeasurableEquiv hZ).symm)

end RationalQuadraticSpaceMatrix
