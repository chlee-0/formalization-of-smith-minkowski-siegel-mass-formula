import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicAdmissiblePrincipalBlockTopology
import SMSFormula.RationalCliffordSpinCandidateIntegralLocalFactorNormalization
import Mathlib.Probability.ProductMeasure

/-!
# Exceptional and integral-tail splitting for Clifford--Spin blocks

For a finite set `S`, the admissible Clifford--Spin block uses the normalized
exceptional set obtained by adjoining all fixed multiplication and
identity-coordinate bad places.  Its mixed local carrier therefore has the
full p-adic candidate group at the normalized exceptional places and the
literal integral subgroup elsewhere.

This file splits that mixed carrier into its finite exceptional product and
its good integral tail.  The split is a continuous multiplicative
equivalence.  The tail carries the infinite product of the normalized local
probability measures constructed from the chart-glued p-adic Spin Haar
measures.  Its total mass, finite-coordinate marginals, componentwise left
invariance, and pushforward to the unrestricted good-place product are
literal.

No measure is put on the exceptional product, no mixed-block cylinder measure
is constructed, and no comparison with the full-adelic reference Haar scale
or the rational Spin top form is asserted.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance finiteAdelicSpinIntegralTailDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteAdelicSpinIntegralTailPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicSpinIntegralTailGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance finiteAdelicSpinIntegralTailGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

/-! ## Exceptional and tail carriers -/

/-- The finite product of unrestricted local candidate groups at the
normalized exceptional places. -/
abbrev FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S}) →
    V.HeightOnePadicCliffordSpinCandidateGroup v.1

/-- The dependent product of integral local candidate factors away from the
normalized exceptional set. -/
abbrev FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) →
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v

/-- The unrestricted good-place product containing the integral tail. -/
abbrev FiniteAdelicCliffordSpinCandidateAdmissibleUnrestrictedGoodTail
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) →
    V.HeightOnePadicCliffordSpinCandidateGroup v.1

/-- Assemble exceptional and integral-tail components into the admissible
mixed local carrier. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) →
      V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S :=
  fun g v =>
    if hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S then
      ⟨g.1 ⟨v, hv⟩, fun hnv => (hnv hv).elim⟩
    else
      g.2 ⟨v, hv⟩

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_mem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
      S g v).1 = g.1 ⟨v, hv⟩ := by
  simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed, hv]

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_notMem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
      S g v).1 = (g.2 ⟨v, hv⟩).1 := by
  simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed, hv]

/-- Exceptional/tail assembly is multiplicative. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixedHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) →*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S where
  toFun :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed S
  map_one' := by
    funext v
    apply Subtype.ext
    by_cases hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S
    · simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed,
        hv]
    · simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed,
        hv]
  map_mul' := by
    intro g h
    funext v
    apply Subtype.ext
    by_cases hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S
    · simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed,
        hv]
    · simp [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed,
        hv]

/-- Extract the exceptional and integral-tail components of a mixed local
family. -/
def finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S →
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  fun g =>
    (fun v => (g v.1).1,
      fun v => g v.1)

/-- Exceptional/tail extraction is multiplicative. -/
def finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTailHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S →*
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) where
  toFun :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail S
  map_one' := by
    apply Prod.ext
    · funext v
      rfl
    · funext v
      apply Subtype.ext
      rfl
  map_mul' := by
    intro g h
    apply Prod.ext
    · funext v
      rfl
    · funext v
      apply Subtype.ext
      rfl

/-- The admissible mixed local product is algebraically the product of its
finite exceptional part and its good integral tail. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) ≃*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S where
  toFun :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixedHom S
  invFun :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTailHom S
  left_inv := by
    intro g
    apply Prod.ext
    · funext v
      change
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
          S g v.1).1 = g.1 v
      exact
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_mem
          S g v.1 v.2
    · funext v
      apply Subtype.ext
      change
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
          S g v.1).1 = (g.2 v).1
      simpa using
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_notMem
          S g v.1 v.2
  right_inv := by
    intro g
    funext v
    apply Subtype.ext
    by_cases hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S
    · change
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
          S
          (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail
            S g) v).1 = (g v).1
      simpa [finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail]
        using
          V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_mem
            S
            (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail
              S g) v hv
    · change
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
          S
          (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail
            S g) v).1 = (g v).1
      simpa [finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail]
        using
          V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_notMem
            S
            (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail
              S g) v hv
  map_mul' :=
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixedHom
      S).map_mul

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv_apply_mem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv
      S g v).1 = g.1 ⟨v, hv⟩ :=
  V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_mem
    S g v hv

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv_apply_notMem
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
      V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv
      S g v).1 = (g.2 ⟨v, hv⟩).1 :=
  V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_notMem
    S g v hv

/-! ## Product topology -/

private def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalCoordinate
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) →
      V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v :=
  fun g => ⟨g.1 ⟨v, hv⟩, fun hnv => (hnv hv).elim⟩

private theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalCoordinate
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    Continuous
      (finiteAdelicCliffordSpinCandidateAdmissibleExceptionalCoordinate
        V S v hv) := by
  apply
    (continuous_induced_rng
      (f := fun x :
          V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
            S v =>
        (x : V.HeightOnePadicCliffordSpinCandidateGroup v))
      (g :=
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalCoordinate
          V S v hv)).2
  exact
    (continuous_apply
      (⟨v, hv⟩ :
        {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S})).comp
      continuous_fst

private def finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailCoordinate
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) →
      V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v :=
  fun g => g.2 ⟨v, hv⟩

private theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailCoordinate
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    Continuous
      (finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailCoordinate
        V S v hv) := by
  apply
    (continuous_induced_rng
      (f := fun x :
          V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
            S v =>
        (x : V.HeightOnePadicCliffordSpinCandidateGroup v))
      (g :=
        finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailCoordinate
          V S v hv)).2
  have htail : Continuous (fun
      g : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S =>
      g.2 (⟨v, hv⟩ : V.CliffordSpinCandidateAdmissibleIntegralPlace S)) :=
    (continuous_apply
      (⟨v, hv⟩ : V.CliffordSpinCandidateAdmissibleIntegralPlace S)).comp
      continuous_snd
  exact continuous_subtype_val.comp htail

private theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed S) := by
  apply continuous_pi
  intro v
  by_cases hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S
  · have hfun :
        (fun g =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
            S g v) =
          finiteAdelicCliffordSpinCandidateAdmissibleExceptionalCoordinate
            V S v hv := by
      funext g
      apply Subtype.ext
      exact
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_mem
          S g v hv
    rw [hfun]
    exact
      continuous_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalCoordinate
        V S v hv
  · have hfun :
        (fun g =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
            S g v) =
          finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailCoordinate
            V S v hv := by
      funext g
      apply Subtype.ext
      exact
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed_apply_notMem
          S g v hv
    rw [hfun]
    exact
      continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailCoordinate
        V S v hv

private theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail S) := by
  exact Continuous.prodMk
    (continuous_pi fun v =>
      continuous_subtype_val.comp (continuous_apply v.1))
    (continuous_pi fun v => by
      exact continuous_apply v.1)

/-- The exceptional/tail splitting is a homeomorphism for the displayed
product topologies. -/
def finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) ≃ₜ
      V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S where
  toEquiv :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedMulEquiv S
  continuous_toFun :=
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
      V S
  continuous_invFun :=
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleMixedToExceptionalTail
      V S

/-- The admissible exceptional/tail split is continuously multiplicative. -/
def
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedContinuousMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) ≃ₜ*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S :=
  ContinuousMulEquiv.mk'
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailMixedHomeomorph
      S)
    (by
      intro g h
      change
        V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
            S (g * h) =
          V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
              S g *
            V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixed
              S h
      simpa only [
        finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixedHom]
        using
          (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToMixedHom
            S).map_mul g h)

/-! ## Normalized integral-tail measure -/

/-- The infinite product of normalized chart-glued Haar probability measures
on the good integral factors. -/
def finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) :=
  Measure.infinitePi fun
      v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S v

/-- The normalized good integral tail has total mass one. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isProbability
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsProbabilityMeasure
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) := by
  letI (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
      IsProbabilityMeasure
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      S v
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
  infer_instance

/-- Every finite-coordinate marginal is the finite product of the normalized
good local factors. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_map_restrict
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (T : Finset (V.CliffordSpinCandidateAdmissibleIntegralPlace S)) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
      S).map T.restrict =
      Measure.pi fun v : {v // v ∈ T} =>
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v.1 := by
  letI (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
      IsProbabilityMeasure
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      S v
  simpa only [
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure]
    using
      (Measure.infinitePi_map_restrict
        (μ := fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
            S v)
        (I := T))

/-- The normalized good integral tail is invariant under componentwise left
multiplication. -/
instance
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
        S) := by
  letI (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
      IsProbabilityMeasure
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      S v
  letI (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
      Measure.IsMulLeftInvariant
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isMulLeftInvariant
      S v
  refine ⟨fun g => ?_⟩
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
  change
    Measure.map (fun x v => g v * x v)
        (Measure.infinitePi fun
          v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
            S v) =
      Measure.infinitePi fun
        v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
        V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v
  rw [Measure.infinitePi_map_pi
    (μ := fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
      V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S v)
    (f := fun v x => g v * x)
    (fun v => measurable_const_mul (g v))]
  congr 1
  funext v
  exact map_mul_left_eq_self
    (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S v)
    (g v)

/-! ## Inclusion into the unrestricted good-place product -/

/-- Componentwise inclusion of the integral tail into the unrestricted local
candidate groups at all good places. -/
def finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S →*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleUnrestrictedGoodTail S where
  toFun g v := (g v).1
  map_one' := by
    funext v
    rfl
  map_mul' := by
    intro g h
    funext v
    rfl

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailInclusion_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S)
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailInclusion S g v =
      (g v).1 :=
  rfl

theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailInclusion S) :=
  continuous_pi fun v =>
    continuous_subtype_val.comp (continuous_apply v)

/-- Inclusion pushes the normalized tail measure to the product of the
explicitly rescaled ambient integral restrictions. -/
theorem
    map_finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailInclusion S)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
          S) =
      Measure.infinitePi fun
          v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
        (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1)⁻¹ •
          (V.padicCliffordSpinCandidateChartGluedMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1).restrict
              {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 g} := by
  letI (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
      IsProbabilityMeasure
        (V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
          S v) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      S v
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleIntegralTailInclusion
    finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure
  change
    Measure.map (fun x v => (x v).1)
        (Measure.infinitePi fun
          v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
          V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
            S v) =
      Measure.infinitePi fun
          v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
        (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1)⁻¹ •
          (V.padicCliffordSpinCandidateChartGluedMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1).restrict
              {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v.1 g}
  rw [Measure.infinitePi_map_pi
    (μ := fun v : V.CliffordSpinCandidateAdmissibleIntegralPlace S =>
      V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S v)
    (f := fun _ x => (x.1 :
      V.HeightOnePadicCliffordSpinCandidateGroup _))
    (fun _ => continuous_subtype_val.measurable)]
  congr 1
  funext v
  exact
    V.map_finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
      S v

end RationalQuadraticSpaceMatrix
