import SMSFormula.RationalCliffordGeneralSpinHorizontalIntegralLocalFactor
import Mathlib.Probability.ProductMeasure

/-!
# Exceptional and normalized-tail horizontal GSpin measures

The fixed placewise horizontal `GSpin` Haar measures determine two pieces after
choosing a finite set `S`.  At the exceptional places
`S ∪ cliffordGeneralSpinHorizontalIntegralBadPlaces` we keep the
unnormalized local Haar measures.  At every remaining place we use the
probability measure on the compact-open integral subgroup constructed in the
preceding file.

This file forms the finite exceptional product and the infinite normalized
good tail.  The tail has exact finite-coordinate marginals, is invariant under
componentwise left translation, and pushes through the componentwise subgroup
inclusion to the product of the explicit reciprocal-volume ambient
restrictions.  Their direct product is the horizontal exceptional/tail source
measure.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance horizontalExceptionalTailDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalExceptionalTailPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalExceptionalTailGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance horizontalExceptionalTailGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

/-! ## Exceptional and good-tail carriers -/

/-- The finite product of unrestricted local `GSpin` groups at the horizontal
exceptional places. -/
abbrev CliffordGeneralSpinHorizontalExceptionalProduct
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces}) →
    V.HeightOnePadicCliffordGeneralSpinGroup v.1

/-- The dependent product of compact-open integral `GSpin` subgroups at all
horizontal good places. -/
abbrev CliffordGeneralSpinHorizontalIntegralTail
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) →
    V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v

/-- The unrestricted product containing the horizontal integral tail. -/
abbrev CliffordGeneralSpinHorizontalUnrestrictedGoodTail
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) →
    V.HeightOnePadicCliffordGeneralSpinGroup v.1

/-! ## Normalized infinite good tail -/

/-- The infinite product of the normalized horizontal integral-factor
probability measures. -/
def cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Measure.infinitePi fun
      v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v

/-- The normalized horizontal good tail has total mass one. -/
instance
    cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isProbability
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsProbabilityMeasure
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) := by
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
          S v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability
      S v
  unfold cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
  infer_instance

/-- Every finite-coordinate marginal is the finite product of the fixed
normalized good local factors. -/
theorem
    cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_map_restrict
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (T : Finset (V.CliffordGeneralSpinHorizontalIntegralPlace S)) :
    (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S).map
        T.restrict =
      Measure.pi fun v : {v // v ∈ T} ↦
        V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
          S v.1 := by
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
          S v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability
      S v
  simpa only [
    cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure] using
      (Measure.infinitePi_map_restrict
        (μ := fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
          V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
            S v)
        (I := T))

/-- The normalized horizontal good tail is invariant under componentwise left
multiplication. -/
instance
    cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) := by
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
          S v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability
      S v
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      Measure.IsMulLeftInvariant
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
          S v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isMulLeftInvariant
      S v
  refine ⟨fun g ↦ ?_⟩
  unfold cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
  change
    Measure.map (fun x v ↦ g v * x v)
        (Measure.infinitePi fun
          v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
          V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
            S v) =
      Measure.infinitePi fun
        v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
        V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
          S v
  rw [Measure.infinitePi_map_pi
    (μ := fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
      V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
        S v)
    (f := fun v x ↦ g v * x)
    (fun v ↦ measurable_const_mul (g v))]
  congr 1
  funext v
  exact map_mul_left_eq_self
    (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v)
    (g v)

/-! ## Inclusion into the unrestricted good-place product -/

/-- Componentwise inclusion of the integral tail into the unrestricted local
`GSpin` groups at all horizontal good places. -/
def cliffordGeneralSpinHorizontalIntegralTailInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalIntegralTail S →*
      V.CliffordGeneralSpinHorizontalUnrestrictedGoodTail S where
  toFun g v := (g v).1
  map_one' := by
    funext v
    rfl
  map_mul' := by
    intro g h
    funext v
    rfl

@[simp]
theorem cliffordGeneralSpinHorizontalIntegralTailInclusion_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S)
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.cliffordGeneralSpinHorizontalIntegralTailInclusion S g v = (g v).1 :=
  rfl

theorem continuous_cliffordGeneralSpinHorizontalIntegralTailInclusion
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (V.cliffordGeneralSpinHorizontalIntegralTailInclusion S) :=
  continuous_pi fun v ↦ continuous_subtype_val.comp (continuous_apply v)

/-- Inclusion pushes the normalized tail to the product of the explicit
reciprocal-volume ambient horizontal Haar restrictions. -/
theorem map_cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalIntegralTailInclusion S)
        (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) =
      Measure.infinitePi fun
          v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
        (V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1)⁻¹ •
          (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1).restrict
              {g | V.PadicCliffordGeneralSpinIsIntegral
                (Rat.HeightOneSpectrum.primesEquiv v.1).1 g} := by
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
          S v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability
      S v
  unfold cliffordGeneralSpinHorizontalIntegralTailInclusion
    cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
  change
    Measure.map (fun x v ↦ (x v).1)
        (Measure.infinitePi fun
          v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
          V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
            S v) =
      Measure.infinitePi fun
          v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
        (V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1)⁻¹ •
          (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1).restrict
              {g | V.PadicCliffordGeneralSpinIsIntegral
                (Rat.HeightOneSpectrum.primesEquiv v.1).1 g}
  rw [Measure.infinitePi_map_pi
    (μ := fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
      V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
        S v)
    (f := fun _ x ↦ (x.1 : V.HeightOnePadicCliffordGeneralSpinGroup _))
    (fun _ ↦ continuous_subtype_val.measurable)]
  congr 1
  funext v
  exact
    V.map_padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
      S v

/-! ## Finite exceptional product -/

/-- The fixed horizontal p-adic `GSpin` Haar measure on the exact height-one
local carrier used at an exceptional place. -/
def heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
    (Rat.HeightOneSpectrum.primesEquiv v).1

theorem heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsHaarMeasure
      (V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v) :=
  V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
    (Rat.HeightOneSpectrum.primesEquiv v).1

instance heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SigmaFinite (V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v) := by
  letI : Measure.IsHaarMeasure
      (V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v) :=
    V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure_isHaarMeasure v
  infer_instance

instance
    heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsMulLeftInvariant
      (V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v) :=
  (V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure_isHaarMeasure v)
    |>.toIsMulLeftInvariant

/-- The finite dependent product of the literal horizontal p-adic `GSpin`
Haar measures at the exceptional places. -/
def cliffordGeneralSpinHorizontalExceptionalProductMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Measure.pi fun
      v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces} ↦
    V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1

@[simp]
theorem cliffordGeneralSpinHorizontalExceptionalProductMeasure_pi
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
      Set (V.HeightOnePadicCliffordGeneralSpinGroup v.1)) :
    V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S
        (Set.pi Set.univ s) =
      ∏ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
        V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1 (s v) := by
  unfold cliffordGeneralSpinHorizontalExceptionalProductMeasure
  exact Measure.pi_pi _ s

@[simp]
theorem cliffordGeneralSpinHorizontalExceptionalProductMeasure_univ
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S Set.univ =
      ∏ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
        V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1 Set.univ := by
  unfold cliffordGeneralSpinHorizontalExceptionalProductMeasure
  exact Measure.pi_univ _

instance cliffordGeneralSpinHorizontalExceptionalProductMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := by
  unfold cliffordGeneralSpinHorizontalExceptionalProductMeasure
  infer_instance

instance
    cliffordGeneralSpinHorizontalExceptionalProductMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := by
  unfold cliffordGeneralSpinHorizontalExceptionalProductMeasure
  exact Measure.pi.isMulLeftInvariant _

/-! ## Direct exceptional/tail source product -/

/-- The unnormalized exceptional product times the normalized integral-tail
probability measure. -/
def cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).prod
    (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)

/-- The normalized good tail contributes one to the total mass of the direct
source product. -/
@[simp]
theorem cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_univ
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S Set.univ =
      ∏ v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces},
        V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1 Set.univ := by
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) :=
    V.cliffordGeneralSpinHorizontalExceptionalProductMeasure_isSigmaFinite S
  letI : SFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := by
    infer_instance
  letI : IsProbabilityMeasure
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isProbability S
  letI : IsZeroOrProbabilityMeasure
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  rw [cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure,
    ← Set.univ_prod_univ, Measure.prod_prod,
    V.cliffordGeneralSpinHorizontalExceptionalProductMeasure_univ S,
    measure_univ, mul_one]

/-- The direct horizontal exceptional/tail source product is invariant under
componentwise left multiplication. -/
instance
    cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_isMulLeftInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S) := by
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) :=
    V.cliffordGeneralSpinHorizontalExceptionalProductMeasure_isSigmaFinite S
  letI : SFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := by
    infer_instance
  letI : IsProbabilityMeasure
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isProbability S
  letI : IsZeroOrProbabilityMeasure
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) := by
    infer_instance
  letI : IsFiniteMeasure
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) :=
    IsFiniteMeasure.toSigmaFinite _
  unfold cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure
  exact Measure.prod.instIsMulLeftInvariant

end RationalQuadraticSpaceMatrix
