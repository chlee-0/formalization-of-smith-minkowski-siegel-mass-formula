import SMSFormula.RationalIdeleDifferentialLocalFactor

/-!
# Exceptional and normalized-tail differential idele measures

For a finite set `S` of rational finite places, use the normalized local
multiplicative Haar measure on the unrestricted local unit group at places in
`S`, and the compact integral-unit probability factor at every place outside
`S`.  This file constructs the finite exceptional product, the infinite
normalized tail, their direct product, and the exact inclusion pushforward of
the tail.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance rationalIdeleExceptionalTailDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance rationalIdeleExceptionalTailPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance rationalIdeleExceptionalTailMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance rationalIdeleExceptionalTailBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

/-! ## Exceptional and tail carriers -/

/-- The finite product of unrestricted local multiplicative groups at the
chosen exceptional places. -/
abbrev RationalIdeleDifferentialExceptionalProduct
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ S}) →
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ

/-- The product of compact integral-unit groups away from the chosen finite
exceptional set. -/
abbrev RationalIdeleDifferentialIntegralTail
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∉ S}) →
    padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1

/-- The unrestricted local product containing the integral tail. -/
abbrev RationalIdeleDifferentialUnrestrictedTail
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∉ S}) →
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ

/-! ## Normalized infinite tail -/

/-- The infinite product of the volume-one integral-unit factors away from
`S`. -/
noncomputable def rationalIdeleDifferentialNormalizedIntegralTailMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalIdeleDifferentialIntegralTail S) :=
  Measure.infinitePi fun v : {v // v ∉ S} ↦
    rationalPadicIdeleIntegralFactorMeasure v.1

noncomputable instance
    rationalIdeleDifferentialNormalizedIntegralTailMeasure_isProbability
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsProbabilityMeasure
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) := by
  letI (v : {v // v ∉ S}) :
      IsProbabilityMeasure (rationalPadicIdeleIntegralFactorMeasure v.1) :=
    rationalPadicIdeleIntegralFactorMeasure_isProbability v.1
  unfold rationalIdeleDifferentialNormalizedIntegralTailMeasure
  infer_instance

/-- Every finite-coordinate marginal of the complement tail is the finite
product of the same literal local probability factors. -/
theorem rationalIdeleDifferentialNormalizedIntegralTailMeasure_map_restrict
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (T : Finset {v // v ∉ S}) :
    (rationalIdeleDifferentialNormalizedIntegralTailMeasure S).map T.restrict =
      Measure.pi fun v : {v // v ∈ T} ↦
        rationalPadicIdeleIntegralFactorMeasure v.1.1 := by
  letI (v : {v // v ∉ S}) :
      IsProbabilityMeasure (rationalPadicIdeleIntegralFactorMeasure v.1) :=
    rationalPadicIdeleIntegralFactorMeasure_isProbability v.1
  simpa only [rationalIdeleDifferentialNormalizedIntegralTailMeasure] using
    (Measure.infinitePi_map_restrict
      (μ := fun v : {v // v ∉ S} ↦
        rationalPadicIdeleIntegralFactorMeasure v.1)
      (I := T))

noncomputable instance
    rationalIdeleDifferentialNormalizedIntegralTailMeasure_isMulLeftInvariant
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) := by
  letI (v : {v // v ∉ S}) :
      IsProbabilityMeasure (rationalPadicIdeleIntegralFactorMeasure v.1) :=
    rationalPadicIdeleIntegralFactorMeasure_isProbability v.1
  letI (v : {v // v ∉ S}) :
      Measure.IsMulLeftInvariant
        (rationalPadicIdeleIntegralFactorMeasure v.1) :=
    rationalPadicIdeleIntegralFactorMeasure_isMulLeftInvariant v.1
  refine ⟨fun g ↦ ?_⟩
  unfold rationalIdeleDifferentialNormalizedIntegralTailMeasure
  change
    Measure.map (fun x v ↦ g v * x v)
        (Measure.infinitePi fun v : {v // v ∉ S} ↦
          rationalPadicIdeleIntegralFactorMeasure v.1) =
      Measure.infinitePi fun v : {v // v ∉ S} ↦
        rationalPadicIdeleIntegralFactorMeasure v.1
  rw [Measure.infinitePi_map_pi
    (μ := fun v : {v // v ∉ S} ↦
      rationalPadicIdeleIntegralFactorMeasure v.1)
    (f := fun v x ↦ g v * x)
    (fun v ↦ measurable_const_mul (g v))]
  congr 1
  funext v
  exact map_mul_left_eq_self
    (rationalPadicIdeleIntegralFactorMeasure v.1) (g v)

/-! ## Inclusion into the unrestricted complement product -/

/-- Componentwise inclusion of the integral tail into unrestricted local
multiplicative groups. -/
def rationalIdeleDifferentialIntegralTailInclusion
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalIdeleDifferentialIntegralTail S →*
      RationalIdeleDifferentialUnrestrictedTail S where
  toFun z v := (z v).1
  map_one' := by
    funext v
    rfl
  map_mul' := by
    intro z w
    funext v
    rfl

@[simp]
theorem rationalIdeleDifferentialIntegralTailInclusion_apply
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : RationalIdeleDifferentialIntegralTail S)
    (v : {v // v ∉ S}) :
    rationalIdeleDifferentialIntegralTailInclusion S z v = (z v).1 :=
  rfl

theorem continuous_rationalIdeleDifferentialIntegralTailInclusion
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (rationalIdeleDifferentialIntegralTailInclusion S) :=
  continuous_pi fun v ↦ continuous_subtype_val.comp (continuous_apply v)

/-- Tail inclusion exposes the infinite product of the literal restricted
ambient local Haar measures. -/
theorem map_rationalIdeleDifferentialNormalizedIntegralTailMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (rationalIdeleDifferentialIntegralTailInclusion S)
        (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) =
      Measure.infinitePi fun v : {v // v ∉ S} ↦
        (rationalPadicIdeleDifferentialHaarMeasure v.1).restrict
          (padicIntegralUnitsSubgroup
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 :
            Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ) := by
  letI (v : {v // v ∉ S}) :
      IsProbabilityMeasure (rationalPadicIdeleIntegralFactorMeasure v.1) :=
    rationalPadicIdeleIntegralFactorMeasure_isProbability v.1
  unfold rationalIdeleDifferentialIntegralTailInclusion
    rationalIdeleDifferentialNormalizedIntegralTailMeasure
  change
    Measure.map (fun z v ↦ (z v).1)
        (Measure.infinitePi fun v : {v // v ∉ S} ↦
          rationalPadicIdeleIntegralFactorMeasure v.1) =
      Measure.infinitePi fun v : {v // v ∉ S} ↦
        (rationalPadicIdeleDifferentialHaarMeasure v.1).restrict
          (padicIntegralUnitsSubgroup
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 :
            Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
  rw [Measure.infinitePi_map_pi
    (μ := fun v : {v // v ∉ S} ↦
      rationalPadicIdeleIntegralFactorMeasure v.1)
    (f := fun _ z ↦
      (z.1 : ℚ_[(Rat.HeightOneSpectrum.primesEquiv _).1]ˣ))
    (fun _ ↦ continuous_subtype_val.measurable)]
  congr 1
  funext v
  exact map_rationalPadicIdeleIntegralFactorMeasure v.1

/-! ## Finite exceptional product -/

/-- The finite product of literal local differential Haar measures on the
unrestricted exceptional coordinates. -/
noncomputable def rationalIdeleDifferentialExceptionalProductMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalIdeleDifferentialExceptionalProduct S) :=
  Measure.pi fun v : {v // v ∈ S} ↦
    rationalPadicIdeleDifferentialHaarMeasure v.1

@[simp]
theorem rationalIdeleDifferentialExceptionalProductMeasure_pi
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : ∀ v : {v // v ∈ S},
      Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ) :
    rationalIdeleDifferentialExceptionalProductMeasure S (Set.pi Set.univ s) =
      ∏ v : {v // v ∈ S},
        rationalPadicIdeleDifferentialHaarMeasure v.1 (s v) := by
  unfold rationalIdeleDifferentialExceptionalProductMeasure
  exact Measure.pi_pi _ s

noncomputable instance
    rationalIdeleDifferentialExceptionalProductMeasure_isSigmaFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite (rationalIdeleDifferentialExceptionalProductMeasure S) := by
  letI (v : {v // v ∈ S}) :
      Measure.IsHaarMeasure
        (rationalPadicIdeleDifferentialHaarMeasure v.1) :=
    rationalPadicIdeleDifferentialHaarMeasure_isHaarMeasure v.1
  unfold rationalIdeleDifferentialExceptionalProductMeasure
  infer_instance

noncomputable instance
    rationalIdeleDifferentialExceptionalProductMeasure_isMulLeftInvariant
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (rationalIdeleDifferentialExceptionalProductMeasure S) := by
  letI (v : {v // v ∈ S}) :
      Measure.IsMulLeftInvariant
        (rationalPadicIdeleDifferentialHaarMeasure v.1) :=
    (rationalPadicIdeleDifferentialHaarMeasure_isHaarMeasure v.1)
      |>.toIsMulLeftInvariant
  unfold rationalIdeleDifferentialExceptionalProductMeasure
  exact Measure.pi.isMulLeftInvariant _

/-! ## Direct exceptional/tail source -/

/-- The finite unrestricted exceptional product times the normalized compact
tail away from `S`. -/
noncomputable def rationalIdeleDifferentialExceptionalTailSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (RationalIdeleDifferentialExceptionalProduct S ×
      RationalIdeleDifferentialIntegralTail S) :=
  (rationalIdeleDifferentialExceptionalProductMeasure S).prod
    (rationalIdeleDifferentialNormalizedIntegralTailMeasure S)

noncomputable instance
    rationalIdeleDifferentialExceptionalTailSourceMeasure_isSigmaFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SigmaFinite (rationalIdeleDifferentialExceptionalTailSourceMeasure S) := by
  letI : SigmaFinite
      (rationalIdeleDifferentialExceptionalProductMeasure S) :=
    rationalIdeleDifferentialExceptionalProductMeasure_isSigmaFinite S
  letI : IsProbabilityMeasure
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) :=
    rationalIdeleDifferentialNormalizedIntegralTailMeasure_isProbability S
  unfold rationalIdeleDifferentialExceptionalTailSourceMeasure
  infer_instance

noncomputable instance
    rationalIdeleDifferentialExceptionalTailSourceMeasure_isMulLeftInvariant
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsMulLeftInvariant
      (rationalIdeleDifferentialExceptionalTailSourceMeasure S) := by
  letI : SigmaFinite
      (rationalIdeleDifferentialExceptionalProductMeasure S) :=
    rationalIdeleDifferentialExceptionalProductMeasure_isSigmaFinite S
  letI : IsProbabilityMeasure
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) :=
    rationalIdeleDifferentialNormalizedIntegralTailMeasure_isProbability S
  letI : SigmaFinite
      (rationalIdeleDifferentialNormalizedIntegralTailMeasure S) := by
    infer_instance
  unfold rationalIdeleDifferentialExceptionalTailSourceMeasure
  exact Measure.prod.instIsMulLeftInvariant

end RationalQuadraticSpaceMatrix
