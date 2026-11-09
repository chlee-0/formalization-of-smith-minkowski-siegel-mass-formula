import SMSFormula.RationalIdeleDifferentialHaar
import SMSFormula.AdelicDoubleCosets
import Mathlib.Probability.ProductMeasure

/-!
# Normalized local factors for differential rational-idele Haar

At every finite rational place, the compact-open subgroup of p-adic units
fixes the local multiplicative Haar scale by volume one.  Comapping that
ambient measure to the compact subgroup gives a literal probability Haar
factor.  Their infinite product is the normalized integral tail and has the
expected exact finite-coordinate marginals.

This is the local-factor side of the finite-idele restricted-product
normalization.  No identification with the already constructed ambient
finite-idele Haar measure, exceptional-cylinder transport, square-map
modulus, Euler product, or idele-class quotient comparison is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance rationalIdeleDifferentialLocalPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance rationalIdeleDifferentialLocalMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  borel _

local instance rationalIdeleDifferentialLocalBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  ⟨rfl⟩

local instance rationalIdeleDifferentialLocalSecondCountableTopology
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

/-! ## Local compact normalization -/

/-- The p-adic integral-unit subgroup as the positive compact fixing the
local multiplicative Haar scale. -/
noncomputable def rationalPadicIdeleIntegralPositiveCompacts
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    PositiveCompacts ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ where
  carrier := padicIntegralUnitsSubgroup
    (Rat.HeightOneSpectrum.primesEquiv v).1
  isCompact' := isCompact_padicIntegralUnitsSubgroup
    (Rat.HeightOneSpectrum.primesEquiv v).1
  interior_nonempty' := by
    rw [(isOpen_padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1).interior_eq]
    exact ⟨1, Subgroup.one_mem _⟩

/-- Local p-adic multiplicative Haar normalized to give the integral units
literal mass one. -/
noncomputable def rationalPadicIdeleDifferentialHaarMeasure
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  Measure.haarMeasure (rationalPadicIdeleIntegralPositiveCompacts v)

@[simp]
theorem rationalPadicIdeleDifferentialHaarMeasure_integralUnits
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    rationalPadicIdeleDifferentialHaarMeasure v
        (padicIntegralUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v).1 :
          Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) = 1 := by
  exact Measure.haarMeasure_self

noncomputable instance rationalPadicIdeleDifferentialHaarMeasure_isHaarMeasure
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsHaarMeasure (rationalPadicIdeleDifferentialHaarMeasure v) := by
  unfold rationalPadicIdeleDifferentialHaarMeasure
  infer_instance

noncomputable instance rationalPadicIdeleDifferentialHaarMeasure_isSigmaFinite
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SigmaFinite (rationalPadicIdeleDifferentialHaarMeasure v) := by
  letI : Measure.IsHaarMeasure
      (rationalPadicIdeleDifferentialHaarMeasure v) :=
    rationalPadicIdeleDifferentialHaarMeasure_isHaarMeasure v
  infer_instance

/-! ## Probability measure on the integral factor -/

/-- The normalized ambient local Haar measure comapped to its integral-unit
subgroup. -/
noncomputable def rationalPadicIdeleIntegralFactorMeasure
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  Measure.comap
    (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1).subtype
    (rationalPadicIdeleDifferentialHaarMeasure v)

theorem rationalPadicIdeleIntegralFactorMeasurableSpace_eq
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (inferInstance : MeasurableSpace
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1)) =
      (@Subtype.instMeasurableSpace
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ
        (fun z ↦ z ∈ padicIntegralUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v).1)
        (inferInstance : MeasurableSpace
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)) :=
  rfl

@[simp]
theorem rationalPadicIdeleIntegralFactorMeasure_univ
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    rationalPadicIdeleIntegralFactorMeasure v Set.univ = 1 := by
  change
    (Measure.comap
      (fun z : padicIntegralUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v).1 ↦
        (z.1 : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ))
      (rationalPadicIdeleDifferentialHaarMeasure v)) Set.univ = 1
  rw [subgroup_comap_measure_univ_eq_of_subtype_mspace
    (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1)
    (rationalPadicIdeleIntegralFactorMeasurableSpace_eq v)
    (isOpen_padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1).measurableSet]
  exact rationalPadicIdeleDifferentialHaarMeasure_integralUnits v

noncomputable instance rationalPadicIdeleIntegralFactorMeasure_isProbability
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    IsProbabilityMeasure (rationalPadicIdeleIntegralFactorMeasure v) :=
  ⟨rationalPadicIdeleIntegralFactorMeasure_univ v⟩

noncomputable instance rationalPadicIdeleIntegralFactorMeasure_isMulLeftInvariant
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsMulLeftInvariant
      (rationalPadicIdeleIntegralFactorMeasure v) := by
  letI : Measure.IsMulLeftInvariant
      (rationalPadicIdeleDifferentialHaarMeasure v) :=
    (rationalPadicIdeleDifferentialHaarMeasure_isHaarMeasure v)
      |>.toIsMulLeftInvariant
  exact subgroup_comap_measure_isMulLeftInvariant_of_subtype_mspace
    (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1)
    (rationalPadicIdeleIntegralFactorMeasurableSpace_eq v)
    (isOpen_padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1).measurableSet

/-- The integral-factor probability measure pushes to the restriction of the
literal local differential Haar measure. -/
theorem map_rationalPadicIdeleIntegralFactorMeasure
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.map
        (padicIntegralUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v).1).subtype
        (rationalPadicIdeleIntegralFactorMeasure v) =
      (rationalPadicIdeleDifferentialHaarMeasure v).restrict
        (padicIntegralUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v).1 :
          Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) := by
  exact subgroup_comap_measure_map_eq_restrict_of_subtype_mspace
    (padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1)
    (rationalPadicIdeleIntegralFactorMeasurableSpace_eq v)
    (isOpen_padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1).measurableSet

/-! ## Infinite normalized integral tail -/

/-- The product of p-adic integral-unit groups at all finite rational
places. -/
abbrev RationalIdeleIntegralTail :=
  (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
    padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1

/-- The infinite product of the literal mass-one local integral factors. -/
noncomputable def rationalIdeleNormalizedIntegralTailMeasure :
    Measure RationalIdeleIntegralTail :=
  Measure.infinitePi fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦
    rationalPadicIdeleIntegralFactorMeasure v

noncomputable instance rationalIdeleNormalizedIntegralTailMeasure_isProbability :
    IsProbabilityMeasure rationalIdeleNormalizedIntegralTailMeasure := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      IsProbabilityMeasure (rationalPadicIdeleIntegralFactorMeasure v) :=
    rationalPadicIdeleIntegralFactorMeasure_isProbability v
  unfold rationalIdeleNormalizedIntegralTailMeasure
  infer_instance

/-- Every finite-coordinate marginal of the normalized integral tail is the
finite product of the same literal local factors. -/
theorem rationalIdeleNormalizedIntegralTailMeasure_map_restrict
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    rationalIdeleNormalizedIntegralTailMeasure.map T.restrict =
      Measure.pi fun v : {v // v ∈ T} ↦
        rationalPadicIdeleIntegralFactorMeasure v.1 := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      IsProbabilityMeasure (rationalPadicIdeleIntegralFactorMeasure v) :=
    rationalPadicIdeleIntegralFactorMeasure_isProbability v
  simpa only [rationalIdeleNormalizedIntegralTailMeasure] using
    (Measure.infinitePi_map_restrict
      (μ := fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        rationalPadicIdeleIntegralFactorMeasure v)
      (I := T))

/-- The normalized integral tail is invariant under componentwise left
multiplication. -/
noncomputable instance
    rationalIdeleNormalizedIntegralTailMeasure_isMulLeftInvariant :
    Measure.IsMulLeftInvariant rationalIdeleNormalizedIntegralTailMeasure := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      IsProbabilityMeasure (rationalPadicIdeleIntegralFactorMeasure v) :=
    rationalPadicIdeleIntegralFactorMeasure_isProbability v
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Measure.IsMulLeftInvariant
        (rationalPadicIdeleIntegralFactorMeasure v) :=
    rationalPadicIdeleIntegralFactorMeasure_isMulLeftInvariant v
  refine ⟨fun g ↦ ?_⟩
  unfold rationalIdeleNormalizedIntegralTailMeasure
  change
    Measure.map (fun x v ↦ g v * x v)
        (Measure.infinitePi fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦
          rationalPadicIdeleIntegralFactorMeasure v) =
      Measure.infinitePi fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦
        rationalPadicIdeleIntegralFactorMeasure v
  rw [Measure.infinitePi_map_pi
    (μ := fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦
      rationalPadicIdeleIntegralFactorMeasure v)
    (f := fun v x ↦ g v * x)
    (fun v ↦ measurable_const_mul (g v))]
  congr 1
  funext v
  exact map_mul_left_eq_self (rationalPadicIdeleIntegralFactorMeasure v) (g v)

end RationalQuadraticSpaceMatrix
