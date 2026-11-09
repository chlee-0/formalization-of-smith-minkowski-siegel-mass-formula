import SMSFormula.MeasureInversionTransport
import SMSFormula.RationalCliffordGeneralSpinHorizontalBlockHaar
import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteAdelicHaarRegularity
import SMSFormula.RationalCliffordGeneralSpinPlacewiseHorizontalUnimodular

/-!
# Finite-adelic unimodularity of horizontal intrinsic general Spin

The placewise horizontal measures are inversion invariant at their literal
differential scales.  This property passes through the good integral subgroup
comaps, reciprocal-volume normalization, infinite tail, exceptional product,
fixed-block multiplicative equivalences, ambient inclusions, and the directed
supremum defining the genuine finite-adelic horizontal measure.

No Euler product, quotient measure, or new Haar scalar occurs.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2400000

local instance horizontalFiniteUnimodularPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalFiniteUnimodularLocalMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) := borel _

local instance horizontalFiniteUnimodularLocalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) := ⟨rfl⟩

local instance horizontalFiniteUnimodularIntegralSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    SecondCountableTopology
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalFiniteUnimodularIntegralBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    BorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Subtype.borelSpace _

local instance horizontalFiniteUnimodularExceptionalSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalFiniteUnimodularExceptionalBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Pi.borelSpace

local instance horizontalFiniteUnimodularTailSecondCountable
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalFiniteUnimodularTailBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalIntegralTail S) :=
  Pi.borelSpace

local instance horizontalFiniteUnimodularFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup := borel _

local instance horizontalFiniteUnimodularFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup := ⟨rfl⟩

local instance horizontalFiniteUnimodularBlockBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-! ## Local factors -/

instance heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsInvInvariant
      (V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v) := by
  unfold heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure
  exact V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isInvInvariant
    (Rat.HeightOneSpectrum.primesEquiv v).1

instance padicCliffordGeneralSpinHorizontalIntegralFactorMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Measure.IsInvInvariant
      (V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure S v) := by
  letI : Measure.IsInvInvariant
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isInvInvariant
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  unfold padicCliffordGeneralSpinHorizontalIntegralFactorMeasure
  exact Measure.subgroup_comap_measure_isInvInvariant_of_subtype_mspace
    (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
    (V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasurableSpace_eq S v)
    (V.isOpen_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v).measurableSet

instance
    padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Measure.IsInvInvariant
      (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v) := by
  unfold padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
  exact Measure.isInvInvariant_smul _ _

/-! ## Tail and exceptional products -/

instance cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) := by
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability
      S v
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      Measure.IsInvInvariant
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isInvInvariant
      S v
  constructor
  unfold cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
  change
    Measure.map (fun x v ↦ (x v)⁻¹)
        (Measure.infinitePi fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
          V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v) =
      Measure.infinitePi fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
        V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v
  rw [Measure.infinitePi_map_pi
    (μ := fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
      V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v)
    (f := fun _ x ↦ x⁻¹) (fun _ ↦ measurable_inv)]
  congr 1
  funext v
  exact Measure.map_inv_eq_self
    (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v)

instance cliffordGeneralSpinHorizontalExceptionalProductMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := by
  unfold cliffordGeneralSpinHorizontalExceptionalProductMeasure
  exact Measure.pi.isInvInvariant _

instance cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.cliffordGeneralSpinHorizontalExceptionalTailSourceMeasure S) := by
  letI : SigmaFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) :=
    V.cliffordGeneralSpinHorizontalExceptionalProductMeasure_isSigmaFinite S
  letI : SFinite
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S) := by infer_instance
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
  exact Measure.isInvInvariant_prod _ _

/-! ## Restricted, genuine, and ambient blocks -/

instance cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure S) := by
  unfold cliffordGeneralSpinHorizontalRestrictedPrincipalBlockMeasure
  exact Measure.isInvInvariant_map_of_commutes _ _
    (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
      S).continuous.measurable
    (fun x ↦
      (V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockContinuousMulEquiv
        S).map_inv x)

instance
    cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure S) := by
  unfold cliffordGeneralSpinHorizontalCoherentRestrictedPrincipalBlockMeasure
  exact Measure.isInvInvariant_smul _ _

instance cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S) := by
  unfold cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure
  exact Measure.isInvInvariant_map_of_commutes _ _
    (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockHomeomorph
      S).symm.continuous.measurable
    (fun x ↦
      (V.cliffordGeneralSpinHorizontalGenuineRestrictedPrincipalBlockContinuousMulEquiv
        S).symm.map_inv x)

/-- Inversion in the transported genuine block is literal ambient inversion
on underlying intrinsic finite-adelic points. -/
@[simp]
theorem cliffordGeneralSpinHorizontalGenuinePrincipalBlock_inv_val
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :
    (x⁻¹).1 = x.1⁻¹ := by
  have honeMul : (1 : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S).1 *
      x.1 = x.1 := by
    rw [← V.cliffordGeneralSpinHorizontalGenuinePrincipalBlock_mul_val S]
    simp
  have hone : (1 : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S).1 = 1 := by
    have h := congrArg (fun y ↦ y * x.1⁻¹) honeMul
    simpa [mul_assoc] using h
  have hmul : (x⁻¹).1 * x.1 = 1 := by
    calc
      (x⁻¹).1 * x.1 = (x⁻¹ * x).1 :=
        (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlock_mul_val S _ _).symm
      _ = (1 : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S).1 := by
        exact congrArg Subtype.val (by simp)
      _ = 1 := hone
  calc
    (x⁻¹).1 = (x⁻¹).1 * (x.1 * x.1⁻¹) := by simp
    _ = ((x⁻¹).1 * x.1) * x.1⁻¹ := by rw [mul_assoc]
    _ = x.1⁻¹ := by rw [hmul, one_mul]

instance
    cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.IsInvInvariant
      (V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure S) := by
  unfold cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure
  exact Measure.isInvInvariant_map_of_commutes _ _
    (V.continuous_cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion
      S).measurable
    (fun x ↦ V.cliffordGeneralSpinHorizontalGenuinePrincipalBlock_inv_val S x)

/-! ## Directed finite-adelic measure -/

instance finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isInvInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsInvInvariant
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  unfold finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
  exact Measure.directedSup_isInvInvariant
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure
    (fun _ _ hST ↦
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_mono
        hST)
    (fun S ↦
      V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockAmbientMeasure_isInvInvariant
        S)

theorem finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isMulRightInvariant
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsMulRightInvariant
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  letI : Measure.IsHaarMeasure
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  exact Measure.isMulRightInvariant_of_isInvInvariant
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure

end RationalQuadraticSpaceMatrix
