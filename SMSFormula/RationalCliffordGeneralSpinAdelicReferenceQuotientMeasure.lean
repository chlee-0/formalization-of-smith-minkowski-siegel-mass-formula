import SMSFormula.RationalCliffordGeneralSpinAdelicMeasurableFundamentalDomain
import SMSFormula.RationalCliffordGeneralSpinAdelicHaarPrecursor
import SMSFormula.RationalCliffordGeneralSpinAdelicHorizontalTorsor

/-!
# Reference-Haar quotient measure for adelic intrinsic general Spin

The countable quotient-slice atlas supplies a measurable set meeting every
rational left coset exactly once.  This file turns that transversal into
Mathlib's `IsFundamentalDomain`, proves the nonnegative periodization identity,
and constructs measurable-Weil quotient data at the chosen reference Haar
scale.

The reference scale remains arbitrary.  In particular, this does not
identify the quotient measure with either crossed differential normalization
or compare the horizontal and vertical iterated cutoffs.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 100000

/-! ## Exact fundamental-domain structure -/

/-- Every full-adelic point has exactly one rational-diagonal left translate
in the chosen measurable fundamental domain. -/
theorem existsUnique_rationalGeneralSpinDiagonal_mul_mem_measurableFundamentalDomain
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    ∃! gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
      (gamma : V.FullAdelicCliffordGeneralSpinGroup) * x ∈
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain := by
  rcases
      V.existsUnique_fullAdelicCliffordGeneralSpinFundamentalDomainRepresentative x with
    ⟨z, hz, hunique⟩
  let gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    ⟨z * x⁻¹,
      (V.fullAdelicCliffordGeneralSpinLeftQuotientMap_eq_iff x z).mp
        hz.2.symm⟩
  have hgamma :
      (gamma : V.FullAdelicCliffordGeneralSpinGroup) * x ∈
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain := by
    simpa [gamma, mul_assoc] using hz.1
  refine ⟨gamma, hgamma, ?_⟩
  intro delta hdelta
  have hmul :
      (delta : V.FullAdelicCliffordGeneralSpinGroup) * x =
        (gamma : V.FullAdelicCliffordGeneralSpinGroup) * x :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_injOn_fundamentalDomain
      hdelta hgamma
      ((leftCosetMap_gamma_mul
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup delta x).trans
        (leftCosetMap_gamma_mul
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup gamma x).symm)
  apply Subtype.ext
  have hcancel := congrArg
    (fun y : V.FullAdelicCliffordGeneralSpinGroup => y * x⁻¹) hmul
  simpa [mul_assoc] using hcancel

/-- The chosen measurable transversal is an exact fundamental domain for the
rational diagonal action and the reference Haar measure. -/
theorem fullAdelicCliffordGeneralSpinReferenceHaar_isFundamentalDomain :
    IsFundamentalDomain
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
      V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure :=
  IsFundamentalDomain.mk'
    (V.measurableSet_fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain
      |>.nullMeasurableSet)
    (by
      intro x
      change ∃! gamma :
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
        (gamma : V.FullAdelicCliffordGeneralSpinGroup) * x ∈
          V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain
      exact
        V.existsUnique_rationalGeneralSpinDiagonal_mul_mem_measurableFundamentalDomain x)

/-! ## Periodization at the reference Haar scale -/

/-- The measurable periodization identity over the chosen fundamental domain
for every nonnegative measurable function. -/
theorem lintegral_generalSpinReferenceHaar_restrict_leftPeriodize_eq_lintegral
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y,
        leftPeriodize
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
          (V.fullAdelicCliffordGeneralSpinLeftQuotientMap y)
      ∂V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure.restrict
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain =
      ∫⁻ y, f y ∂V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure := by
  letI : Countable
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable
  exact
    lintegral_restrict_leftPeriodize_eq_lintegral_of_isFundamentalDomain
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup hf
      V.fullAdelicCliffordGeneralSpinReferenceHaar_isFundamentalDomain

/-! ## Certified reference quotient data -/

/-- Measurable-Weil quotient data at the arbitrary reference Haar
scale.  This is not crossed invariant-differential data. -/
noncomputable def fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData :
    V.CliffordGeneralSpinReferenceHaarMeasurableWeilMeasureData :=
  CliffordGeneralSpinReferenceHaarMeasurableWeilMeasureData.ofFundamentalDomain
    (V := V)
    V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain
    (fun f hf =>
      V.lintegral_generalSpinReferenceHaar_restrict_leftPeriodize_eq_lintegral f hf)

/-- The certified reference quotient measure is literally the pushforward of
reference Haar restricted to the chosen measurable fundamental domain. -/
theorem fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData_quotientMeasure :
    V.fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData.quotientMeasure =
      V.fullAdelicCliffordGeneralSpinReferenceFundamentalDomainQuotientMeasure
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain :=
  rfl

/-- Its total reference quotient volume is the reference Haar mass of the
chosen fundamental domain.  No value is assigned to this mass. -/
theorem fullAdelicCliffordGeneralSpinReferenceQuotientVolume_eq_domainMass :
    V.fullAdelicCliffordGeneralSpinReferenceHaarMeasurableWeilData.referenceQuotientVolumeENNReal =
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain := by
  rw [CliffordGeneralSpinReferenceHaarMeasurableWeilMeasureData.referenceQuotientVolumeENNReal_eq]
  change
    V.fullAdelicCliffordGeneralSpinReferenceFundamentalDomainQuotientMeasure
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain Set.univ = _
  exact
    V.fullAdelicCliffordGeneralSpinReferenceFundamentalDomainQuotientMeasure_univ
      V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain

end RationalQuadraticSpaceMatrix
