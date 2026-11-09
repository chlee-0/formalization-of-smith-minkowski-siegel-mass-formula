import SMSFormula.RationalCliffordSpinCandidateAdelicMeasurableFundamentalDomain

/-!
# Reference-Haar quotient measure for the adelic Spin candidate

The measurable set constructed from the countable quotient-slice atlas meets
every rational left coset exactly once.  This file converts that statement to
Mathlib's `IsFundamentalDomain`, invokes the generic nonnegative
periodization-integral identity, and constructs the corresponding measurable-
Weil quotient data for the chosen reference Haar measure.

The reference Haar scale is arbitrary.  It is not identified here with an
invariant-differential Tamagawa normalization.
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

/-- For every full-adelic point there is exactly one rational diagonal element
whose left translate lies in the chosen measurable fundamental domain. -/
theorem existsUnique_rationalDiagonal_smul_mem_measurableFundamentalDomain
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    ∃! gamma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
      (gamma : V.FullAdelicCliffordSpinCandidateGroup) * x ∈
        V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain := by
  rcases V.existsUnique_fundamentalDomainRepresentative x with
    ⟨z, hz, hunique⟩
  let gamma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :=
    ⟨z * x⁻¹,
      (V.fullAdelicCliffordSpinCandidateLeftQuotientMap_eq_iff x z).mp
        hz.2.symm⟩
  have hgamma :
      (gamma : V.FullAdelicCliffordSpinCandidateGroup) * x ∈
        V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain := by
    simpa [gamma, mul_assoc] using hz.1
  refine ⟨gamma, hgamma, ?_⟩
  intro delta hdelta
  have hmul :
      (delta : V.FullAdelicCliffordSpinCandidateGroup) * x =
        (gamma : V.FullAdelicCliffordSpinCandidateGroup) * x :=
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_injOn_fundamentalDomain
      hdelta hgamma
      ((leftCosetMap_gamma_mul
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup delta x).trans
        (leftCosetMap_gamma_mul
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup gamma x).symm)
  apply Subtype.ext
  have hcancel := congrArg
    (fun y : V.FullAdelicCliffordSpinCandidateGroup => y * x⁻¹) hmul
  simpa [mul_assoc] using hcancel

/-- The chosen measurable set is an exact fundamental domain for the rational
diagonal action and the reference Haar measure. -/
theorem fullAdelicCliffordSpinCandidateReferenceHaar_isFundamentalDomain :
    IsFundamentalDomain
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
      V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain
      V.fullAdelicCliffordSpinCandidateReferenceHaarMeasure :=
  IsFundamentalDomain.mk'
    (V.measurableSet_fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain
      |>.nullMeasurableSet)
    (by
      intro x
      change ∃! gamma :
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
        (gamma : V.FullAdelicCliffordSpinCandidateGroup) * x ∈
          V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain
      exact
        V.existsUnique_rationalDiagonal_smul_mem_measurableFundamentalDomain x)

/-! ## Periodization at the reference Haar scale -/

/-- The measurable periodization identity over the chosen fundamental domain
for every nonnegative measurable function. -/
theorem lintegral_referenceHaar_restrict_leftPeriodize_eq_lintegral
    (f : V.FullAdelicCliffordSpinCandidateGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y,
        leftPeriodize
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f
          (V.fullAdelicCliffordSpinCandidateLeftQuotientMap y)
      ∂V.fullAdelicCliffordSpinCandidateReferenceHaarMeasure.restrict
        V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain =
      ∫⁻ y, f y ∂V.fullAdelicCliffordSpinCandidateReferenceHaarMeasure := by
  letI : Countable
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :=
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup_countable
  exact
    lintegral_restrict_leftPeriodize_eq_lintegral_of_isFundamentalDomain
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup hf
      V.fullAdelicCliffordSpinCandidateReferenceHaar_isFundamentalDomain

/-! ## Certified reference quotient data -/

/-- Measurable-Weil quotient data at the arbitrary reference Haar
scale.  This is not invariant-differential Tamagawa data. -/
noncomputable def fullAdelicCliffordSpinCandidateReferenceHaarMeasurableWeilData :
    V.CliffordSpinCandidateReferenceHaarMeasurableWeilMeasureData :=
  CliffordSpinCandidateReferenceHaarMeasurableWeilMeasureData.ofFundamentalDomain
    (V := V)
    V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain
    (fun f hf =>
      V.lintegral_referenceHaar_restrict_leftPeriodize_eq_lintegral f hf)

/-- The certified reference quotient measure is literally the pushforward of
reference Haar restricted to the chosen measurable fundamental domain. -/
theorem fullAdelicCliffordSpinCandidateReferenceHaarMeasurableWeilData_quotientMeasure :
    V.fullAdelicCliffordSpinCandidateReferenceHaarMeasurableWeilData.quotientMeasure =
      V.fullAdelicCliffordSpinCandidateReferenceFundamentalDomainQuotientMeasure
        V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain :=
  rfl

/-- Its total reference quotient volume is the reference Haar mass of the
chosen fundamental domain.  No value is assigned to this mass. -/
theorem fullAdelicCliffordSpinCandidateReferenceQuotientVolume_eq_domainMass :
    V.fullAdelicCliffordSpinCandidateReferenceHaarMeasurableWeilData.referenceQuotientVolumeENNReal =
      V.fullAdelicCliffordSpinCandidateReferenceHaarMeasure
        V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain := by
  rw [CliffordSpinCandidateReferenceHaarMeasurableWeilMeasureData.referenceQuotientVolumeENNReal_eq]
  change
    V.fullAdelicCliffordSpinCandidateReferenceFundamentalDomainQuotientMeasure
        V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain Set.univ = _
  exact
    V.fullAdelicCliffordSpinCandidateReferenceFundamentalDomainQuotientMeasure_univ
      V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain

end RationalQuadraticSpaceMatrix
