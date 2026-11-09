import SMSFormula.RationalCliffordGeneralSpinAdelicHorizontalBorel
import SMSFormula.SpecialOrthogonalFullAdelicDifferentialMeasurableWeilQuotient
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Reference Haar precursor for the adelic general-Spin quotient

The completed intrinsic `GSpin` topology supplies a locally compact Hausdorff
group with a closed discrete rational diagonal and a genuine Borel quotient.
This file installs an arbitrary reference Haar measure, proves the rational
diagonal countable, and records the measurable-Weil constructor associated to
an exact measurable fundamental domain.

The reference scale is not identified with either crossed differential
normalization.  In particular, this file does not assert the horizontal or
vertical disintegration needed for the Spin--`SO` comparison.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## Countability -/

/-- Rational intrinsic general-Spin points are countable through their finite
Clifford coordinate vector. -/
noncomputable instance rationalCliffordGeneralSpinGroupCountable :
    Countable V.RationalCliffordGeneralSpinGroup := by
  let coordinate := fun x : V.RationalCliffordGeneralSpinGroup =>
    (V.cliffordCoordinateBaseChangeBasis ℚ).repr
      (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℚ)
  apply Function.Injective.countable (f := coordinate)
  intro x y hxy
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V ℚ
  apply Units.ext
  exact (V.cliffordCoordinateBaseChangeBasis ℚ).repr.injective hxy

/-- The rational diagonal subgroup of full-adelic intrinsic general Spin is
countable. -/
theorem rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable :
    Countable V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup := by
  let diagonalLift :
      V.RationalCliffordGeneralSpinGroup →
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    fun q =>
      ⟨V.rationalCliffordGeneralSpinFullAdelicDiagonalHom q, ⟨q, rfl⟩⟩
  apply Function.Surjective.countable (f := diagonalLift)
  intro gamma
  rcases gamma.2 with ⟨q, hq⟩
  refine ⟨q, Subtype.ext ?_⟩
  exact hq

/-! ## A reference Haar measure -/

/-- An arbitrary reference Haar measure on full-adelic intrinsic general
Spin.  Its scale is not tied to the crossed differential data. -/
noncomputable def fullAdelicCliffordGeneralSpinReferenceHaarMeasure :
    Measure V.FullAdelicCliffordGeneralSpinGroup :=
  Measure.haar

/-- The reference measure is a genuine left Haar measure. -/
noncomputable instance
    fullAdelicCliffordGeneralSpinReferenceHaarMeasureIsHaarMeasure :
    Measure.IsHaarMeasure
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure := by
  unfold fullAdelicCliffordGeneralSpinReferenceHaarMeasure
  infer_instance

/-- The reference Haar measure is left invariant. -/
noncomputable instance
    fullAdelicCliffordGeneralSpinReferenceHaarMeasureIsMulLeftInvariant :
    Measure.IsMulLeftInvariant
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure := by
  infer_instance

/-- The reference Haar measure is nonzero. -/
theorem fullAdelicCliffordGeneralSpinReferenceHaarMeasure_ne_zero :
    V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure ≠ 0 := by
  intro hzero
  have huniv :
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure Set.univ ≠ 0 :=
    isOpen_univ.measure_ne_zero
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure Set.univ_nonempty
  rw [hzero] at huniv
  exact huniv rfl

/-- The finite-coordinate second-countability witness makes the reference
Haar measure sigma-finite. -/
noncomputable instance
    fullAdelicCliffordGeneralSpinReferenceHaarMeasureSigmaFinite :
    SigmaFinite V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure := by
  letI : SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology
  unfold fullAdelicCliffordGeneralSpinReferenceHaarMeasure Measure.haar
  infer_instance

/-- The reference Haar measure is regular. -/
theorem fullAdelicCliffordGeneralSpinReferenceHaarMeasure_regular :
    V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure.Regular := by
  unfold fullAdelicCliffordGeneralSpinReferenceHaarMeasure Measure.haar
  infer_instance

/-! ## Quotient measures from a fundamental domain -/

/-- Push the reference Haar restricted to a proposed fundamental domain to
the actual rational adelic `GSpin` quotient.  No fundamental-domain property
is asserted by this definition. -/
noncomputable def
    fullAdelicCliffordGeneralSpinReferenceFundamentalDomainQuotientMeasure
    (F : Set V.FullAdelicCliffordGeneralSpinGroup) :
    Measure V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  leftQuotientFundamentalDomainMeasure
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
    V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure F

/-- The proposed quotient measure has total mass equal to the reference Haar
mass of its source set. -/
@[simp]
theorem
    fullAdelicCliffordGeneralSpinReferenceFundamentalDomainQuotientMeasure_univ
    (F : Set V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinReferenceFundamentalDomainQuotientMeasure F
        Set.univ =
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure F := by
  unfold
    fullAdelicCliffordGeneralSpinReferenceFundamentalDomainQuotientMeasure
  exact leftQuotientFundamentalDomainMeasure_univ_map_mspace
    (Gamma := V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (μG := V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure)
    (F := F) rfl

/-- Reference-Haar quotient data certified by the sound measurable Weil
formula.  This structure carries no crossed differential normalization. -/
structure CliffordGeneralSpinReferenceHaarMeasurableWeilMeasureData where
  quotientMeasure : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient
  isMeasurableWeilQuotientMeasure :
    IsLeftMeasurableWeilQuotientMeasure
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
      V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure
      quotientMeasure

namespace CliffordGeneralSpinReferenceHaarMeasurableWeilMeasureData

/-- Construct reference measurable-Weil data from a proposed fundamental
domain once its measurable periodization identity is proved. -/
noncomputable def ofFundamentalDomain
    (F : Set V.FullAdelicCliffordGeneralSpinGroup)
    (hfund :
      ∀ f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞,
        Measurable f →
          ∫⁻ y,
              leftPeriodize
                V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
                (V.fullAdelicCliffordGeneralSpinLeftQuotientMap y)
              ∂V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure.restrict F =
            ∫⁻ y, f y
              ∂V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure) :
    V.CliffordGeneralSpinReferenceHaarMeasurableWeilMeasureData where
  quotientMeasure :=
    V.fullAdelicCliffordGeneralSpinReferenceFundamentalDomainQuotientMeasure F
  isMeasurableWeilQuotientMeasure := by
    letI : Countable
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable
    constructor
    intro f hf
    unfold
      fullAdelicCliffordGeneralSpinReferenceFundamentalDomainQuotientMeasure
    rw [leftQuotientFundamentalDomainMeasure_eq_map_restrict]
    exact
      lintegral_leftPeriodize_eq_of_map_restrict_fundamentalDomain_countable
        (Gamma :=
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
        (μG := V.fullAdelicCliffordGeneralSpinReferenceHaarMeasure)
        (F := F) rfl hf (hfund f hf)

/-- Total quotient volume at the arbitrary reference Haar scale. -/
def referenceQuotientVolumeENNReal
    (D : V.CliffordGeneralSpinReferenceHaarMeasurableWeilMeasureData) :
    ℝ≥0∞ :=
  D.quotientMeasure Set.univ

@[simp]
theorem referenceQuotientVolumeENNReal_eq
    (D : V.CliffordGeneralSpinReferenceHaarMeasurableWeilMeasureData) :
    D.referenceQuotientVolumeENNReal = D.quotientMeasure Set.univ :=
  rfl

end CliffordGeneralSpinReferenceHaarMeasurableWeilMeasureData

end RationalQuadraticSpaceMatrix
