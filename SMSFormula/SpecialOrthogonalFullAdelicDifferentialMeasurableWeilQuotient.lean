import SMSFormula.SpecialOrthogonalFullAdelicDifferentialFundamentalDomainPeriodization

/-!
# Measurable Weil interface for the differential quotient

The general Weil predicate quantifies over arbitrary `ENNReal`-valued
functions.  The standard measure-theoretic statement quantifies over measurable
integrands.  This module records that measurable interface and proves it for
the concrete differential quotient measure.

No quotient volume is evaluated here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

set_option synthInstance.maxHeartbeats 100000

namespace PositiveDefiniteIntegralLattice

universe u

variable {n : ℕ}

/-- Sound left Weil quotient-measure interface for measurable nonnegative
integrands. -/
structure IsLeftMeasurableWeilQuotientMeasure
    {G : Type u} [Group G] [MeasurableSpace G]
    (Gamma : Subgroup G) [MeasurableSpace (leftCosetSet Gamma)]
    (μG : Measure G) (μX : Measure (leftCosetSet Gamma)) : Prop where
  lintegral_leftPeriodize_eq :
    ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ X, leftPeriodize Gamma f X ∂μX = ∫⁻ y, f y ∂μG

/-- The arbitrary-integrand Weil interface implies the measurable-integrand
interface. -/
theorem IsLeftWeilQuotientMeasure.toIsLeftMeasurableWeilQuotientMeasure
    {G : Type u} [Group G] [MeasurableSpace G]
    {Gamma : Subgroup G} [MeasurableSpace (leftCosetSet Gamma)]
    {μG : Measure G} {μX : Measure (leftCosetSet Gamma)}
    (hWeil : IsLeftWeilQuotientMeasure Gamma μG μX) :
    IsLeftMeasurableWeilQuotientMeasure Gamma μG μX where
  lintegral_leftPeriodize_eq f _ :=
    hWeil.lintegral_leftPeriodize_eq f

/-- The rational full-adelic diagonal subgroup is countable because it is the
surjective image of the countable rational special-orthogonal matrix
subgroup. -/
theorem rationalSpecialOrthogonalFullAdelicDiagonalSubgroup_countable
    (L : PositiveDefiniteIntegralLattice n) :
    Countable L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup := by
  let diagonalLift :
      L.rationalSpecialOrthogonalMatrixSubgroup →
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup :=
    fun q =>
      ⟨L.rationalSpecialOrthogonalFullAdelicDiagonalHom q, ⟨q, rfl⟩⟩
  apply Function.Surjective.countable (f := diagonalLift)
  intro gamma
  rcases gamma.2 with ⟨q, hq⟩
  refine ⟨q, Subtype.ext ?_⟩
  exact hq

/-- The quotient measure obtained from the differential Haar and the lifted
proper fundamental domain satisfies the sound measurable Weil formula. -/
theorem concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_isLeftMeasurableWeilQuotientMeasure
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    IsLeftMeasurableWeilQuotientMeasure
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P)
      (L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P) := by
  letI : Countable
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup :=
    L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup_countable
  constructor
  intro f hf
  rw [
    L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_eq_leftQuotientFundamentalDomainMeasure,
    leftQuotientFundamentalDomainMeasure_eq_map_restrict
  ]
  exact
    lintegral_leftPeriodize_eq_of_map_restrict_fundamentalDomain_countable
      (Gamma := L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
      (μG := L.fullAdelicSpecialOrthogonalDifferentialMeasure P)
      (F := L.concreteFullAdelicProperTransversal)
      rfl hf
      (L.lintegral_restrict_concreteFullAdelicSpecialOrthogonalLeftPeriodize_eq_lintegral
        inst hP hf)

end PositiveDefiniteIntegralLattice
