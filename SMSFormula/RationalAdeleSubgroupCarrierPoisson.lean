import SMSFormula.RationalAdeleCompactOpenCosetPoisson
import SMSFormula.RationalFiniteAdeleStandardFamilySpanning

/-!
# Poisson for the Gaussian times the indicator of a sandwiched subgroup

The decomposition step is `standardScaleOne_eq_sum_cosetIndicator`, which writes any function that
is standard carried at one and standard periodic at `N` as a finite sum of level-`N` class
indicators, with no representative chosen.  So for a carrier `K` with
`N Zhat^n subset K subset Zhat^n` the indicator `1_K` is such a function -- carried because `K` sits
inside the integral vectors, periodic because `K` is a subgroup containing `N Zhat^n` -- and the
decomposition is immediate.

Feeding it into the finite-linearity Poisson theorem gives rational-diagonal Poisson summation for
the polar Gaussian times `1_K`, with the real and finite Fourier transforms and no hypothesis beyond
a positive width and a nonzero level.

Scope: this is the carrier inside the integral vectors.  The moved carrier of the translated test is
only sandwiched between `N Zhat^n` and `N^-1 Zhat^n`, so applying this to it still needs the
finite-only dilation covariance to bring it inside, with its `m^N` factor and width change kept
explicit.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- A carrier inside the integral vectors gives a function carried at scale one. -/
theorem isStandardCarried_one_indicator {K : Set (Fin n → RationalFiniteAdele)}
    (hK : K ⊆ integralFiniteAdeleVectors n) :
    IsStandardCarried 1 (K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)) := by
  intro x hx
  refine Set.indicator_of_notMem (fun hmem ↦ hx ?_) _
  show (1 : ℕ) • x ∈ integralFiniteAdeleVectors n
  rw [one_smul]
  exact hK hmem

/-- A subgroup carrier containing `N Zhat^n` gives a function periodic at `N`. -/
theorem isStandardPeriodic_indicator {N : ℕ} {K : Set (Fin n → RationalFiniteAdele)}
    (hadd : ∀ {x y : Fin n → RationalFiniteAdele}, x ∈ K → y ∈ K → x + y ∈ K)
    (hneg : ∀ {x : Fin n → RationalFiniteAdele}, x ∈ K → -x ∈ K)
    (hNK : ∀ u ∈ integralFiniteAdeleVectors n, (N • u : Fin n → RationalFiniteAdele) ∈ K) :
    IsStandardPeriodic N (K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)) := by
  intro x u hu
  by_cases h : x ∈ K
  · rw [Set.indicator_of_mem (hadd h (hNK u hu)), Set.indicator_of_mem h]
    rfl
  · refine (Set.indicator_of_notMem ?_ _).trans (Set.indicator_of_notMem h _).symm
    intro hmem
    refine h ?_
    have hback : x = (x + N • u) + -(N • u) := by abel
    rw [hback]
    exact hadd hmem (hneg (hNK u hu))

/-- The decomposition, from the existing spanning theorem: a sandwiched subgroup indicator is a
finite combination of level-`N` class indicators, with no representative chosen. -/
theorem indicator_eq_sum_cosetIndicator {N : ℕ} [NeZero N]
    {K : Set (Fin n → RationalFiniteAdele)}
    (hK : K ⊆ integralFiniteAdeleVectors n)
    (hadd : ∀ {x y : Fin n → RationalFiniteAdele}, x ∈ K → y ∈ K → x + y ∈ K)
    (hneg : ∀ {x : Fin n → RationalFiniteAdele}, x ∈ K → -x ∈ K)
    (hNK : ∀ u ∈ integralFiniteAdeleVectors n, (N • u : Fin n → RationalFiniteAdele) ∈ K) :
    K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ) =
      fun x ↦ ∑ alpha,
        standardFamilyQuotientLift (K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
            (isStandardPeriodic_indicator hadd hneg hNK) alpha *
          standardCosetIndicator n N alpha x :=
  standardScaleOne_eq_sum_cosetIndicator (isStandardCarried_one_indicator hK)
    (isStandardPeriodic_indicator hadd hneg hNK)

/-- Poisson for the polar Gaussian times a sandwiched subgroup indicator, with the actual real and
finite Fourier transforms and no hypothesis beyond a positive width and a nonzero level. -/
theorem tsum_polarGaussian_subgroupIndicator_poisson
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {N : ℕ} (hN : N ≠ 0) [NeZero N]
    {K : Set (Fin n → RationalFiniteAdele)}
    (hK : K ⊆ integralFiniteAdeleVectors n)
    (hadd : ∀ {x y : Fin n → RationalFiniteAdele}, x ∈ K → y ∈ K → x + y ∈ K)
    (hneg : ∀ {x : Fin n → RationalFiniteAdele}, x ∈ K → -x ∈ K)
    (hNK : ∀ u ∈ integralFiniteAdeleVectors n, (N • u : Fin n → RationalFiniteAdele) ∈ K) :
    (∑' q : Fin n → ℚ, polarRealGaussian L b (rationalRealVector n q) *
        K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ)
          (rationalFiniteAdeleVectorDiagonal n q)) =
      ∑' q : Fin n → ℚ,
        Fourier.fourierIntegral (realCoordinateFourierChar n) volume (polarRealGaussian L b)
            (rationalRealVector n q) *
          ∑ alpha,
            standardFamilyQuotientLift (K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
                (isStandardPeriodic_indicator hadd hneg hNK) alpha *
              standardFiniteFourier (standardCosetIndicator n N alpha)
                (rationalFiniteAdeleVectorDiagonal n q) := by
  have hspan := indicator_eq_sum_cosetIndicator (N := N) hK hadd hneg hNK
  refine Eq.trans (tsum_congr fun q ↦ ?_)
    (tsum_polarGaussian_cosetCombination_poisson L hb hN Finset.univ
      (standardFamilyQuotientLift (K.indicator (1 : (Fin n → RationalFiniteAdele) → ℂ))
        (isStandardPeriodic_indicator hadd hneg hNK)))
  rw [congrFun hspan (rationalFiniteAdeleVectorDiagonal n q)]

end RationalQuadraticSpaceMatrix

end
