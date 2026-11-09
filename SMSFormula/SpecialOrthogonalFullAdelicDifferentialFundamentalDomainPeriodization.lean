import SMSFormula.SpecialOrthogonalFullAdelicDifferentialQuotientMeasure

/-!
# Periodization over the differential proper fundamental domain

The rational diagonal subgroup is countable, and the internally constructed
full-adelic differential measure is invariant under its left action.  The
strict proper fundamental domain therefore unfolds the ambient integral of
every measurable nonnegative function as the integral of its rational
periodization over that domain.

This module proves only the fundamental-domain integral.  It does not assert
the stronger project-local Weil quotient interface, whose current definition
has an additional descended-measurability requirement.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 500000

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- For a measurable nonnegative function, integration of its rational
periodization over the lifted proper fundamental domain equals its ambient
full-adelic differential integral. -/
theorem lintegral_restrict_concreteFullAdelicSpecialOrthogonalLeftPeriodize_eq_lintegral
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    {f : L.ConcreteFullAdelicSpecialOrthogonalGroup → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y,
        leftPeriodize
          L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f
          (L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap y)
      ∂(L.fullAdelicSpecialOrthogonalDifferentialMeasure P).restrict
        L.concreteFullAdelicProperTransversal =
      ∫⁻ y, f y ∂L.fullAdelicSpecialOrthogonalDifferentialMeasure P := by
  let diagonalLift :
      L.rationalSpecialOrthogonalMatrixSubgroup →
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup :=
    fun q =>
      ⟨L.rationalSpecialOrthogonalFullAdelicDiagonalHom q, ⟨q, rfl⟩⟩
  have diagonalLift_surjective : Function.Surjective diagonalLift := by
    intro gamma
    rcases gamma.2 with ⟨q, hq⟩
    refine ⟨q, Subtype.ext ?_⟩
    exact hq
  letI : Countable
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup :=
    diagonalLift_surjective.countable
  letI : MulAction L.ConcreteFullAdelicSpecialOrthogonalGroup
      L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    Monoid.toMulAction L.ConcreteFullAdelicSpecialOrthogonalGroup
  letI : MulAction
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    Subgroup.instMulAction
  letI : MeasurableConstSMul
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    ⟨fun c => by
      change Measurable
        (fun x : L.ConcreteFullAdelicSpecialOrthogonalGroup =>
          (c : L.ConcreteFullAdelicSpecialOrthogonalGroup) * x)
      exact measurable_const_mul _⟩
  letI : SMulInvariantMeasure
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      L.ConcreteFullAdelicSpecialOrthogonalGroup
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) := by
    constructor
    intro c s hs
    change
      L.fullAdelicSpecialOrthogonalDifferentialMeasure P
          ((fun x : L.ConcreteFullAdelicSpecialOrthogonalGroup =>
            (c : L.ConcreteFullAdelicSpecialOrthogonalGroup) * x) ⁻¹' s) =
        L.fullAdelicSpecialOrthogonalDifferentialMeasure P s
    exact Measure.measure_preimage_of_map_eq_self
      (L.map_mul_left_fullAdelicSpecialOrthogonalDifferentialMeasure hP
        (c : L.ConcreteFullAdelicSpecialOrthogonalGroup))
      hs.nullMeasurableSet
  exact
    lintegral_restrict_leftPeriodize_eq_lintegral_of_isFundamentalDomain
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup hf
      (L.concreteFullAdelicProperTransversal_isFundamentalDomain_differential
        inst P)

end PositiveDefiniteIntegralLattice
