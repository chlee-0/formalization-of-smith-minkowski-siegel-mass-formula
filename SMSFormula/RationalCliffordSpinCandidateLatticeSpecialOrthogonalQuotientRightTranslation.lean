import SMSFormula.RationalCliffordSpinCandidateLatticeRawOnoTamagawaData
import SMSFormula.RationalCliffordSpinCandidateLatticeProperQuotientFiniteDoubleCoset
import SMSFormula.RationalSpecialOrthogonalRawOnoRightQuotient
import SMSFormula.AdelicMeasurableWeilQuotientUniqueness
import SMSFormula.SpecialOrthogonalFullAdelicDifferentialMeasurableWeilQuotient

/-!
# Right translation of the concrete special-orthogonal quotient

The lattice differential measure on the concrete full-adelic `SO` carrier is
right invariant once the inverse-product convergence certificate is
available.  This is transported from the raw rational-form `SO` datum, so no
new normalization is introduced.

Right multiplication therefore preserves the concrete left-quotient measure.
The quotient proof uses the measurable Weil identity and uniqueness from the
exact proper fundamental domain.  This is the quotient-Haar symmetry needed
before comparing the complete selector-profile measure with the horizontal
selector slices; it does not assert pointwise equivariance of the
proper-domain selector.
-/

noncomputable section

open RationalQuadraticSpaceMatrix
open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- Right multiplication is measurable on the concrete rational `SO` left
quotient. -/
theorem measurable_concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul
    (L : PositiveDefiniteIntegralLattice n)
    (x : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    Measurable (L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul x) := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  have hrep : Measurable
      (fun y : L.ConcreteFullAdelicSpecialOrthogonalGroup =>
        L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap (y * x)) :=
    L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap_measurable.comp
      (continuous_mul_right x).measurable
  simpa [concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul,
    Function.comp_def] using measurable_iff_comap_le.mp hrep

/-- The concrete lattice differential measure is inversion invariant under
the exact hypotheses that construct its raw Spin--`SO` datum. -/
theorem fullAdelicSpecialOrthogonalDifferentialMeasure_isInvInvariant_of_convergence
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    Measure.IsInvInvariant
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) := by
  let D :=
    cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L hn inst hP hconv
  let E :=
    (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm
  have hmap : Measure.IsInvInvariant
      (Measure.map E.toHomeomorph
        (L.fullAdelicSpecialOrthogonalDifferentialMeasure P)) := by
    simpa [D, E,
      rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure] using
      D.specialOrthogonalRaw.adelicMeasure_isInvInvariant
  exact Measure.isInvInvariant_of_map_of_commutes
    (mu := L.fullAdelicSpecialOrthogonalDifferentialMeasure P)
    (f := E.toHomeomorph)
    E.toHomeomorph.measurableEmbedding
    (fun x => E.map_inv x) hmap

/-- The concrete lattice differential measure is right invariant under the
same exact convergence hypotheses. -/
theorem fullAdelicSpecialOrthogonalDifferentialMeasure_isMulRightInvariant_of_convergence
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    Measure.IsMulRightInvariant
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) := by
  letI : Measure.IsMulLeftInvariant
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) :=
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_isMulLeftInvariant hP
  letI : Measure.IsInvInvariant
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) :=
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_isInvInvariant_of_convergence
      hn inst hP hconv
  exact Measure.isMulRightInvariant_of_isInvInvariant
    (L.fullAdelicSpecialOrthogonalDifferentialMeasure P)

/-- The literal concrete `SO(Q)\\SO(A)` differential quotient measure is
invariant under every adelic right translation. -/
theorem map_concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_rightMul
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (x : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    Measure.map (L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul x)
        (L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P) =
      L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P := by
  letI : Countable L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup :=
    L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup_countable
  letI : Measure.IsInvInvariant
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) :=
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_isInvInvariant_of_convergence
      hn inst hP hconv
  letI : Measure.IsHaarMeasure
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) :=
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_isHaarMeasure hP
  letI : Measure.IsMulLeftInvariant
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) := by
    infer_instance
  letI : Measure.IsMulRightInvariant
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) :=
    Measure.isMulRightInvariant_of_isInvInvariant
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P)
  let translated := Measure.map
    (L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul x)
    (L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P)
  have htranslated : IsLeftMeasurableWeilQuotientMeasure
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) translated := by
    constructor
    intro f hf
    have hpre : Measurable
        (leftPreperiodize
          L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f) :=
      leftPreperiodize_measurable_of_countable
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup hf
    have hperiod : Measurable
        (leftPeriodize
          L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f) := by
      exact leftPeriodize_measurable_map_of_leftPreperiodize
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup hpre
    rw [lintegral_map' hperiod.aemeasurable
      (L.measurable_concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul x).aemeasurable]
    let fx : L.ConcreteFullAdelicSpecialOrthogonalGroup → ℝ≥0∞ :=
      fun y => f (y * x)
    have hfx : Measurable fx := hf.comp (continuous_mul_right x).measurable
    have hperiodTranslate :
        (leftPeriodize
            L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f) ∘
            L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul x =
          leftPeriodize
            L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup fx := by
      funext q
      induction q using Quot.inductionOn with
      | _ y =>
        change leftPreperiodize
            L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f (y * x) =
          leftPreperiodize
            L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup fx y
        unfold leftPreperiodize fx
        apply tsum_congr
        intro gamma
        simp [mul_assoc]
    change (∫⁻ a,
      ((leftPeriodize
          L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f) ∘
        L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul x) a
        ∂L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P) = _
    rw [hperiodTranslate]
    rw [L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_isLeftMeasurableWeilQuotientMeasure
      inst hP |>.lintegral_leftPeriodize_eq fx hfx]
    calc
      (∫⁻ y, fx y ∂L.fullAdelicSpecialOrthogonalDifferentialMeasure P) =
          ∫⁻ y, f y ∂Measure.map (fun y => y * x)
            (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) := by
        rw [lintegral_map' hf.aemeasurable
          (continuous_mul_right x).measurable.aemeasurable]
      _ = ∫⁻ y, f y ∂L.fullAdelicSpecialOrthogonalDifferentialMeasure P := by
        rw [MeasureTheory.map_mul_right_eq_self]
  have htranslatedEq := htranslated.eq_leftQuotientFundamentalDomainMeasure
    L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup rfl
    (L.concreteFullAdelicProperTransversal_measurableSet inst)
    L.concreteFullAdelicProperTransversal_existsUnique_diagonal
  have horiginalEq :=
    L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_isLeftMeasurableWeilQuotientMeasure
      inst hP
      |>.eq_leftQuotientFundamentalDomainMeasure
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup rfl
        (L.concreteFullAdelicProperTransversal_measurableSet inst)
        L.concreteFullAdelicProperTransversal_existsUnique_diagonal
  simpa only [translated] using htranslatedEq.trans horiginalEq.symm

end PositiveDefiniteIntegralLattice
