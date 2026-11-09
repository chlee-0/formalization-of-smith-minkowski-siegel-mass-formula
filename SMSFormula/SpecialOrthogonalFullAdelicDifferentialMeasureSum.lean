import SMSFormula.SpecialOrthogonalFullAdelicRealFiniteCosetDifferentialMeasure

/-!
# Countable sum of the full-adelic coset differential measures

The ambient differential measure is defined as the literal countable sum of
the one-coset measures constructed from the open stabilizer.  Its restriction
to every chosen coset is exactly that coset's contribution.  Positivity of
the stabilizer mass makes the sum nonzero, and the countable cover by finite
coset contributions makes it sigma-finite.

No ambient left-invariance, regular-Haar assertion, reference comparison,
quotient measure, or Tamagawa theorem occurs here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The literal countable sum of the translated stabilizer-coset
differential measures on the concrete full-adelic special orthogonal group. -/
noncomputable def fullAdelicSpecialOrthogonalDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    Measure L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  Measure.sum fun
    C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex =>
      L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C

/-- On a measurable set, the ambient differential measure is the series of
the one-coset contributions. -/
theorem fullAdelicSpecialOrthogonalDifferentialMeasure_apply
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    {A : Set L.ConcreteFullAdelicSpecialOrthogonalGroup}
    (hA : MeasurableSet A) :
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P A =
      ∑' C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex,
        L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C A := by
  exact Measure.sum_apply _ hA

/-- Restriction of the countable ambient sum to a chosen coset recovers
exactly that one-coset contribution. -/
theorem restrict_fullAdelicSpecialOrthogonalDifferentialMeasure_coset
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex) :
    (L.fullAdelicSpecialOrthogonalDifferentialMeasure P).restrict
        (L.fullAdelicRealFiniteLatticeStabilizerCoset C) =
      L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C := by
  ext A hA
  rw [Measure.restrict_apply hA,
    fullAdelicSpecialOrthogonalDifferentialMeasure,
    Measure.sum_apply _
      (hA.inter
        (L.measurableSet_fullAdelicRealFiniteLatticeStabilizerCoset C)),
    tsum_eq_single C]
  · rw [← Measure.restrict_apply hA,
      L.restrict_fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C]
  · intro D hDC
    apply
      L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_apply_eq_zero_of_disjoint
        P D
        (hA.inter
          (L.measurableSet_fullAdelicRealFiniteLatticeStabilizerCoset C))
    exact
      (L.pairwiseDisjoint_fullAdelicRealFiniteLatticeStabilizerCoset
        (Ne.symm hDC)).mono Set.inter_subset_right (fun _ h => h)

/-- A positive cutoff-product limit makes the ambient countable sum
nonzero. -/
theorem fullAdelicSpecialOrthogonalDifferentialMeasure_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P ≠ 0 := by
  intro hzero
  let C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex :=
    ((1 : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
      L.FullAdelicRealFiniteLatticeStabilizerCosetIndex)
  have hall :
      ∀ D : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex,
        L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P D = 0 := by
    apply Measure.sum_eq_zero.mp
    simpa only [fullAdelicSpecialOrthogonalDifferentialMeasure] using hzero
  exact
    (L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_ne_zero hP C)
      (hall C)

/-- Under a positive cutoff-product limit, the countable ambient sum is
sigma-finite.  Its total mass is intentionally left unevaluated and may be
infinite. -/
theorem fullAdelicSpecialOrthogonalDifferentialMeasure_sigmaFinite
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    SigmaFinite (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) := by
  let S : Set (Set L.ConcreteFullAdelicSpecialOrthogonalGroup) :=
    Set.range L.fullAdelicRealFiniteLatticeStabilizerCoset
  have hS : S.Countable := by
    simpa only [S] using
      (Set.countable_range
        (fun C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex =>
          L.fullAdelicRealFiniteLatticeStabilizerCoset C))
  apply Measure.sigmaFinite_of_countable hS ?_ ?_
  · intro A hA
    rcases hA with ⟨C, rfl⟩
    letI : IsFiniteMeasure
        (L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C) :=
      L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure_isFinite hP C
    calc
      L.fullAdelicSpecialOrthogonalDifferentialMeasure P
          (L.fullAdelicRealFiniteLatticeStabilizerCoset C) =
          ((L.fullAdelicSpecialOrthogonalDifferentialMeasure P).restrict
            (L.fullAdelicRealFiniteLatticeStabilizerCoset C)) Set.univ := by
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      _ =
          L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C
            Set.univ := by
        rw [L.restrict_fullAdelicSpecialOrthogonalDifferentialMeasure_coset P C]
      _ < ∞ := IsFiniteMeasure.measure_univ_lt_top
  · change ⋃₀ S = Set.univ
    change
      ⋃₀ (Set.range
        (fun C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex =>
          L.fullAdelicRealFiniteLatticeStabilizerCoset C)) = Set.univ
    rw [Set.sUnion_range]
    exact L.iUnion_fullAdelicRealFiniteLatticeStabilizerCoset

end PositiveDefiniteIntegralLattice
