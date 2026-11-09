import SMSFormula.SpecialOrthogonalFullAdelicDifferentialCosetCovariance

/-!
# Left invariance of the full-adelic differential measure

The ambient differential measure is the literal countable sum of the
translated open-stabilizer coset measures.  Ambient left multiplication maps
each summand to the summand indexed by the explicit quotient permutation.
Reindexing that sum proves left invariance.

No regular-Haar assertion, reference-Haar comparison, quotient measure, or
Tamagawa theorem occurs here.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Reindexing the coset-measure sum by ambient left multiplication does not
change the sum. -/
theorem sum_fullAdelicRealFiniteAmbientCosetDifferentialMeasure_comp_leftMulEquiv
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    Measure.sum
        (fun C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex =>
          L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P
            (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv
              g C)) =
      Measure.sum
        (fun C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex =>
          L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C) := by
  ext A hA
  rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
  exact
    (L.fullAdelicRealFiniteLatticeStabilizerCosetIndexLeftMulEquiv g).tsum_eq
      (fun C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex =>
        L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C A)

/-- The literal countable ambient differential measure is invariant under
every ambient left translation. -/
theorem map_mul_left_fullAdelicSpecialOrthogonalDifferentialMeasure
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    Measure.map
        (fun x : L.ConcreteFullAdelicSpecialOrthogonalGroup => g * x)
        (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) =
      L.fullAdelicSpecialOrthogonalDifferentialMeasure P := by
  unfold fullAdelicSpecialOrthogonalDifferentialMeasure
  have hg :
      AEMeasurable
        (fun x : L.ConcreteFullAdelicSpecialOrthogonalGroup => g * x)
        (Measure.sum
          (fun C : L.FullAdelicRealFiniteLatticeStabilizerCosetIndex =>
            L.fullAdelicRealFiniteAmbientCosetDifferentialMeasure P C)) :=
    (continuous_const.mul continuous_id).measurable.aemeasurable
  rw [Measure.map_sum hg]
  simp_rw [
    L.map_mul_left_fullAdelicRealFiniteAmbientCosetDifferentialMeasure hP g]
  exact
    L.sum_fullAdelicRealFiniteAmbientCosetDifferentialMeasure_comp_leftMulEquiv
      P g

/-- Under the explicit positive cutoff-limit hypothesis, the ambient
differential measure is left invariant. -/
theorem fullAdelicSpecialOrthogonalDifferentialMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    Measure.IsMulLeftInvariant
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) where
  map_mul_left_eq_self g :=
    L.map_mul_left_fullAdelicSpecialOrthogonalDifferentialMeasure hP g

end PositiveDefiniteIntegralLattice
