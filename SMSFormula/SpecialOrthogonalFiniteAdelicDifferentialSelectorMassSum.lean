import SMSFormula.SpecialOrthogonalFiniteAdelicDifferentialSelectorMass

/-!
# Sum of the proper finite-adelic differential selector masses

The exact differential mass of one proper local-stabilizer selector is summed
over the finite proper rational double-coset set.  Finite distributivity
separates the literal internally constructed finite differential stabilizer
volume from the arithmetic reciprocal-cardinality sum.  The latter is
identified directly with the real cast of `properClassGenusMass`.

No ambient finite-domain measure, reference Haar comparison, or real-place
factor occurs here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The finite sum of proper selector masses factors by the literal finite
differential stabilizer volume. -/
theorem concreteProperDifferentialSelectorMassSum_eq_volume_mul_sum
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (P : ℝ) :
    @Finset.sum L.ConcreteProperRationalDoubleCosetSet ℝ≥0∞ _
        (@Finset.univ L.ConcreteProperRationalDoubleCosetSet inst)
        (fun C =>
          L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P
            (L.concreteProperLocalRightStabilizerEmbeddingRealSlice
              (Quot.out C))) =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
        @Finset.sum L.ConcreteProperRationalDoubleCosetSet ℝ≥0∞ _
          (@Finset.univ L.ConcreteProperRationalDoubleCosetSet inst)
          (fun C =>
            ENNReal.ofReal
              (1 / (Nat.card
                (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
                  (Quot.out C)) :
                ℝ))) := by
  letI : Fintype L.ConcreteProperRationalDoubleCosetSet := inst
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  exact
    L.concreteProperLocalRightStabilizerEmbeddingRealSlice_differential_measure
      (Quot.out C) P

/-- The `ENNReal` reciprocal-cardinality sum over the selected proper double
cosets is exactly the real cast of the proper class genus mass. -/
theorem concreteProperSelectorInverseCardinalityENNRealSum_eq_properClassGenusMass
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    @Finset.sum L.ConcreteProperRationalDoubleCosetSet ℝ≥0∞ _
        (@Finset.univ L.ConcreteProperRationalDoubleCosetSet inst)
        (fun C =>
          ENNReal.ofReal
            (1 / (Nat.card
              (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
                (Quot.out C)) :
              ℝ))) =
      ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ)) := by
  letI : Fintype L.ConcreteProperRationalDoubleCosetSet := inst
  let v : L.ConcreteProperRationalDoubleCosetSet → ℝ := fun C =>
    1 / (Nat.card
      (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
        (Quot.out C)) : ℝ)
  have hv_nonneg : ∀ C, 0 ≤ v C := fun C =>
    one_div_nonneg.mpr (Nat.cast_nonneg _)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun C _ => hv_nonneg C)]
  apply congrArg ENNReal.ofReal
  calc
    (∑ C : L.ConcreteProperRationalDoubleCosetSet, v C) =
        ∑ C : L.ConcreteProperRationalDoubleCosetSet,
          1 / (Nat.card
            (L.concreteProperArithmeticStabilizerSubgroup (Quot.out C)) :
            ℝ) := by
      apply Finset.sum_congr rfl
      intro C _
      change
        1 / (Nat.card
          (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
            (Quot.out C)) : ℝ) =
          1 / (Nat.card
            (L.concreteProperArithmeticStabilizerSubgroup (Quot.out C)) : ℝ)
      rw [L.concreteProperLocalRightStabilizerInCompactOpen_cardinality]
    _ =
        ((∑ C : L.ConcreteProperRationalDoubleCosetSet,
          ((Nat.card
            (L.concreteProperArithmeticStabilizerSubgroup (Quot.out C)) :
            ℚ)⁻¹) : ℚ) :
          ℝ) := by
      push_cast
      simp only [one_div]
    _ = ((L.properClassGenusMass : ℚ) : ℝ) := by
      apply congrArg (fun x : ℚ => (x : ℝ))
      calc
        (∑ C : L.ConcreteProperRationalDoubleCosetSet,
            ((Nat.card
              (L.concreteProperArithmeticStabilizerSubgroup (Quot.out C)) :
              ℚ)⁻¹)) =
            @Finset.sum L.ConcreteProperRationalDoubleCosetSet ℚ _
              (@Finset.univ L.ConcreteProperRationalDoubleCosetSet
                L.concreteProperRationalDoubleCosetSetFintype)
              (fun C =>
                ((Nat.card
                  (L.concreteProperArithmeticStabilizerSubgroup (Quot.out C)) :
                  ℚ)⁻¹)) := by
          apply Finset.sum_congr
          · ext C
            simp
          · intro C _
            rfl
        _ = L.properClassGenusMass := by
          simpa [concreteProperArithmeticStabilizerSubgroup] using
            L.concreteProperArithmeticStabilizerMassSum_eq_properClassGenusMass

/-- The finite sum of the literal proper selector differential masses is the
finite differential stabilizer volume times the `ENNReal` real cast of proper
class genus mass. -/
theorem concreteProperDifferentialSelectorMassSum_eq_volume_mul_properClassGenusMass
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (P : ℝ) :
    @Finset.sum L.ConcreteProperRationalDoubleCosetSet ℝ≥0∞ _
        (@Finset.univ L.ConcreteProperRationalDoubleCosetSet inst)
        (fun C =>
          L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P
            (L.concreteProperLocalRightStabilizerEmbeddingRealSlice
              (Quot.out C))) =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
        ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ)) := by
  rw [
    L.concreteProperDifferentialSelectorMassSum_eq_volume_mul_sum inst P,
    L.concreteProperSelectorInverseCardinalityENNRealSum_eq_properClassGenusMass
      inst
  ]

end PositiveDefiniteIntegralLattice
