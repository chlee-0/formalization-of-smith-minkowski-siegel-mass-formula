import SMSFormula.SpecialOrthogonalFullAdelicProperPieceAmbientIdentification
import SMSFormula.SpecialOrthogonalFiniteAdelicDifferentialSelectorMassSum

/-!
# Differential volume of the full-adelic proper domain

The measurable, pairwise-disjoint proper pieces are identified with the
restrictions of the internally constructed ambient differential Haar measure.
Finite additivity therefore expresses the proper-domain volume as the sum of
their transported source-product masses.  Factoring the literal real
differential total mass and applying the already proved finite selector sum
gives the exact real-times-finite-times-proper-mass formula.

The real differential mass, finite differential stabilizer volume, and proper
class genus mass remain literal.  No reference Haar comparison, Tamagawa
specialization, or rational tangent-basis specialization occurs here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The ambient differential mass of the lifted proper domain is the finite
sum of the transported differential masses of its disjoint proper pieces. -/
theorem
    fullAdelicSpecialOrthogonalDifferentialMeasure_properTransversal_eq_sum_piece
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        L.concreteFullAdelicProperTransversal =
      @Finset.sum L.ConcreteProperRationalDoubleCosetSet ℝ≥0∞ _
        (@Finset.univ L.ConcreteProperRationalDoubleCosetSet inst)
        (fun C =>
          L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C
            Set.univ) := by
  letI : Fintype L.ConcreteProperRationalDoubleCosetSet := inst
  calc
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        L.concreteFullAdelicProperTransversal =
      L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        (⋃ C : L.ConcreteProperRationalDoubleCosetSet,
          L.concreteFullAdelicProperTransversalPiece C) := by
            rw [L.iUnion_concreteFullAdelicProperTransversalPiece]
    _ =
        ∑' C : L.ConcreteProperRationalDoubleCosetSet,
          L.fullAdelicSpecialOrthogonalDifferentialMeasure P
            (L.concreteFullAdelicProperTransversalPiece C) := by
      exact measure_iUnion
        (fun C D hCD =>
          L.pairwiseDisjoint_concreteFullAdelicProperTransversalPiece hCD)
        (fun C =>
          L.concreteFullAdelicProperTransversalPiece_measurableSet C)
    _ =
        ∑ C : L.ConcreteProperRationalDoubleCosetSet,
          L.fullAdelicSpecialOrthogonalDifferentialMeasure P
            (L.concreteFullAdelicProperTransversalPiece C) := by
      rw [tsum_fintype]
    _ =
        ∑ C : L.ConcreteProperRationalDoubleCosetSet,
          ((L.fullAdelicSpecialOrthogonalDifferentialMeasure P).restrict
            (L.concreteFullAdelicProperTransversalPiece C)) Set.univ := by
      apply Finset.sum_congr rfl
      intro C _
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    _ =
        ∑ C : L.ConcreteProperRationalDoubleCosetSet,
          L.concreteFullAdelicProperTransversalPieceDifferentialMeasure P C
            Set.univ := by
      apply Finset.sum_congr rfl
      intro C _
      rw [
        L.concreteFullAdelicProperTransversalPieceDifferentialMeasure_eq_restrict_ambient
          hP C
      ]

/-- After expanding the transported source-product mass of every piece, the
proper-domain differential volume factors as the real differential total mass
times the finite sum of the literal finite selector masses. -/
theorem
    fullAdelicSpecialOrthogonalDifferentialMeasure_properTransversal_eq_real_mul_selector_sum
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        L.concreteFullAdelicProperTransversal =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        @Finset.sum L.ConcreteProperRationalDoubleCosetSet ℝ≥0∞ _
          (@Finset.univ L.ConcreteProperRationalDoubleCosetSet inst)
          (fun C =>
            L.finiteAdelicSpecialOrthogonalDifferentialStabilizerMeasure P
              (L.concreteProperLocalRightStabilizerEmbeddingRealSlice
                (Quot.out C))) := by
  letI : Fintype L.ConcreteProperRationalDoubleCosetSet := inst
  rw [
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_properTransversal_eq_sum_piece
      inst hP
  ]
  simp_rw [
    L.concreteFullAdelicProperTransversalPieceDifferentialMeasure_univ_eq_real_mul_selector
      hP
  ]
  rw [Finset.mul_sum]

/-- The exact internally normalized differential volume of the lifted
full-adelic proper domain: real differential mass times finite differential
stabilizer volume times proper class genus mass. -/
theorem
    fullAdelicSpecialOrthogonalDifferentialMeasure_properTransversal_eq_real_mul_finiteVolume_mul_properClassGenusMass
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    L.fullAdelicSpecialOrthogonalDifferentialMeasure P
        L.concreteFullAdelicProperTransversal =
      L.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ *
        (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
          ENNReal.ofReal (((L.properClassGenusMass : ℚ) : ℝ))) := by
  rw [
    L.fullAdelicSpecialOrthogonalDifferentialMeasure_properTransversal_eq_real_mul_selector_sum
      inst hP,
    L.concreteProperDifferentialSelectorMassSum_eq_volume_mul_properClassGenusMass
      inst P
  ]

end PositiveDefiniteIntegralLattice
