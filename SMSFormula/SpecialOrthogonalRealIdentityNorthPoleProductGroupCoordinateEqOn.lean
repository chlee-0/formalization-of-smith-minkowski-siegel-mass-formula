import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductGroup

/-!
# Exact-source-set product-group coordinate comparison

This small layer packages the exact-source pointwise comparison between the
measurable transition coordinate and the higher coordinate of the actual
group product as `Set.EqOn`. The almost-everywhere restriction step remains
separate.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductGroupCoordinateEqOnMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductGroupCoordinateEqOnMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductGroupCoordinateEqOnGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductGroupCoordinateEqOnGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The transition after lower source coordinates and the higher coordinate
after the actual group product agree on the exact source set. -/
theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableTransition_lowerSourceAmbient_eqOn_higherCoordinate_lowerGroup
    (n : ℕ) :
    Set.EqOn
      (fun p =>
        identitySpecialOrthogonalNorthPoleProductMeasurableTransition n
          (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
            n p))
      (fun p =>
        identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n
          (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n p))
      (identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        n) := by
  intro p hp
  exact
    identitySpecialOrthogonalNorthPoleProductMeasurableTransition_lowerSourceAmbient_eq
      n p hp

end PositiveDefiniteIntegralLattice
