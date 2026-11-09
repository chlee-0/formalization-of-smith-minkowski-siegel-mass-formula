import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductGroupCoordinateEqOn

/-!
# Restricted almost-everywhere product-group coordinate comparison

This layer combines the opaque exact-set comparison with the generic fact
that a restricted measure is almost everywhere supported on its restricting
measurable set.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleProductGroupCoordinateRestrictedAEMappedTangentMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalMappedTangent n) :=
  borel _

local instance identityNorthPoleProductGroupCoordinateRestrictedAEMappedTangentBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalMappedTangent n) :=
  ⟨rfl⟩

local instance identityNorthPoleProductGroupCoordinateRestrictedAEGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  borel _

local instance identityNorthPoleProductGroupCoordinateRestrictedAEGroupBorelSpace
    (n : ℕ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((1 : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

theorem
    identitySpecialOrthogonalNorthPoleProductMeasurableTransition_lowerSourceAmbient_ae_eq_higherCoordinate_lowerGroup
    (n : ℕ) :
    (fun p =>
        identitySpecialOrthogonalNorthPoleProductMeasurableTransition n
          (identitySpecialOrthogonalNorthPoleProductLowerSourceAmbientCoordinate
            n p)) =ᵐ[
        identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure
          n]
      (fun p =>
        identitySpecialOrthogonalNorthPoleProductMeasurableHigherChartCoordinate
          n
          (identitySpecialOrthogonalNorthPoleProductMeasurableLowerGroup n p)) := by
  rw [
    identitySpecialOrthogonalNorthPoleProductRestrictedLowerDifferentialSphereMeasure]
  exact
    (MeasureTheory.ae_restrict_mem
      (measurableSet_identitySpecialOrthogonalNorthPoleProductLowerDifferentialSphereSourceSet
        n)).mono
      (identitySpecialOrthogonalNorthPoleProductMeasurableTransition_lowerSourceAmbient_eqOn_higherCoordinate_lowerGroup
        n)

end PositiveDefiniteIntegralLattice
