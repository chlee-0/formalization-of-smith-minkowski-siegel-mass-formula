import SMSFormula.PadicCayleyTranslatedChartTopology
import SMSFormula.PadicCayleyHomeomorph
import SMSFormula.PadicCayleyCoordinateJacobianDensityENNRealPositive
import SMSFormula.PadicCayleyDomainOpenness
import Mathlib.MeasureTheory.Measure.Regular
import SMSFormula.PadicCayleyTargetChartMeasureFullSupport
import SMSFormula.PadicCayleyTargetChartJacobianFormula

/-!
# Explicit Jacobian densities on translated p-adic Cayley charts

The identity-target Jacobian is pulled first through the inverse
matrix-carrier/subgroup bridge and then through inverse left translation.
This gives a continuous strictly positive density on every exact translated
target.  The translated weighted measure is exactly the translated coordinate
measure weighted by this density, and reciprocal weighting recovers the
coordinate measure.

For symmetric nonsingular forms the density is evaluated as

`‖2‖₊^(n.choose 2) * ‖det(c⁻¹g + 1)‖₊⁻¹^(n-1)`,

with the corresponding odd-prime and dyadic specializations.  All statements
remain on exact chart subtypes; no full-group measure, invariance, overlap
comparison, or chart gluing is introduced.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyTranslatedJacobianMatrixCarrierMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (Matrix.specialOrthogonalMatrixSet
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTranslatedJacobianMatrixCarrierBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (Matrix.specialOrthogonalMatrixSet
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

local instance padicCayleyTranslatedJacobianSubgroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTranslatedJacobianSubgroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The Jacobian density on the exact Cayley target translated around `c`,
obtained by evaluating the identity-target density after inverse
left translation and inverse transport through the subgroup bridge. -/
def padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (g : padicCayleySpecialOrthogonalTranslatedTarget F p c) : ℝ≥0∞ :=
  Matrix.padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
    p n F hF
      ((padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph
        F p).symm
        ((padicCayleySpecialOrthogonalLeftTranslateHomeomorph
          F p c).symm g))

/-- The translated-target Jacobian density is continuous. -/
theorem
    continuous_padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Continuous
      (padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
        p n F hF c) := by
  exact
    (Matrix.continuous_padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal
      p n F hF).comp
      ((padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph
        F p).symm.continuous.comp
        (padicCayleySpecialOrthogonalLeftTranslateHomeomorph
          F p c).symm.continuous)

/-- The translated-target Jacobian density is measurable. -/
theorem
    measurable_padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measurable
      (padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
        p n F hF c) :=
  (continuous_padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
    p n F hF c).measurable

/-- The translated-target Jacobian density is strictly positive. -/
theorem
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_pos
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (g : padicCayleySpecialOrthogonalTranslatedTarget F p c) :
    0 <
      padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
        p n F hF c g := by
  exact
    Matrix.padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_pos
      p n F hF _

/-- For a symmetric nonsingular form, the translated Jacobian density is the
closed determinant formula in inverse-translated target coordinates. -/
theorem
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (g : padicCayleySpecialOrthogonalTranslatedTarget F p c) :
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
        p n F hF c g =
      ((‖(2 : ℚ_[p])‖₊ ^ (n.choose 2) *
          ‖Matrix.det
            ((((c⁻¹ * g.1).1.1.1 :
                Matrix (Fin n) (Fin n) ℚ_[p]) + 1))‖₊⁻¹ ^ (n - 1) :
        ℝ≥0) : ℝ≥0∞) := by
  simpa only [
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal,
    coe_padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph_symm_apply,
    coe_padicCayleySpecialOrthogonalLeftTranslateHomeomorph_symm_apply] using
    Matrix.padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_eq
      p n F hFsymm hF
        ((padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph
          F p).symm
          ((padicCayleySpecialOrthogonalLeftTranslateHomeomorph
            F p c).symm g))

/-- At an odd prime, the translated density has only the
inverse-`c⁻¹g + 1` determinant factor. -/
theorem
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_eq_of_ne_two
    (hp_two : p ≠ 2)
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (g : padicCayleySpecialOrthogonalTranslatedTarget F p c) :
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
        p n F hF c g =
      ((‖Matrix.det
          ((((c⁻¹ * g.1).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[p]) + 1))‖₊⁻¹ ^ (n - 1) :
        ℝ≥0) : ℝ≥0∞) := by
  simpa only [
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal,
    coe_padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph_symm_apply,
    coe_padicCayleySpecialOrthogonalLeftTranslateHomeomorph_symm_apply] using
    Matrix.padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_eq_of_ne_two
      p n hp_two F hFsymm hF
        ((padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph
          F p).symm
          ((padicCayleySpecialOrthogonalLeftTranslateHomeomorph
            F p c).symm g))

/-- At the dyadic place, the translated density retains
`(2⁻¹)^(n.choose 2)`. -/
theorem
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal_eq_two
    (F : Matrix (Fin n) (Fin n) ℚ) (hFsymm : F.IsSymm)
    (hF : F.det ≠ 0)
    (c : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[2])))
    (g : padicCayleySpecialOrthogonalTranslatedTarget F 2 c) :
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal
        2 n F hF c g =
      ((((2 : ℝ≥0)⁻¹) ^ (n.choose 2) *
          ‖Matrix.det
            ((((c⁻¹ * g.1).1.1.1 :
                Matrix (Fin n) (Fin n) ℚ_[2]) + 1))‖₊⁻¹ ^ (n - 1) :
        ℝ≥0) : ℝ≥0∞) := by
  simpa only [
    padicCayleySpecialOrthogonalTranslatedTargetJacobianDensityENNReal,
    coe_padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph_symm_apply,
    coe_padicCayleySpecialOrthogonalLeftTranslateHomeomorph_symm_apply] using
    Matrix.padicCayleySpecialOrthogonalInverseDomainJacobianDensityENNReal_eq_two
      n F hFsymm hF
        ((padicCayleySpecialOrthogonalSubgroupInverseDomainHomeomorph
          F 2).symm
          ((padicCayleySpecialOrthogonalLeftTranslateHomeomorph
            F 2 c).symm g))

end PositiveDefiniteIntegralLattice
