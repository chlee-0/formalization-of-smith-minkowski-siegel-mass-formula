import SMSFormula.HaarMeasureUnimodularInversion
import SMSFormula.SkewAdjointRealSpecialOrthogonalAdjointDeterminant

/-!
# Real special-orthogonal differential unimodularity

The determinant-one adjoint calculation makes conjugation preserve the
fixed-scale real differential measure.  Factoring right multiplication as
left multiplication after that conjugation proves right invariance.  The
existing regular Haar structure then supplies inversion invariance.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal Topology

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

local instance realDifferentialUnimodularGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realDifferentialUnimodularGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The explicit adjoint self-congruence is literal group conjugation. -/
theorem specialOrthogonalRealAdjointFormCongruenceData_groupEquiv_apply
    (F : Matrix (Fin n) (Fin n) ℚ)
    (g x : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    (specialOrthogonalRealAdjointFormCongruenceData F g).groupEquiv x =
      g⁻¹ * x * g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rfl

/-- Right multiplication factors through the measure-preserving adjoint
self-congruence followed by left multiplication. -/
theorem specialOrthogonalReal_mulRight_eq_mulLeft_comp_adjoint
    (F : Matrix (Fin n) (Fin n) ℚ)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    (Homeomorph.mulRight g :
        specialFormPreservingMatrixSubgroup
            (F.map (algebraMap ℚ ℝ)) →
          specialFormPreservingMatrixSubgroup
            (F.map (algebraMap ℚ ℝ))) =
      Homeomorph.mulLeft g ∘
        (specialOrthogonalRealAdjointFormCongruenceData F g).groupEquiv := by
  funext x
  change x * g =
    g * (specialOrthogonalRealAdjointFormCongruenceData F g).groupEquiv x
  rw [specialOrthogonalRealAdjointFormCongruenceData_groupEquiv_apply]
  group

/-- The real invariant-differential measure is invariant under every right
translation. -/
theorem map_specialFormPreservingSmoothRealDifferentialMeasure_mul_right
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    Measure.map (Homeomorph.mulRight g)
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) =
      specialFormPreservingSmoothRealDifferentialMeasure F hF hdet := by
  let C :=
    (specialOrthogonalRealAdjointFormCongruenceData F g).groupEquiv.toHomeomorph
  let L := Homeomorph.mulLeft g
  let μ := specialFormPreservingSmoothRealDifferentialMeasure F hF hdet
  rw [specialOrthogonalReal_mulRight_eq_mulLeft_comp_adjoint F g]
  change Measure.map (L ∘ C) μ = μ
  rw [← Measure.map_map L.continuous.measurable C.continuous.measurable]
  rw [map_specialFormPreservingSmoothRealDifferentialMeasure_adjoint
    F hF hdet g]
  exact map_specialFormPreservingSmoothRealDifferentialMeasure_mul_left
    F hF hdet g

/-- Right invariance is installed at the actual real differential scale. -/
instance specialFormPreservingSmoothRealDifferentialMeasure_isMulRightInvariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Measure.IsMulRightInvariant
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) where
  map_mul_right_eq_self g := by
    simpa only [Homeomorph.coe_mulRight] using
      map_specialFormPreservingSmoothRealDifferentialMeasure_mul_right
        F hF hdet g

/-- The real invariant-differential measure is invariant under inversion. -/
theorem specialFormPreservingSmoothRealDifferentialMeasure_isInvInvariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Measure.IsInvInvariant
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) := by
  let μ := specialFormPreservingSmoothRealDifferentialMeasure F hF hdet
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_locallyCompact F hF hdet
  letI : Measure.IsHaarMeasure μ :=
    specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
      F hF hdet
  letI : Measure.IsMulRightInvariant μ :=
    specialFormPreservingSmoothRealDifferentialMeasure_isMulRightInvariant
      F hF hdet
  letI : Measure.Regular μ :=
    specialFormPreservingSmoothRealDifferentialMeasure_regular F hF hdet
  exact Measure.isInvInvariant_of_isMulRightInvariant_of_regular μ

/-- Inversion invariance is installed for full-adelic product transport. -/
instance specialFormPreservingSmoothRealDifferentialMeasure_instInvInvariant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Measure.IsInvInvariant
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) :=
  specialFormPreservingSmoothRealDifferentialMeasure_isInvInvariant
    F hF hdet

end PositiveDefiniteIntegralLattice
