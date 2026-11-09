import SMSFormula.SpecialOrthogonalRealCongruenceOverlapChangeOfVariables

/-!
# Ambient density functions for real congruence chart overlaps

The chart densities live on open coordinate-target subtypes.  This
module extends them measurably by zero to the fixed source tangent carrier so
they can be used with the ambient restricted change-of-variables theorem.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceOverlapAmbientDensityMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceOverlapAmbientDensityBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- The source identity-chart density, extended by zero from its open target
to the ambient source tangent carrier. -/
def specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) : ENNReal :=
  Function.extend
    (Subtype.val :
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target →
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F hF hdet 1)
    (fun _ => 0) x

/-- The independently chosen target identity-chart density, extended by
zero and pulled back through tangent congruence to the fixed source carrier. -/
def specialFormPreservingSmoothRealCongruenceAmbientTargetDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (z : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) : ENNReal :=
  Function.extend
    (Subtype.val :
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target →
      (skewAdjointMatricesLieSubalgebra
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule)
    (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1)
    (fun _ => 0)
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W z)

/-- The ambient source density is measurable. -/
theorem measurable_specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    Measurable
      (specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
        F hF hdet) := by
  exact
    (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealIdentityChart
        F hF hdet).open_target.measurableSet).measurable_extend
      (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet 1)
      measurable_const

/-- The ambient target density is measurable. -/
theorem measurable_specialFormPreservingSmoothRealCongruenceAmbientTargetDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measurable
      (specialFormPreservingSmoothRealCongruenceAmbientTargetDensity
        F hF hdet W) := by
  apply Measurable.comp _ (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
    F W).continuous.measurable
  exact
    (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).open_target.measurableSet).measurable_extend
      (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1)
      measurable_const

/-- On the identity-chart target, the ambient source density is the
subtype density. -/
theorem specialFormPreservingSmoothRealCongruenceAmbientSourceDensity_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target) :
    specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
        F hF hdet x =
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet 1 ⟨x, hx⟩ := by
  exact Function.Injective.extend_apply Subtype.val_injective _ _ ⟨x, hx⟩

/-- On the pulled-back target chart, the ambient target density is the
target-form subtype density. -/
theorem specialFormPreservingSmoothRealCongruenceAmbientTargetDensity_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (z : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hz :
      Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W z ∈
        (specialFormPreservingSmoothRealIdentityChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target) :
    specialFormPreservingSmoothRealCongruenceAmbientTargetDensity
        F hF hdet W z =
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
        ⟨Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W z,
          hz⟩ := by
  exact Function.Injective.extend_apply Subtype.val_injective _ _ ⟨_, hz⟩

end PositiveDefiniteIntegralLattice
