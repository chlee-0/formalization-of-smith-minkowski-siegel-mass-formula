import SMSFormula.SpecialOrthogonalRealCongruenceChart

/-!
# Overlap of transported and standard real congruence charts

For `F' = Wᵀ F W`, this module compares the transported cross-form chart on
`SO(F')(ℝ)` with the independently selected identity chart for `F'`. It
defines their exact same-point group overlap, both coordinate images, and the
transition homeomorphism between those images.

All commutation statements are pointwise. No equality of functions between
nested dependent subtypes is packaged.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator ContDiff

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceOverlapGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realCongruenceOverlapGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance realCongruenceOverlapTangentMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceOverlapTangentBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- The target-form identity chart with its exact source and target. -/
def specialFormPreservingSmoothRealCongruenceTargetIdentityChartHomeomorph
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source ≃ₜ
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target :=
  (specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)).toHomeomorphSourceTarget

/-- The exact same-point intersection of the transported chart source and
the independently selected target-form identity chart source. -/
def specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set (specialFormPreservingMatrixSubgroup
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))) :=
  specialFormPreservingSmoothRealCongruenceChartSourceSet F hF hdet W ∩
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source

/-- The common group-overlap subtype. -/
abbrev specialFormPreservingSmoothRealCongruenceChartGroupOverlap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :=
  specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet F hF hdet W

/-- The common group overlap is open. -/
theorem isOpen_specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    IsOpen
      (specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
        F hF hdet W) :=
  (isOpen_specialFormPreservingSmoothRealCongruenceChartSourceSet
    F hF hdet W).inter
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).open_source

/-- Transported coordinates whose represented target-group point also lies in
the independently selected target-form identity chart. -/
def specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set (specialFormPreservingSmoothRealCongruenceChartTarget
      F hF hdet W) :=
  (fun y =>
    ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
      F hF hdet W).symm y).1) ⁻¹'
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source

/-- Standard target-form identity coordinates whose represented group point
also lies in the transported chart source. -/
def specialFormPreservingSmoothRealCongruenceChartStandardCoordinateOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target :=
  (fun z =>
    ((specialFormPreservingSmoothRealCongruenceTargetIdentityChartHomeomorph
      F hF hdet W).symm z).1) ⁻¹'
    specialFormPreservingSmoothRealCongruenceChartSourceSet F hF hdet W

/-- The transported-coordinate overlap subtype. -/
abbrev specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :=
  specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
    F hF hdet W

/-- The standard-coordinate overlap subtype. -/
abbrev specialFormPreservingSmoothRealCongruenceChartStandardCoordinateOverlap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :=
  specialFormPreservingSmoothRealCongruenceChartStandardCoordinateOverlapSet
    F hF hdet W

/-- The transported-coordinate overlap is open. -/
theorem isOpen_specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    IsOpen
      (specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :=
  (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).open_source.preimage
    (continuous_subtype_val.comp
      (specialFormPreservingSmoothRealCongruenceChartHomeomorph
        F hF hdet W).symm.continuous)

/-- The standard-coordinate overlap is open. -/
theorem isOpen_specialFormPreservingSmoothRealCongruenceChartStandardCoordinateOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    IsOpen
      (specialFormPreservingSmoothRealCongruenceChartStandardCoordinateOverlapSet
        F hF hdet W) :=
  (isOpen_specialFormPreservingSmoothRealCongruenceChartSourceSet
    F hF hdet W).preimage
      (continuous_subtype_val.comp
        (specialFormPreservingSmoothRealCongruenceTargetIdentityChartHomeomorph
          F hF hdet W).symm.continuous)

/-- Common group points expressed in transported coordinates. -/
def specialFormPreservingSmoothRealCongruenceChartGroupOverlapToTransported
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartGroupOverlap
        F hF hdet W ≃ₜ
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlap
        F hF hdet W where
  toFun x := ⟨
    specialFormPreservingSmoothRealCongruenceChartHomeomorph
      F hF hdet W ⟨x.1, x.2.1⟩,
    by
      change
        ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
          F hF hdet W).symm
            (specialFormPreservingSmoothRealCongruenceChartHomeomorph
              F hF hdet W ⟨x.1, x.2.1⟩)).1 ∈
          (specialFormPreservingSmoothRealIdentityChart
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source
      rw [(specialFormPreservingSmoothRealCongruenceChartHomeomorph
        F hF hdet W).symm_apply_apply]
      exact x.2.2⟩
  invFun y := ⟨
    ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
      F hF hdet W).symm y.1).1,
    ⟨((specialFormPreservingSmoothRealCongruenceChartHomeomorph
      F hF hdet W).symm y.1).2, y.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    change
      ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
        F hF hdet W).symm
          (specialFormPreservingSmoothRealCongruenceChartHomeomorph
            F hF hdet W ⟨x.1, x.2.1⟩)).1 = x.1
    exact congrArg Subtype.val
      ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
        F hF hdet W).symm_apply_apply ⟨x.1, x.2.1⟩)
  right_inv y := by
    apply Subtype.ext
    exact
      (specialFormPreservingSmoothRealCongruenceChartHomeomorph
        F hF hdet W).apply_symm_apply y.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      (specialFormPreservingSmoothRealCongruenceChartHomeomorph
        F hF hdet W).continuous.comp
        (continuous_subtype_val.subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
        F hF hdet W).symm.continuous.comp continuous_subtype_val)

/-- The ambient target-form identity coordinate of a transported coordinate.
On the exact overlap this lies in the target of the target chart. -/
def specialFormPreservingSmoothRealCongruenceChartAmbientTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W) :
    (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule :=
  specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
    ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
      F hF hdet W).symm y).1

/-- On the exact overlap, the ambient transition belongs to the target
of the target identity chart. -/
theorem specialFormPreservingSmoothRealCongruenceChartAmbientTransition_mem_target
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy :
      y ∈ specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceChartAmbientTransition
        F hF hdet W y ∈
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target :=
  (specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)).map_source hy

/-- The ambient transition and transported coordinate represent the same
target-group point, pointwise on the exact overlap. -/
theorem specialFormPreservingSmoothRealCongruenceChartAmbientTransition_samePoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W)
    (hy :
      y ∈ specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).symm
        (specialFormPreservingSmoothRealCongruenceChartAmbientTransition
          F hF hdet W y) =
      ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
        F hF hdet W).symm y).1 := by
  exact
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).left_inv hy

/-- The ambient transition is continuous on the exact transported-coordinate
overlap. -/
theorem continuousOn_specialFormPreservingSmoothRealCongruenceChartAmbientTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    ContinuousOn
      (specialFormPreservingSmoothRealCongruenceChartAmbientTransition
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) := by
  exact
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).continuousOn.comp
        ((continuous_subtype_val.comp
          (specialFormPreservingSmoothRealCongruenceChartHomeomorph
            F hF hdet W).symm.continuous).continuousOn)
        (fun _ hy => hy)

end PositiveDefiniteIntegralLattice
