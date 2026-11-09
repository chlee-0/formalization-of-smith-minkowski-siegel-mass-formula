import SMSFormula.SpecialOrthogonalRealCongruenceOverlapWeightedMeasure

/-!
# Target-carrier transport for weighted real congruence overlaps

This module moves the weighted ambient target measure from the fixed source
tangent carrier through tangent congruence.  The reciprocal rational-basis
determinant enters only through the coordinate-measure transport theorem.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceOverlapTargetTransportSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceOverlapTargetTransportSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance realCongruenceOverlapTargetTransportTargetMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceOverlapTargetTransportTargetBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- The standard target-coordinate overlap as an ambient target tangent set. -/
def specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set ((skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule) :=
  Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W ''
    specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
      F hF hdet W

/-- The standard target identity-chart density, extended by zero to its
ambient tangent carrier. -/
def specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (z : (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule) : ENNReal :=
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
    (fun _ => 0) z

/-- The standard ambient target overlap is open. -/
theorem isOpen_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    IsOpen
      (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W) :=
  (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
    F W).toHomeomorph.isOpenMap _
      (isOpen_specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
        F hF hdet W)

/-- The standard ambient target overlap is measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    MeasurableSet
      (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W) :=
  (isOpen_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
    F hF hdet W).measurableSet

/-- The standard ambient target overlap is the explicit intersection on which
the target identity chart represents a point in the transported chart source. -/
theorem specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W =
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target ∩
        (fun z =>
          (specialFormPreservingRealCongruenceContinuousMulEquiv
            F W).symm
            ((specialFormPreservingSmoothRealIdentityChart
              (Matrix.skewAdjointCongruenceForm F W)
              (skewAdjointCongruenceForm_isSymm F hF W)
              (skewAdjointCongruenceForm_det_ne_zero F hdet W)).symm z)) ⁻¹'
          (specialFormPreservingSmoothRealIdentityChart F hF hdet).source := by
  exact
    image_realCrossChartAmbientTarget
      (specialFormPreservingSmoothRealIdentityChart F hF hdet)
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W))
      (specialFormPreservingRealCongruenceContinuousMulEquiv
        F W).toHomeomorph
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W)

/-- The standard target density is measurable on the ambient target tangent
carrier. -/
theorem measurable_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measurable
      (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
        F hF hdet W) := by
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

/-- The pulled-back ambient target density is definitionally the standard
target density after tangent congruence. -/
theorem specialFormPreservingSmoothRealCongruenceAmbientTargetDensity_eq_comp
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceAmbientTargetDensity
        F hF hdet W =
      specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
          F hF hdet W ∘
        Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W :=
  rfl

/-- The inverse image of the standard target overlap under tangent congruence
is the fixed-carrier ambient target overlap. -/
theorem preimage_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W ⁻¹'
        specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
          F hF hdet W =
      specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
        F hF hdet W := by
  exact Set.preimage_image_eq _
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).injective

/-- Tangent congruence transports the restricted coordinate measure with the
explicit reciprocal rational-basis determinant. -/
theorem map_restrict_skewAdjointRealCoordinateDetMeasure_congruence_ambientTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W)
        ((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
            F hF hdet W)) =
      (Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        (Matrix.skewAdjointRealCoordinateDetMeasure
          (Matrix.skewAdjointCongruenceForm F W) 0).restrict
            (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
              F hF hdet W) := by
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  let V :=
    specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
      F hF hdet W
  let T :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
      F hF hdet W
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  let ν := Matrix.skewAdjointRealCoordinateDetMeasure
    (Matrix.skewAdjointCongruenceForm F W) 0
  let c : ℝ≥0 := (Real.toNNReal
    |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹
  have hT : MeasurableSet T :=
    measurableSet_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
      F hF hdet W
  have hpre : e ⁻¹' T = V :=
    preimage_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
      F hF hdet W
  calc
    Measure.map e (μ.restrict V) =
        Measure.map e (μ.restrict (e ⁻¹' T)) := by rw [hpre]
    _ = (Measure.map e μ).restrict T := by
      rw [Measure.restrict_map e.continuous.measurable hT]
    _ = (c • ν).restrict T := by
      rw [Matrix.map_skewAdjointRealCoordinateDetMeasure_congruence]
    _ = c • ν.restrict T := by rw [Measure.restrict_smul]

/-- Tangent congruence transports the weighted ambient target measure to the
independently normalized target-form coordinate measure with the same explicit
reciprocal basis determinant. -/
theorem map_withDensity_skewAdjointRealCoordinateDetMeasure_congruence_ambientTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W)
        (((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
            F hF hdet W)).withDensity
          (specialFormPreservingSmoothRealCongruenceAmbientTargetDensity
            F hF hdet W)) =
      (Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        (((Matrix.skewAdjointRealCoordinateDetMeasure
          (Matrix.skewAdjointCongruenceForm F W) 0).restrict
            (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
              F hF hdet W)).withDensity
          (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
            F hF hdet W)) := by
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  let μ :=
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
      (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
        F hF hdet W)
  let ν :=
    (Matrix.skewAdjointRealCoordinateDetMeasure
      (Matrix.skewAdjointCongruenceForm F W) 0).restrict
        (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
          F hF hdet W)
  let g :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
      F hF hdet W
  let c : ℝ≥0 := (Real.toNNReal
    |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹
  rw [specialFormPreservingSmoothRealCongruenceAmbientTargetDensity_eq_comp]
  calc
    Measure.map e (μ.withDensity (g ∘ e)) =
        (Measure.map e μ).withDensity g :=
      map_withDensity_comp_of_measurable e μ g e.continuous.measurable
        (measurable_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
          F hF hdet W)
    _ = (c • ν).withDensity g := by
      rw [map_restrict_skewAdjointRealCoordinateDetMeasure_congruence_ambientTarget]
    _ = c • ν.withDensity g := by
      ext s hs
      simp [withDensity_apply, hs]

/-- Composing the weighted cross-form transition with tangent congruence
lands in the independently normalized target-form coordinate measure. -/
theorem map_withDensity_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition_targetCarrier
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (fun x =>
          Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
            (specialFormPreservingSmoothRealCongruenceChartSourceTransition
              F hF hdet W x))
        (((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
            F hF hdet W)).withDensity
          (specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
            F hF hdet)) =
      (Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        (((Matrix.skewAdjointRealCoordinateDetMeasure
          (Matrix.skewAdjointCongruenceForm F W) 0).restrict
            (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
              F hF hdet W)).withDensity
          (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
            F hF hdet W)) := by
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  let Ψ :=
    specialFormPreservingSmoothRealCongruenceChartSourceTransition
      F hF hdet W
  let Ψm :=
    specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition
      F hF hdet W
  let μ :=
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W)
  let source :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceDensity F hF hdet
  have hU :
      MeasurableSet
        (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
          F hF hdet W) :=
    measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
      F hF hdet W
  have hΨeq : Ψm =ᵐ[μ] Ψ := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    exact
      specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition_eq
        F hF hdet W x hx
  have hΨeq_source : Ψm =ᵐ[μ.withDensity source] Ψ :=
    (withDensity_absolutelyContinuous μ source).ae_eq hΨeq
  calc
    Measure.map (fun x => e (Ψ x)) (μ.withDensity source) =
        Measure.map (fun x => e (Ψm x)) (μ.withDensity source) := by
      apply Measure.map_congr
      filter_upwards [hΨeq_source] with x hx
      rw [hx]
    _ = Measure.map e (Measure.map Ψm (μ.withDensity source)) := by
      rw [Measure.map_map e.continuous.measurable
        (measurable_specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition
          F hF hdet W)]
      rfl
    _ = Measure.map e (Measure.map Ψ (μ.withDensity source)) := by
      rw [Measure.map_congr hΨeq_source]
    _ = Measure.map e
        (((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealCongruenceAmbientTargetOverlapSet
            F hF hdet W)).withDensity
          (specialFormPreservingSmoothRealCongruenceAmbientTargetDensity
            F hF hdet W)) := by
      rw [map_withDensity_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition]
    _ = (Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        (((Matrix.skewAdjointRealCoordinateDetMeasure
          (Matrix.skewAdjointCongruenceForm F W) 0).restrict
            (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
              F hF hdet W)).withDensity
          (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
            F hF hdet W)) :=
      map_withDensity_skewAdjointRealCoordinateDetMeasure_congruence_ambientTarget
        F hF hdet W

end PositiveDefiniteIntegralLattice
