import SMSFormula.SpecialOrthogonalRealFormCongruenceOverlapWeightedMeasure

/-!
# Target-carrier transport for explicit real-congruence overlaps

This module moves the weighted fixed-carrier target measure through the
explicit tangent equivalence.  The reciprocal rational-basis determinant
enters only through the coordinate-measure transport theorem.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realFormCongruenceOverlapTargetTransportSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realFormCongruenceOverlapTargetTransportSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance realFormCongruenceOverlapTargetTransportTargetMeasurableSpace
    (F' : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F'.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realFormCongruenceOverlapTargetTransportTargetBorelSpace
    (F' : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F'.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- The standard target identity-chart density, extended by zero to its
ambient tangent carrier. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
    (F' : Matrix (Fin n) (Fin n) ℚ)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (z : (skewAdjointMatricesLieSubalgebra
      (F'.map (algebraMap ℚ ℝ))).toSubmodule) : ENNReal :=
  Function.extend
    (Subtype.val :
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').target →
        (skewAdjointMatricesLieSubalgebra
          (F'.map (algebraMap ℚ ℝ))).toSubmodule)
    (specialFormPreservingSmoothRealChartCoordinateDensityENNReal
      F' hF' hdet' 1)
    (fun _ => 0) z

/-- Applying the tangent equivalence to the pulled-back target overlap gives
the standard target-coordinate overlap. -/
theorem image_specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    c.tangentEquiv ''
        specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
          F F' hF hdet hF' hdet' c =
      specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c :=
  image_realCrossChartAmbientTarget
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet')
    c.groupEquiv.toHomeomorph c.tangentEquiv

/-- The standard target-coordinate overlap is the explicit target identity
chart intersection representing points in the transported source chart. -/
theorem specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet_eq
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c =
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').target ∩
        (fun z =>
          c.groupEquiv.symm
            ((specialFormPreservingSmoothRealIdentityChart
              F' hF' hdet').symm z)) ⁻¹'
          (specialFormPreservingSmoothRealIdentityChart F hF hdet).source :=
  rfl

/-- The standard target density is measurable on the ambient target tangent
carrier. -/
theorem measurable_specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
    (F' : Matrix (Fin n) (Fin n) ℚ)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0) :
    Measurable
      (specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
        F' hF' hdet') := by
  exact
    (MeasurableEmbedding.subtype_coe
      (specialFormPreservingSmoothRealIdentityChart
        F' hF' hdet').open_target.measurableSet).measurable_extend
      (measurable_specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F' hF' hdet' 1)
      measurable_const

/-- The pulled-back target density is the standard target density after the
explicit tangent equivalence. -/
theorem specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity_eq_comp
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity
        F F' hF' hdet' c =
      specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
          F' hF' hdet' ∘
        c.tangentEquiv :=
  rfl

/-- The preimage of the standard target overlap is exactly the pulled-back
fixed-carrier target overlap. -/
theorem preimage_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    c.tangentEquiv ⁻¹'
        specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
          F F' hF hdet hF' hdet' c =
      specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
        F F' hF hdet hF' hdet' c := by
  rw [←
    image_specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
      F F' hF hdet hF' hdet' c]
  exact Set.preimage_image_eq _ c.tangentEquiv.injective

/-- The tangent equivalence transports the restricted coordinate measure with
the reciprocal determinant of the independently fixed rational bases. -/
theorem map_restrict_skewAdjointRealCoordinateDetMeasure_formCongruence_ambientTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map c.tangentEquiv
        ((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
            F F' hF hdet hF' hdet' c)) =
      (Real.toNNReal |c.detScalar|)⁻¹ •
        (Matrix.skewAdjointRealCoordinateDetMeasure F' 0).restrict
          (specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
            F F' hF hdet hF' hdet' c) := by
  let e := c.tangentEquiv
  let V :=
    specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
      F F' hF hdet hF' hdet' c
  let T :=
    specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
      F F' hF hdet hF' hdet' c
  let μ := Matrix.skewAdjointRealCoordinateDetMeasure F 0
  let ν := Matrix.skewAdjointRealCoordinateDetMeasure F' 0
  let q : ℝ≥0 := (Real.toNNReal |c.detScalar|)⁻¹
  have hT : MeasurableSet T :=
    (isOpen_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
      F F' hF hdet hF' hdet' c).measurableSet
  have hpre : e ⁻¹' T = V :=
    preimage_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
      F F' hF hdet hF' hdet' c
  calc
    Measure.map e (μ.restrict V) =
        Measure.map e (μ.restrict (e ⁻¹' T)) := by rw [hpre]
    _ = (Measure.map e μ).restrict T := by
      rw [Measure.restrict_map e.continuous.measurable hT]
    _ = (q • ν).restrict T := by
      rw [SpecialOrthogonalRealFormCongruenceData.map_tangentCoordinateMeasure]
    _ = q • ν.restrict T := by rw [Measure.restrict_smul]

/-- The tangent equivalence transports the weighted target measure with the
same reciprocal rational-basis determinant. -/
theorem map_withDensity_skewAdjointRealCoordinateDetMeasure_formCongruence_ambientTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map c.tangentEquiv
        (((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
            F F' hF hdet hF' hdet' c)).withDensity
          (specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity
            F F' hF' hdet' c)) =
      (Real.toNNReal |c.detScalar|)⁻¹ •
        (((Matrix.skewAdjointRealCoordinateDetMeasure F' 0).restrict
          (specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
            F F' hF hdet hF' hdet' c)).withDensity
          (specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
            F' hF' hdet')) := by
  let e := c.tangentEquiv
  let μ :=
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
      (specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
        F F' hF hdet hF' hdet' c)
  let ν :=
    (Matrix.skewAdjointRealCoordinateDetMeasure F' 0).restrict
      (specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c)
  let g :=
    specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
      F' hF' hdet'
  let q : ℝ≥0 := (Real.toNNReal |c.detScalar|)⁻¹
  rw [specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity_eq_comp]
  calc
    Measure.map e (μ.withDensity (g ∘ e)) =
        (Measure.map e μ).withDensity g :=
      map_withDensity_comp_of_measurable e μ g e.continuous.measurable
        (measurable_specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
          F' hF' hdet')
    _ = (q • ν).withDensity g := by
      rw [
        map_restrict_skewAdjointRealCoordinateDetMeasure_formCongruence_ambientTarget]
    _ = q • ν.withDensity g := by
      ext s hs
      simp [withDensity_apply, hs]

/-- Composing the weighted cross transition with the tangent equivalence lands
in the independently normalized target-form coordinate measure. -/
theorem map_withDensity_specialFormPreservingSmoothRealFormCongruenceAmbientTransition_targetCarrier
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map
        (fun x =>
          c.tangentEquiv
            (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
              F F' hF hdet hF' hdet' c x))
        (((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
            F F' hF hdet hF' hdet' c)).withDensity
          (specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
            F hF hdet)) =
      (Real.toNNReal |c.detScalar|)⁻¹ •
        (((Matrix.skewAdjointRealCoordinateDetMeasure F' 0).restrict
          (specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
            F F' hF hdet hF' hdet' c)).withDensity
          (specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
            F' hF' hdet')) := by
  let e := c.tangentEquiv
  let Ψ :=
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c
  let Ψm :=
    specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition
      F F' hF hdet hF' hdet' c
  let μ :=
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c)
  let source :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity F hF hdet
  have hU :
      MeasurableSet
        (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
          F F' hF hdet hF' hdet' c) :=
    (isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c).measurableSet
  have hΨeq : Ψm =ᵐ[μ] Ψ := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    exact
      specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition_eq
        F F' hF hdet hF' hdet' c x hx
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
        (measurable_specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition
          F F' hF hdet hF' hdet' c)]
      rfl
    _ = Measure.map e (Measure.map Ψ (μ.withDensity source)) := by
      rw [Measure.map_congr hΨeq_source]
    _ = Measure.map e
        (((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
          (specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
            F F' hF hdet hF' hdet' c)).withDensity
          (specialFormPreservingSmoothRealFormCongruenceAmbientTargetDensity
            F F' hF' hdet' c)) := by
      rw [
        map_withDensity_specialFormPreservingSmoothRealFormCongruenceAmbientTransition]
    _ = (Real.toNNReal |c.detScalar|)⁻¹ •
        (((Matrix.skewAdjointRealCoordinateDetMeasure F' 0).restrict
          (specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
            F F' hF hdet hF' hdet' c)).withDensity
          (specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
            F' hF' hdet')) :=
      map_withDensity_skewAdjointRealCoordinateDetMeasure_formCongruence_ambientTarget
        F F' hF hdet hF' hdet' c

end PositiveDefiniteIntegralLattice
