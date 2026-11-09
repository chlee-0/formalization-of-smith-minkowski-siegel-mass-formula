import SMSFormula.SpecialOrthogonalRealCongruenceOverlapTargetTransport

/-!
# Common-group transport for real congruence overlaps

This module specializes the generic ambient overlap homeomorphisms to a real
special-orthogonal congruence.  Both ambient coordinate overlaps are sent to
the same exact group subtype, without constructing a homeomorphism between
the nested coordinate-overlap subtypes.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- If a coordinate change is the composite of two identifications with a
common carrier, its measure transport immediately compares the two induced
measures on that carrier. -/
theorem map_left_eq_smul_map_right_of_map_trans_symm
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (S : α ≃ᵐ β) (R : γ ≃ᵐ β)
    (μ : Measure α) (ν : Measure γ) (c : ℝ≥0)
    (hmap : Measure.map (S.trans R.symm) μ = c • ν) :
    Measure.map S μ = c • Measure.map R ν := by
  calc
    Measure.map S μ =
        Measure.map R (Measure.map (S.trans R.symm) μ) := by
      rw [Measure.map_map R.measurable (S.trans R.symm).measurable]
      apply Measure.map_congr
      filter_upwards [] with x
      exact (R.apply_symm_apply (S x)).symm
    _ = Measure.map R (c • ν) := by rw [hmap]
    _ = c • Measure.map R ν := by rw [Measure.map_smul]

local instance realCongruenceOverlapGroupTransportSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceOverlapGroupTransportSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance realCongruenceOverlapGroupTransportTargetMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realCongruenceOverlapGroupTransportTargetBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance realCongruenceOverlapGroupTransportGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))) :=
  borel _

local instance realCongruenceOverlapGroupTransportGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The generic common group overlap is definitionally the
transported/standard group intersection. -/
theorem realCrossChartAmbientGroupOverlap_eq_specialFormPreservingSmoothRealCongruence
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    realCrossChartAmbientGroupOverlap
        (specialFormPreservingSmoothRealIdentityChart F hF hdet)
        (specialFormPreservingSmoothRealIdentityChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W))
        (specialFormPreservingRealCongruenceContinuousMulEquiv
          F W).toHomeomorph =
      specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
        F hF hdet W :=
  rfl

/-- Fixed-source ambient coordinates mapped to their represented point in the
common target-group overlap. -/
def specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapToGroup
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W ≃ₜ
      specialFormPreservingSmoothRealCongruenceChartGroupOverlap
        F hF hdet W :=
  realCrossChartAmbientSourceToGroup
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W))
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph

/-- Standard target ambient coordinates mapped back to their represented
point in the common target-group overlap. -/
def specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapToGroup
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W ≃ₜ
      specialFormPreservingSmoothRealCongruenceChartGroupOverlap
        F hF hdet W :=
  (Homeomorph.setCongr
    (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet_eq
      F hF hdet W)).trans
    (realCrossChartAmbientTargetRangeToGroup
      (specialFormPreservingSmoothRealIdentityChart F hF hdet)
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W))
      (specialFormPreservingRealCongruenceContinuousMulEquiv
        F W).toHomeomorph)

/-- The source overlap homeomorphism is group congruence after the source
identity-chart inverse. -/
theorem coe_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapToGroup
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
      F hF hdet W) :
    (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapToGroup
      F hF hdet W x).1 =
      specialFormPreservingRealCongruenceContinuousMulEquiv F W
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x.1) :=
  rfl

/-- The target overlap homeomorphism is the target identity-chart inverse. -/
theorem coe_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapToGroup
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (z :
      specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W) :
    (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapToGroup
      F hF hdet W z).1 =
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).symm z.1 :=
  rfl

/-- The ambient coordinate transition, packaged between the two ordinary
overlap subtypes through their common represented group point. -/
def specialFormPreservingSmoothRealCongruenceAmbientSourceToStandardTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W ≃ₜ
      specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W :=
  (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapToGroup
    F hF hdet W).trans
      (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapToGroup
        F hF hdet W).symm

/-- The packaged overlap transition has the expected ambient coordinate
formula. -/
theorem coe_specialFormPreservingSmoothRealCongruenceAmbientSourceToStandardTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
      F hF hdet W) :
    (specialFormPreservingSmoothRealCongruenceAmbientSourceToStandardTarget
      F hF hdet W x).1 =
      Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
        (specialFormPreservingSmoothRealCongruenceChartSourceTransition
          F hF hdet W x.1) := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  let C := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  change
    (realCrossChartAmbientSourceToTargetRange I J C.toHomeomorph x).1 =
      e (specialFormPreservingSmoothRealCongruenceChartSourceTransition
        F hF hdet W x.1)
  rw [coe_realCrossChartAmbientSourceToTargetRange]
  exact congrArg e
    (specialFormPreservingSmoothRealCongruenceChartSourceTransition_eq_crossChart
      F hF hdet W x.1 x.2).symm

/-- The weighted source ambient measure pulled back to its exact overlap
subtype. -/
def specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure
      (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W) :=
  Measure.comap Subtype.val
    ((Matrix.skewAdjointRealCoordinateDetMeasure F 0).withDensity
      (specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
        F hF hdet))

/-- The independently normalized weighted target ambient measure pulled back
to its exact overlap subtype. -/
def specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure
      (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W) :=
  Measure.comap Subtype.val
    ((Matrix.skewAdjointRealCoordinateDetMeasure
      (Matrix.skewAdjointCongruenceForm F W) 0).withDensity
        (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
          F hF hdet W))

/-- Mapping the source overlap-subtype measure to its ambient tangent carrier
recovers the weighted restricted measure used in change of variables. -/
theorem map_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure
          F hF hdet W) =
      ((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
        (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
          F hF hdet W)).withDensity
        (specialFormPreservingSmoothRealCongruenceAmbientSourceDensity
          F hF hdet) := by
  rw [specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure,
    map_comap_subtype_coe
      (measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W),
    restrict_withDensity
      (measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W)]

/-- Mapping the target overlap-subtype measure to its ambient tangent carrier
recovers the independently normalized weighted restricted measure. -/
theorem map_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure
          F hF hdet W) =
      ((Matrix.skewAdjointRealCoordinateDetMeasure
        (Matrix.skewAdjointCongruenceForm F W) 0).restrict
          (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
            F hF hdet W)).withDensity
        (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
          F hF hdet W) := by
  rw [specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure,
    map_comap_subtype_coe
      (measurableSet_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W),
    restrict_withDensity
      (measurableSet_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
        F hF hdet W)]

/-- The coordinate homeomorphism transports the source overlap measure to the
independently normalized target overlap measure with exactly the reciprocal
rational-basis determinant. -/
theorem map_specialFormPreservingSmoothRealCongruenceAmbientSourceToStandardTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingSmoothRealCongruenceAmbientSourceToStandardTarget
          F hF hdet W)
        (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure
          F hF hdet W) =
      (Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure
          F hF hdet W := by
  let U :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
      F hF hdet W
  let T :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
      F hF hdet W
  let K :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceToStandardTarget
      F hF hdet W
  let e := Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W
  let Ψ :=
    specialFormPreservingSmoothRealCongruenceChartSourceTransition
      F hF hdet W
  let Ψm :=
    specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition
      F hF hdet W
  let μ :=
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict U
  let source :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceDensity F hF hdet
  let μs :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure
      F hF hdet W
  let μt :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure
      F hF hdet W
  let c : ℝ≥0 := (Real.toNNReal
    |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹
  have hT : MeasurableSet T :=
    measurableSet_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapSet
      F hF hdet W
  have hΨm : Measurable Ψm :=
    measurable_specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition
      F hF hdet W
  have hΨeq : Ψm =ᵐ[μ] Ψ := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapSet
        F hF hdet W)] with x hx
    exact
      specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition_eq
        F hF hdet W x hx
  have hΨeq_source : Ψm =ᵐ[μ.withDensity source] Ψ :=
    (withDensity_absolutelyContinuous μ source).ae_eq hΨeq
  apply (MeasurableEmbedding.subtype_coe hT).map_injective
  calc
    Measure.map Subtype.val (Measure.map K μs) =
        Measure.map (fun x : U => (K x).1) μs := by
      rw [Measure.map_map continuous_subtype_val.measurable K.measurable]
      rfl
    _ = Measure.map (fun x : U => e (Ψ x.1)) μs := by
      apply Measure.map_congr
      filter_upwards [] with x
      simpa only [K, e, Ψ, U] using
        (coe_specialFormPreservingSmoothRealCongruenceAmbientSourceToStandardTarget
          F hF hdet W x)
    _ = Measure.map (fun x : U => e (Ψm x.1)) μs := by
      apply Measure.map_congr
      filter_upwards [] with x
      exact congrArg e
        (specialFormPreservingSmoothRealCongruenceAmbientMeasurableTransition_eq
          F hF hdet W x.1 x.2).symm
    _ = Measure.map (fun x => e (Ψm x))
        (Measure.map Subtype.val μs) := by
      symm
      calc
        Measure.map (fun x => e (Ψm x))
            (Measure.map Subtype.val μs) =
            Measure.map ((fun x => e (Ψm x)) ∘ Subtype.val) μs :=
          Measure.map_map
            (e.continuous.measurable.comp hΨm)
            continuous_subtype_val.measurable
        _ = Measure.map (fun x : U => e (Ψm x.1)) μs := rfl
    _ = Measure.map (fun x => e (Ψm x)) (μ.withDensity source) := by
      rw [map_specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure]
    _ = Measure.map (fun x => e (Ψ x)) (μ.withDensity source) := by
      apply Measure.map_congr
      filter_upwards [hΨeq_source] with x hx
      rw [hx]
    _ = c •
        (((Matrix.skewAdjointRealCoordinateDetMeasure
          (Matrix.skewAdjointCongruenceForm F W) 0).restrict T).withDensity
            (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetDensity
              F hF hdet W)) := by
      simpa [U, T, e, Ψ, μ, source, c] using
        map_withDensity_specialFormPreservingSmoothRealCongruenceAmbientSourceTransition_targetCarrier
          F hF hdet W
    _ = c • Measure.map Subtype.val μt := by
      rw [map_specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure]
    _ = Measure.map Subtype.val (c • μt) := by
      rw [Measure.map_smul]

/-- The local measure on the common group overlap induced by transported
source coordinates. -/
def specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure
      (specialFormPreservingSmoothRealCongruenceChartGroupOverlap
        F hF hdet W) :=
  Measure.map
    (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapToGroup
      F hF hdet W)
    (specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure
      F hF hdet W)

/-- The local measure on the common group overlap induced by independently
normalized standard target coordinates. -/
def specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure
      (specialFormPreservingSmoothRealCongruenceChartGroupOverlap
        F hF hdet W) :=
  Measure.map
    (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapToGroup
      F hF hdet W)
    (specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure
      F hF hdet W)

/-- On their exact common group overlap, the transported and independently
normalized chart measures differ by precisely the reciprocal tangent
basis-comparison determinant. -/
theorem specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure
        F hF hdet W =
      (Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure
          F hF hdet W := by
  let S :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapToGroup
      F hF hdet W
  let R :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapToGroup
      F hF hdet W
  let K :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceToStandardTarget
      F hF hdet W
  let μs :=
    specialFormPreservingSmoothRealCongruenceAmbientSourceOverlapMeasure
      F hF hdet W
  let μt :=
    specialFormPreservingSmoothRealCongruenceAmbientStandardTargetOverlapMeasure
      F hF hdet W
  let c : ℝ≥0 := (Real.toNNReal
    |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹
  change Measure.map S μs = c • Measure.map R μt
  apply map_left_eq_smul_map_right_of_map_trans_symm
    S.toMeasurableEquiv R.toMeasurableEquiv μs μt c
  simpa only [S, R, K] using
      map_specialFormPreservingSmoothRealCongruenceAmbientSourceToStandardTarget
        F hF hdet W

end PositiveDefiniteIntegralLattice
