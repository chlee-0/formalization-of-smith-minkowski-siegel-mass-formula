import SMSFormula.SpecialOrthogonalRealFormCongruenceOverlapTargetTransport

/-!
# Common-group transport for explicit real-congruence overlaps

This module pulls the two weighted ambient coordinate measures back to their
ordinary overlap subtypes and maps them to the same exact group-overlap
subtype.  No nested target-side coordinate homeomorphism is constructed.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Transport through two measurable identifications with a common carrier
converts a coordinate comparison into a comparison on that carrier. -/
theorem map_left_eq_smul_map_right_of_map_trans_symm_explicitRealForm
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (S : α ≃ᵐ β) (R : γ ≃ᵐ β)
    (μ : Measure α) (ν : Measure γ) (q : ℝ≥0)
    (hmap : Measure.map (S.trans R.symm) μ = q • ν) :
    Measure.map S μ = q • Measure.map R ν := by
  calc
    Measure.map S μ =
        Measure.map R (Measure.map (S.trans R.symm) μ) := by
      rw [Measure.map_map R.measurable (S.trans R.symm).measurable]
      apply Measure.map_congr
      filter_upwards [] with x
      exact (R.apply_symm_apply (S x)).symm
    _ = Measure.map R (q • ν) := by rw [hmap]
    _ = q • Measure.map R ν := by rw [Measure.map_smul]

local instance realFormCongruenceOverlapGroupTransportSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realFormCongruenceOverlapGroupTransportSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance realFormCongruenceOverlapGroupTransportTargetMeasurableSpace
    (F' : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F'.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realFormCongruenceOverlapGroupTransportTargetBorelSpace
    (F' : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F'.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance realFormCongruenceOverlapGroupTransportGroupMeasurableSpace
    (F' : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realFormCongruenceOverlapGroupTransportGroupBorelSpace
    (F' : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The ambient coordinate transition packaged between the ordinary source
and standard target overlap subtypes. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientSourceToStandardTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c ≃ₜ
      specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c :=
  (specialFormPreservingSmoothRealFormCongruenceAmbientSourceToGroup
    F F' hF hdet hF' hdet' c).trans
      (specialFormPreservingSmoothRealFormCongruenceStandardTargetToGroup
        F F' hF hdet hF' hdet' c).symm

/-- The packaged overlap transition is tangent equivalence after the
fixed-carrier cross transition. -/
theorem coe_specialFormPreservingSmoothRealFormCongruenceAmbientSourceToStandardTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c) :
    (specialFormPreservingSmoothRealFormCongruenceAmbientSourceToStandardTarget
      F F' hF hdet hF' hdet' c x).1 =
      c.tangentEquiv
        (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c x.1) :=
  coe_specialFormPreservingSmoothRealFormCongruenceSourceToStandardTarget
    F F' hF hdet hF' hdet' c x

/-- The weighted source ambient measure pulled back to its exact overlap
subtype. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :=
  Measure.comap Subtype.val
    ((Matrix.skewAdjointRealCoordinateDetMeasure F 0).withDensity
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
        F hF hdet))

/-- The independently normalized weighted target measure pulled back to its
standard target-coordinate overlap subtype. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure
      (specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c) :=
  Measure.comap Subtype.val
    ((Matrix.skewAdjointRealCoordinateDetMeasure F' 0).withDensity
      (specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
        F' hF' hdet'))

/-- Mapping the source overlap-subtype measure to the ambient tangent carrier
recovers the weighted restricted source measure. -/
theorem map_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure
          F F' hF hdet hF' hdet' c) =
      ((Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict
        (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
          F F' hF hdet hF' hdet' c)).withDensity
        (specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity
          F hF hdet) := by
  rw [
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure,
    map_comap_subtype_coe
      (isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c).measurableSet,
    restrict_withDensity
      (isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c).measurableSet]

/-- Mapping the standard target overlap-subtype measure to its ambient tangent
carrier recovers the weighted restricted target measure. -/
theorem map_specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map Subtype.val
        (specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure
          F F' hF hdet hF' hdet' c) =
      ((Matrix.skewAdjointRealCoordinateDetMeasure F' 0).restrict
        (specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
          F F' hF hdet hF' hdet' c)).withDensity
        (specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
          F' hF' hdet') := by
  rw [
    specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure,
    map_comap_subtype_coe
      (isOpen_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c).measurableSet,
    restrict_withDensity
      (isOpen_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c).measurableSet]

/-- The coordinate homeomorphism transports the source overlap measure to the
standard target overlap measure with exactly the reciprocal rational-basis
determinant. -/
theorem map_specialFormPreservingSmoothRealFormCongruenceAmbientSourceToStandardTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map
        (specialFormPreservingSmoothRealFormCongruenceAmbientSourceToStandardTarget
          F F' hF hdet hF' hdet' c)
        (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure
          F F' hF hdet hF' hdet' c) =
      (Real.toNNReal |c.detScalar|)⁻¹ •
        specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure
          F F' hF hdet hF' hdet' c := by
  let U :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c
  let T :=
    specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
      F F' hF hdet hF' hdet' c
  let K :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceToStandardTarget
      F F' hF hdet hF' hdet' c
  let e := c.tangentEquiv
  let Ψ :=
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c
  let Ψm :=
    specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition
      F F' hF hdet hF' hdet' c
  let μ :=
    (Matrix.skewAdjointRealCoordinateDetMeasure F 0).restrict U
  let source :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceDensity F hF hdet
  let μs :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure
      F F' hF hdet hF' hdet' c
  let μt :=
    specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure
      F F' hF hdet hF' hdet' c
  let q : ℝ≥0 := (Real.toNNReal |c.detScalar|)⁻¹
  have hT : MeasurableSet T :=
    (isOpen_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
      F F' hF hdet hF' hdet' c).measurableSet
  have hΨm : Measurable Ψm :=
    measurable_specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition
      F F' hF hdet hF' hdet' c
  have hΨeq : Ψm =ᵐ[μ] Ψ := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c).measurableSet] with x hx
    exact
      specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition_eq
        F F' hF hdet hF' hdet' c x hx
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
        (coe_specialFormPreservingSmoothRealFormCongruenceAmbientSourceToStandardTarget
          F F' hF hdet hF' hdet' c x)
    _ = Measure.map (fun x : U => e (Ψm x.1)) μs := by
      apply Measure.map_congr
      filter_upwards [] with x
      exact congrArg e
        (specialFormPreservingSmoothRealFormCongruenceAmbientMeasurableTransition_eq
          F F' hF hdet hF' hdet' c x.1 x.2).symm
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
      rw [
        map_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure]
    _ = Measure.map (fun x => e (Ψ x)) (μ.withDensity source) := by
      apply Measure.map_congr
      filter_upwards [hΨeq_source] with x hx
      rw [hx]
    _ = q •
        (((Matrix.skewAdjointRealCoordinateDetMeasure F' 0).restrict T).withDensity
          (specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetDensity
            F' hF' hdet')) := by
      simpa [U, T, e, Ψ, μ, source, q] using
        map_withDensity_specialFormPreservingSmoothRealFormCongruenceAmbientTransition_targetCarrier
          F F' hF hdet hF' hdet' c
    _ = q • Measure.map Subtype.val μt := by
      rw [
        map_specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure]
    _ = Measure.map Subtype.val (q • μt) := by
      rw [Measure.map_smul]

/-- The local common-group measure induced by transported source
coordinates. -/
def specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure
      (specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c) :=
  Measure.map
    (specialFormPreservingSmoothRealFormCongruenceAmbientSourceToGroup
      F F' hF hdet hF' hdet' c)
    (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure
      F F' hF hdet hF' hdet' c)

/-- The local common-group measure induced by independently normalized target
coordinates. -/
def specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure
      (specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c) :=
  Measure.map
    (specialFormPreservingSmoothRealFormCongruenceStandardTargetToGroup
      F F' hF hdet hF' hdet' c)
    (specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure
      F F' hF hdet hF' hdet' c)

/-- On the exact common group overlap, the transported and independently
normalized chart measures differ by the reciprocal tangent basis determinant. -/
theorem specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure_eq
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure
        F F' hF hdet hF' hdet' c =
      (Real.toNNReal |c.detScalar|)⁻¹ •
        specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure
          F F' hF hdet hF' hdet' c := by
  let S :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceToGroup
      F F' hF hdet hF' hdet' c
  let R :=
    specialFormPreservingSmoothRealFormCongruenceStandardTargetToGroup
      F F' hF hdet hF' hdet' c
  let K :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceToStandardTarget
      F F' hF hdet hF' hdet' c
  let μs :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure
      F F' hF hdet hF' hdet' c
  let μt :=
    specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure
      F F' hF hdet hF' hdet' c
  let q : ℝ≥0 := (Real.toNNReal |c.detScalar|)⁻¹
  change Measure.map S μs = q • Measure.map R μt
  apply map_left_eq_smul_map_right_of_map_trans_symm_explicitRealForm
    S.toMeasurableEquiv R.toMeasurableEquiv μs μt q
  simpa only [S, R, K] using
    map_specialFormPreservingSmoothRealFormCongruenceAmbientSourceToStandardTarget
      F F' hF hdet hF' hdet' c

end PositiveDefiniteIntegralLattice
