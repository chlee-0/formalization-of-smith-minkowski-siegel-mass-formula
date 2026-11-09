import SMSFormula.SpecialOrthogonalRealCongruenceHaarScalarFiniteMass

/-!
# Selected masses for the real congruence comparison
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceHaarScalarSelectedMassGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realCongruenceHaarScalarSelectedMassGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The selected subset of the exact common group-overlap subtype. -/
def specialFormPreservingRealCongruenceFiniteCommonOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set (specialFormPreservingSmoothRealCongruenceChartGroupOverlap
      F hF hdet W) :=
  Subtype.val ⁻¹'
    specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W

/-- The standard induced overlap mass of the selected common set. -/
def specialFormPreservingRealCongruenceFiniteStandardOverlapMass
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) : ℝ≥0∞ :=
  specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure
      F hF hdet W
    (specialFormPreservingRealCongruenceFiniteCommonOverlapSet F hF hdet W)

/-- The transported induced overlap mass of the selected common set. -/
def specialFormPreservingRealCongruenceFiniteTransportedOverlapMass
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) : ℝ≥0∞ :=
  specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure
      F hF hdet W
    (specialFormPreservingRealCongruenceFiniteCommonOverlapSet F hF hdet W)

/-- The transported global source mass of the selected common set. -/
def specialFormPreservingRealCongruenceFiniteTransportedGlobalMass
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) : ℝ≥0∞ :=
  Measure.map
      (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)
    (specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W)

/-- The selected standard overlap mass recovers the selected target global
mass. -/
theorem specialFormPreservingRealCongruenceFiniteStandardOverlapMass_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingRealCongruenceFiniteStandardOverlapMass
        F hF hdet W =
      specialFormPreservingRealCongruenceFiniteCommonMass F hF hdet W := by
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  let jt :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapToTargetIdentitySource
      F hF hdet W
  let μt :=
    specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure
      F hF hdet W
  let σt := specialFormPreservingSmoothRealChartSourceDensityMeasure
    F' hF' hdet' 1
  let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  let Pt :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTargetIdentitySource
      F hF hdet W
  let Q :=
    specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
      F hF hdet W
  let B := specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W
  have hQ : IsOpen Q :=
    isOpen_specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
      F hF hdet W
  have hB : IsOpen B :=
    isOpen_specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W
  have hBQ : B ⊆ Q :=
    specialFormPreservingRealCongruenceFiniteCommonSet_subset_overlap
      F hF hdet W
  have hPt : (Subtype.val : J.source → _) ⁻¹' Q = Pt := by
    ext x
    change
      x.1 ∈ specialFormPreservingSmoothRealCongruenceChartSourceSet
          F hF hdet W ∧ x.1 ∈ J.source ↔
        x.1 ∈ specialFormPreservingSmoothRealCongruenceChartSourceSet
          F hF hdet W
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  have hchartt : ν.restrict J.source = Measure.map Subtype.val σt := by
    simpa [ν, σt, J, F', hF', hdet',
      specialFormPreservingSmoothRealChartAmbientDensityMeasure] using
        (restrict_specialFormPreservingSmoothRealDifferentialMeasure_source
          F' hF' hdet' 1)
  exact measure_preimage_eq_measure_of_map_eq_native_restrict
    jt Subtype.val Subtype.val μt σt ν Pt J.source Q B
    (continuous_subtype_val.subtype_mk _).measurable
    continuous_subtype_val.measurable continuous_subtype_val.measurable
    hQ.measurableSet hB.measurableSet (fun _ => rfl)
    (map_specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure_targetIdentitySource
      F hF hdet W)
    hchartt hPt (fun _ hx => hx.2) hBQ

/-- The selected transported overlap mass recovers the selected transported
global source mass. -/
theorem specialFormPreservingRealCongruenceFiniteTransportedOverlapMass_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingRealCongruenceFiniteTransportedOverlapMass
        F hF hdet W =
      specialFormPreservingRealCongruenceFiniteTransportedGlobalMass
        F hF hdet W := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let e := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let es :=
    specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
      F hF hdet W
  let js :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapToTransportedSource
      F hF hdet W
  let μ := specialFormPreservingSmoothRealDifferentialMeasure F hF hdet
  let μs :=
    specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure
      F hF hdet W
  let σ := specialFormPreservingSmoothRealChartSourceDensityMeasure
    F hF hdet 1
  let σs :=
    specialFormPreservingSmoothRealCongruenceChartSourceDensityMeasure
      F hF hdet W
  let Ps :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource
      F hF hdet W
  let Q :=
    specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
      F hF hdet W
  let B := specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W
  let R := e ⁻¹' B
  have hB : IsOpen B :=
    isOpen_specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W
  have hBQ : B ⊆ Q :=
    specialFormPreservingRealCongruenceFiniteCommonSet_subset_overlap
      F hF hdet W
  have hPB : (Subtype.val :
      specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W → _) ⁻¹' B ⊆ Ps := by
    intro x hx
    exact (hBQ hx).2
  have hSB : MeasurableSet ((Subtype.val :
      specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W → _) ⁻¹' B) :=
    hB.measurableSet.preimage continuous_subtype_val.measurable
  have hR : MeasurableSet R := hB.measurableSet.preimage e.measurable
  have hRsub : R ⊆ I.source := by
    intro x hx
    have hxQ := hBQ hx
    have hx1 := hxQ.1
    change e.symm (e x) ∈ I.source at hx1
    simpa using hx1
  have hpre :
      es ⁻¹' ((Subtype.val :
        specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W → _) ⁻¹' B) =
        (Subtype.val : I.source → _) ⁻¹' R := by
    ext x
    rfl
  have hnatives := congrArg (fun m :
      Measure (specialFormPreservingSmoothRealCongruenceChartSource
        F hF hdet W) =>
        m ((Subtype.val :
          specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W → _) ⁻¹' B))
    (map_specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure_source
      F hF hdet W)
  have hjs : Measurable js :=
    (continuous_subtype_val.subtype_mk _).measurable
  have hnatives' :
      μs (Subtype.val ⁻¹' B) =
        σs ((Subtype.val :
          specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W → _) ⁻¹' B) := by
    change
      Measure.map js μs
          ((Subtype.val :
            specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W → _) ⁻¹' B) =
        (σs.restrict Ps)
          ((Subtype.val :
            specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W → _) ⁻¹' B)
      at hnatives
    rw [Measure.map_apply hjs hSB, Measure.restrict_apply hSB,
      Set.inter_eq_left.mpr hPB] at hnatives
    simpa only [Set.preimage_preimage] using hnatives
  have hσs :
      σs ((Subtype.val :
          specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W → _) ⁻¹' B) =
        σ ((Subtype.val : I.source → _) ⁻¹' R) := by
    change
      Measure.map es σ
          ((Subtype.val :
            specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W → _) ⁻¹' B) =
        σ ((Subtype.val : I.source → _) ⁻¹' R)
    rw [Measure.map_apply es.measurable hSB, hpre]
  have hcharts : μ.restrict I.source = Measure.map Subtype.val σ := by
    simpa [μ, σ, I,
      specialFormPreservingSmoothRealChartAmbientDensityMeasure] using
        (restrict_specialFormPreservingSmoothRealDifferentialMeasure_source
          F hF hdet 1)
  have hglobals := congrArg (fun m :
      Measure (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) => m R) hcharts
  have hglobals' :
      μ R = σ ((Subtype.val : I.source → _) ⁻¹' R) := by
    change (μ.restrict I.source) R = Measure.map Subtype.val σ R at hglobals
    rw [Measure.restrict_apply hR,
      Measure.map_apply continuous_subtype_val.measurable hR,
      Set.inter_eq_left.mpr hRsub] at hglobals
    exact hglobals
  calc
    μs (Subtype.val ⁻¹' B) =
        σs ((Subtype.val :
          specialFormPreservingSmoothRealCongruenceChartSource F hF hdet W → _) ⁻¹' B) :=
      hnatives'
    _ = σ ((Subtype.val : I.source → _) ⁻¹' R) := hσs
    _ = μ R := hglobals'.symm
    _ = Measure.map e.toHomeomorph μ B := by
      symm
      rw [Measure.map_apply e.measurable hB.measurableSet]
      rfl

/-- The selected overlap masses retain the reciprocal tangent-basis scalar. -/
theorem specialFormPreservingRealCongruenceFiniteTransportedOverlapMass_eq_smul
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingRealCongruenceFiniteTransportedOverlapMass
        F hF hdet W =
      (↑((Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹) : ℝ≥0∞) *
        specialFormPreservingRealCongruenceFiniteStandardOverlapMass
          F hF hdet W := by
  have h := congrArg (fun m :
      Measure (specialFormPreservingSmoothRealCongruenceChartGroupOverlap
        F hF hdet W) =>
        m (specialFormPreservingRealCongruenceFiniteCommonOverlapSet
          F hF hdet W))
    (specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure_eq
      F hF hdet W)
  change
    specialFormPreservingRealCongruenceFiniteTransportedOverlapMass F hF hdet W =
      ((Real.toNNReal
        |Matrix.skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
          specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure
            F hF hdet W)
        (specialFormPreservingRealCongruenceFiniteCommonOverlapSet
          F hF hdet W)
    at h
  simpa only [Measure.smul_apply, ENNReal.smul_def,
    specialFormPreservingRealCongruenceFiniteStandardOverlapMass] using h

/-- The selected transported global mass retains the Haar comparison scalar. -/
theorem specialFormPreservingRealCongruenceFiniteTransportedGlobalMass_eq_smul
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingRealCongruenceFiniteTransportedGlobalMass
        F hF hdet W =
      specialFormPreservingRealCongruenceHaarScalar F hF hdet W *
        specialFormPreservingRealCongruenceFiniteCommonMass
          F hF hdet W := by
  have h := congrArg (fun m :
      Measure (specialFormPreservingMatrixSubgroup
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))) =>
        m (specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W))
    (map_specialFormPreservingSmoothRealDifferentialMeasure_congruence_eq_smul
      F hF hdet W)
  change
    specialFormPreservingRealCongruenceFiniteTransportedGlobalMass F hF hdet W =
      (specialFormPreservingRealCongruenceHaarScalar F hF hdet W •
        specialFormPreservingSmoothRealDifferentialMeasure
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W))
        (specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W)
    at h
  simpa [Measure.smul_apply, ENNReal.smul_def,
    specialFormPreservingRealCongruenceFiniteCommonMass] using h

end PositiveDefiniteIntegralLattice
