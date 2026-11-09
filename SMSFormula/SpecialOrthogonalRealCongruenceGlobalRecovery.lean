import SMSFormula.SpecialOrthogonalRealCongruenceOverlapChartRestriction

/-!
# Global recovery from real congruence overlap restrictions

This module combines native chart-source restriction statements with recovery
of the global real differential measure.  The generic measure lemma keeps the
specialized dependent chart inclusions out of the measure-algebra proof.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceGlobalRecoveryGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realCongruenceGlobalRecoveryGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- A measure known on a native source restriction recovers the corresponding
ambient restriction after composing the two measurable inclusions. -/
theorem map_eq_restrict_of_map_eq_native_restrict
    {O S G : Type*}
    [MeasurableSpace O] [MeasurableSpace S] [MeasurableSpace G]
    (j : O → S) (i : S → G) (k : O → G)
    (μ : Measure O) (σ : Measure S) (ν : Measure G)
    (P : Set S) (A Q : Set G)
    (hj : Measurable j) (hi : Measurable i) (hQ : MeasurableSet Q)
    (hcomp : ∀ x, i (j x) = k x)
    (hmap : Measure.map j μ = σ.restrict P)
    (hchart : ν.restrict A = Measure.map i σ)
    (hpre : i ⁻¹' Q = P) (hsub : Q ⊆ A) :
    Measure.map k μ = ν.restrict Q := by
  calc
    Measure.map k μ = Measure.map (i ∘ j) μ := by
      apply Measure.map_congr
      filter_upwards [] with x
      exact (hcomp x).symm
    _ = Measure.map i (Measure.map j μ) :=
      (Measure.map_map hi hj).symm
    _ = Measure.map i (σ.restrict P) := by rw [hmap]
    _ = (Measure.map i σ).restrict Q := by
      symm
      rw [Measure.restrict_map hi hQ, hpre]
    _ = (ν.restrict A).restrict Q := by rw [hchart]
    _ = ν.restrict Q := by
      rw [Measure.restrict_restrict hQ]
      congr 1
      exact Set.inter_eq_left.mpr hsub

/-- Scalar-valued version of native chart recovery.  It avoids constructing
the ambient measure equality when only the mass of the common set is needed. -/
theorem measure_univ_eq_measure_of_map_eq_native_restrict
    {O S G : Type*}
    [MeasurableSpace O] [MeasurableSpace S] [MeasurableSpace G]
    (j : O → S) (i : S → G)
    (μ : Measure O) (σ : Measure S) (ν : Measure G)
    (P : Set S) (A Q : Set G)
    (hj : Measurable j) (hi : Measurable i) (hQ : MeasurableSet Q)
    (hmap : Measure.map j μ = σ.restrict P)
    (hchart : ν.restrict A = Measure.map i σ)
    (hpre : i ⁻¹' Q = P) (hsub : Q ⊆ A) :
    μ Set.univ = ν Q := by
  have hnative := congrArg (fun m : Measure S => m Set.univ) hmap
  have hnative' : μ Set.univ = σ P := by
    change Measure.map j μ Set.univ = (σ.restrict P) Set.univ at hnative
    rw [Measure.map_apply hj MeasurableSet.univ,
      Measure.restrict_apply MeasurableSet.univ] at hnative
    simpa using hnative
  have hglobal := congrArg (fun m : Measure G => m Q) hchart
  have hglobal' : ν Q = σ P := by
    change (ν.restrict A) Q = Measure.map i σ Q at hglobal
    rw [Measure.restrict_apply hQ, Measure.map_apply hi hQ, hpre] at hglobal
    rw [Set.inter_eq_left.mpr hsub] at hglobal
    exact hglobal
  exact hnative'.trans hglobal'.symm

/-- The total mass of the standard induced overlap measure is the global
target differential mass of the exact common group set. -/
theorem specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure_univ
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure
        F hF hdet W Set.univ =
      specialFormPreservingSmoothRealDifferentialMeasure
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)
        (specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
          F hF hdet W) := by
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  let j :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapToTargetIdentitySource
      F hF hdet W
  let μ :=
    specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure
      F hF hdet W
  let σ :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure F' hF' hdet' 1
  let ν :=
    specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  let P :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTargetIdentitySource
      F hF hdet W
  let Q :=
    specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
      F hF hdet W
  have hQ : MeasurableSet Q :=
    (isOpen_specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
      F hF hdet W).measurableSet
  have hpre : (Subtype.val : J.source → _) ⁻¹' Q = P := by
    ext x
    change
      x.1 ∈ specialFormPreservingSmoothRealCongruenceChartSourceSet
          F hF hdet W ∧ x.1 ∈ J.source ↔
        x.1 ∈ specialFormPreservingSmoothRealCongruenceChartSourceSet
          F hF hdet W
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  have hchart : ν.restrict J.source = Measure.map Subtype.val σ := by
    simpa [ν, σ, J, F', hF', hdet',
      specialFormPreservingSmoothRealChartAmbientDensityMeasure] using
        (restrict_specialFormPreservingSmoothRealDifferentialMeasure_source
          F' hF' hdet' 1)
  exact measure_univ_eq_measure_of_map_eq_native_restrict
    j Subtype.val μ σ ν P J.source Q
    (continuous_subtype_val.subtype_mk _).measurable
    continuous_subtype_val.measurable hQ
    (map_specialFormPreservingSmoothRealCongruenceStandardGroupOverlapMeasure_targetIdentitySource
      F hF hdet W)
    hchart hpre (fun _ hx => hx.2)

/-- The total mass of the transported induced overlap measure is the
transported global source differential mass of the exact common group set. -/
theorem specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure_univ
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure
        F hF hdet W Set.univ =
      Measure.map
        (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)
        (specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
          F hF hdet W) := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let e := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let es :=
    specialFormPreservingSmoothRealCongruenceChartSourceHomeomorph
      F hF hdet W
  let j :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapToTransportedSource
      F hF hdet W
  let μo :=
    specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure
      F hF hdet W
  let σ :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet 1
  let σt :=
    specialFormPreservingSmoothRealCongruenceChartSourceDensityMeasure
      F hF hdet W
  let μ := specialFormPreservingSmoothRealDifferentialMeasure F hF hdet
  let P :=
    specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource
      F hF hdet W
  let Q :=
    specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
      F hF hdet W
  let R := e ⁻¹' Q
  have hP : MeasurableSet P :=
    measurableSet_specialFormPreservingSmoothRealCongruenceGroupOverlapWithinTransportedSource
      F hF hdet W
  have hQ : MeasurableSet Q :=
    (isOpen_specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
      F hF hdet W).measurableSet
  have hR : MeasurableSet R := hQ.preimage e.measurable
  have hRsub : R ⊆ I.source := by
    intro x hx
    change e x ∈
      specialFormPreservingSmoothRealCongruenceChartSourceSet F hF hdet W ∩
        (specialFormPreservingSmoothRealIdentityChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source at hx
    have hx1 := hx.1
    change e.symm (e x) ∈ I.source at hx1
    simpa using hx1
  have hpre : es ⁻¹' P = (Subtype.val : I.source → _) ⁻¹' R := by
    ext x
    change
      e x.1 ∈
          (specialFormPreservingSmoothRealIdentityChart
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source ↔
        e x.1 ∈
          specialFormPreservingSmoothRealCongruenceChartSourceSet F hF hdet W ∩
            (specialFormPreservingSmoothRealIdentityChart
              (Matrix.skewAdjointCongruenceForm F W)
              (skewAdjointCongruenceForm_isSymm F hF W)
              (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source
    exact ⟨fun hx => ⟨es x |>.2, hx⟩, fun hx => hx.2⟩
  have hnative := congrArg (fun m :
      Measure (specialFormPreservingSmoothRealCongruenceChartSource
        F hF hdet W) => m Set.univ)
    (map_specialFormPreservingSmoothRealCongruenceTransportedGroupOverlapMeasure_source
      F hF hdet W)
  have hj : Measurable j :=
    (continuous_subtype_val.subtype_mk _).measurable
  have hnative' : μo Set.univ = σt P := by
    change Measure.map j μo Set.univ = (σt.restrict P) Set.univ at hnative
    rw [Measure.map_apply hj MeasurableSet.univ,
      Measure.restrict_apply MeasurableSet.univ] at hnative
    simpa using hnative
  have ht : σt P = σ ((Subtype.val : I.source → _) ⁻¹' R) := by
    change Measure.map es σ P =
      σ ((Subtype.val : I.source → _) ⁻¹' R)
    rw [Measure.map_apply es.measurable hP, hpre]
  have hchart : μ.restrict I.source = Measure.map Subtype.val σ := by
    simpa [μ, σ, I,
      specialFormPreservingSmoothRealChartAmbientDensityMeasure] using
        (restrict_specialFormPreservingSmoothRealDifferentialMeasure_source
          F hF hdet 1)
  have hglobal := congrArg (fun m :
      Measure (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) => m R) hchart
  have hglobal' :
      μ R = σ ((Subtype.val : I.source → _) ⁻¹' R) := by
    change (μ.restrict I.source) R = Measure.map Subtype.val σ R at hglobal
    rw [Measure.restrict_apply hR,
      Measure.map_apply continuous_subtype_val.measurable hR,
      Set.inter_eq_left.mpr hRsub] at hglobal
    exact hglobal
  calc
    μo Set.univ = σt P := hnative'
    _ = σ ((Subtype.val : I.source → _) ⁻¹' R) := ht
    _ = μ R := hglobal'.symm
    _ = Measure.map e.toHomeomorph μ Q := by
      symm
      rw [Measure.map_apply e.measurable hQ]
      rfl

end PositiveDefiniteIntegralLattice
