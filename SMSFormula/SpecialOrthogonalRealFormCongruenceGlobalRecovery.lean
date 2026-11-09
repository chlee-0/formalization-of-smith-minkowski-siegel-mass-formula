import SMSFormula.SpecialOrthogonalRealCongruenceHaarScalar
import SMSFormula.SpecialOrthogonalRealFormCongruenceOverlapNativeGroupRestriction

/-!
# Global recovery for explicit real-congruence overlaps

This module evaluates the two native chart-restriction identities on arbitrary
measurable subsets of the exact common group overlap.  The transported
calculation remains on the original source identity chart until the final
application of the explicit real group congruence.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realFormCongruenceGlobalRecoveryGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realFormCongruenceGlobalRecoveryGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- On every measurable subset of the exact common overlap, the standard
induced measure recovers the target global differential measure. -/
theorem specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure_preimage
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (B : Set (specialFormPreservingMatrixSubgroup
      (F'.map (algebraMap ℚ ℝ))))
    (hB : MeasurableSet B)
    (hBQ : B ⊆
      specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure
        F F' hF hdet hF' hdet' c
        (Subtype.val ⁻¹' B) =
      specialFormPreservingSmoothRealDifferentialMeasure
        F' hF' hdet' B := by
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  let j :=
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapToTargetIdentitySource
      F F' hF hdet hF' hdet' c
  let μ :=
    specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure
      F F' hF hdet hF' hdet' c
  let σ :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure F' hF' hdet' 1
  let ν :=
    specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  let P :=
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTargetIdentitySource
      F F' hF hdet hF' hdet' c
  let Q :=
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
      F F' hF hdet hF' hdet' c
  have hQ : MeasurableSet Q :=
    (isOpen_specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
      F F' hF hdet hF' hdet' c).measurableSet
  have hpre : (Subtype.val : J.source → _) ⁻¹' Q = P := by
    ext x
    change
      x.1 ∈
          specialFormPreservingSmoothRealFormCongruenceChartSourceSet
            F F' hF hdet c ∧
          x.1 ∈ J.source ↔
        x.1 ∈
          specialFormPreservingSmoothRealFormCongruenceChartSourceSet
            F F' hF hdet c
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  have hchart : ν.restrict J.source = Measure.map Subtype.val σ := by
    simpa [ν, σ, J,
      specialFormPreservingSmoothRealChartAmbientDensityMeasure] using
        (restrict_specialFormPreservingSmoothRealDifferentialMeasure_source
          F' hF' hdet' 1)
  exact measure_preimage_eq_measure_of_map_eq_native_restrict
    j Subtype.val Subtype.val μ σ ν P J.source Q B
    (continuous_subtype_val.subtype_mk _).measurable
    continuous_subtype_val.measurable continuous_subtype_val.measurable
    hQ hB (fun _ => rfl)
    (map_specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure_targetIdentitySource
      F F' hF hdet hF' hdet' c)
    hchart hpre (fun _ hx => hx.2) hBQ

/-- On every measurable subset of the exact common overlap, the transported
induced measure recovers the explicit congruence pushforward of the source
global differential measure. -/
theorem specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure_preimage
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (B : Set (specialFormPreservingMatrixSubgroup
      (F'.map (algebraMap ℚ ℝ))))
    (hB : MeasurableSet B)
    (hBQ : B ⊆
      specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure
        F F' hF hdet hF' hdet' c
        (Subtype.val ⁻¹' B) =
      Measure.map c.groupEquiv.toHomeomorph
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) B := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let es :=
    specialFormPreservingSmoothRealFormCongruenceChartSourceHomeomorph
      F F' hF hdet c
  let js :=
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapToTransportedSource
      F F' hF hdet hF' hdet' c
  let μ := specialFormPreservingSmoothRealDifferentialMeasure F hF hdet
  let μs :=
    specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure
      F F' hF hdet hF' hdet' c
  let σ :=
    specialFormPreservingSmoothRealChartSourceDensityMeasure F hF hdet 1
  let σs :=
    specialFormPreservingSmoothRealFormCongruenceChartSourceDensityMeasure
      F F' hF hdet c
  let Ps :=
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTransportedSource
      F F' hF hdet hF' hdet' c
  let R := c.groupEquiv ⁻¹' B
  have hPB : (Subtype.val :
      specialFormPreservingSmoothRealFormCongruenceChartSource
        F F' hF hdet c → _) ⁻¹' B ⊆ Ps := by
    intro x hx
    exact (hBQ hx).2
  have hSB : MeasurableSet ((Subtype.val :
      specialFormPreservingSmoothRealFormCongruenceChartSource
        F F' hF hdet c → _) ⁻¹' B) :=
    hB.preimage continuous_subtype_val.measurable
  have hR : MeasurableSet R := hB.preimage c.groupEquiv.measurable
  have hRsub : R ⊆ I.source := by
    intro x hx
    have hxQ := hBQ hx
    have hx1 := hxQ.1
    change c.groupEquiv.symm (c.groupEquiv x) ∈ I.source at hx1
    simpa using hx1
  have hpre :
      es ⁻¹' ((Subtype.val :
        specialFormPreservingSmoothRealFormCongruenceChartSource
          F F' hF hdet c → _) ⁻¹' B) =
        (Subtype.val : I.source → _) ⁻¹' R := by
    ext x
    rfl
  have hnatives := congrArg (fun m :
      Measure (specialFormPreservingSmoothRealFormCongruenceChartSource
        F F' hF hdet c) =>
        m ((Subtype.val :
          specialFormPreservingSmoothRealFormCongruenceChartSource
            F F' hF hdet c → _) ⁻¹' B))
    (map_specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure_source
      F F' hF hdet hF' hdet' c)
  have hjs : Measurable js :=
    (continuous_subtype_val.subtype_mk _).measurable
  have hnatives' :
      μs (Subtype.val ⁻¹' B) =
        σs ((Subtype.val :
          specialFormPreservingSmoothRealFormCongruenceChartSource
            F F' hF hdet c → _) ⁻¹' B) := by
    change
      Measure.map js μs
          ((Subtype.val :
            specialFormPreservingSmoothRealFormCongruenceChartSource
              F F' hF hdet c → _) ⁻¹' B) =
        (σs.restrict Ps)
          ((Subtype.val :
            specialFormPreservingSmoothRealFormCongruenceChartSource
              F F' hF hdet c → _) ⁻¹' B)
      at hnatives
    rw [Measure.map_apply hjs hSB, Measure.restrict_apply hSB,
      Set.inter_eq_left.mpr hPB] at hnatives
    simpa only [Set.preimage_preimage] using hnatives
  have hσs :
      σs ((Subtype.val :
          specialFormPreservingSmoothRealFormCongruenceChartSource
            F F' hF hdet c → _) ⁻¹' B) =
        σ ((Subtype.val : I.source → _) ⁻¹' R) := by
    change
      Measure.map es σ
          ((Subtype.val :
            specialFormPreservingSmoothRealFormCongruenceChartSource
              F F' hF hdet c → _) ⁻¹' B) =
        σ ((Subtype.val : I.source → _) ⁻¹' R)
    rw [Measure.map_apply es.measurable hSB, hpre]
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
    μs (Subtype.val ⁻¹' B) =
        σs ((Subtype.val :
          specialFormPreservingSmoothRealFormCongruenceChartSource
            F F' hF hdet c → _) ⁻¹' B) :=
      hnatives'
    _ = σ ((Subtype.val : I.source → _) ⁻¹' R) := hσs
    _ = μ R := hglobal'.symm
    _ = Measure.map c.groupEquiv.toHomeomorph μ B := by
      symm
      rw [Measure.map_apply c.groupEquiv.measurable hB]
      rfl

/-- The total standard overlap mass is the target global differential mass of
the exact common group set. -/
theorem specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure_univ
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure
        F F' hF hdet hF' hdet' c Set.univ =
      specialFormPreservingSmoothRealDifferentialMeasure
        F' hF' hdet'
        (specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
          F F' hF hdet hF' hdet' c) := by
  let Q :=
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
      F F' hF hdet hF' hdet' c
  have hQ : MeasurableSet Q :=
    (isOpen_specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
      F F' hF hdet hF' hdet' c).measurableSet
  have hpre : (Subtype.val :
      specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c → _) ⁻¹' Q = Set.univ := by
    ext x
    exact iff_of_true x.2 (Set.mem_univ x)
  have h :=
    specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure_preimage
      F F' hF hdet hF' hdet' c Q hQ (fun _ hx => hx)
  rw [hpre] at h
  exact h

/-- The total transported overlap mass is the explicit congruence pushforward
of the source global differential mass on the exact common group set. -/
theorem specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure_univ
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure
        F F' hF hdet hF' hdet' c Set.univ =
      Measure.map c.groupEquiv.toHomeomorph
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)
        (specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
          F F' hF hdet hF' hdet' c) := by
  let Q :=
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
      F F' hF hdet hF' hdet' c
  have hQ : MeasurableSet Q :=
    (isOpen_specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
      F F' hF hdet hF' hdet' c).measurableSet
  have hpre : (Subtype.val :
      specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c → _) ⁻¹' Q = Set.univ := by
    ext x
    exact iff_of_true x.2 (Set.mem_univ x)
  have h :=
    specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure_preimage
      F F' hF hdet hF' hdet' c Q hQ (fun _ hx => hx)
  rw [hpre] at h
  exact h

end PositiveDefiniteIntegralLattice
