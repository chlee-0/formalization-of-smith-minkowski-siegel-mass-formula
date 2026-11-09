import SMSFormula.SpecialOrthogonalRealFormCongruenceOverlapChartRestriction

/-!
# Native group restrictions for explicit real-congruence overlaps

This module transports the two native coordinate-restriction identities to
the exact common group overlap.  Global differential-Haar recovery is left to
a subsequent layer.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realFormCongruenceNativeGroupRestrictionSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance realFormCongruenceNativeGroupRestrictionSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance realFormCongruenceNativeGroupRestrictionGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realFormCongruenceNativeGroupRestrictionGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Inclusion of the common group overlap into the target identity-chart
source. -/
def specialFormPreservingSmoothRealFormCongruenceGroupOverlapToTargetIdentitySource
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c →
      (specialFormPreservingSmoothRealIdentityChart
        F' hF' hdet').source :=
  fun q => ⟨q.1, q.2.2⟩

/-- The common group overlap viewed inside the target identity-chart source. -/
def specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTargetIdentitySource
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').source :=
  Subtype.val ⁻¹'
    specialFormPreservingSmoothRealFormCongruenceChartSourceSet
      F F' hF hdet c

/-- The target identity-source internal common overlap is measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTargetIdentitySource
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    MeasurableSet
      (specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTargetIdentitySource
        F F' hF hdet hF' hdet' c) :=
  (isOpen_specialFormPreservingSmoothRealFormCongruenceChartSourceSet
    F F' hF hdet c).measurableSet.preimage continuous_subtype_val.measurable

/-- Pulling the target-source common overlap back through target identity
coordinates gives the standard target ambient overlap. -/
theorem preimage_specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTargetIdentitySource
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    (specialFormPreservingSmoothRealIdentityChart
      F' hF' hdet').toHomeomorphSourceTarget.symm ⁻¹'
        specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTargetIdentitySource
          F F' hF hdet hF' hdet' c =
      specialFormPreservingSmoothRealFormCongruenceStandardTargetWithinIdentityTarget
        F F' hF hdet hF' hdet' c := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  ext z
  change
    J.symm z ∈
        specialFormPreservingSmoothRealFormCongruenceChartSourceSet
          F F' hF hdet c ↔
      z.1 ∈
        specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
          F F' hF hdet hF' hdet' c
  rw [
    specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet_eq]
  change
    c.groupEquiv.symm (J.symm z) ∈ I.source ↔
      z.1 ∈ J.target ∧ c.groupEquiv.symm (J.symm z) ∈ I.source
  exact ⟨fun hz => ⟨z.2, hz⟩, fun hz => hz.2⟩

/-- The standard common-group measure is exactly the target identity-chart
source density restricted to the common overlap. -/
theorem map_specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure_targetIdentitySource
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map
        (specialFormPreservingSmoothRealFormCongruenceGroupOverlapToTargetIdentitySource
          F F' hF hdet hF' hdet' c)
        (specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure
          F F' hF hdet hF' hdet' c) =
      (specialFormPreservingSmoothRealChartSourceDensityMeasure
        F' hF' hdet' 1).restrict
          (specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTargetIdentitySource
            F F' hF hdet hF' hdet' c) := by
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  let R :=
    specialFormPreservingSmoothRealFormCongruenceStandardTargetToGroup
      F F' hF hdet hF' hdet' c
  let jt :=
    specialFormPreservingSmoothRealFormCongruenceStandardTargetToIdentityTarget
      F F' hF hdet hF' hdet' c
  let jg :=
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapToTargetIdentitySource
      F F' hF hdet hF' hdet' c
  let μt :=
    specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure
      F F' hF hdet hF' hdet' c
  let τ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure F' hF' hdet' 1
  let P :=
    specialFormPreservingSmoothRealFormCongruenceStandardTargetWithinIdentityTarget
      F F' hF hdet hF' hdet' c
  let Q :=
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTargetIdentitySource
      F F' hF hdet hF' hdet' c
  have hjg : Measurable jg :=
    (continuous_subtype_val.subtype_mk _).measurable
  change Measure.map jg (Measure.map R μt) =
    (Measure.map J.toHomeomorphSourceTarget.symm τ).restrict Q
  calc
    Measure.map jg (Measure.map R μt) =
        Measure.map J.toHomeomorphSourceTarget.symm
          (Measure.map jt μt) := by
      rw [Measure.map_map hjg R.measurable,
        Measure.map_map J.toHomeomorphSourceTarget.symm.measurable
          (measurableEmbedding_specialFormPreservingSmoothRealFormCongruenceStandardTargetToIdentityTarget
            F F' hF hdet hF' hdet' c).measurable]
      apply Measure.map_congr
      filter_upwards [] with z
      apply Subtype.ext
      rfl
    _ = Measure.map J.toHomeomorphSourceTarget.symm (τ.restrict P) := by
      rw [
        map_specialFormPreservingSmoothRealFormCongruenceAmbientStandardTargetOverlapMeasure_identityTarget]
    _ = (Measure.map J.toHomeomorphSourceTarget.symm τ).restrict Q := by
      symm
      rw [Measure.restrict_map
        J.toHomeomorphSourceTarget.symm.measurable
        (measurableSet_specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTargetIdentitySource
          F F' hF hdet hF' hdet' c),
        preimage_specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTargetIdentitySource]

/-- Inclusion of the common group overlap into the transported chart source. -/
def specialFormPreservingSmoothRealFormCongruenceGroupOverlapToTransportedSource
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c →
      specialFormPreservingSmoothRealFormCongruenceChartSource
        F F' hF hdet c :=
  fun q => ⟨q.1, q.2.1⟩

/-- The common group overlap viewed inside the transported chart source. -/
def specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTransportedSource
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set
      (specialFormPreservingSmoothRealFormCongruenceChartSource
        F F' hF hdet c) :=
  Subtype.val ⁻¹'
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').source

/-- The transported-source internal common overlap is measurable. -/
theorem measurableSet_specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTransportedSource
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    MeasurableSet
      (specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTransportedSource
        F F' hF hdet hF' hdet' c) :=
  (specialFormPreservingSmoothRealIdentityChart
    F' hF' hdet').open_source.measurableSet.preimage
      continuous_subtype_val.measurable

/-- Pulling the transported-source common overlap back through source
identity coordinates gives the fixed-source ambient overlap. -/
theorem preimage_specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTransportedSource
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    ((specialFormPreservingSmoothRealIdentityChart F hF hdet
        ).toHomeomorphSourceTarget.symm.trans
      (specialFormPreservingSmoothRealFormCongruenceChartSourceHomeomorph
        F F' hF hdet c)) ⁻¹'
        specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTransportedSource
          F F' hF hdet hF' hdet' c =
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceWithinIdentityTarget
        F F' hF hdet hF' hdet' c := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  ext x
  change
    c.groupEquiv (I.symm x) ∈ J.source ↔
      x.1 ∈
        specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
          F F' hF hdet hF' hdet' c
  change
    c.groupEquiv (I.symm x) ∈ J.source ↔
      x.1 ∈ I.target ∧ c.groupEquiv (I.symm x) ∈ J.source
  exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩

/-- The transported common-group measure is exactly the transported chart
source density restricted to the common overlap. -/
theorem map_specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure_source
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map
        (specialFormPreservingSmoothRealFormCongruenceGroupOverlapToTransportedSource
          F F' hF hdet hF' hdet' c)
        (specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure
          F F' hF hdet hF' hdet' c) =
      (specialFormPreservingSmoothRealFormCongruenceChartSourceDensityMeasure
        F F' hF hdet c).restrict
          (specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTransportedSource
            F F' hF hdet hF' hdet' c) := by
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let es :=
    specialFormPreservingSmoothRealFormCongruenceChartSourceHomeomorph
      F F' hF hdet c
  let L := I.toHomeomorphSourceTarget.symm.trans es
  let S :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceToGroup
      F F' hF hdet hF' hdet' c
  let jt :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceToIdentityTarget
      F F' hF hdet hF' hdet' c
  let jg :=
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapToTransportedSource
      F F' hF hdet hF' hdet' c
  let μs :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure
      F F' hF hdet hF' hdet' c
  let τ :=
    specialFormPreservingSmoothRealChartTargetDensityMeasure F hF hdet 1
  let P :=
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceWithinIdentityTarget
      F F' hF hdet hF' hdet' c
  let Q :=
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTransportedSource
      F F' hF hdet hF' hdet' c
  have hjg : Measurable jg :=
    (continuous_subtype_val.subtype_mk _).measurable
  have hL :
      Measure.map L τ =
        specialFormPreservingSmoothRealFormCongruenceChartSourceDensityMeasure
          F F' hF hdet c := by
    rw [
      specialFormPreservingSmoothRealFormCongruenceChartSourceDensityMeasure,
      specialFormPreservingSmoothRealChartSourceDensityMeasure]
    rw [Measure.map_map es.measurable
      I.toHomeomorphSourceTarget.symm.measurable]
    rfl
  change Measure.map jg (Measure.map S μs) =
    (specialFormPreservingSmoothRealFormCongruenceChartSourceDensityMeasure
      F F' hF hdet c).restrict Q
  calc
    Measure.map jg (Measure.map S μs) =
        Measure.map L (Measure.map jt μs) := by
      rw [Measure.map_map hjg S.measurable,
        Measure.map_map L.measurable
          (measurableEmbedding_specialFormPreservingSmoothRealFormCongruenceAmbientSourceToIdentityTarget
            F F' hF hdet hF' hdet' c).measurable]
      apply Measure.map_congr
      filter_upwards [] with x
      apply Subtype.ext
      rfl
    _ = Measure.map L (τ.restrict P) := by
      rw [
        map_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapMeasure_identityTarget]
    _ = (Measure.map L τ).restrict Q := by
      symm
      rw [Measure.restrict_map L.measurable
        (measurableSet_specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTransportedSource
          F F' hF hdet hF' hdet' c),
        preimage_specialFormPreservingSmoothRealFormCongruenceGroupOverlapWithinTransportedSource]
    _ = (specialFormPreservingSmoothRealFormCongruenceChartSourceDensityMeasure
          F F' hF hdet c).restrict Q := by rw [hL]

end PositiveDefiniteIntegralLattice
