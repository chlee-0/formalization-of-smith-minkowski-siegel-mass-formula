import SMSFormula.SpecialOrthogonalRealCongruenceHaarScalar

/-!
# A finite positive common mass for real congruence charts
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceHaarScalarFiniteMassGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realCongruenceHaarScalarFiniteMassGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Identity belongs to the exact transported/standard common group overlap. -/
theorem one_mem_specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    (1 : specialFormPreservingMatrixSubgroup
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))) ∈
      specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
        F hF hdet W := by
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  let e := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  constructor
  · change e.symm 1 ∈
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).source
    simpa only [map_one] using
      (self_mem_specialFormPreservingSmoothRealChart_source
        F hF hdet 1)
  · exact self_mem_specialFormPreservingSmoothRealChart_source
      F' hF' hdet' 1

/-- A target-group neighborhood of identity with finite differential mass. -/
def specialFormPreservingRealCongruenceFiniteNeighborhood
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set (specialFormPreservingMatrixSubgroup
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))) :=
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  letI : IsLocallyFiniteMeasure ν :=
    specialFormPreservingSmoothRealDifferentialMeasure_isLocallyFinite
      F' hF' hdet'
  Classical.choose (ν.exists_isOpen_measure_lt_top (1 : _))

/-- The selected finite neighborhood contains identity, is open, and has
finite differential mass. -/
theorem specialFormPreservingRealCongruenceFiniteNeighborhood_spec
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    let F' := Matrix.skewAdjointCongruenceForm F W
    let hF' := skewAdjointCongruenceForm_isSymm F hF W
    let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
    let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
    (1 : specialFormPreservingMatrixSubgroup
      (F'.map (algebraMap ℚ ℝ))) ∈
        specialFormPreservingRealCongruenceFiniteNeighborhood F hF hdet W ∧
      IsOpen
        (specialFormPreservingRealCongruenceFiniteNeighborhood F hF hdet W) ∧
      ν (specialFormPreservingRealCongruenceFiniteNeighborhood F hF hdet W) <
        ⊤ := by
  dsimp only
  let ν := specialFormPreservingSmoothRealDifferentialMeasure
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  letI : IsLocallyFiniteMeasure ν :=
    specialFormPreservingSmoothRealDifferentialMeasure_isLocallyFinite
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  exact Classical.choose_spec
    (ν.exists_isOpen_measure_lt_top (1 : _))

/-- The selected finite common-open subset. -/
def specialFormPreservingRealCongruenceFiniteCommonSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Set (specialFormPreservingMatrixSubgroup
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))) :=
  specialFormPreservingRealCongruenceFiniteNeighborhood F hF hdet W ∩
    specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
      F hF hdet W

/-- The selected finite common set is open. -/
theorem isOpen_specialFormPreservingRealCongruenceFiniteCommonSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    IsOpen
      (specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W) :=
  (specialFormPreservingRealCongruenceFiniteNeighborhood_spec
      F hF hdet W).2.1.inter
    (isOpen_specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
      F hF hdet W)

/-- The selected finite common set lies in the exact common overlap. -/
theorem specialFormPreservingRealCongruenceFiniteCommonSet_subset_overlap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W ⊆
      specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
        F hF hdet W :=
  Set.inter_subset_right

/-- The target differential mass of the selected finite common-open set. -/
def specialFormPreservingRealCongruenceFiniteCommonMass
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) : ℝ≥0∞ :=
  specialFormPreservingSmoothRealDifferentialMeasure
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)
    (specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W)

/-- The selected common mass is nonzero. -/
theorem specialFormPreservingRealCongruenceFiniteCommonMass_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingRealCongruenceFiniteCommonMass F hF hdet W ≠ 0 := by
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  let B := specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W
  letI : Measure.IsOpenPosMeasure ν :=
    specialFormPreservingSmoothRealDifferentialMeasure_isOpenPosMeasure
      F' hF' hdet'
  have hB : IsOpen B :=
    isOpen_specialFormPreservingRealCongruenceFiniteCommonSet F hF hdet W
  have h1B : (1 : specialFormPreservingMatrixSubgroup
      (F'.map (algebraMap ℚ ℝ))) ∈ B :=
    ⟨(specialFormPreservingRealCongruenceFiniteNeighborhood_spec
        F hF hdet W).1,
      one_mem_specialFormPreservingSmoothRealCongruenceChartGroupOverlapSet
        F hF hdet W⟩
  exact ne_of_gt (hB.measure_pos ν ⟨1, h1B⟩)

/-- The selected common mass is finite. -/
theorem specialFormPreservingRealCongruenceFiniteCommonMass_ne_top
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingRealCongruenceFiniteCommonMass F hF hdet W ≠ ⊤ := by
  apply ne_of_lt
  exact (measure_mono Set.inter_subset_left).trans_lt
    (specialFormPreservingRealCongruenceFiniteNeighborhood_spec
      F hF hdet W).2.2

end PositiveDefiniteIntegralLattice
