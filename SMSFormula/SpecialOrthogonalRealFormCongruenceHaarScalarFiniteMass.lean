import SMSFormula.SpecialOrthogonalRealFormCongruenceHaarScalar

/-!
# A finite positive common mass for explicit real congruence

This module chooses an open finite-mass target neighborhood of identity and
intersects it with the exact explicit-real common chart overlap.  Evaluation
of local and global comparison identities on the selected set is left to a
subsequent layer.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realFormCongruenceHaarScalarFiniteMassGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realFormCongruenceHaarScalarFiniteMassGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Identity belongs to the exact common group overlap for every explicit
real congruence. -/
theorem one_mem_specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    (1 : specialFormPreservingMatrixSubgroup
      (F'.map (algebraMap ℚ ℝ))) ∈
      specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c := by
  constructor
  · change c.groupEquiv.symm 1 ∈
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).source
    simpa only [map_one] using
      (self_mem_specialFormPreservingSmoothRealChart_source
        F hF hdet 1)
  · exact self_mem_specialFormPreservingSmoothRealChart_source
      F' hF' hdet' 1

/-- A target-group neighborhood of identity with finite target differential
mass. -/
def specialFormPreservingRealFormCongruenceFiniteNeighborhood
    (F' : Matrix (Fin n) (Fin n) ℚ)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0) :
    Set (specialFormPreservingMatrixSubgroup
      (F'.map (algebraMap ℚ ℝ))) :=
  let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  letI : IsLocallyFiniteMeasure ν :=
    specialFormPreservingSmoothRealDifferentialMeasure_isLocallyFinite
      F' hF' hdet'
  Classical.choose (ν.exists_isOpen_measure_lt_top (1 : _))

/-- The selected neighborhood contains identity, is open, and has finite
target differential mass. -/
theorem specialFormPreservingRealFormCongruenceFiniteNeighborhood_spec
    (F' : Matrix (Fin n) (Fin n) ℚ)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0) :
    let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
    (1 : specialFormPreservingMatrixSubgroup
      (F'.map (algebraMap ℚ ℝ))) ∈
        specialFormPreservingRealFormCongruenceFiniteNeighborhood
          F' hF' hdet' ∧
      IsOpen
        (specialFormPreservingRealFormCongruenceFiniteNeighborhood
          F' hF' hdet') ∧
      ν (specialFormPreservingRealFormCongruenceFiniteNeighborhood
          F' hF' hdet') < ⊤ := by
  dsimp only
  let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  letI : IsLocallyFiniteMeasure ν :=
    specialFormPreservingSmoothRealDifferentialMeasure_isLocallyFinite
      F' hF' hdet'
  exact Classical.choose_spec
    (ν.exists_isOpen_measure_lt_top (1 : _))

/-- The selected finite common-open subset. -/
def specialFormPreservingRealFormCongruenceFiniteCommonSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set (specialFormPreservingMatrixSubgroup
      (F'.map (algebraMap ℚ ℝ))) :=
  specialFormPreservingRealFormCongruenceFiniteNeighborhood
      F' hF' hdet' ∩
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
      F F' hF hdet hF' hdet' c

/-- The selected finite common set is open. -/
theorem isOpen_specialFormPreservingRealFormCongruenceFiniteCommonSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    IsOpen
      (specialFormPreservingRealFormCongruenceFiniteCommonSet
        F F' hF hdet hF' hdet' c) :=
  (specialFormPreservingRealFormCongruenceFiniteNeighborhood_spec
      F' hF' hdet').2.1.inter
    (isOpen_specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
      F F' hF hdet hF' hdet' c)

/-- The selected finite common set is measurable. -/
theorem measurableSet_specialFormPreservingRealFormCongruenceFiniteCommonSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    MeasurableSet
      (specialFormPreservingRealFormCongruenceFiniteCommonSet
        F F' hF hdet hF' hdet' c) :=
  (isOpen_specialFormPreservingRealFormCongruenceFiniteCommonSet
    F F' hF hdet hF' hdet' c).measurableSet

/-- The selected finite common set lies in the exact common overlap. -/
theorem specialFormPreservingRealFormCongruenceFiniteCommonSet_subset_overlap
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingRealFormCongruenceFiniteCommonSet
        F F' hF hdet hF' hdet' c ⊆
      specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c :=
  Set.inter_subset_right

/-- The target differential mass of the selected finite common-open set. -/
def specialFormPreservingRealFormCongruenceFiniteCommonMass
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') : ℝ≥0∞ :=
  specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
    (specialFormPreservingRealFormCongruenceFiniteCommonSet
      F F' hF hdet hF' hdet' c)

/-- The selected common mass is strictly positive. -/
theorem specialFormPreservingRealFormCongruenceFiniteCommonMass_pos
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    0 < specialFormPreservingRealFormCongruenceFiniteCommonMass
      F F' hF hdet hF' hdet' c := by
  let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  let B := specialFormPreservingRealFormCongruenceFiniteCommonSet
    F F' hF hdet hF' hdet' c
  letI : Measure.IsOpenPosMeasure ν :=
    specialFormPreservingSmoothRealDifferentialMeasure_isOpenPosMeasure
      F' hF' hdet'
  have hB : IsOpen B :=
    isOpen_specialFormPreservingRealFormCongruenceFiniteCommonSet
      F F' hF hdet hF' hdet' c
  have h1B :
      (1 : specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) ∈ B :=
    ⟨(specialFormPreservingRealFormCongruenceFiniteNeighborhood_spec
        F' hF' hdet').1,
      one_mem_specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c⟩
  exact hB.measure_pos ν ⟨1, h1B⟩

/-- The selected common mass is strictly below infinity. -/
theorem specialFormPreservingRealFormCongruenceFiniteCommonMass_lt_top
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingRealFormCongruenceFiniteCommonMass
        F F' hF hdet hF' hdet' c < ⊤ := by
  exact (measure_mono Set.inter_subset_left).trans_lt
    (specialFormPreservingRealFormCongruenceFiniteNeighborhood_spec
      F' hF' hdet').2.2

/-- The selected common mass is nonzero. -/
theorem specialFormPreservingRealFormCongruenceFiniteCommonMass_ne_zero
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingRealFormCongruenceFiniteCommonMass
      F F' hF hdet hF' hdet' c ≠ 0 :=
  ne_of_gt
    (specialFormPreservingRealFormCongruenceFiniteCommonMass_pos
      F F' hF hdet hF' hdet' c)

/-- The selected common mass is finite. -/
theorem specialFormPreservingRealFormCongruenceFiniteCommonMass_ne_top
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingRealFormCongruenceFiniteCommonMass
      F F' hF hdet hF' hdet' c ≠ ⊤ :=
  ne_of_lt
    (specialFormPreservingRealFormCongruenceFiniteCommonMass_lt_top
      F F' hF hdet hF' hdet' c)

end PositiveDefiniteIntegralLattice
