import SMSFormula.SpecialOrthogonalRealFormCongruenceHaarScalarFiniteMass

/-!
# Selected masses for explicit real-congruence comparison

This module evaluates the local determinant comparison and global Haar
comparison on the finite positive common set.  The final cancellation of that
common factor is left to a subsequent opaque certificate.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realFormCongruenceSelectedMassGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realFormCongruenceSelectedMassGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- The selected subset of the exact common group-overlap subtype. -/
def specialFormPreservingRealFormCongruenceFiniteCommonOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set
      (specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c) :=
  Subtype.val ⁻¹'
    specialFormPreservingRealFormCongruenceFiniteCommonSet
      F F' hF hdet hF' hdet' c

/-- The selected common-overlap subtype set is measurable. -/
theorem measurableSet_specialFormPreservingRealFormCongruenceFiniteCommonOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    MeasurableSet
      (specialFormPreservingRealFormCongruenceFiniteCommonOverlapSet
        F F' hF hdet hF' hdet' c) :=
  (measurableSet_specialFormPreservingRealFormCongruenceFiniteCommonSet
    F F' hF hdet hF' hdet' c).preimage
      continuous_subtype_val.measurable

/-- The standard induced overlap mass of the selected common set. -/
def specialFormPreservingRealFormCongruenceFiniteStandardOverlapMass
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') : ℝ≥0∞ :=
  specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure
      F F' hF hdet hF' hdet' c
    (specialFormPreservingRealFormCongruenceFiniteCommonOverlapSet
      F F' hF hdet hF' hdet' c)

/-- The transported induced overlap mass of the selected common set. -/
def specialFormPreservingRealFormCongruenceFiniteTransportedOverlapMass
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') : ℝ≥0∞ :=
  specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure
      F F' hF hdet hF' hdet' c
    (specialFormPreservingRealFormCongruenceFiniteCommonOverlapSet
      F F' hF hdet hF' hdet' c)

/-- The transported global source mass of the selected common set. -/
def specialFormPreservingRealFormCongruenceFiniteTransportedGlobalMass
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') : ℝ≥0∞ :=
  Measure.map c.groupEquiv.toHomeomorph
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)
    (specialFormPreservingRealFormCongruenceFiniteCommonSet
      F F' hF hdet hF' hdet' c)

/-- The selected standard overlap mass recovers the selected target global
mass. -/
theorem specialFormPreservingRealFormCongruenceFiniteStandardOverlapMass_eq
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingRealFormCongruenceFiniteStandardOverlapMass
        F F' hF hdet hF' hdet' c =
      specialFormPreservingRealFormCongruenceFiniteCommonMass
        F F' hF hdet hF' hdet' c := by
  exact
    specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure_preimage
      F F' hF hdet hF' hdet' c
      (specialFormPreservingRealFormCongruenceFiniteCommonSet
        F F' hF hdet hF' hdet' c)
      (measurableSet_specialFormPreservingRealFormCongruenceFiniteCommonSet
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingRealFormCongruenceFiniteCommonSet_subset_overlap
        F F' hF hdet hF' hdet' c)

/-- The selected transported overlap mass recovers the selected transported
global source mass. -/
theorem specialFormPreservingRealFormCongruenceFiniteTransportedOverlapMass_eq
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingRealFormCongruenceFiniteTransportedOverlapMass
        F F' hF hdet hF' hdet' c =
      specialFormPreservingRealFormCongruenceFiniteTransportedGlobalMass
        F F' hF hdet hF' hdet' c := by
  exact
    specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure_preimage
      F F' hF hdet hF' hdet' c
      (specialFormPreservingRealFormCongruenceFiniteCommonSet
        F F' hF hdet hF' hdet' c)
      (measurableSet_specialFormPreservingRealFormCongruenceFiniteCommonSet
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingRealFormCongruenceFiniteCommonSet_subset_overlap
        F F' hF hdet hF' hdet' c)

/-- The selected overlap masses are scaled by the reciprocal explicit
tangent-basis determinant. -/
theorem specialFormPreservingRealFormCongruenceFiniteTransportedOverlapMass_eq_smul
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingRealFormCongruenceFiniteTransportedOverlapMass
        F F' hF hdet hF' hdet' c =
      (↑((Real.toNNReal |c.detScalar|)⁻¹) : ℝ≥0∞) *
        specialFormPreservingRealFormCongruenceFiniteStandardOverlapMass
          F F' hF hdet hF' hdet' c := by
  have h := congrArg (fun m : Measure
      (specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c) =>
        m (specialFormPreservingRealFormCongruenceFiniteCommonOverlapSet
          F F' hF hdet hF' hdet' c))
    (specialFormPreservingSmoothRealFormCongruenceTransportedGroupOverlapMeasure_eq
      F F' hF hdet hF' hdet' c)
  change
    specialFormPreservingRealFormCongruenceFiniteTransportedOverlapMass
        F F' hF hdet hF' hdet' c =
      ((Real.toNNReal |c.detScalar|)⁻¹ •
        specialFormPreservingSmoothRealFormCongruenceStandardGroupOverlapMeasure
          F F' hF hdet hF' hdet' c)
        (specialFormPreservingRealFormCongruenceFiniteCommonOverlapSet
          F F' hF hdet hF' hdet' c)
    at h
  simpa only [Measure.smul_apply, ENNReal.smul_def,
    specialFormPreservingRealFormCongruenceFiniteStandardOverlapMass] using h

/-- The selected transported global mass is scaled by the explicit-real Haar
comparison scalar. -/
theorem specialFormPreservingRealFormCongruenceFiniteTransportedGlobalMass_eq_smul
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingRealFormCongruenceFiniteTransportedGlobalMass
        F F' hF hdet hF' hdet' c =
      specialFormPreservingRealFormCongruenceHaarScalar
          F F' hF hdet hF' hdet' c *
        specialFormPreservingRealFormCongruenceFiniteCommonMass
          F F' hF hdet hF' hdet' c := by
  have h := congrArg (fun m : Measure
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) =>
        m (specialFormPreservingRealFormCongruenceFiniteCommonSet
          F F' hF hdet hF' hdet' c))
    (map_specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_eq_smul
      F F' hF hdet hF' hdet' c)
  change
    specialFormPreservingRealFormCongruenceFiniteTransportedGlobalMass
        F F' hF hdet hF' hdet' c =
      (specialFormPreservingRealFormCongruenceHaarScalar
          F F' hF hdet hF' hdet' c •
        specialFormPreservingSmoothRealDifferentialMeasure
          F' hF' hdet')
        (specialFormPreservingRealFormCongruenceFiniteCommonSet
          F F' hF hdet hF' hdet' c)
    at h
  simpa [Measure.smul_apply, ENNReal.smul_def,
    specialFormPreservingRealFormCongruenceFiniteCommonMass] using h

end PositiveDefiniteIntegralLattice
