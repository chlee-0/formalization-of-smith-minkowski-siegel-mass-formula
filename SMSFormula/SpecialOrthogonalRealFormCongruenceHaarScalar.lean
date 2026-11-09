import SMSFormula.SpecialOrthogonalRealFormCongruenceGlobalRecovery

/-!
# Haar uniqueness for explicit real-form congruence

This module defines the canonical Haar-uniqueness scalar comparing the source
differential measure transported through an explicit real congruence with the
independently normalized target differential measure.  Identification with
the tangent-basis determinant is left to a finite-positive local cancellation
argument.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realFormCongruenceHaarScalarGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realFormCongruenceHaarScalarGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- An explicit real group congruence transports source differential Haar to
a Haar measure on the target group. -/
theorem map_specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_isHaarMeasure
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.IsHaarMeasure
      (Measure.map c.groupEquiv.toHomeomorph
        (specialFormPreservingSmoothRealDifferentialMeasure
          F hF hdet)) := by
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_locallyCompact F' hF' hdet'
  letI : SecondCountableTopology
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_secondCountable F'
  letI : Measure.IsHaarMeasure
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) :=
    specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
      F hF hdet
  exact
    c.groupEquiv.toMulEquiv.isHaarMeasure_map
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)
      c.groupEquiv.continuous c.groupEquiv.symm.continuous

/-- The canonical Haar-uniqueness scalar for an explicit real congruence. Its
identification with `|c.detScalar|⁻¹` is a separate local normalization
theorem. -/
def specialFormPreservingRealFormCongruenceHaarScalar
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') : ℝ≥0∞ :=
  let μ := Measure.map c.groupEquiv.toHomeomorph
    (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)
  let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_locallyCompact F' hF' hdet'
  letI : SecondCountableTopology
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_secondCountable F'
  letI : Measure.IsHaarMeasure μ :=
    map_specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_isHaarMeasure
      F F' hF hdet hF' hdet' c
  letI : Measure.IsHaarMeasure ν :=
    specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
      F' hF' hdet'
  Measure.haarScalarFactor μ ν

/-- Haar uniqueness compares transported source differential Haar with target
differential Haar by the explicit-real congruence scalar. -/
theorem map_specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_eq_smul
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Measure.map c.groupEquiv.toHomeomorph
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) =
      specialFormPreservingRealFormCongruenceHaarScalar
          F F' hF hdet hF' hdet' c •
        specialFormPreservingSmoothRealDifferentialMeasure
          F' hF' hdet' := by
  let μ :=
    Measure.map c.groupEquiv.toHomeomorph
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)
  let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_locallyCompact F' hF' hdet'
  letI : SecondCountableTopology
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_secondCountable F'
  letI : Measure.IsHaarMeasure μ :=
    map_specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_isHaarMeasure
      F F' hF hdet hF' hdet' c
  letI : Measure.IsHaarMeasure ν :=
    specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
      F' hF' hdet'
  simpa [specialFormPreservingRealFormCongruenceHaarScalar, μ, ν] using
    Measure.isMulLeftInvariant_eq_smul μ ν

/-- The global comparison gives the explicit-real total differential-mass
relation. -/
theorem specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_univ
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealDifferentialMeasure
        F hF hdet Set.univ =
      specialFormPreservingRealFormCongruenceHaarScalar
          F F' hF hdet hF' hdet' c *
        specialFormPreservingSmoothRealDifferentialMeasure
          F' hF' hdet' Set.univ := by
  let μ := specialFormPreservingSmoothRealDifferentialMeasure F hF hdet
  have h := congrArg
    (fun m : Measure
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) => m Set.univ)
    (map_specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_eq_smul
      F F' hF hdet hF' hdet' c)
  have hmap :
      Measure.map c.groupEquiv.toHomeomorph μ Set.univ =
        μ Set.univ := by
    rw [Measure.map_apply c.groupEquiv.measurable MeasurableSet.univ]
    simp
  change Measure.map c.groupEquiv.toHomeomorph μ Set.univ =
    (specialFormPreservingRealFormCongruenceHaarScalar
        F F' hF hdet hF' hdet' c •
      specialFormPreservingSmoothRealDifferentialMeasure
        F' hF' hdet') Set.univ at h
  rw [hmap] at h
  simpa [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using h

/-- The positive-diagonal-to-identity Haar-uniqueness scalar. -/
abbrev positiveDiagonalRealFormCongruenceHaarScalar
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) : ℝ≥0∞ :=
  specialFormPreservingRealFormCongruenceHaarScalar
    (Matrix.diagonal d) 1
    (positiveDiagonalForm_isSymm d)
    (positiveDiagonalForm_det_ne_zero d hd)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (positiveDiagonalRealFormCongruenceData d hd)

/-- Haar uniqueness for inverse-square-root scaling from a positive rational
diagonal form to the identity model. -/
theorem map_positiveDiagonalSmoothRealDifferentialMeasure_eq_smul
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    Measure.map
        (positiveDiagonalRealFormCongruenceData d hd).groupEquiv.toHomeomorph
        (specialFormPreservingSmoothRealDifferentialMeasure
          (Matrix.diagonal d)
          (positiveDiagonalForm_isSymm d)
          (positiveDiagonalForm_det_ne_zero d hd)) =
      positiveDiagonalRealFormCongruenceHaarScalar d hd •
        specialFormPreservingSmoothRealDifferentialMeasure
          1 identityRationalForm_isSymm
          identityRationalForm_det_ne_zero :=
  map_specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_eq_smul
    (Matrix.diagonal d) 1
    (positiveDiagonalForm_isSymm d)
    (positiveDiagonalForm_det_ne_zero d hd)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (positiveDiagonalRealFormCongruenceData d hd)

/-- The positive-diagonal differential total mass is the Haar-uniqueness
scalar times the identity-model differential total mass. -/
theorem positiveDiagonalSmoothRealDifferentialMeasure_univ
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    specialFormPreservingSmoothRealDifferentialMeasure
        (Matrix.diagonal d)
        (positiveDiagonalForm_isSymm d)
        (positiveDiagonalForm_det_ne_zero d hd) Set.univ =
      positiveDiagonalRealFormCongruenceHaarScalar d hd *
        specialFormPreservingSmoothRealDifferentialMeasure
          (1 : Matrix (Fin n) (Fin n) ℚ)
          identityRationalForm_isSymm
          identityRationalForm_det_ne_zero Set.univ :=
  specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_univ
    (Matrix.diagonal d) 1
    (positiveDiagonalForm_isSymm d)
    (positiveDiagonalForm_det_ne_zero d hd)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (positiveDiagonalRealFormCongruenceData d hd)

end PositiveDefiniteIntegralLattice
