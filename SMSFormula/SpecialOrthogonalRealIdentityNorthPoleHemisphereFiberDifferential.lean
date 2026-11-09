import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductLiteralSphereFiberMeasure

/-!
# The identity differential fiber on the positive hemisphere

This module identifies the north-pole-section representative used by the
local sphere-side product with the sphere-indexed differential fiber
candidate.  The pointwise measure equality, its kernel-application form,
and the normalized-sphere-restriction almost-everywhere form are kept
separate.

No kernel integration, coupled higher-chart restriction inside a bind,
total-mass cancellation, rank recurrence, or Gamma evaluation is used here.
-/

open scoped Matrix Matrix.Norms.Operator NNReal ENNReal ProbabilityTheory

noncomputable section

open Matrix MeasureTheory Set Metric

namespace PositiveDefiniteIntegralLattice

local instance identityNorthPoleHemisphereFiberDifferentialGroupMeasurableSpace
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identityNorthPoleHemisphereFiberDifferentialGroupBorelSpace
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- The north-pole section at the recovered positive-hemisphere coordinate has
the original sphere point as its last column. -/
theorem
    identitySpecialOrthogonalLastColumn_northPoleSection_coordinateHomeomorph
    (n : ℕ)
    (x : identitySpecialOrthogonalLastColumnSphere (n + 1))
    (hx :
      x ∈ identitySpecialOrthogonalNorthPoleHemisphere (n + 1)) :
    identitySpecialOrthogonalLastColumn (n + 1)
        (identitySpecialOrthogonalNorthPoleSection (n + 1)
          (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
            (n + 1) ⟨x, hx⟩)) =
      x := by
  calc
    identitySpecialOrthogonalLastColumn (n + 1)
        (identitySpecialOrthogonalNorthPoleSection (n + 1)
          (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
            (n + 1) ⟨x, hx⟩)) =
      identitySpecialOrthogonalNorthPoleInverse (n + 1)
        (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
          (n + 1) ⟨x, hx⟩) :=
      identitySpecialOrthogonalLastColumn_northPoleSection
        (n + 1) _
    _ = x := by
      exact
        congrArg Subtype.val
          ((identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
            (n + 1)).symm_apply_apply ⟨x, hx⟩)

/-- On the positive hemisphere, the existing sphere-indexed differential
fiber candidate is the full lower differential Haar pushed through the
north-pole-section fiber parametrization. -/
theorem
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure_eq_map_northPoleSection
    (n : ℕ)
    (x : identitySpecialOrthogonalLastColumnSphere (n + 1))
    (hx :
      x ∈ identitySpecialOrthogonalNorthPoleHemisphere (n + 1)) :
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure n x =
      Measure.map
        (identitySpecialOrthogonalLastColumnFiberParametrization n
          (identitySpecialOrthogonalNorthPoleSection (n + 1)
            (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
              (n + 1) ⟨x, hx⟩)))
        (identitySpecialOrthogonalDifferentialMeasure n) := by
  let g :=
    identitySpecialOrthogonalNorthPoleSection (n + 1)
      (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
        (n + 1) ⟨x, hx⟩)
  have hcol :
      identitySpecialOrthogonalLastColumn (n + 1) g = x :=
    identitySpecialOrthogonalLastColumn_northPoleSection_coordinateHomeomorph
      n x hx
  calc
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure n x =
      identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure n
        (identitySpecialOrthogonalLastColumn (n + 1) g) :=
      congrArg
        (identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure n)
        hcol.symm
    _ = identitySpecialOrthogonalLastColumnFiberDifferentialMeasure n g :=
      identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure_lastColumn
        n g
    _ =
      Measure.map
        (identitySpecialOrthogonalLastColumnFiberParametrization n g)
        (identitySpecialOrthogonalDifferentialMeasure n) :=
      rfl

/-- Kernel-application form of the positive-hemisphere differential fiber
identification. -/
theorem
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_apply_eq_map_northPoleSection
    (n : ℕ)
    (x : identitySpecialOrthogonalLastColumnSphere (n + 1))
    (hx :
      x ∈ identitySpecialOrthogonalNorthPoleHemisphere (n + 1)) :
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n x =
      Measure.map
        (identitySpecialOrthogonalLastColumnFiberParametrization n
          (identitySpecialOrthogonalNorthPoleSection (n + 1)
            (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
              (n + 1) ⟨x, hx⟩)))
        (identitySpecialOrthogonalDifferentialMeasure n) := by
  rw [
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_apply,
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialMeasure_eq_map_northPoleSection
      n x hx]

/-- The kernel identification holds almost everywhere under normalized sphere
measure restricted to the positive hemisphere. The universal quantifier over
the membership proof makes the statement independent of proof choice. -/
theorem
    ae_identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_apply_eq_map_northPoleSection
    (n : ℕ) :
    ∀ᵐ x ∂
      (identitySpecialOrthogonalNormalizedSphereMeasure (n + 1)).restrict
        (identitySpecialOrthogonalNorthPoleHemisphere (n + 1)),
      ∀ hx :
        x ∈ identitySpecialOrthogonalNorthPoleHemisphere (n + 1),
        identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel n x =
          Measure.map
            (identitySpecialOrthogonalLastColumnFiberParametrization n
              (identitySpecialOrthogonalNorthPoleSection (n + 1)
                (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
                  (n + 1) ⟨x, hx⟩)))
            (identitySpecialOrthogonalDifferentialMeasure n) := by
  filter_upwards [
    MeasureTheory.ae_restrict_mem
      (measurableSet_identitySpecialOrthogonalNorthPoleHemisphere
        (n + 1))] with x hx
  intro hx'
  exact
    identitySpecialOrthogonalLastColumnSphereFiberDifferentialKernel_apply_eq_map_northPoleSection
      n x hx'

end PositiveDefiniteIntegralLattice
