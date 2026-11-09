import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleSection
import SMSFormula.SpecialOrthogonalRealIdentitySphereMeasureInvariant

/-!
# Sphere measure in identity north-pole coordinates

This module transports Mathlib's additive-Haar-induced sphere measure from
the positive hemisphere to the open Euclidean unit ball.  It also records the
intrinsic graph-density candidate and its north-pole normalization.  The
codimension-one graph-area formula needed to identify the two measures is not
asserted here.
-/

open scoped ENNReal Matrix Matrix.Norms.Operator

noncomputable section

open MeasureTheory
open Metric Set

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 100000

/-- The Euclidean sphere measure restricted to the positive-hemisphere
subtype. -/
def identitySpecialOrthogonalNorthPoleHemisphereSphereMeasure (n : ℕ) :
    Measure
      (identitySpecialOrthogonalNorthPoleHemisphere n :
        Set (identitySpecialOrthogonalLastColumnSphere n)) :=
  Measure.comap Subtype.val
    ((volume :
      Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere)

/-- Positive-hemisphere sphere measure in the open-ball coordinates. -/
def identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure (n : ℕ) :
    Measure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  Measure.map
    (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n)
    (identitySpecialOrthogonalNorthPoleHemisphereSphereMeasure n)

/-- Mapping the coordinate measure back through the north-pole chart recovers
the positive-hemisphere sphere measure. -/
theorem map_identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_symm
    (n : ℕ) :
    Measure.map
        (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).symm
        (identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n) =
      identitySpecialOrthogonalNorthPoleHemisphereSphereMeasure n := by
  rw [identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure]
  exact MeasurableEquiv.map_map_symm
    (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
      n).symm.toMeasurableEquiv

/-- The coordinate pushforward has exactly the sphere mass of the positive
hemisphere. -/
theorem identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n Set.univ =
      (volume :
        Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
          (identitySpecialOrthogonalNorthPoleHemisphere n) := by
  rw [identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure,
    Measure.map_apply
      (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).measurable
      MeasurableSet.univ]
  simp only [preimage_univ,
    identitySpecialOrthogonalNorthPoleHemisphereSphereMeasure]
  rw [comap_subtype_coe_apply
    (measurableSet_identitySpecialOrthogonalNorthPoleHemisphere n)]
  simp

theorem identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ_pos
    (n : ℕ) :
    0 <
      identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n
        Set.univ := by
  rw [identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ]
  exact
    (isOpen_identitySpecialOrthogonalNorthPoleHemisphere n).measure_pos _
      ⟨identitySpecialOrthogonalNorthPole n,
        identitySpecialOrthogonalNorthPole_mem_hemisphere n⟩

theorem identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_ne_zero
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n ≠ 0 := by
  intro h
  have hpos :=
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ_pos n
  rw [h] at hpos
  simp at hpos

theorem identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ_lt_top
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n
        Set.univ < ⊤ := by
  rw [identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure_univ]
  exact measure_lt_top _ _

/-- The normalized sphere measure restricted to the positive-hemisphere
subtype. -/
def identitySpecialOrthogonalNorthPoleHemisphereNormalizedSphereMeasure
    (n : ℕ) :
    Measure
      (identitySpecialOrthogonalNorthPoleHemisphere n :
        Set (identitySpecialOrthogonalLastColumnSphere n)) :=
  Measure.comap Subtype.val
    (identitySpecialOrthogonalNormalizedSphereMeasure n)

/-- Normalized sphere measure in the open-ball coordinates. -/
def identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure
    (n : ℕ) :
    Measure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  Measure.map
    (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n)
    (identitySpecialOrthogonalNorthPoleHemisphereNormalizedSphereMeasure n)

/-- Coordinate transport commutes with the already fixed global sphere
normalization. -/
theorem
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure_eq_smul
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure n =
      ((volume :
        Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere Set.univ)⁻¹ •
        identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure n := by
  rw [identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure,
    identitySpecialOrthogonalNorthPoleHemisphereNormalizedSphereMeasure,
    identitySpecialOrthogonalNormalizedSphereMeasure,
    Measure.comap_smul, Measure.map_smul,
    identitySpecialOrthogonalNorthPoleCoordinateSphereMeasure,
    identitySpecialOrthogonalNorthPoleHemisphereSphereMeasure]

/-- The normalized coordinate pushforward has exactly the normalized sphere
mass of the positive hemisphere. -/
theorem
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure_univ
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure n
        Set.univ =
      identitySpecialOrthogonalNormalizedSphereMeasure n
        (identitySpecialOrthogonalNorthPoleHemisphere n) := by
  rw [identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure,
    Measure.map_apply
      (identitySpecialOrthogonalNorthPoleCoordinateHomeomorph n).measurable
      MeasurableSet.univ]
  simp only [preimage_univ,
    identitySpecialOrthogonalNorthPoleHemisphereNormalizedSphereMeasure]
  rw [comap_subtype_coe_apply
    (measurableSet_identitySpecialOrthogonalNorthPoleHemisphere n)]
  simp

theorem
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure_univ_lt_top
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure n
        Set.univ < ⊤ := by
  rw [
    identitySpecialOrthogonalNorthPoleCoordinateNormalizedSphereMeasure_univ]
  exact measure_lt_top _ _

/-- The graph-area density expected from the square-root lift.  It remains a
candidate until a codimension-one area formula is proved from the radial
definition of `Measure.toSphere`. -/
def identitySpecialOrthogonalNorthPoleCoordinateDensity
    (v : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal
    (identitySpecialOrthogonalNorthPoleFinalCoordinate v)⁻¹

theorem identitySpecialOrthogonalNorthPoleCoordinateDensity_pos
    {n : ℕ} {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    0 < identitySpecialOrthogonalNorthPoleCoordinateDensity v := by
  rw [identitySpecialOrthogonalNorthPoleCoordinateDensity,
    ENNReal.ofReal_pos]
  exact inv_pos.mpr
    (identitySpecialOrthogonalNorthPoleFinalCoordinate_pos hv)

theorem identitySpecialOrthogonalNorthPoleCoordinateDensity_ne_top
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleCoordinateDensity v ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem measurable_identitySpecialOrthogonalNorthPoleCoordinateDensity
    (n : ℕ) :
    Measurable
      (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n)) := by
  exact ENNReal.continuous_ofReal.measurable.comp
    ((continuous_identitySpecialOrthogonalNorthPoleFinalCoordinate
      n).measurable.inv)

/-- The candidate graph density is continuous on the exact open ball. -/
theorem continuousOn_identitySpecialOrthogonalNorthPoleCoordinateDensity
    (n : ℕ) :
    ContinuousOn
      (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  apply ENNReal.continuous_ofReal.comp_continuousOn
  apply
    (continuous_identitySpecialOrthogonalNorthPoleFinalCoordinate
      n).continuousOn.inv₀
  intro v hv
  exact
    (identitySpecialOrthogonalNorthPoleFinalCoordinate_pos hv).ne'

/-- On the open-ball subtype the candidate graph density is continuous. -/
theorem continuous_identitySpecialOrthogonalNorthPoleCoordinateDensity_subtype
    (n : ℕ) :
    Continuous
      (fun v : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        identitySpecialOrthogonalNorthPoleCoordinateDensity v.1) :=
  (continuousOn_identitySpecialOrthogonalNorthPoleCoordinateDensity
    n).comp_continuous continuous_subtype_val (fun v => v.2)

/-- The graph-density candidate has the required unit Jacobian normalization
at the north pole. -/
@[simp]
theorem identitySpecialOrthogonalNorthPoleCoordinateDensity_zero
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinateDensity
        (0 : EuclideanSpace ℝ (Fin n)) = 1 := by
  simp [identitySpecialOrthogonalNorthPoleCoordinateDensity,
    identitySpecialOrthogonalNorthPoleFinalCoordinate]

/-- The candidate density measure on the exact open-ball subtype.  This
definition does not identify it with the transported sphere measure. -/
def identitySpecialOrthogonalNorthPoleCoordinateDensityMeasure (n : ℕ) :
    Measure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  Measure.comap Subtype.val
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (identitySpecialOrthogonalNorthPoleCoordinateDensity (n := n)))

end PositiveDefiniteIntegralLattice
