import SMSFormula.SpecialOrthogonalRealIdentitySphereAveraging

/-!
# Differential normalization of the identity last-column pushforward
-/

open scoped Matrix Matrix.Norms.Operator ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 100000

local instance identitySpecialOrthogonalGroupMeasurableSpace_differentialPushforward
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identitySpecialOrthogonalGroupBorelSpace_differentialPushforward
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- Canonical differential Haar is its total mass times probability Haar.
The scalar is evaluated from Haar uniqueness on the compact identity group. -/
theorem identitySpecialOrthogonalDifferentialMeasure_eq_univ_smul_probabilityHaar
    (n : ℕ) :
    identitySpecialOrthogonalDifferentialMeasure n =
      identitySpecialOrthogonalDifferentialMeasure n Set.univ •
        identitySpecialOrthogonalProbabilityHaarMeasure n := by
  let c : ℝ≥0∞ :=
    Measure.haarScalarFactor
      (identitySpecialOrthogonalDifferentialMeasure n)
      (identitySpecialOrthogonalProbabilityHaarMeasure n)
  have hhaar :
      identitySpecialOrthogonalDifferentialMeasure n =
        c • identitySpecialOrthogonalProbabilityHaarMeasure n := by
    simpa [c] using
      Measure.isMulInvariant_eq_smul_of_compactSpace
        (identitySpecialOrthogonalDifferentialMeasure n)
        (identitySpecialOrthogonalProbabilityHaarMeasure n)
  have hc :
      c = identitySpecialOrthogonalDifferentialMeasure n Set.univ := by
    have hmass := congrArg
      (fun μ : Measure (identitySpecialOrthogonalGroup n) => μ Set.univ)
      hhaar
    change identitySpecialOrthogonalDifferentialMeasure n Set.univ =
      (c • identitySpecialOrthogonalProbabilityHaarMeasure n) Set.univ at hmass
    simpa [Measure.smul_apply, ENNReal.smul_def,
      identitySpecialOrthogonalProbabilityHaarMeasure_univ] using hmass.symm
  simpa [hc] using hhaar

/-- The last-column pushforward of canonical differential Haar is its source
total mass times normalized Euclidean sphere measure. This is only a global
pushforward normalization; no fiber disintegration is asserted. -/
theorem identitySpecialOrthogonalLastColumnDifferentialMeasure_eq_univ_smul_normalizedSphere
    (n : ℕ) (hn : 0 < n) :
    identitySpecialOrthogonalLastColumnDifferentialMeasure n =
      identitySpecialOrthogonalDifferentialMeasure n Set.univ •
        identitySpecialOrthogonalNormalizedSphereMeasure n := by
  calc
    identitySpecialOrthogonalLastColumnDifferentialMeasure n =
        Measure.map (identitySpecialOrthogonalLastColumn n)
          (identitySpecialOrthogonalDifferentialMeasure n) := rfl
    _ = Measure.map (identitySpecialOrthogonalLastColumn n)
        (identitySpecialOrthogonalDifferentialMeasure n Set.univ •
          identitySpecialOrthogonalProbabilityHaarMeasure n) := by
      exact congrArg
        (Measure.map (identitySpecialOrthogonalLastColumn n))
        (identitySpecialOrthogonalDifferentialMeasure_eq_univ_smul_probabilityHaar n)
    _ = identitySpecialOrthogonalDifferentialMeasure n Set.univ •
        Measure.map (identitySpecialOrthogonalLastColumn n)
          (identitySpecialOrthogonalProbabilityHaarMeasure n) := by
      rw [Measure.map_smul]
    _ = identitySpecialOrthogonalDifferentialMeasure n Set.univ •
        identitySpecialOrthogonalLastColumnProbabilityMeasure n := rfl
    _ = identitySpecialOrthogonalDifferentialMeasure n Set.univ •
        identitySpecialOrthogonalNormalizedSphereMeasure n := by
      rw [
        identitySpecialOrthogonalLastColumnProbabilityMeasure_eq_normalizedSphereMeasure
          n hn]

end PositiveDefiniteIntegralLattice
