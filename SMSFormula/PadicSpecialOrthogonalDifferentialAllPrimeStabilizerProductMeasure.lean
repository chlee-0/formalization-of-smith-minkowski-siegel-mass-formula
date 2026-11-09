import SMSFormula.PadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure
import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteStabilizerVolume

/-!
# Absolutely scaled all-prime differential stabilizer product measure

The canonical normalized product of the local integral
special-orthogonal stabilizers is multiplied by the internally computed finite
differential stabilizer-volume scalar.  Its total mass is therefore the named
finite differential volume, and every finite coordinate marginal retains the
same scalar.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialAllPrimeProductPrimeFact
    (q : {p : ℕ // Nat.Prime p}) : Fact (Nat.Prime q.1) :=
  ⟨q.2⟩

local instance
    localPadicSpecialOrthogonalDifferentialAllPrimeProductMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialAllPrimeProductBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  ⟨rfl⟩

/-- The absolute differential measure on the all-prime product of the literal
local integral special stabilizers.  Its scalar is the internally computed
finite differential stabilizer volume attached to the cutoff-product limit
`P`. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    Measure
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct :=
  L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
    L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure

/-- The absolute all-prime product measure has exactly the named finite
differential stabilizer volume as its total mass. -/
@[simp]
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
        P Set.univ =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P := by
  rw [
    localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure,
    Measure.smul_apply, measure_univ]
  change
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P * 1 =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P
  exact mul_one _

/-- The total mass of the absolute all-prime product measure is nonzero. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_univ_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
        P Set.univ ≠
      0 := by
  rw [
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_univ
      P]
  exact
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_zero P

/-- A positive cutoff-product limit makes the total mass of the absolute
all-prime product measure finite. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_univ_ne_top
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
        P Set.univ ≠
      ⊤ := by
  rw [
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_univ
      P]
  exact
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_ne_top hP

/-- Under a positive cutoff-product limit, the absolute all-prime product is
a finite measure.  This certificate can be installed locally where the
explicit positivity hypothesis is available. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_isFinite
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    IsFiniteMeasure
      (L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
        P) where
  measure_univ_lt_top :=
    (L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_univ_ne_top
      hP).lt_top

/-- The reciprocal of the total mass is the named finite differential
stabilizer inverse volume. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_univ_inv
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    (L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
        P Set.univ)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume
        P := by
  rw [
    L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_univ
      P]
  exact
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_eq_inv_volume
      P).symm

/-- Absolute scaling preserves left invariance of the normalized all-prime
product measure. -/
instance
    localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    Measure.IsMulLeftInvariant
      (L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
        P) := by
  unfold
    localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
  infer_instance

/-- Every finite coordinate marginal of the absolute all-prime differential
product is the same finite differential volume scalar times the finite
normalized product. -/
theorem
    localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure_map_restrict
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (S : Finset {p : ℕ // Nat.Prime p}) :
    (L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
        P).map S.restrict =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
        Measure.pi fun q : {q // q ∈ S} ↦
          L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
            q.1 := by
  calc
    (L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure
          P).map S.restrict =
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
          L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure.map
            S.restrict := by
      rw [
        localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProductMeasure,
        Measure.map_smul]
    _ =
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
          Measure.pi fun q : {q // q ∈ S} ↦
            L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
              q.1 :=
      congrArg
        (fun μ =>
          L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P •
            μ)
        (L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure_map_restrict
          S)

end PositiveDefiniteIntegralLattice
