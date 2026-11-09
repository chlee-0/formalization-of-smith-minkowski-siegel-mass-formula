import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteProductMeasure
import Mathlib.Probability.ProductMeasure

/-!
# Normalized all-prime product of the local differential stabilizer measures

Each literal local differential stabilizer measure is divided by its own
already computed positive finite total mass.  The resulting probability
measures are assembled by `Measure.infinitePi` on the dependent product of the
actual local integral special-orthogonal stabilizers.

This is the canonical normalized compact product only.  It is not scaled by
the finite differential stabilizer-volume scalar and is not identified with an
adelic or restricted-product carrier.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialNormalizedProductPrimeFact
    (q : {p : ℕ // Nat.Prime p}) : Fact (Nat.Prime q.1) :=
  ⟨q.2⟩

local instance
    localPadicSpecialOrthogonalDifferentialNormalizedProductMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialNormalizedProductBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  ⟨rfl⟩

/-- Normalize the literal local differential stabilizer measure by the
inverse of its positive finite total mass. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    Measure
      (L.localPadicSpecialOrthogonalDifferentialStabilizerAtPrime q) :=
  (L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q)⁻¹ •
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime q

/-- The normalized local differential stabilizer measure has total mass one. -/
@[simp]
theorem
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime_univ
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
        q Set.univ =
      1 := by
  rw [
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime,
    Measure.smul_apply,
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime_univ q]
  exact ENNReal.inv_mul_cancel
    (L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_zero
      q)
    (L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_top q)

/-- Every normalized local differential stabilizer measure is a probability
measure. -/
instance
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime_isProbability
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    IsProbabilityMeasure
      (L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
        q) where
  measure_univ :=
    L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime_univ
      q

/-- Normalization by the total-mass scalar preserves local left invariance. -/
instance
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    Measure.IsMulLeftInvariant
      (L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
        q) := by
  unfold
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
  infer_instance

/-- The dependent product of the integral differential special stabilizers
over all rational primes. -/
abbrev localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct
    (L : PositiveDefiniteIntegralLattice n) :=
  (q : {p : ℕ // Nat.Prime p}) →
    L.localPadicSpecialOrthogonalDifferentialStabilizerAtPrime q

/-- The canonical probability product of the normalized local differential
stabilizer measures. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure
      L.localPadicSpecialOrthogonalDifferentialAllPrimeStabilizerProduct :=
  Measure.infinitePi fun q : {p : ℕ // Nat.Prime p} ↦
    L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
      q

/-- The canonical all-prime normalized stabilizer product is a probability
measure. -/
instance
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure_isProbability
    (L : PositiveDefiniteIntegralLattice n) :
    IsProbabilityMeasure
      L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure := by
  letI (q : {p : ℕ // Nat.Prime p}) :
      IsProbabilityMeasure
        (L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
          q) :=
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime_isProbability
      L q
  unfold
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure
  infer_instance

/-- Every finite coordinate marginal of the canonical normalized all-prime
product is the finite `Measure.pi` of the same normalized local factors. -/
theorem
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure_map_restrict
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure.map
        S.restrict =
      Measure.pi fun q : {q // q ∈ S} ↦
        L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
          q.1 := by
  letI (q : {p : ℕ // Nat.Prime p}) :
      IsProbabilityMeasure
        (L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
          q) :=
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime_isProbability
      L q
  simpa only [
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure]
    using
      (Measure.infinitePi_map_restrict
        (μ := fun q : {p : ℕ // Nat.Prime p} ↦
          L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
            q)
        (I := S))

/-- The canonical normalized all-prime stabilizer product remains left
invariant under componentwise multiplication. -/
instance
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsMulLeftInvariant
      L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure := by
  letI (q : {p : ℕ // Nat.Prime p}) :
      IsProbabilityMeasure
        (L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
          q) :=
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime_isProbability
      L q
  letI (q : {p : ℕ // Nat.Prime p}) :
      MeasurableMul
        (L.localPadicSpecialOrthogonalDifferentialStabilizerAtPrime q) :=
    inferInstance
  letI (q : {p : ℕ // Nat.Prime p}) :
      Measure.IsMulLeftInvariant
        (L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
          q) :=
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime_isMulLeftInvariant
      L q
  refine ⟨fun g ↦ ?_⟩
  unfold
    localPadicSpecialOrthogonalDifferentialNormalizedStabilizerProductMeasure
  change
    Measure.map (fun x q ↦ g q * x q)
        (Measure.infinitePi fun q : {p : ℕ // Nat.Prime p} ↦
          L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
            q) =
      Measure.infinitePi fun q : {p : ℕ // Nat.Prime p} ↦
        L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
          q
  rw [
    Measure.infinitePi_map_pi
      (μ := fun q : {p : ℕ // Nat.Prime p} ↦
        L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
          q)
      (f := fun q x ↦ g q * x)
      (fun q ↦ measurable_const_mul (g q))]
  congr 1
  funext q
  exact map_mul_left_eq_self
    (L.localPadicSpecialOrthogonalDifferentialNormalizedStabilizerMeasureAtPrime
      q)
    (g q)

end PositiveDefiniteIntegralLattice
