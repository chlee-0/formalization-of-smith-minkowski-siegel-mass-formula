import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteStabilizerVolume
import SMSFormula.PadicSpecialOrthogonalDifferentialCongruence
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite products of the local differential stabilizer measures

This module forms literal finite dependent products of the internally
constructed differential measures on the integral p-adic special-orthogonal
stabilizers.  The total mass is the product of the already computed local
stabilizer volumes.

No restricted product, reference Haar measure, real-place factor, or Tamagawa
theorem is introduced.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance localPadicSpecialOrthogonalDifferentialFiniteProductPrimeFact
    (q : {p : ℕ // Nat.Prime p}) : Fact (Nat.Prime q.1) :=
  ⟨q.2⟩

local instance
    localPadicSpecialOrthogonalDifferentialFiniteProductMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialFiniteProductBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[q.1]))) :=
  ⟨rfl⟩

/-- The corrected differential special stabilizer at a rational prime, with
the required local primality instance installed through the prime subtype. -/
abbrev localPadicSpecialOrthogonalDifferentialStabilizerAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :=
  @localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
    n L q.1 ⟨q.2⟩

/-- The literal corrected differential measure on the special stabilizer at
a rational prime. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    Measure
      (L.localPadicSpecialOrthogonalDifferentialStabilizerAtPrime q) :=
  @localPadicSpecialOrthogonalDifferentialStabilizerMeasure
    n L q.1 ⟨q.2⟩

/-- The prime-indexed differential stabilizer measure has the local
stabilizer volume as its total mass. -/
@[simp]
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime_univ
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime q
        Set.univ =
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [
    localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime,
    localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime] using
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure_univ q.1

/-- Each prime-indexed local differential stabilizer measure is finite. -/
instance
    localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime_isFinite
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    IsFiniteMeasure
      (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime q) where
  measure_univ_lt_top := by
    rw [
      L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime_univ q]
    exact
      (L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_top
        q).lt_top

/-- Each prime-indexed local differential stabilizer measure remains left
invariant. -/
instance
    localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) (q : {p : ℕ // Nat.Prime p}) :
    Measure.IsMulLeftInvariant
      (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime q) := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  simpa only [
    localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime] using
    (inferInstance :
      Measure.IsMulLeftInvariant
        (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure q.1))

/-- The finite dependent product of the local differential special
stabilizers indexed by a finite set of rational primes. -/
abbrev localPadicSpecialOrthogonalDifferentialFiniteStabilizerProduct
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :=
  (q : {q // q ∈ S}) →
    L.localPadicSpecialOrthogonalDifferentialStabilizerAtPrime q.1

/-- The literal finite dependent product of the locally constructed
differential stabilizer measures. -/
noncomputable def
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerProductMeasure
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    Measure
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerProduct S) :=
  Measure.pi fun q : {q // q ∈ S} ↦
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime q.1

/-- The total mass of the literal finite differential product measure is the
finite product of the corrected local stabilizer volumes. -/
@[simp]
theorem
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerProductMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerProductMeasure S
        Set.univ =
      ∏ q ∈ S,
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q := by
  letI (q : {q // q ∈ S}) :
      IsFiniteMeasure
        (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime
          q.1) :=
    localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime_isFinite
      L q.1
  letI (q : {q // q ∈ S}) :
      SigmaFinite
        (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime
          q.1) :=
    @IsFiniteMeasure.toSigmaFinite _ _
      (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime q.1)
      (localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime_isFinite
        L q.1)
  rw [
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerProductMeasure,
    Measure.pi_univ]
  simp only [
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime_univ,
    Finset.prod_coe_sort]

/-- The finite product of the local differential stabilizer measures is
finite. -/
instance
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerProductMeasure_isFinite
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    IsFiniteMeasure
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerProductMeasure
        S) :=
  Measure.pi.instIsFiniteMeasure _

/-- The finite product of the local differential stabilizer measures is left
invariant under componentwise multiplication. -/
instance
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerProductMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    Measure.IsMulLeftInvariant
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerProductMeasure
        S) := by
  letI (q : {q // q ∈ S}) :
      SigmaFinite
        (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime
          q.1) :=
    @IsFiniteMeasure.toSigmaFinite _ _
      (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime q.1)
      (localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime_isFinite
        L q.1)
  letI (q : {q // q ∈ S}) :
      MeasurableMul
        (L.localPadicSpecialOrthogonalDifferentialStabilizerAtPrime q.1) :=
    inferInstance
  letI (q : {q // q ∈ S}) :
      Measure.IsMulLeftInvariant
        (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime
          q.1) :=
    localPadicSpecialOrthogonalDifferentialStabilizerMeasureAtPrime_isMulLeftInvariant
      L q.1
  unfold
    localPadicSpecialOrthogonalDifferentialFiniteStabilizerProductMeasure
  exact Measure.pi.isMulLeftInvariant _

end PositiveDefiniteIntegralLattice
