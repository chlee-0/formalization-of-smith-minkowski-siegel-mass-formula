import SMSFormula.IntegralQuadraticFormMassTransport
import SMSFormula.Product

/-!
# Bad primes of an integral quadratic form and raw odd-prime congruence solutions

For an integral quadratic form `H`, the direct integral bilinear Gram
matrix is `A = H.polarGramMatrix`.  This file defines its natural bad-prime
set and proves that it agrees with the bad-prime set of the scaled integral
integral model.  It also compares, at every odd prime power, the raw matrix solutions
preserving `A` with the old integral model solutions preserving `2A`.

No local-dual quotient or density factor is identified here, and no statement
at the dyadic prime is made.
-/

open Matrix

noncomputable section

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

/-! ## Natural bad-prime set of the integral quadratic form -/

/-- The dyadic prime together with the prime divisors of the integral polar
discriminant `det(A)`. -/
def massBadPrimeSet : Finset {p : ℕ // Nat.Prime p} :=
  insert ⟨2, Nat.prime_two⟩
    ((H.polarDeterminant.natAbs.primeFactors.attach).map
      ⟨fun p => ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩,
        by
          intro p q hpq
          exact Subtype.ext
            (show p.1 = q.1 from
              congrArg (fun r : {p : ℕ // Nat.Prime p} => r.1) hpq)⟩)

theorem mem_massBadPrimeSet_iff
    (p : {p : ℕ // Nat.Prime p}) :
    p ∈ H.massBadPrimeSet ↔
      p.1 = 2 ∨ p.1 ∣ H.polarDeterminant.natAbs := by
  have hdisc_ne : H.polarDeterminant.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (ne_of_gt H.polarDeterminant_pos)
  simp only [massBadPrimeSet, Finset.mem_insert, Finset.mem_map,
    Finset.mem_attach]
  constructor
  · intro hp
    rcases hp with hp | ⟨q, _hqmem, hq⟩
    · exact Or.inl (congrArg (fun r : {p : ℕ // Nat.Prime p} => r.1) hp)
    · refine Or.inr ?_
      have hq_dvd : q.1 ∣ H.polarDeterminant.natAbs :=
        (Nat.mem_primeFactors.mp q.2).2.1
      have hq_val : q.1 = p.1 :=
        congrArg (fun r : {p : ℕ // Nat.Prime p} => r.1) hq
      simpa [hq_val] using hq_dvd
  · intro hp
    rcases hp with hp | hp
    · exact Or.inl (Subtype.ext hp)
    · exact Or.inr
        ⟨⟨p.1, Nat.mem_primeFactors.mpr ⟨p.2, hp, hdisc_ne⟩⟩,
          trivial, Subtype.ext rfl⟩

/-- The scaled integral model discriminant is `det(2A) = 2^n det(A)`. -/
theorem latticeOfPolarForm_polarDeterminant_eq_two_pow_mul_polarDeterminant :
    H.latticeOfPolarForm.polarDeterminant =
      (2 : ℤ) ^ n * H.polarDeterminant := by
  simpa [PositiveDefiniteIntegralLattice.pairingDeterminant, polarDeterminant] using
    H.latticeOfPolarForm.polarDeterminant_eq_two_pow_mul_pairingDeterminant

/-- Inserting the dyadic prime makes the direct polar-discriminant support
identical to the scaled integral model's bilinear-discriminant support. -/
theorem massBadPrimeSet_eq_latticeOfPolarForm :
    H.massBadPrimeSet =
      PositiveDefiniteIntegralLattice.massBadPrimeSet H.latticeOfPolarForm := by
  ext p
  rw [H.mem_massBadPrimeSet_iff,
    PositiveDefiniteIntegralLattice.mem_massBadPrimeSet_iff]
  by_cases hp_two : p.1 = 2
  · simp [hp_two]
  · simp only [hp_two, false_or]
    rw [H.latticeOfPolarForm_polarDeterminant_eq_two_pow_mul_polarDeterminant,
      Int.natAbs_mul, Int.natAbs_pow]
    norm_num
    constructor
    · intro hp
      exact dvd_mul_of_dvd_right hp _
    · intro hp
      rcases p.2.dvd_mul.mp hp with hp_pow | hp_disc
      · exact False.elim (hp_two <| by
          have hp_dvd_two : p.1 ∣ 2 :=
            Nat.Prime.dvd_of_dvd_pow p.2 hp_pow
          exact (Nat.dvd_prime Nat.prime_two).mp hp_dvd_two |>.resolve_left p.2.ne_one)
      · exact hp_disc

/-! ## Direct raw polar-Gram congruence solutions -/

/-- Matrices modulo `p^k` preserving the direct polar Gram matrix `A`. -/
def polarGramCongruenceSolutionMatrices (p k : ℕ)
    [Fact (Nat.Prime p)] :
    Finset (Matrix (Fin n) (Fin n)
      (ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ))) :=
  PositiveDefiniteIntegralLattice.congruenceSolutionMatrices H.polarGramMatrix
    (PositiveDefiniteIntegralLattice.primePowModulus p k)

theorem mem_polarGramCongruenceSolutionMatrices_iff
    {p k : ℕ} [Fact (Nat.Prime p)]
    {X : Matrix (Fin n) (Fin n)
      (ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ))} :
    X ∈ H.polarGramCongruenceSolutionMatrices p k ↔
      Xᵀ * PositiveDefiniteIntegralLattice.matrixMod H.polarGramMatrix
          (PositiveDefiniteIntegralLattice.primePowModulus p k) * X =
        PositiveDefiniteIntegralLattice.matrixMod H.polarGramMatrix
          (PositiveDefiniteIntegralLattice.primePowModulus p k) := by
  exact PositiveDefiniteIntegralLattice.mem_congruenceSolutionMatrices_iff

/-- Every direct polar-Gram solution is a solution for the scaled integral model's
old polar Gram matrix `2A`. -/
theorem mem_latticeOfPolarForm_gramCongruenceSolutionMatrices_of_mem_polarGram
    {p k : ℕ} [Fact (Nat.Prime p)]
    {X : Matrix (Fin n) (Fin n)
      (ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ))}
    (hX : X ∈ H.polarGramCongruenceSolutionMatrices p k) :
    X ∈ H.latticeOfPolarForm.gramCongruenceSolutionMatrices p k := by
  rw [PositiveDefiniteIntegralLattice.mem_gramCongruenceSolutionMatrices_iff]
  have hdirect := H.mem_polarGramCongruenceSolutionMatrices_iff.mp hX
  let m : ℕ+ := PositiveDefiniteIntegralLattice.primePowModulus p k
  have hgram := PositiveDefiniteIntegralLattice.matrixMod_polarGramMatrix_eq_two_smul_pairingMatrix
    H.latticeOfPolarForm m
  rw [hgram]
  calc
    Xᵀ * ((2 : ZMod (m : ℕ)) •
        PositiveDefiniteIntegralLattice.matrixMod H.polarGramMatrix m) * X =
        (2 : ZMod (m : ℕ)) •
          (Xᵀ * PositiveDefiniteIntegralLattice.matrixMod H.polarGramMatrix m * X) := by
            exact PositiveDefiniteIntegralLattice.matrix_conj_smul
              (2 : ZMod (m : ℕ))
              (PositiveDefiniteIntegralLattice.matrixMod H.polarGramMatrix m) X
    _ = (2 : ZMod (m : ℕ)) •
        PositiveDefiniteIntegralLattice.matrixMod H.polarGramMatrix m := by rw [hdirect]

/-- At an odd prime, every scaled-integral model raw Gram solution preserves `A`
after cancelling the unit `2` in `ZMod (p^k)`. -/
theorem mem_polarGram_of_mem_latticeOfPolarForm_gramCongruenceSolutionMatrices
    {p k : ℕ} [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    {X : Matrix (Fin n) (Fin n)
      (ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ))}
    (hX : X ∈ H.latticeOfPolarForm.gramCongruenceSolutionMatrices p k) :
    X ∈ H.polarGramCongruenceSolutionMatrices p k := by
  rw [H.mem_polarGramCongruenceSolutionMatrices_iff]
  exact PositiveDefiniteIntegralLattice.pairingMatrix_congruence_of_mem_gramCongruenceSolutionMatrices_odd
    (L := H.latticeOfPolarForm) (p := p) (k := k) (X := X) hp_two hX

/-- At an odd prime power, the two raw solution predicates are literally
equivalent on the same matrix carrier. -/
theorem mem_polarGramCongruenceSolutionMatrices_iff_latticeOfPolarForm
    {p k : ℕ} [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    {X : Matrix (Fin n) (Fin n)
      (ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ))} :
    X ∈ H.polarGramCongruenceSolutionMatrices p k ↔
      X ∈ H.latticeOfPolarForm.gramCongruenceSolutionMatrices p k := by
  exact ⟨H.mem_latticeOfPolarForm_gramCongruenceSolutionMatrices_of_mem_polarGram,
    H.mem_polarGram_of_mem_latticeOfPolarForm_gramCongruenceSolutionMatrices hp_two⟩

/-- The actual equivalence of direct and scaled-integral model raw solution subtypes
at an odd prime power.  It is constructed before any cardinality statement. -/
def polarGramCongruenceSolutionsEquivLatticeOfPolarForm
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    {X : Matrix (Fin n) (Fin n)
        (ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ)) //
      X ∈ H.polarGramCongruenceSolutionMatrices p k} ≃
    {X : Matrix (Fin n) (Fin n)
        (ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ)) //
      X ∈ H.latticeOfPolarForm.gramCongruenceSolutionMatrices p k} where
  toFun X :=
    ⟨X.1, H.mem_polarGramCongruenceSolutionMatrices_iff_latticeOfPolarForm hp_two |>.mp X.2⟩
  invFun X :=
    ⟨X.1, H.mem_polarGramCongruenceSolutionMatrices_iff_latticeOfPolarForm hp_two |>.mpr X.2⟩
  left_inv X := by rfl
  right_inv X := by rfl

/-- The raw solution counts agree, only after the literal subtype equivalence
has been constructed. -/
theorem card_polarGramCongruenceSolutionMatrices_eq_latticeOfPolarForm
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    (H.polarGramCongruenceSolutionMatrices p k).card =
      H.latticeOfPolarForm.gramCongruenceSolutionCount p k := by
  rw [PositiveDefiniteIntegralLattice.gramCongruenceSolutionCount]
  simpa using Fintype.card_congr
    (H.polarGramCongruenceSolutionsEquivLatticeOfPolarForm p k hp_two)

end PositiveDefiniteIntegralQuadraticForm

end
