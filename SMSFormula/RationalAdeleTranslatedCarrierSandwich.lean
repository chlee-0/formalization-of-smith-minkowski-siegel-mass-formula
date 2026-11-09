import SMSFormula.RationalAdeleTranslatedTestCarrier
import SMSFormula.RationalAdeleFiniteLocalTruncation

/-!
# The compact open sandwich for the moved carrier

The general argument obtains `N Zhat^n subset K subset N^-1 Zhat^n` for an arbitrary compact open
additive subgroup, from finite indices.  For the carrier that actually occurs -- the preimage of
the integral finite adele vectors under a finite adelic matrix -- there is a cheaper route the
answer itself names: bounded denominators.

Every finite adele has a natural denominator (an existing theorem).  Choosing one for each of the
finitely many entries and multiplying gives a single natural `N` clearing a whole matrix.  Applying
that to the matrix and to its inverse gives both inclusions at once, with no compactness, openness
or finite-index argument.

Negative scope: the decomposition of the carrier into level-`N` classes is not done here, and no
Poisson identity for the translated test follows yet.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix
open scoped BigOperators

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A whole finite adelic matrix has a single natural denominator. -/
theorem exists_natScale_matrix_entries_mem_integral
    (M : Matrix (Fin n) (Fin n) RationalFiniteAdele) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∀ i j, (N : RationalFiniteAdele) * M i j ∈ integralFiniteAdeleSubring := by
  classical
  choose N hN0 hNmem using fun p : Fin n × Fin n ↦ exists_natScale_mem_integral (M p.1 p.2)
  refine ⟨∏ p : Fin n × Fin n, N p, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun p _ ↦ hN0 p
  · intro i j
    have hsplit : (∏ p : Fin n × Fin n, N p) =
        N (i, j) * ∏ p ∈ Finset.univ.erase (i, j), N p :=
      (Finset.mul_prod_erase Finset.univ N (Finset.mem_univ (i, j))).symm
    have hcast : ((∏ p : Fin n × Fin n, N p : ℕ) : RationalFiniteAdele) =
        ((∏ p ∈ Finset.univ.erase ((i, j) : Fin n × Fin n), N p : ℕ) : RationalFiniteAdele) *
          ((N (i, j) : ℕ) : RationalFiniteAdele) := by
      rw [hsplit]
      push_cast
      ring
    rw [hcast, mul_assoc]
    exact Subring.mul_mem _ (natCast_mem integralFiniteAdeleSubring _) (hNmem (i, j))

/-- First inclusion: scaling the standard carrier by a denominator of `M` lands inside the moved
carrier, so `N Zhat^n` sits inside it. -/
theorem mulVec_natScale_mem_integral
    (M : Matrix (Fin n) (Fin n) RationalFiniteAdele) {N : ℕ}
    (hN : ∀ i j, (N : RationalFiniteAdele) * M i j ∈ integralFiniteAdeleSubring)
    {y : Fin n → RationalFiniteAdele} (hy : y ∈ integralFiniteAdeleVectors n) :
    M.mulVec (fun i ↦ (N : RationalFiniteAdele) * y i) ∈ integralFiniteAdeleVectors n := by
  intro i
  show (∑ j, M i j * ((N : RationalFiniteAdele) * y j)) ∈ integralFiniteAdeleSubring
  refine Subring.sum_mem _ fun j _ ↦ ?_
  have hrw : M i j * ((N : RationalFiniteAdele) * y j) =
      ((N : RationalFiniteAdele) * M i j) * y j := by ring
  rw [hrw]
  exact Subring.mul_mem _ (hN i j) (hy j)

/-- Second inclusion: the moved carrier, scaled by a denominator of the inverse, lands inside the
standard carrier, so it sits inside `N^-1 Zhat^n`. -/
theorem natScale_mem_integral_of_mulVec_mem
    (M : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ) {N : ℕ}
    (hN : ∀ i j, (N : RationalFiniteAdele) *
      (↑M⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdele) i j ∈ integralFiniteAdeleSubring)
    {y : Fin n → RationalFiniteAdele}
    (hy : (M.1).mulVec y ∈ integralFiniteAdeleVectors n) :
    (fun i ↦ (N : RationalFiniteAdele) * y i) ∈ integralFiniteAdeleVectors n := by
  have hinv : (↑M⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdele).mulVec ((M.1).mulVec y) = y := by
    rw [Matrix.mulVec_mulVec]
    simp
  intro i
  show (N : RationalFiniteAdele) * y i ∈ integralFiniteAdeleSubring
  have hrec : (∑ j, ((N : RationalFiniteAdele) *
      (↑M⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdele) i j) * ((M.1).mulVec y) j) =
      (N : RationalFiniteAdele) * y i := by
    have hterm : ∀ j : Fin n, ((N : RationalFiniteAdele) *
        (↑M⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdele) i j) * ((M.1).mulVec y) j =
        (N : RationalFiniteAdele) *
          ((↑M⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdele) i j * ((M.1).mulVec y) j) :=
      fun j ↦ by ring
    simp only [hterm, ← Finset.mul_sum]
    congr 1
    exact congrFun hinv i
  rw [← hrec]
  exact Subring.sum_mem _ fun j _ ↦
    Subring.mul_mem _ (hN i j) (hy j)

/-- The sandwich, for the carrier that actually occurs: one natural `N` gives both inclusions. -/
theorem exists_natScale_translatedCarrier_sandwich
    (M : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ) :
    ∃ N : ℕ, N ≠ 0 ∧
      (∀ y ∈ integralFiniteAdeleVectors n,
        (M.1).mulVec (fun i ↦ (N : RationalFiniteAdele) * y i) ∈
          integralFiniteAdeleVectors n) ∧
      (∀ y : Fin n → RationalFiniteAdele, (M.1).mulVec y ∈ integralFiniteAdeleVectors n →
        (fun i ↦ (N : RationalFiniteAdele) * y i) ∈ integralFiniteAdeleVectors n) := by
  obtain ⟨N₁, hN₁, hM⟩ := exists_natScale_matrix_entries_mem_integral M.1
  obtain ⟨N₂, hN₂, hMinv⟩ :=
    exists_natScale_matrix_entries_mem_integral
      (↑M⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdele)
  refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, ?_, ?_⟩
  · intro y hy
    refine mulVec_natScale_mem_integral M.1 (fun i j ↦ ?_) hy
    have hrw : ((N₁ * N₂ : ℕ) : RationalFiniteAdele) * M.1 i j =
        ((N₂ : ℕ) : RationalFiniteAdele) * (((N₁ : ℕ) : RationalFiniteAdele) * M.1 i j) := by
      push_cast
      ring
    rw [hrw]
    exact Subring.mul_mem _ (natCast_mem integralFiniteAdeleSubring _) (hM i j)
  · intro y hy
    refine natScale_mem_integral_of_mulVec_mem M (fun i j ↦ ?_) hy
    have hrw : ((N₁ * N₂ : ℕ) : RationalFiniteAdele) *
        (↑M⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdele) i j =
        ((N₁ : ℕ) : RationalFiniteAdele) *
          (((N₂ : ℕ) : RationalFiniteAdele) *
            (↑M⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdele) i j) := by
      push_cast
      ring
    rw [hrw]
    exact Subring.mul_mem _ (natCast_mem integralFiniteAdeleSubring _) (hMinv i j)

end PositiveDefiniteIntegralLattice

end
