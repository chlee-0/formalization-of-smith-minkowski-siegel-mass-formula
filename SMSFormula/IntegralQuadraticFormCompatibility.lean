import SMSFormula.IntegralQuadraticFormExplicitFinal
import SMSFormula.Final

/-!
# Compatibility with the integral-matrix convention

For an old integral quadratic matrix `F`, the integral-quadratic-form conversion has
polar Gram matrix `2F`.  This is the old associated bilinear Gram matrix, not
the form matrix of the scaled integral integral model.  The compatibility below is
therefore proved directly from the `Q`/`2F` quotient definitions.
-/

open Matrix

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

/-- The scaled integral model of the converted matrix-convention form stores `2F`, as distinct
from the stored matrix `F` of the lattice. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_pairingMatrix :
    L.toIntegralQuadraticForm.latticeOfPolarForm.pairingMatrix =
      (2 : ℤ) • L.pairingMatrix := by
  rfl

/-- The polar discriminant of the converted integral quadratic form is the old
associated bilinear discriminant. -/
theorem toIntegralQuadraticForm_polarDeterminant :
    L.toIntegralQuadraticForm.polarDeterminant = L.polarDeterminant := by
  rw [PositiveDefiniteIntegralQuadraticForm.polarDeterminant, polarDeterminant,
    L.polarGramMatrix_eq_two_smul_pairingMatrix]
  rfl

/-- Consequently the bad-prime sets of the integral quadratic form and of the integral lattice are
literally equal. -/
theorem toIntegralQuadraticForm_massBadPrimeSet :
    L.toIntegralQuadraticForm.massBadPrimeSet =
      L.massBadPrimeSet := by
  ext p
  rw [PositiveDefiniteIntegralQuadraticForm.mem_massBadPrimeSet_iff,
    mem_massBadPrimeSet_iff,
    L.toIntegralQuadraticForm_polarDeterminant]

/-- The converted scaled-integral model half-polar matrix over `ℤ_p` is the original
associated bilinear Gram matrix. -/
theorem toIntegralQuadraticForm_latticeOfPolarForm_pairingMatrix_padic_eq_polarGramMatrix_padic
    (p : ℕ) [Fact (Nat.Prime p)] :
    L.toIntegralQuadraticForm.latticeOfPolarForm.pairingMatrix_padic p =
      L.polarGramMatrix_padic p := by
  rw [L.polarGramMatrix_padic_eq_two_smul_pairingMatrix_padic p]
  change (((2 : ℤ) • L.pairingMatrix).map (Int.cast : ℤ → ℤ_[p])) =
    (2 : ℤ_[p]) • L.pairingMatrix.map (Int.cast : ℤ → ℤ_[p])
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul,
    Int.cast_ofNat]

/-- At every prime and depth, the direct polar-dual denominator of the
converted form is the old source-associated-bilinear denominator. -/
theorem toIntegralQuadraticForm_polarDualPadicDenominator_eq_associated
    (p k : ℕ) [Fact (Nat.Prime p)] :
    L.toIntegralQuadraticForm.polarDualPadicDenominator p k =
      L.associatedBilinearDualPadicDenominator p k := by
  rw [L.toIntegralQuadraticForm
    |>.polarDualPadicDenominator_eq_latticeOfPolarForm_localDual]
  ext d
  rw [mem_localDualPadicDenominator_iff,
    mem_associatedBilinearDualPadicDenominator_iff,
    L.toIntegralQuadraticForm_latticeOfPolarForm_pairingMatrix_padic_eq_polarGramMatrix_padic]

/-- Integral-coordinate integral models of the two denominators are equal before any
quotient cardinality is taken. -/
theorem toIntegralQuadraticForm_polarDualDenominatorIntegralPreimage_eq_associated
    (p k : ℕ) [Fact (Nat.Prime p)] :
    L.toIntegralQuadraticForm.polarDualPadicDenominatorIntegralPreimage p k =
      L.associatedBilinearDualPadicDenominatorIntegralPreimage p k := by
  rw [PositiveDefiniteIntegralQuadraticForm.polarDualPadicDenominatorIntegralPreimage,
    associatedBilinearDualPadicDenominatorIntegralPreimage,
    L.toIntegralQuadraticForm_polarDualPadicDenominator_eq_associated]

/-- The direct integral-coordinate quotient is explicitly linearly equivalent
to the old associated-bilinear quotient. -/
def toIntegralQuadraticForm_polarDualQuotientEquivAssociated
    (p k : ℕ) [Fact (Nat.Prime p)] :
    ((Fin n → ℤ) ⧸
        L.toIntegralQuadraticForm.polarDualPadicDenominatorIntegralPreimage p k) ≃ₗ[ℤ]
      ((Fin n → ℤ) ⧸
        L.associatedBilinearDualPadicDenominatorIntegralPreimage p k) :=
  Submodule.Quotient.equiv
    (L.toIntegralQuadraticForm.polarDualPadicDenominatorIntegralPreimage p k)
    (L.associatedBilinearDualPadicDenominatorIntegralPreimage p k)
    (LinearEquiv.refl ℤ (Fin n → ℤ))
    (by
      simpa using
        L.toIntegralQuadraticForm_polarDualDenominatorIntegralPreimage_eq_associated p k)

@[simp] theorem toIntegralQuadraticForm_polarDualQuotientEquivAssociated_mkQ
    (p k : ℕ) [Fact (Nat.Prime p)] (x : Fin n → ℤ) :
    L.toIntegralQuadraticForm_polarDualQuotientEquivAssociated p k
        ((L.toIntegralQuadraticForm
          |>.polarDualPadicDenominatorIntegralPreimage p k).mkQ x) =
      (L.associatedBilinearDualPadicDenominatorIntegralPreimage p k).mkQ x := by
  simp [toIntegralQuadraticForm_polarDualQuotientEquivAssociated,
    Submodule.Quotient.equiv]
  rfl

/-- Transport one direct basis-image family to the old associated quotient. -/
def toIntegralQuadraticForm_polarDualFamilyToAssociated
    (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : Fin n → ((Fin n → ℤ) ⧸
      L.toIntegralQuadraticForm.polarDualPadicDenominatorIntegralPreimage p k)) :
    Fin n → ((Fin n → ℤ) ⧸
      L.associatedBilinearDualPadicDenominatorIntegralPreimage p k) :=
  fun i => L.toIntegralQuadraticForm_polarDualQuotientEquivAssociated p k (Y i)

theorem quotientBasisFamilyMap_toIntegralQuadraticForm_polarDualFamilyToAssociated
    (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : Fin n → ((Fin n → ℤ) ⧸
      L.toIntegralQuadraticForm.polarDualPadicDenominatorIntegralPreimage p k))
    (x : Fin n → ℤ) :
    quotientBasisFamilyMap
        (L.associatedBilinearDualPadicDenominatorIntegralPreimage p k)
        (L.toIntegralQuadraticForm_polarDualFamilyToAssociated p k Y) x =
      L.toIntegralQuadraticForm_polarDualQuotientEquivAssociated p k
        (quotientBasisFamilyMap
          (L.toIntegralQuadraticForm
            |>.polarDualPadicDenominatorIntegralPreimage p k) Y x) := by
  classical
  simp [quotientBasisFamilyMap,
    toIntegralQuadraticForm_polarDualFamilyToAssociated]

/-- Transporting a direct solution family preserves the quadratic condition
because the converted integral quadratic form is literally the old one. -/
theorem toIntegralQuadraticForm_polarDualFamilyToAssociated_mem
    (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : L.toIntegralQuadraticForm.polarDualQuotientSolutionFamily p k) :
    L.toIntegralQuadraticForm_polarDualFamilyToAssociated p k Y.1 ∈
      localDualQuotientSolutionFamilies L p k
        (L.associatedBilinearDualPadicDenominatorIntegralPreimage p k)
        (associatedBilinearDualPadicDenominatorIntegralPreimage_rank
          (n := n) L p k) := by
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  have hpre :
      quotientBasisFamilyMap
          (L.toIntegralQuadraticForm
            |>.polarDualPadicDenominatorIntegralPreimage p k) Y.1 x =
        (L.toIntegralQuadraticForm
          |>.polarDualPadicDenominatorIntegralPreimage p k).mkQ y := by
    apply (L.toIntegralQuadraticForm_polarDualQuotientEquivAssociated p k).injective
    rw [← L.quotientBasisFamilyMap_toIntegralQuadraticForm_polarDualFamilyToAssociated
      p k Y.1 x,
      L.toIntegralQuadraticForm_polarDualQuotientEquivAssociated_mkQ]
    exact hxy
  simpa [L.toIntegralQuadraticForm_quadForm] using
    ((L.toIntegralQuadraticForm
      |>.mem_polarDualQuotientSolutionFamilies_iff.mp Y.2) x y hpre)

/-- Transport an old associated-quotient family back to the direct quotient. -/
def associatedQuotientFamilyToToIntegralQuadraticFormPolarDual
    (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : Fin n → ((Fin n → ℤ) ⧸
      L.associatedBilinearDualPadicDenominatorIntegralPreimage p k)) :
    Fin n → ((Fin n → ℤ) ⧸
      L.toIntegralQuadraticForm.polarDualPadicDenominatorIntegralPreimage p k) :=
  fun i =>
    (L.toIntegralQuadraticForm_polarDualQuotientEquivAssociated p k).symm (Y i)

theorem associatedQuotientFamilyToToIntegralQuadraticFormPolarDual_mem
    (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : L.associatedBilinearDualQuotientSolutionFamily p k) :
    L.associatedQuotientFamilyToToIntegralQuadraticFormPolarDual p k Y.1 ∈
      L.toIntegralQuadraticForm.polarDualQuotientSolutionFamilies p k := by
  rw [PositiveDefiniteIntegralQuadraticForm.mem_polarDualQuotientSolutionFamilies_iff]
  intro x y hxy
  have hmap :
      quotientBasisFamilyMap
          (L.associatedBilinearDualPadicDenominatorIntegralPreimage p k) Y.1 x =
        (L.associatedBilinearDualPadicDenominatorIntegralPreimage p k).mkQ y := by
    apply
      (L.toIntegralQuadraticForm_polarDualQuotientEquivAssociated p k).symm.injective
    simpa [associatedQuotientFamilyToToIntegralQuadraticFormPolarDual,
      quotientBasisFamilyMap, map_sum] using hxy
  simpa [L.toIntegralQuadraticForm_quadForm] using
    ((mem_localDualQuotientSolutionFamilies_iff.mp Y.2) x y hmap)

/-- Actual equivalence of the direct and old source-associated solution-family
types, constructed before comparing their cardinalities. -/
def toIntegralQuadraticForm_polarDualSolutionFamilyEquivAssociated
    (p k : ℕ) [Fact (Nat.Prime p)] :
    L.toIntegralQuadraticForm.polarDualQuotientSolutionFamily p k ≃
      L.associatedBilinearDualQuotientSolutionFamily p k where
  toFun Y :=
    ⟨L.toIntegralQuadraticForm_polarDualFamilyToAssociated p k Y.1,
      L.toIntegralQuadraticForm_polarDualFamilyToAssociated_mem p k Y⟩
  invFun Y :=
    ⟨L.associatedQuotientFamilyToToIntegralQuadraticFormPolarDual p k Y.1,
      L.associatedQuotientFamilyToToIntegralQuadraticFormPolarDual_mem p k Y⟩
  left_inv Y := by
    apply Subtype.ext
    ext i
    exact
      (L.toIntegralQuadraticForm_polarDualQuotientEquivAssociated p k).symm_apply_apply
        (Y.1 i)
  right_inv Y := by
    apply Subtype.ext
    ext i
    exact
      (L.toIntegralQuadraticForm_polarDualQuotientEquivAssociated p k).apply_symm_apply
        (Y.1 i)

/-- The direct finite quotient count for a converted matrix-convention form is exactly its
associated-bilinear quotient count. -/
theorem toIntegralQuadraticForm_polarDualQuotientCount_eq_associated
    (p k : ℕ) [Fact (Nat.Prime p)] :
    L.toIntegralQuadraticForm.polarDualQuotientCount p k =
      L.associatedBilinearDualQuotientCount p k := by
  rw [PositiveDefiniteIntegralQuadraticForm.polarDualQuotientCount,
    associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
  exact Nat.card_congr
    (L.toIntegralQuadraticForm_polarDualSolutionFamilyEquivAssociated p k)

/-! ## Direct local-factor compatibility -/

/-- The direct determinant factor of the converted form is the old associated
bilinear Gram determinant factor. -/
theorem toIntegralQuadraticForm_polarGramDetPadicNormFactor
    (p : ℕ) [Fact (Nat.Prime p)] :
    L.toIntegralQuadraticForm.polarGramDetPadicNormFactor p =
      L.gramDetPadicNormFactor p := by
  unfold PositiveDefiniteIntegralQuadraticForm.polarGramDetPadicNormFactor
    gramDetPadicNormFactor
  rw [L.toIntegralQuadraticForm_polarDeterminant]

/-- At an odd prime, every old Hensel depth evaluates the direct converted
factor to the original integral local density. -/
theorem toIntegralQuadraticForm_oddPrimeDirectFixedKDensity_eq_alpha
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (hk : IsLocalDensityHenselExponent L p k) :
    (L.toIntegralQuadraticForm).oddPrimeDirectFixedKDensityWithPolarDetFactor
        p k hp_two =
      L.normalizedLocalDensity p := by
  rw [L.normalizedLocalDensity_eq_associatedBilinearDualQuotientCount p k hk]
  unfold PositiveDefiniteIntegralQuadraticForm.oddPrimeDirectFixedKDensityWithPolarDetFactor
    PositiveDefiniteIntegralQuadraticForm.oddPrimeDirectFixedKDensityFactor
  rw [L.toIntegralQuadraticForm_polarDualQuotientCount_eq_associated,
    L.toIntegralQuadraticForm_polarGramDetPadicNormFactor,
    twoPadicNormInvPow_eq_one_of_ne_two hp_two]
  push_cast
  ring

/-- At a dyadic old Hensel depth, the direct converted fixed-depth expression
is the original integral local density. -/
theorem toIntegralQuadraticForm_dyadicDirectFixedKDensity_eq_alpha
    (k : ℕ) (hk : IsLocalDensityHenselExponent L 2 k) :
    (L.toIntegralQuadraticForm).dyadicDirectFixedKDensityWithPolarDetFactor k =
      L.normalizedLocalDensity 2 := by
  rw [L.normalizedLocalDensity_eq_associatedBilinearDualQuotientCount 2 k hk]
  unfold PositiveDefiniteIntegralQuadraticForm.dyadicDirectFixedKDensityWithPolarDetFactor
    PositiveDefiniteIntegralQuadraticForm.dyadicDirectFixedKDensityFactor
  rw [L.toIntegralQuadraticForm_polarDualQuotientCount_eq_associated,
    L.toIntegralQuadraticForm_polarGramDetPadicNormFactor]
  push_cast
  ring

/-- The stable direct odd-prime alpha of the converted form is the original
old alpha.  A common depth is built by adding the two preferred Hensel depths. -/
theorem toIntegralQuadraticForm_oddPrimeNormalizedLocalDensity
    (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    L.toIntegralQuadraticForm.oddPrimeNormalizedLocalDensity p hp_two =
      L.normalizedLocalDensity p := by
  let H := L.toIntegralQuadraticForm
  let S := H.latticeOfPolarForm
  let kS := localDensityHenselExponent S p
  let kL := localDensityHenselExponent L p
  let k := kS + kL
  have hkS : IsLocalDensityHenselExponent S p k := by
    exact (isLocalDensityHenselExponent_preferred S p).add S p kS kL
  have hkL : IsLocalDensityHenselExponent L p k := by
    have h := (isLocalDensityHenselExponent_preferred L p).add L p kL kS
    simpa [k, Nat.add_comm] using h
  calc
    H.oddPrimeNormalizedLocalDensity p hp_two =
        H.oddPrimeDirectFixedKDensityWithPolarDetFactor p k hp_two :=
      H.oddPrimeNormalizedLocalDensity_eq_fixedK p k hp_two hkS
    _ = L.normalizedLocalDensity p :=
      L.toIntegralQuadraticForm_oddPrimeDirectFixedKDensity_eq_alpha
        p k hp_two hkL

/-- The stable direct dyadic alpha of the converted form is the dyadic alpha of the
matrix-convention form.  The proof compares both at one common sufficiently deep level
and keeps track of the one-step shift of the direct integral model. -/
theorem toIntegralQuadraticForm_dyadicNormalizedLocalDensity :
    L.toIntegralQuadraticForm.dyadicNormalizedLocalDensity =
      L.normalizedLocalDensity 2 := by
  let H := L.toIntegralQuadraticForm
  let S := H.latticeOfPolarForm
  let kS := localDensityHenselExponent S 2
  let kL := localDensityHenselExponent L 2
  let k := kL + kS
  have hkL : IsLocalDensityHenselExponent L 2 k := by
    exact (isLocalDensityHenselExponent_preferred L 2).add L 2 kL kS
  have hkSsucc : IsLocalDensityHenselExponent S 2 (k + 1) := by
    have h :=
      (isLocalDensityHenselExponent_preferred S 2).add S 2 kS (kL + 1)
    simpa [k, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  calc
    H.dyadicNormalizedLocalDensity = S.normalizedLocalDensity 2 :=
      H.dyadicNormalizedLocalDensity_eq_latticeOfPolarForm
    _ = H.dyadicDirectFixedKDensityWithPolarDetFactor k :=
      (H.dyadicDirectFixedKDensityWithPolarDetFactor_eq_latticeOfPolarForm_alpha
        k hkSsucc).symm
    _ = L.normalizedLocalDensity 2 :=
      L.toIntegralQuadraticForm_dyadicDirectFixedKDensity_eq_alpha k hkL

/-- The direct all-prime local density of a matrix-convention form viewed as an integral
quadratic form is exactly its local density in the matrix convention. -/
theorem toIntegralQuadraticForm_normalizedLocalDensity
    (p : ℕ) [Fact (Nat.Prime p)] :
    L.toIntegralQuadraticForm.normalizedLocalDensity p =
      L.normalizedLocalDensity p := by
  by_cases hp : p = 2
  · subst p
    simpa [PositiveDefiniteIntegralQuadraticForm.normalizedLocalDensity] using
      L.toIntegralQuadraticForm_dyadicNormalizedLocalDensity
  · simpa [PositiveDefiniteIntegralQuadraticForm.normalizedLocalDensity, hp] using
      L.toIntegralQuadraticForm_oddPrimeNormalizedLocalDensity p hp

/-! ## Direct product compatibility -/

theorem toIntegralQuadraticForm_massLocalFactor
    (p : ℕ) [Fact (Nat.Prime p)] :
    L.toIntegralQuadraticForm.massLocalFactor p =
      L.massLocalFactor p := by
  exact L.toIntegralQuadraticForm_normalizedLocalDensity p

theorem toIntegralQuadraticForm_massLocalInverseFactor
    (p : ℕ) [Fact (Nat.Prime p)] :
    L.toIntegralQuadraticForm.massLocalInverseFactor p =
      L.massLocalInverseFactor p := by
  rw [PositiveDefiniteIntegralQuadraticForm.massLocalInverseFactor,
    massLocalInverseFactor,
    L.toIntegralQuadraticForm_massLocalFactor]

theorem toIntegralQuadraticForm_massLocalFactorAtPrime
    (p : {p : ℕ // Nat.Prime p}) :
    L.toIntegralQuadraticForm.massLocalFactorAtPrime p =
      L.massLocalFactorAtPrime p := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  exact L.toIntegralQuadraticForm_massLocalFactor p.1

theorem toIntegralQuadraticForm_massLocalInverseFactorAtPrime
    (p : {p : ℕ // Nat.Prime p}) :
    L.toIntegralQuadraticForm.massLocalInverseFactorAtPrime p =
      L.massLocalInverseFactorAtPrime p := by
  rw [PositiveDefiniteIntegralQuadraticForm.massLocalInverseFactorAtPrime,
    massLocalInverseFactorAtPrime,
    L.toIntegralQuadraticForm_massLocalFactorAtPrime]

/-- Finite direct products for a matrix-convention form viewed as an integral quadratic form
reduce to the matrix-convention finite products term by term. -/
theorem toIntegralQuadraticForm_massFinitePrimeInverseProduct
    (S : Finset {p : ℕ // Nat.Prime p}) :
    L.toIntegralQuadraticForm.massFinitePrimeInverseProduct S =
      L.massFinitePrimeInverseProduct S := by
  unfold PositiveDefiniteIntegralQuadraticForm.massFinitePrimeInverseProduct
    massFinitePrimeInverseProduct
  apply Finset.prod_congr rfl
  intro p _hp
  exact L.toIntegralQuadraticForm_massLocalInverseFactorAtPrime p

/-- Cutoff products likewise reduce literally to the old cutoff product. -/
theorem toIntegralQuadraticForm_massPartialPrimeInverseProduct
    (N : ℕ) :
    L.toIntegralQuadraticForm.massPartialPrimeInverseProduct N =
      L.massPartialPrimeInverseProduct N := by
  unfold PositiveDefiniteIntegralQuadraticForm.massPartialPrimeInverseProduct
    massPartialPrimeInverseProduct
  exact
    L.toIntegralQuadraticForm_massFinitePrimeInverseProduct
      (rationalPrimesUpTo N)

/-- Direct cutoff-product convergence for the converted form is exactly the
old convergence predicate. -/
theorem toIntegralQuadraticForm_massLocalInverseProductTendsTo
    (P : ℝ) :
    L.toIntegralQuadraticForm.massLocalInverseProductTendsTo P ↔
      L.massLocalInverseProductTendsTo P := by
  unfold PositiveDefiniteIntegralQuadraticForm.massLocalInverseProductTendsTo
    massLocalInverseProductTendsTo
  rw [show
    (fun N : ℕ =>
      L.toIntegralQuadraticForm.massPartialPrimeInverseProduct N) =
        (fun N : ℕ => L.massPartialPrimeInverseProduct N) by
      funext N
      exact
        L.toIntegralQuadraticForm_massPartialPrimeInverseProduct N]

/-- The archimedean-times-limit product side has the same rank convention and
is definitionally compatible. -/
theorem toIntegralQuadraticForm_massFormulaProductSide (P : ℝ) :
    L.toIntegralQuadraticForm.massFormulaProductSide P =
      L.massFormulaProductSide P := by
  rfl

/-- The explicit odd named limit reduces to the named odd limit of the matrix convention. -/
theorem toIntegralQuadraticForm_oddRankOrdinaryMassProductLimit
    (N s : ℕ) :
    L.toIntegralQuadraticForm.oddRankOrdinaryMassProductLimit N s =
      L.oddRankOrdinaryMassProductLimit N s := by
  unfold PositiveDefiniteIntegralQuadraticForm.oddRankOrdinaryMassProductLimit
    oddRankOrdinaryMassProductLimit
  rw [L.toIntegralQuadraticForm_massPartialPrimeInverseProduct]

end PositiveDefiniteIntegralLattice

end
