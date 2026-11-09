import SMSFormula.IntegralQuadraticFormOddPrimeLocalFactor

/-!
# The exact dyadic depth shift for integral quadratic forms

For an integral quadratic form with polar Gram matrix `A`, the direct local dual
uses `A`, whereas the source-associated dual of the scaled integral integral model
uses `2A`.  At the dyadic prime this changes depth: the direct denominator and
quadratic congruence at depth `k` agree with the integral model source objects at depth
`k+1`.

This file carries that equality through actual quotient linear equivalences
and solution-family equivalences.  The normalized dyadic local-density
factors are compared in `SMSFormula.IntegralQuadraticFormDyadicLocalFactor`.
-/

noncomputable section

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

/-! ## Denominator and quotient depth shift -/

/-- The direct `A`-dual denominator at dyadic depth `k` is the scaled integral model's
source-associated `2A`-dual denominator at depth `k+1`. -/
theorem polarDualPadicDenominator_eq_latticeOfPolarForm_associatedDual_succ_dyadic
    (k : ℕ) :
    H.polarDualPadicDenominator 2 k =
      H.latticeOfPolarForm.associatedBilinearDualPadicDenominator 2 (k + 1) := by
  rw [H.polarDualPadicDenominator_eq_latticeOfPolarForm_localDual]
  exact
    H.latticeOfPolarForm
      |>.associatedBilinearDualPadicDenominator_succ_eq_localDualPadicDenominator_dyadic
        k
      |>.symm

/-- Integral-coordinate form of the exact dyadic denominator shift. -/
theorem
    polarDualPadicDenominatorIntegralPreimage_eq_latticeOfPolarForm_associatedDual_succ_dyadic
    (k : ℕ) :
    H.polarDualPadicDenominatorIntegralPreimage 2 k =
      PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage
        H.latticeOfPolarForm 2 (k + 1) := by
  rw [H.polarDualPadicDenominatorIntegralPreimage_eq_latticeOfPolarForm_localDual]
  exact
    H.latticeOfPolarForm
      |>.associatedBilinearDualPadicDenominatorIntegralPreimage_succ_eq_localDualPadicDenominatorIntegralPreimage_dyadic
        k
      |>.symm

/-- The integral-coordinate quotients are explicitly linearly equivalent
across the dyadic depth shift. -/
noncomputable def
    polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic
    (k : ℕ) :
    ((Fin n → ℤ) ⧸ H.polarDualPadicDenominatorIntegralPreimage 2 k) ≃ₗ[ℤ]
      ((Fin n → ℤ) ⧸
        PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage
          H.latticeOfPolarForm 2 (k + 1)) :=
  Submodule.Quotient.equiv
    (H.polarDualPadicDenominatorIntegralPreimage 2 k)
    (PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage
      H.latticeOfPolarForm 2 (k + 1))
    (LinearEquiv.refl ℤ (Fin n → ℤ))
    (by
      simpa using
        H.polarDualPadicDenominatorIntegralPreimage_eq_latticeOfPolarForm_associatedDual_succ_dyadic
          k)

@[simp] theorem
    polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic_mkQ
    (k : ℕ) (x : Fin n → ℤ) :
    H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic
        k ((H.polarDualPadicDenominatorIntegralPreimage 2 k).mkQ x) =
      (PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage
        H.latticeOfPolarForm 2 (k + 1)).mkQ x := by
  simp
    [polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic,
      Submodule.Quotient.equiv]
  rfl

/-! ## Quadratic congruence depth shift -/

/-- Equality of direct quadratic values modulo `2^k` is exactly equality of
the scaled-integral model values modulo `2^(k+1)`.  The proof passes through integer
divisibility and cancels a nonzero integer factor, never a dyadic residue-ring
element. -/
theorem quadForm_zmod_eq_iff_latticeOfPolarForm_succ_dyadic
    (k : ℕ) (x y : Fin n → ℤ) :
    ((H.quadForm y : ℤ) :
        ZMod (PositiveDefiniteIntegralLattice.primePowModulus 2 k : ℕ)) =
        (H.quadForm x : ZMod (PositiveDefiniteIntegralLattice.primePowModulus 2 k : ℕ)) ↔
      (H.latticeOfPolarForm.quadForm y :
        ZMod (PositiveDefiniteIntegralLattice.primePowModulus 2 (k + 1) : ℕ)) =
        (H.latticeOfPolarForm.quadForm x :
          ZMod (PositiveDefiniteIntegralLattice.primePowModulus 2 (k + 1) : ℕ)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub,
    ZMod.intCast_eq_intCast_iff_dvd_sub]
  rw [H.latticeOfPolarForm_quadForm, H.latticeOfPolarForm_quadForm]
  change ((2 : ℤ) ^ k ∣ H.quadForm x - H.quadForm y) ↔
    (2 : ℤ) ^ (k + 1) ∣
      2 * H.quadForm x - 2 * H.quadForm y
  rw [show 2 * H.quadForm x - 2 * H.quadForm y =
      (2 : ℤ) * (H.quadForm x - H.quadForm y) by ring,
    pow_succ]
  simpa [mul_comm] using
    (mul_dvd_mul_iff_left
      (show (2 : ℤ) ≠ 0 by norm_num)
      (a := (2 : ℤ))
      (b := (2 : ℤ) ^ k)
      (c := H.quadForm x - H.quadForm y)).symm

/-! ## Solution-family depth shift -/

/-- Transport a direct depth-`k` family through the shifted quotient
equivalence. -/
noncomputable def polarDualQuotientFamilyToLatticeOfPolarFormAssociatedSuccDyadic
    (k : ℕ)
    (Y : Fin n →
      ((Fin n → ℤ) ⧸ H.polarDualPadicDenominatorIntegralPreimage 2 k)) :
    Fin n → ((Fin n → ℤ) ⧸
      PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage
        H.latticeOfPolarForm 2 (k + 1)) :=
  fun i =>
    H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic
      k (Y i)

theorem
    quotientBasisFamilyMap_polarDualQuotientFamilyToLatticeOfPolarFormAssociatedSuccDyadic
    (k : ℕ)
    (Y : Fin n →
      ((Fin n → ℤ) ⧸ H.polarDualPadicDenominatorIntegralPreimage 2 k))
    (x : Fin n → ℤ) :
    PositiveDefiniteIntegralLattice.quotientBasisFamilyMap
        (PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage
          H.latticeOfPolarForm 2 (k + 1))
        (H.polarDualQuotientFamilyToLatticeOfPolarFormAssociatedSuccDyadic k Y) x =
      H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic
        k
        (PositiveDefiniteIntegralLattice.quotientBasisFamilyMap
          (H.polarDualPadicDenominatorIntegralPreimage 2 k) Y x) := by
  classical
  simp [PositiveDefiniteIntegralLattice.quotientBasisFamilyMap,
    polarDualQuotientFamilyToLatticeOfPolarFormAssociatedSuccDyadic]

theorem polarDualQuotientFamilyToLatticeOfPolarFormAssociatedSuccDyadic_mem
    (k : ℕ) (Y : H.polarDualQuotientSolutionFamily 2 k) :
    H.polarDualQuotientFamilyToLatticeOfPolarFormAssociatedSuccDyadic k Y.1 ∈
      PositiveDefiniteIntegralLattice.localDualQuotientSolutionFamilies
        H.latticeOfPolarForm 2 (k + 1)
        (PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage
          H.latticeOfPolarForm 2 (k + 1))
        (PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage_rank
          (n := n) H.latticeOfPolarForm 2 (k + 1)) := by
  rw [PositiveDefiniteIntegralLattice.mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  have hpre :
      PositiveDefiniteIntegralLattice.quotientBasisFamilyMap
          (H.polarDualPadicDenominatorIntegralPreimage 2 k) Y.1 x =
        (H.polarDualPadicDenominatorIntegralPreimage 2 k).mkQ y := by
    apply
      (H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic
        k).injective
    rw [← H.quotientBasisFamilyMap_polarDualQuotientFamilyToLatticeOfPolarFormAssociatedSuccDyadic
      k Y.1 x,
      H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic_mkQ]
    exact hxy
  exact (H.quadForm_zmod_eq_iff_latticeOfPolarForm_succ_dyadic k x y).mp
    ((H.mem_polarDualQuotientSolutionFamilies_iff.mp Y.2) x y hpre)

/-- Transport a shifted source-associated integral model family back to the direct
depth-`k` quotient. -/
noncomputable def latticeOfPolarFormAssociatedSuccDyadicQuotientFamilyToPolarDual
    (k : ℕ)
    (Y : Fin n → ((Fin n → ℤ) ⧸
      PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage
        H.latticeOfPolarForm 2 (k + 1))) :
    Fin n → ((Fin n → ℤ) ⧸
      H.polarDualPadicDenominatorIntegralPreimage 2 k) :=
  fun i =>
    (H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic
      k).symm (Y i)

theorem latticeOfPolarFormAssociatedSuccDyadicQuotientFamilyToPolarDual_mem
    (k : ℕ)
    (Y : PositiveDefiniteIntegralLattice.associatedBilinearDualQuotientSolutionFamily
      H.latticeOfPolarForm 2 (k + 1)) :
    H.latticeOfPolarFormAssociatedSuccDyadicQuotientFamilyToPolarDual k Y.1 ∈
      H.polarDualQuotientSolutionFamilies 2 k := by
  rw [H.mem_polarDualQuotientSolutionFamilies_iff]
  intro x y hxy
  have hmap :
      PositiveDefiniteIntegralLattice.quotientBasisFamilyMap
          (PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage
            H.latticeOfPolarForm 2 (k + 1)) Y.1 x =
        (PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage
          H.latticeOfPolarForm 2 (k + 1)).mkQ y := by
    apply
      (H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic
        k).symm.injective
    simpa [latticeOfPolarFormAssociatedSuccDyadicQuotientFamilyToPolarDual,
      PositiveDefiniteIntegralLattice.quotientBasisFamilyMap, map_sum] using hxy
  exact (H.quadForm_zmod_eq_iff_latticeOfPolarForm_succ_dyadic k x y).mpr
    ((PositiveDefiniteIntegralLattice.mem_localDualQuotientSolutionFamilies_iff.mp Y.2) x y hmap)

/-- Actual equivalence between direct depth-`k` solution families and the
scaled integral model's source-associated depth-`k+1` solution families. -/
noncomputable def
    polarDualQuotientSolutionFamilyEquivLatticeOfPolarFormAssociatedSuccDyadic
    (k : ℕ) :
    H.polarDualQuotientSolutionFamily 2 k ≃
      PositiveDefiniteIntegralLattice.associatedBilinearDualQuotientSolutionFamily
        H.latticeOfPolarForm 2 (k + 1) where
  toFun Y :=
    ⟨H.polarDualQuotientFamilyToLatticeOfPolarFormAssociatedSuccDyadic k Y.1,
      H.polarDualQuotientFamilyToLatticeOfPolarFormAssociatedSuccDyadic_mem k Y⟩
  invFun Y :=
    ⟨H.latticeOfPolarFormAssociatedSuccDyadicQuotientFamilyToPolarDual k Y.1,
      H.latticeOfPolarFormAssociatedSuccDyadicQuotientFamilyToPolarDual_mem k Y⟩
  left_inv Y := by
    apply Subtype.ext
    ext i
    exact
      (H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic
        k).symm_apply_apply (Y.1 i)
  right_inv Y := by
    apply Subtype.ext
    ext i
    exact
      (H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociatedSuccDyadic
        k).apply_symm_apply (Y.1 i)

/-- The direct depth-`k` finite count equals the integral model source-associated
count at the shifted depth `k+1`, only after constructing the family
equivalence. -/
theorem polarDualQuotientCount_eq_latticeOfPolarForm_associated_succ_dyadic
    (k : ℕ) :
    H.polarDualQuotientCount 2 k =
      PositiveDefiniteIntegralLattice.associatedBilinearDualQuotientCount
        H.latticeOfPolarForm 2 (k + 1) := by
  rw [polarDualQuotientCount,
    PositiveDefiniteIntegralLattice.associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
  exact Nat.card_congr
    (H.polarDualQuotientSolutionFamilyEquivLatticeOfPolarFormAssociatedSuccDyadic k)

end PositiveDefiniteIntegralQuadraticForm

end
