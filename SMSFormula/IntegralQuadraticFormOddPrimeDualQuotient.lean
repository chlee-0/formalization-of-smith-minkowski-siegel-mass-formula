import SMSFormula.IntegralQuadraticFormBadPrimeOddCongruence

/-!
# The direct `A`-dual quotient at odd primes

For `H : PositiveDefiniteIntegralQuadraticForm n`, the intrinsic local dual is formed with the
integral polar Gram matrix `A = H.polarGramMatrix`.  The scaled integral
integral model has stored form matrix `A` but source-associated Gram matrix `2A`.
This file identifies the direct `A`-dual first with the integral model form-matrix
dual, and then, only away from two, with the integral model source-associated dual.

The equalities are carried through depth denominators and used to construct
actual quotient linear equivalences.  No local-density normalization or
dyadic comparison is asserted.
-/

open Matrix

noncomputable section

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

/-! ## Intrinsic local `A`-dual -/

/-- The integral polar Gram matrix over the `p`-adic field. -/
def polarGramMatrix_padicField (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix (Fin n) (Fin n) ℚ_[p] :=
  H.polarGramMatrix.map (Int.cast : ℤ → ℚ_[p])

theorem polarGramMatrix_padicField_eq_latticeOfPolarForm_pairingMatrix
    (p : ℕ) [Fact (Nat.Prime p)] :
    H.polarGramMatrix_padicField p =
      H.latticeOfPolarForm.pairingMatrix_padicField p := by
  ext i j
  simp [polarGramMatrix_padicField, PositiveDefiniteIntegralLattice.pairingMatrix_padicField,
    PositiveDefiniteIntegralLattice.pairingMatrix_padic, latticeOfPolarForm]

/-- A vector belongs to the direct local dual of the integral quadratic form when its pairing
with the polar Gram matrix `A` is integral in every coordinate. -/
def IsPolarDualPadicVector (p : ℕ) [Fact (Nat.Prime p)]
    (y : Fin n → ℚ_[p]) : Prop :=
  ∀ i : Fin n,
    (H.polarGramMatrix_padicField p).mulVec y i ∈ PadicInt.subring p

theorem isPolarDualPadicVector_iff_latticeOfPolarForm
    (p : ℕ) [Fact (Nat.Prime p)] (y : Fin n → ℚ_[p]) :
    H.IsPolarDualPadicVector p y ↔
      H.latticeOfPolarForm.IsLocalDualPadicVector p y := by
  unfold IsPolarDualPadicVector PositiveDefiniteIntegralLattice.IsLocalDualPadicVector
  rw [H.polarGramMatrix_padicField_eq_latticeOfPolarForm_pairingMatrix]

/-- The intrinsic local `A`-dual as a `ℤ_p`-submodule.  Its carrier is stated
directly with `A`; only the closure proofs are reused from the integral model object. -/
def polarDualPadicSubmodule (p : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ_[p] (Fin n → ℚ_[p]) :=
  (H.latticeOfPolarForm.localDualPadicSubmodule p).copy
    {y | H.IsPolarDualPadicVector p y}
    (Set.ext fun y => H.isPolarDualPadicVector_iff_latticeOfPolarForm p y)

theorem polarDualPadicSubmodule_eq_latticeOfPolarForm_localDual
    (p : ℕ) [Fact (Nat.Prime p)] :
    H.polarDualPadicSubmodule p =
      H.latticeOfPolarForm.localDualPadicSubmodule p := by
  ext y
  exact H.isPolarDualPadicVector_iff_latticeOfPolarForm p y

/-- Away from two, the direct `A`-dual is also the scaled integral model's
source-associated `2A`-dual. -/
theorem polarDualPadicSubmodule_eq_latticeOfPolarForm_associatedDual_of_ne_two
    (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    H.polarDualPadicSubmodule p =
      H.latticeOfPolarForm.associatedBilinearDualPadicSubmodule p := by
  rw [H.polarDualPadicSubmodule_eq_latticeOfPolarForm_localDual,
    H.latticeOfPolarForm
      |>.associatedBilinearDualPadicSubmodule_eq_localDualPadicSubmodule_of_ne_two
        p hp_two]

/-! ## Intrinsic depth denominator -/

/-- The direct depth-`k` `A`-dual denominator, stated by divisibility of every
integral pairing with `A`. -/
def IsPolarDualPadicDenominatorVector
    (p k : ℕ) [Fact (Nat.Prime p)] (d : Fin n → ℤ_[p]) : Prop :=
  ∀ x : Fin n → ℤ,
    ((p : ℤ_[p]) ^ k ∣
      dotProduct (PositiveDefiniteIntegralLattice.integralVectorToPadic (n := n) p x)
        ((H.polarGramMatrix_padic p).mulVec d))

theorem isPolarDualPadicDenominatorVector_iff_latticeOfPolarForm
    (p k : ℕ) [Fact (Nat.Prime p)] (d : Fin n → ℤ_[p]) :
    H.IsPolarDualPadicDenominatorVector p k d ↔
      d ∈ H.latticeOfPolarForm.localDualPadicDenominator p k := by
  rfl

/-- The direct depth-`k` `A`-dual denominator as a `ℤ_p`-submodule. -/
def polarDualPadicDenominator (p k : ℕ) [Fact (Nat.Prime p)] :
    Submodule ℤ_[p] (Fin n → ℤ_[p]) :=
  (H.latticeOfPolarForm.localDualPadicDenominator p k).copy
    {d | H.IsPolarDualPadicDenominatorVector p k d}
    (Set.ext fun d =>
      H.isPolarDualPadicDenominatorVector_iff_latticeOfPolarForm p k d)

theorem polarDualPadicDenominator_eq_latticeOfPolarForm_localDual
    (p k : ℕ) [Fact (Nat.Prime p)] :
    H.polarDualPadicDenominator p k =
      H.latticeOfPolarForm.localDualPadicDenominator p k := by
  ext d
  exact H.isPolarDualPadicDenominatorVector_iff_latticeOfPolarForm p k d

theorem polarDualPadicDenominator_eq_latticeOfPolarForm_associatedDual_of_ne_two
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    H.polarDualPadicDenominator p k =
      H.latticeOfPolarForm.associatedBilinearDualPadicDenominator p k := by
  rw [H.polarDualPadicDenominator_eq_latticeOfPolarForm_localDual,
    H.latticeOfPolarForm
      |>.associatedBilinearDualPadicDenominator_eq_localDualPadicDenominator_of_ne_two
        p k hp_two]

/-! ## Integral integral models and literal quotient equivalences -/

/-- The integral-coordinate integral model of the direct `A`-dual denominator. -/
def polarDualPadicDenominatorIntegralPreimage
    (p k : ℕ) [Fact (Nat.Prime p)] : Submodule ℤ (Fin n → ℤ) :=
  PositiveDefiniteIntegralLattice.padicSubmoduleIntegralPreimage (n := n) p
    (H.polarDualPadicDenominator p k)

theorem polarDualPadicDenominatorIntegralPreimage_eq_latticeOfPolarForm_localDual
    (p k : ℕ) [Fact (Nat.Prime p)] :
    H.polarDualPadicDenominatorIntegralPreimage p k =
      H.latticeOfPolarForm.localDualPadicDenominatorIntegralPreimage p k := by
  rw [polarDualPadicDenominatorIntegralPreimage,
    H.polarDualPadicDenominator_eq_latticeOfPolarForm_localDual]
  ext d
  rfl

theorem polarDualPadicDenominatorIntegralPreimage_eq_latticeOfPolarForm_associatedDual_of_ne_two
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    H.polarDualPadicDenominatorIntegralPreimage p k =
      H.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage
        p k := by
  rw [H.polarDualPadicDenominatorIntegralPreimage_eq_latticeOfPolarForm_localDual,
    H.latticeOfPolarForm
      |>.associatedBilinearDualPadicDenominatorIntegralPreimage_eq_localDualPadicDenominatorIntegralPreimage_of_ne_two
        p k hp_two]

theorem polarDualPadicDenominatorIntegralPreimage_rank
    (p k : ℕ) [Fact (Nat.Prime p)] :
    Module.finrank ℤ (H.polarDualPadicDenominatorIntegralPreimage p k) = n := by
  rw [H.polarDualPadicDenominatorIntegralPreimage_eq_latticeOfPolarForm_localDual]
  exact PositiveDefiniteIntegralLattice.localDualPadicDenominatorIntegralPreimage_rank
    (n := n) H.latticeOfPolarForm p k

/-- The direct p-adic quotient is explicitly linearly equivalent to the
scaled integral model's source-associated quotient at an odd prime. -/
noncomputable def polarDualPadicQuotientEquivLatticeOfPolarFormAssociated
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    ((Fin n → ℤ_[p]) ⧸ H.polarDualPadicDenominator p k) ≃ₗ[ℤ_[p]]
      ((Fin n → ℤ_[p]) ⧸
        H.latticeOfPolarForm.associatedBilinearDualPadicDenominator p k) :=
  Submodule.Quotient.equiv
    (H.polarDualPadicDenominator p k)
    (H.latticeOfPolarForm.associatedBilinearDualPadicDenominator p k)
    (LinearEquiv.refl ℤ_[p] (Fin n → ℤ_[p]))
    (by
      simpa using
        H.polarDualPadicDenominator_eq_latticeOfPolarForm_associatedDual_of_ne_two
          p k hp_two)

@[simp] theorem polarDualPadicQuotientEquivLatticeOfPolarFormAssociated_mkQ
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (x : Fin n → ℤ_[p]) :
    H.polarDualPadicQuotientEquivLatticeOfPolarFormAssociated p k hp_two
        ((H.polarDualPadicDenominator p k).mkQ x) =
      (H.latticeOfPolarForm.associatedBilinearDualPadicDenominator p k).mkQ x := by
  simp [polarDualPadicQuotientEquivLatticeOfPolarFormAssociated,
    Submodule.Quotient.equiv]

/-- The integral-coordinate quotient is likewise explicitly equivalent to
the integral model source-associated quotient before any cardinality comparison. -/
noncomputable def
    polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    ((Fin n → ℤ) ⧸ H.polarDualPadicDenominatorIntegralPreimage p k) ≃ₗ[ℤ]
      ((Fin n → ℤ) ⧸
        H.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage
          p k) :=
  Submodule.Quotient.equiv
    (H.polarDualPadicDenominatorIntegralPreimage p k)
    (H.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage
      p k)
    (LinearEquiv.refl ℤ (Fin n → ℤ))
    (by
      simpa using
        H.polarDualPadicDenominatorIntegralPreimage_eq_latticeOfPolarForm_associatedDual_of_ne_two
          p k hp_two)

@[simp] theorem
    polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated_mkQ
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (x : Fin n → ℤ) :
      H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated
        p k hp_two
        ((H.polarDualPadicDenominatorIntegralPreimage p k).mkQ x) =
      (H.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage
        p k).mkQ x := by
  simp
    [polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated,
      Submodule.Quotient.equiv]
  rfl

/-! ## Direct quadratic solution families -/

/-- At an odd prime power, equality of direct quadratic values is equivalent
to equality of the scaled integral model values.  The reverse direction cancels the
unit two in the residue ring. -/
theorem quadForm_zmod_eq_iff_latticeOfPolarForm_of_ne_two
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (x y : Fin n → ℤ) :
    ((H.quadForm y : ℤ) :
        ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ)) =
        (H.quadForm x : ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ)) ↔
      (H.latticeOfPolarForm.quadForm y :
        ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ)) =
        (H.latticeOfPolarForm.quadForm x :
          ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ)) := by
  rw [H.latticeOfPolarForm_quadForm, H.latticeOfPolarForm_quadForm]
  simp only [Int.cast_mul, Int.cast_ofNat]
  constructor
  · intro h
    rw [h]
  · intro h
    exact (PositiveDefiniteIntegralLattice.two_isUnit_zmod_primePow p k hp_two).mul_left_cancel h

/-- Direct basis-image families in the integral `A`-dual quotient satisfying
the congruence for `Q_H`, not for the scaled form `2Q_H`. -/
noncomputable def polarDualQuotientSolutionFamilies
    (p k : ℕ) [Fact (Nat.Prime p)] :
    Finset (Fin n →
      ((Fin n → ℤ) ⧸ H.polarDualPadicDenominatorIntegralPreimage p k)) := by
  classical
  have hD_rank :
      Module.finrank ℤ (H.polarDualPadicDenominatorIntegralPreimage p k) = n :=
    H.polarDualPadicDenominatorIntegralPreimage_rank p k
  have hD_rank' :
      Module.finrank ℤ (H.polarDualPadicDenominatorIntegralPreimage p k) =
        Module.finrank ℤ (Fin n → ℤ) := by
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hD_rank
  letI : Finite
      ((Fin n → ℤ) ⧸ H.polarDualPadicDenominatorIntegralPreimage p k) :=
    Submodule.finiteQuotientOfFreeOfRankEq
      (M := Fin n → ℤ) (H.polarDualPadicDenominatorIntegralPreimage p k) hD_rank'
  letI : Fintype
      ((Fin n → ℤ) ⧸ H.polarDualPadicDenominatorIntegralPreimage p k) :=
    Fintype.ofFinite _
  exact Finset.univ.filter fun Y =>
    ∀ x y : Fin n → ℤ,
      PositiveDefiniteIntegralLattice.quotientBasisFamilyMap
          (H.polarDualPadicDenominatorIntegralPreimage p k) Y x =
        (H.polarDualPadicDenominatorIntegralPreimage p k).mkQ y →
      (H.quadForm y : ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ)) =
        (H.quadForm x : ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ))

theorem mem_polarDualQuotientSolutionFamilies_iff
    {p k : ℕ} [Fact (Nat.Prime p)]
    {Y : Fin n →
      ((Fin n → ℤ) ⧸ H.polarDualPadicDenominatorIntegralPreimage p k)} :
    Y ∈ H.polarDualQuotientSolutionFamilies p k ↔
      ∀ x y : Fin n → ℤ,
        PositiveDefiniteIntegralLattice.quotientBasisFamilyMap
            (H.polarDualPadicDenominatorIntegralPreimage p k) Y x =
          (H.polarDualPadicDenominatorIntegralPreimage p k).mkQ y →
        (H.quadForm y : ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ)) =
          (H.quadForm x : ZMod (PositiveDefiniteIntegralLattice.primePowModulus p k : ℕ)) := by
  classical
  simp [polarDualQuotientSolutionFamilies]

/-- The finite type of direct `Q_H` solution families. -/
abbrev polarDualQuotientSolutionFamily
    (p k : ℕ) [Fact (Nat.Prime p)] :=
  {Y : Fin n →
      ((Fin n → ℤ) ⧸ H.polarDualPadicDenominatorIntegralPreimage p k) //
    Y ∈ H.polarDualQuotientSolutionFamilies p k}

/-- Transport a direct family through the literal integral-integral model quotient
equivalence. -/
noncomputable def polarDualQuotientFamilyToLatticeOfPolarFormAssociated
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (Y : Fin n →
      ((Fin n → ℤ) ⧸ H.polarDualPadicDenominatorIntegralPreimage p k)) :
    Fin n → ((Fin n → ℤ) ⧸
      H.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage p k) :=
  fun i =>
    H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated
      p k hp_two (Y i)

theorem quotientBasisFamilyMap_polarDualQuotientFamilyToLatticeOfPolarFormAssociated
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (Y : Fin n →
      ((Fin n → ℤ) ⧸ H.polarDualPadicDenominatorIntegralPreimage p k))
    (x : Fin n → ℤ) :
    PositiveDefiniteIntegralLattice.quotientBasisFamilyMap
        (H.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage p k)
        (H.polarDualQuotientFamilyToLatticeOfPolarFormAssociated p k hp_two Y) x =
      H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated
        p k hp_two
        (PositiveDefiniteIntegralLattice.quotientBasisFamilyMap
          (H.polarDualPadicDenominatorIntegralPreimage p k) Y x) := by
  classical
  simp [PositiveDefiniteIntegralLattice.quotientBasisFamilyMap,
    polarDualQuotientFamilyToLatticeOfPolarFormAssociated]

theorem polarDualQuotientFamilyToLatticeOfPolarFormAssociated_mem
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (Y : H.polarDualQuotientSolutionFamily p k) :
    H.polarDualQuotientFamilyToLatticeOfPolarFormAssociated p k hp_two Y.1 ∈
      PositiveDefiniteIntegralLattice.localDualQuotientSolutionFamilies
        H.latticeOfPolarForm p k
        (H.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage p k)
        (PositiveDefiniteIntegralLattice.associatedBilinearDualPadicDenominatorIntegralPreimage_rank
          (n := n) H.latticeOfPolarForm p k) := by
  rw [PositiveDefiniteIntegralLattice.mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  have hpre :
      PositiveDefiniteIntegralLattice.quotientBasisFamilyMap
          (H.polarDualPadicDenominatorIntegralPreimage p k) Y.1 x =
        (H.polarDualPadicDenominatorIntegralPreimage p k).mkQ y := by
    apply
      (H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated
        p k hp_two).injective
    rw [← H.quotientBasisFamilyMap_polarDualQuotientFamilyToLatticeOfPolarFormAssociated
      p k hp_two Y.1 x,
      H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated_mkQ]
    exact hxy
  exact (H.quadForm_zmod_eq_iff_latticeOfPolarForm_of_ne_two p k hp_two x y).mp
    ((H.mem_polarDualQuotientSolutionFamilies_iff.mp Y.2) x y hpre)

/-- Transport a source-associated integral model family back to the direct quotient. -/
noncomputable def latticeOfPolarFormAssociatedQuotientFamilyToPolarDual
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (Y : Fin n → ((Fin n → ℤ) ⧸
      H.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage p k)) :
    Fin n → ((Fin n → ℤ) ⧸
      H.polarDualPadicDenominatorIntegralPreimage p k) :=
  fun i =>
    (H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated
      p k hp_two).symm (Y i)

theorem latticeOfPolarFormAssociatedQuotientFamilyToPolarDual_mem
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (Y : PositiveDefiniteIntegralLattice.associatedBilinearDualQuotientSolutionFamily
      H.latticeOfPolarForm p k) :
    H.latticeOfPolarFormAssociatedQuotientFamilyToPolarDual p k hp_two Y.1 ∈
      H.polarDualQuotientSolutionFamilies p k := by
  rw [H.mem_polarDualQuotientSolutionFamilies_iff]
  intro x y hxy
  have hmap :
      PositiveDefiniteIntegralLattice.quotientBasisFamilyMap
          (H.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage p k)
          Y.1 x =
        (H.latticeOfPolarForm.associatedBilinearDualPadicDenominatorIntegralPreimage p k).mkQ
          y := by
    apply
      (H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated
        p k hp_two).symm.injective
    simpa [latticeOfPolarFormAssociatedQuotientFamilyToPolarDual,
      PositiveDefiniteIntegralLattice.quotientBasisFamilyMap, map_sum] using hxy
  exact (H.quadForm_zmod_eq_iff_latticeOfPolarForm_of_ne_two p k hp_two x y).mpr
    ((PositiveDefiniteIntegralLattice.mem_localDualQuotientSolutionFamilies_iff.mp Y.2) x y hmap)

/-- Actual equivalence between the direct `Q_H` solution families and the
integral model source-associated `2Q_H` solution families at an odd prime power. -/
noncomputable def polarDualQuotientSolutionFamilyEquivLatticeOfPolarFormAssociated
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    H.polarDualQuotientSolutionFamily p k ≃
      PositiveDefiniteIntegralLattice.associatedBilinearDualQuotientSolutionFamily
        H.latticeOfPolarForm p k where
  toFun Y :=
    ⟨H.polarDualQuotientFamilyToLatticeOfPolarFormAssociated p k hp_two Y.1,
      H.polarDualQuotientFamilyToLatticeOfPolarFormAssociated_mem p k hp_two Y⟩
  invFun Y :=
    ⟨H.latticeOfPolarFormAssociatedQuotientFamilyToPolarDual p k hp_two Y.1,
      H.latticeOfPolarFormAssociatedQuotientFamilyToPolarDual_mem p k hp_two Y⟩
  left_inv Y := by
    apply Subtype.ext
    ext i
    exact
      (H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated
        p k hp_two).symm_apply_apply (Y.1 i)
  right_inv Y := by
    apply Subtype.ext
    ext i
    exact
      (H.polarDualPadicDenominatorIntegralPreimageQuotientEquivLatticeOfPolarFormAssociated
        p k hp_two).apply_symm_apply (Y.1 i)

/-- The direct finite solution-family count. -/
noncomputable def polarDualQuotientCount
    (p k : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  Nat.card (H.polarDualQuotientSolutionFamily p k)

/-- The direct `Q_H` quotient count equals the integral model source-associated count
at every odd prime power, after the literal family equivalence. -/
theorem polarDualQuotientCount_eq_latticeOfPolarForm_associated_of_ne_two
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    H.polarDualQuotientCount p k =
      H.latticeOfPolarForm.associatedBilinearDualQuotientCount p k := by
  rw [polarDualQuotientCount,
    PositiveDefiniteIntegralLattice.associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
  exact Nat.card_congr
    (H.polarDualQuotientSolutionFamilyEquivLatticeOfPolarFormAssociated
      p k hp_two)

end PositiveDefiniteIntegralQuadraticForm

end
