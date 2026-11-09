import SMSFormula.Applications.Examples.BinaryInstantiation

/-!
# The original A2 binary bad-prime factors

All local counts refer to the actual `2Q` integral integral model. No global class
enumeration or proposed numerical genus mass is an input to these proofs.
-/

noncomputable section

namespace MassFormulaReleaseExamples

open BinaryNormIdeal PositiveDefiniteIntegralLattice

theorem a2_normIndex_two :
    Nat.card (OrderUnitNormQuotient ℤ_[2] (-3)) = 1 :=
  card_orderUnitNormQuotient_two_eq_one_of_odd (-3) (by norm_num)

theorem a2_normOneResiduePairs_three : (normOneResiduePairs 3 (-3)).card = 6 := by
  decide

theorem a2_normUnitResiduePairs_three : (normUnitResiduePairs 3 (-3)).card = 6 := by
  decide

theorem a2_normIndex_three :
    Nat.card (OrderUnitNormQuotient ℤ_[3] (-3)) = 2 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [card_orderUnitNormQuotient_eq_finiteNorm]
  change Nat.card (OrderUnitNormQuotient (ZMod 3) (-3)) = 2
  have h := card_orderUnitNorm_ker_mul_scalarUnits (ZMod 3) (-3)
  have hu : Nat.card (ZMod 3)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    norm_num [Nat.totient_prime (by decide : Nat.Prime 3)]
  rw [card_orderUnitNorm_ker_eq_normOneResiduePairs,
    card_orderUnits_eq_normUnitResiduePairs, hu,
    a2_normOneResiduePairs_three, a2_normUnitResiduePairs_three] at h
  omega

theorem a2_badPrimes :
    massBadPrimeSet a2.latticeOfPolarForm =
      {⟨2, Nat.prime_two⟩, ⟨3, by decide⟩} := by
  ext p
  rw [mem_massBadPrimeSet_iff, a2_latticeOfPolarForm_polarDeterminant]
  change (p.val = 2 ∨ p.val ∣ 12) ↔ _
  have hd : p.val ∣ 12 ↔ p.val = 2 ∨ p.val = 3 := by
    have h12 : 12 = 2 * 2 * (3 : ℕ) := by norm_num
    rw [h12, p.prop.dvd_mul, p.prop.dvd_mul]
    have h2 : p.val ∣ 2 ↔ p.val = 2 :=
      Nat.dvd_prime Nat.prime_two |>.trans (by simp [p.prop.ne_one])
    have h3 : p.val ∣ 3 ↔ p.val = 3 :=
      Nat.dvd_prime (by decide : Nat.Prime 3) |>.trans (by simp [p.prop.ne_one])
    rw [h2, h3]
    tauto
  simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, hd]
  tauto

theorem a2_localNormIndexProduct : a2.latticeOfPolarForm.binaryLocalNormIndexProduct = 2 := by
  unfold binaryLocalNormIndexProduct
  rw [a2_badPrimes]
  simp [a2_latticeOfPolarForm_binaryPrimitiveDiscriminant, a2_normIndex_two, a2_normIndex_three]

theorem a2_orderIndex : a2.latticeOfPolarForm.binaryOrderIndex = 1 := by
  letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
  letI := a2.latticeOfPolarForm.binaryFractionNumberField
  have h := congrArg Int.natAbs
    a2.latticeOfPolarForm.binaryPrimitiveDiscriminant_eq_orderIndex_sq_mul_fieldDiscr
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
    a2_latticeOfPolarForm_binaryPrimitiveDiscriminant] at h
  norm_num at h
  have hi := a2.latticeOfPolarForm.binaryOrderIndex_pos
  have hf : 0 < (NumberField.discr
      (FractionRing (DiscriminantOrder a2.latticeOfPolarForm.binaryPrimitiveDiscriminant))).natAbs := by
    by_contra hn
    have hz : (NumberField.discr
        (FractionRing (DiscriminantOrder a2.latticeOfPolarForm.binaryPrimitiveDiscriminant))).natAbs = 0 := by
      omega
    rw [hz, mul_zero] at h
    contradiction
  have hb : a2.latticeOfPolarForm.binaryOrderIndex ^ 2 ≤ 3 := by
    calc
      _ ≤ a2.latticeOfPolarForm.binaryOrderIndex ^ 2 *
          (NumberField.discr
            (FractionRing (DiscriminantOrder a2.latticeOfPolarForm.binaryPrimitiveDiscriminant))).natAbs :=
        Nat.le_mul_of_pos_right _ hf
      _ = 3 := h.symm
  nlinarith

theorem a2_fieldDiscriminant :
    letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
    letI := a2.latticeOfPolarForm.binaryFractionNumberField
    NumberField.discr
      (FractionRing (DiscriminantOrder a2.latticeOfPolarForm.binaryPrimitiveDiscriminant)) = -3 := by
  letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
  letI := a2.latticeOfPolarForm.binaryFractionNumberField
  have h := a2.latticeOfPolarForm.binaryPrimitiveDiscriminant_eq_orderIndex_sq_mul_fieldDiscr
  have hfield : NumberField.discr
      (FractionRing (DiscriminantOrder a2.latticeOfPolarForm.binaryPrimitiveDiscriminant)) =
        a2.latticeOfPolarForm.binaryPrimitiveDiscriminant := by
    simpa only [a2_orderIndex, Nat.cast_one, one_pow, one_mul] using h.symm
  exact hfield.trans a2_latticeOfPolarForm_binaryPrimitiveDiscriminant

theorem a2_fieldSign_two : conductorPrimeSign (-3) 2 = -1 := by decide

theorem a2_fieldSign_three : conductorPrimeSign (-3) 3 = 0 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [conductorPrimeSign_eq, if_neg (by decide : 3 ≠ 2)]
  rw [legendreSym.eq_zero_iff]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (-3) 3).mpr (by norm_num)

theorem a2_massLocalFactor_two : massLocalFactor a2.latticeOfPolarForm 2 = 6 := by
  letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
  letI := a2.latticeOfPolarForm.binaryFractionNumberField
  rw [a2.latticeOfPolarForm.binaryMassLocalFactor_eq_orderNormIndex, a2_fieldDiscriminant]
  norm_num [a2_latticeOfPolarForm_binaryPrimitiveDiscriminant, a2_orderIndex,
    a2_normIndex_two, a2_fieldSign_two]
  rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 3)]
  norm_num

theorem a2_massLocalFactor_three :
    massLocalFactor a2.latticeOfPolarForm 3 = 2 / Real.sqrt 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
  letI := a2.latticeOfPolarForm.binaryFractionNumberField
  rw [a2.latticeOfPolarForm.binaryMassLocalFactor_eq_orderNormIndex, a2_fieldDiscriminant]
  norm_num [a2_latticeOfPolarForm_binaryPrimitiveDiscriminant, a2_orderIndex,
    a2_normIndex_three, a2_fieldSign_three]
  rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  ring

theorem a2_badDensityCorrection :
    a2.latticeOfPolarForm.binaryBadDensityCorrection = Real.sqrt 3 / 8 := by
  letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
  letI := a2.latticeOfPolarForm.binaryFractionNumberField
  rw [a2.latticeOfPolarForm.binaryBadDensityCorrection_eq_sqrt_div_normIndexProduct]
  norm_num [a2_latticeOfPolarForm_binaryPrimitiveDiscriminant, a2_orderIndex,
    a2_localNormIndexProduct]

end MassFormulaReleaseExamples
