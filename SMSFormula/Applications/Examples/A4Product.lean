import SMSFormula.Applications.Examples.A4Character
import SMSFormula.Applications.Examples.A4FiveRecovery
import SMSFormula.Applications.Examples.A4DyadicTransport
import SMSFormula.FiniteOrthogonalGroupGoodPrimeClosedLimit

/-! Original A4 bad factors and its ordered inverse-density product. -/

noncomputable section

namespace MassFormulaReleaseExamples

open PositiveDefiniteIntegralLattice

attribute [local irreducible] a4DyadicModelFamilies

theorem a4_badPrimes : massBadPrimeSet a4.latticeOfPolarForm =
    {⟨2, Nat.prime_two⟩, ⟨5, by decide⟩} := by
  ext p
  rw [mem_massBadPrimeSet_iff, a4_latticeOfPolarForm_polarDeterminant]
  change (p.val = 2 ∨ p.val ∣ 80) ↔ _
  have hd : p.val ∣ 80 ↔ p.val = 2 ∨ p.val = 5 := by
    rw [show 80 = 2 * 2 * 2 * 2 * (5:ℕ) by norm_num,
      p.prop.dvd_mul, p.prop.dvd_mul, p.prop.dvd_mul, p.prop.dvd_mul]
    have h2 : p.val ∣ 2 ↔ p.val = 2 :=
      Nat.dvd_prime Nat.prime_two |>.trans (by simp [p.prop.ne_one])
    have h5 : p.val ∣ 5 ↔ p.val = 5 :=
      Nat.dvd_prime (by decide : Nat.Prime 5) |>.trans (by simp [p.prop.ne_one])
    rw [h2,h5]
    tauto
  simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, hd]
  tauto

theorem a4_badPrimes_le_five : massBadPrimeSet a4.latticeOfPolarForm ⊆ rationalPrimesUpTo 5 := by
  rw [a4_badPrimes]
  decide

theorem a4_goodPrimes_five : rationalPrimesUpTo 5 \ massBadPrimeSet a4.latticeOfPolarForm =
    {⟨3, by decide⟩} := by
  rw [a4_badPrimes]
  decide

theorem a4_goodCharacter_three :
    goodPrimeQuadraticCharacter a4.latticeOfPolarForm ⟨3, by decide⟩ = -1 := by
  rw [goodPrimeQuadraticCharacter, a4_latticeOfPolarForm_polarDeterminant]
  decide +kernel

theorem a4_badInverseProduct : massBadPrimeInverseProduct a4.latticeOfPolarForm =
    25 * Real.sqrt 5 / 144 := by
  unfold massBadPrimeInverseProduct
  rw [a4_badPrimes]
  norm_num [massFinitePrimeInverseProduct, massLocalInverseFactorAtPrime, massLocalFactorAtPrime,
    massLocalFactor, a4_density_two, a4_density_five]
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]

theorem a4_partialInverseProduct_five :
    massPartialPrimeInverseProduct a4.latticeOfPolarForm 5 = 45 * Real.sqrt 5 / 256 := by
  rw [massPartialPrimeInverseProduct_eq_badPrimeSet_mul_goodPrimeClassical
    a4.latticeOfPolarForm 5 a4_badPrimes_le_five]
  rw [massGoodPrimeClassicalInverseProduct_eq_goodPrimeEvenEulerProduct
    a4.latticeOfPolarForm _ (by intro p hp; exact (Finset.mem_sdiff.mp hp).2)
    2 (by decide) (by decide)]
  rw [a4_badInverseProduct, a4_goodPrimes_five]
  norm_num [goodPrimeEvenEulerFactor, goodPrimeEulerCore,
    a4_goodCharacter_three, Real.rpow_neg_natCast]
  ring

theorem primesBelow_six : (6:ℕ).primesBelow = {2,3,5} := by decide

theorem a4_zetaTail_five : goodPrimeEulerCoreZetaTailFactor 5 1 =
    8 * Real.pi^2 / 75 := by
  unfold goodPrimeEulerCoreZetaTailFactor
  norm_num only [Nat.reduceMul, Nat.cast_ofNat, Complex.ofReal_ofNat]
  rw [zeta_two_real_value, goodPrimeEulerCoreInverseProduct_eq_primesBelow]
  norm_num only [Nat.reduceAdd]
  rw [primesBelow_six]
  norm_num [Real.rpow_neg_natCast]
  ring

theorem a4_retainedCharacter_two :
    goodPrimeEvenDirichletCharacter a4.latticeOfPolarForm 2 (2:ZMod (goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2)) = 0 := by
  apply MulChar.map_nonunit
  change ¬ IsUnit ((2:ℕ) : ZMod (goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2))
  rw [ZMod.isUnit_iff_coprime, a4_latticeOfPolarForm_characterModulus]
  decide

theorem a4_retainedCharacter_five :
    goodPrimeEvenDirichletCharacter a4.latticeOfPolarForm 2 (5:ZMod (goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2)) = 0 := by
  apply MulChar.map_nonunit
  change ¬ IsUnit ((5:ℕ) : ZMod (goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2))
  rw [ZMod.isUnit_iff_coprime, a4_latticeOfPolarForm_characterModulus]
  decide

theorem a4_retainedCharacter_three :
    goodPrimeEvenDirichletCharacter a4.latticeOfPolarForm 2 (3:ZMod (goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2)) = -1 := by
  have h := goodPrimeQuadraticCharacter_eq_dirichletCharacter a4.latticeOfPolarForm 2
    ⟨3,by decide⟩ (by rw [a4_badPrimes]; decide) (by decide)
  rw [a4_goodCharacter_three] at h
  norm_num at h
  exact h.symm

theorem a4_dirichletTail_five :
    goodPrimeEvenDirichletTailFactorOfCharacter a4.latticeOfPolarForm 5 2 =
      2 * Real.pi^2 / (9 * Real.sqrt 5) := by
  have hc : goodPrimeEvenDirichletComplexTailFactor a4.latticeOfPolarForm 5 2 =
      (2:ℂ) * (Real.pi:ℂ)^2 / (9 * (Real.sqrt 5:ℂ)) := by
    unfold goodPrimeEvenDirichletComplexTailFactor
    dsimp only
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    rw [a4_retained_LSeries_two, primesBelow_six]
    norm_num [a4_retainedCharacter_two, a4_retainedCharacter_three, a4_retainedCharacter_five,
      Complex.cpow_neg, Complex.cpow_ofNat]
    ring
  have hr : (2:ℂ) * (Real.pi:ℂ)^2 / (9 * (Real.sqrt 5:ℂ)) =
      ((2 * Real.pi^2 / (9 * Real.sqrt 5):ℝ):ℂ) := by push_cast; rfl
  unfold goodPrimeEvenDirichletTailFactorOfCharacter
  rw [hc, hr, Complex.ofReal_re]

theorem a4_evenProductExpression :
    massPartialPrimeInverseProduct a4.latticeOfPolarForm 5 *
      ((Finset.Icc 1 (2-1)).prod (fun j => goodPrimeEulerCoreZetaTailFactor 5 j) *
        goodPrimeEvenDirichletTailFactorOfCharacter a4.latticeOfPolarForm 5 2) =
      Real.pi^4 / 240 := by
  rw [a4_partialInverseProduct_five]
  norm_num only [Nat.reduceSub, Finset.Icc_self, Finset.prod_singleton]
  rw [a4_zetaTail_five, a4_dirichletTail_five]
  field_simp
  ring

theorem a4_inverseProduct_limit :
    massLocalInverseProductTendsTo a4.latticeOfPolarForm (Real.pi^4/240) := by
  have h := massLocalInverseProductTendsTo_of_goodPrimeEvenDirichletEulerProduct_one_lt
    a4.latticeOfPolarForm a4_badPrimes_le_five (s := 2) (by decide) (by decide)
  rwa [a4_evenProductExpression] at h

end MassFormulaReleaseExamples
