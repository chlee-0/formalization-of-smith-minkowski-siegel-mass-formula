import SMSFormula.Applications.Examples.TernaryAnalyticFactors
import Mathlib.Data.Nat.Periodic
import Mathlib.NumberTheory.LSeries.Linearity

/-! The primitive modulus-five character and its cosine expansion. -/

noncomputable section

namespace MassFormulaReleaseExamples

local instance a4CharacterPrime : Fact (Nat.Prime 5) := ⟨by decide⟩

def a4ChiFiveValue (a : ZMod 5) : ℤ :=
  if a = 0 then 0 else if a = 1 ∨ a = 4 then 1 else -1

def a4ChiFiveInt : MulChar (ZMod 5) ℤ where
  toFun := a4ChiFiveValue
  map_one' := by decide
  map_mul' := by
    have h : ∀ a b : ZMod 5, a4ChiFiveValue (a * b) =
        a4ChiFiveValue a * a4ChiFiveValue b := by decide +kernel
    exact h
  map_nonunit' := by
    intro a ha
    have hz : a = 0 := by
      by_contra hn
      exact ha (isUnit_iff_ne_zero.mpr hn)
    rw [hz]
    decide

def a4ChiFive : DirichletCharacter ℂ 5 :=
  a4ChiFiveInt.ringHomComp (Int.castRingHom ℂ)

theorem a4ChiFive_apply (a : ZMod 5) :
    a4ChiFive a = (a4ChiFiveValue a : ℂ) := rfl

theorem a4_cos_two_pi_five : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h := Real.cos_two_mul (Real.pi / 5)
  rw [Real.cos_pi_div_five] at h
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring]
  rw [h]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]

theorem a4_cos_four_pi_five : Real.cos (4 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  rw [show 4 * Real.pi / 5 = Real.pi - Real.pi / 5 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

def a4CosineDifference (n : ℕ) : ℝ :=
  Real.cos (2 * Real.pi * (1/5) * n) - Real.cos (2 * Real.pi * (2/5) * n)

theorem a4CosineDifference_periodic : Function.Periodic a4CosineDifference 5 := by
  intro n
  unfold a4CosineDifference
  push_cast
  rw [show 2 * Real.pi * (1/5) * ((n:ℝ)+5) =
    2 * Real.pi * (1/5) * n + 2 * Real.pi by ring,
    show 2 * Real.pi * (2/5) * ((n:ℝ)+5) =
    (2 * Real.pi * (2/5) * n + 2 * Real.pi) + 2 * Real.pi by ring]
  rw [Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_add_two_pi]

theorem a4CosineDifference_five (n : Fin 5) :
    a4CosineDifference n = Real.sqrt 5 / 2 * (a4ChiFiveValue (n:ℕ) : ℝ) := by
  have h6 : Real.cos (6 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
    rw [show 6 * Real.pi / 5 = 2 * Real.pi - 4 * Real.pi / 5 by ring,
      Real.cos_two_pi_sub, a4_cos_four_pi_five]
  have h8 : Real.cos (8 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    rw [show 8 * Real.pi / 5 = 2 * Real.pi - 2 * Real.pi / 5 by ring,
      Real.cos_two_pi_sub, a4_cos_two_pi_five]
  have h12 : Real.cos (12 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    rw [show 12 * Real.pi / 5 = 2 * Real.pi / 5 + 2 * Real.pi by ring,
      Real.cos_add_two_pi, a4_cos_two_pi_five]
  have h16 : Real.cos (16 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
    rw [show 16 * Real.pi / 5 = 6 * Real.pi / 5 + 2 * Real.pi by ring,
      Real.cos_add_two_pi, h6]
  have hform (m : ℕ) : a4CosineDifference m =
      Real.cos ((2*m:ℕ) * Real.pi / 5) - Real.cos ((4*m:ℕ) * Real.pi / 5) := by
    unfold a4CosineDifference
    push_cast
    congr 2 <;> ring
  have hv : ∀ i : Fin 5, a4ChiFiveValue (i:ℕ) = ![0,1,-1,-1,1] i := by decide +kernel
  rw [hv]
  fin_cases n <;> norm_num [hform, a4_cos_two_pi_five,
    a4_cos_four_pi_five, h6, h8, h12, h16] <;> ring

theorem a4CosineDifference_character (n : ℕ) :
    a4CosineDifference n = Real.sqrt 5 / 2 * (a4ChiFiveValue n : ℝ) := by
  have h := a4CosineDifference_five ⟨n % 5, Nat.mod_lt n (by decide)⟩
  have hz : ((n % 5 : ℕ) : ZMod 5) = (n : ZMod 5) := by
    simpa only [ZMod.val_natCast] using ZMod.natCast_zmod_val (n : ZMod 5)
  simpa only [Fin.val_mk, a4CosineDifference_periodic.map_mod_nat, hz] using h

theorem a4_cosZeta_difference :
    HurwitzZeta.cosZeta ((1/5:ℝ) : UnitAddCircle) 2 - HurwitzZeta.cosZeta ((2/5:ℝ) : UnitAddCircle) 2 =
      (2:ℂ) * Real.pi ^ 2 / 25 := by
  have h1 := HurwitzZeta.cosZeta_two_mul_nat (k := 1) (x := (1/5:ℝ))
    (by decide) (by constructor <;> norm_num)
  have h2 := HurwitzZeta.cosZeta_two_mul_nat (k := 1) (x := (2/5:ℝ))
    (by decide) (by constructor <;> norm_num)
  have hb : bernoulli 2 = (1/6:ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1), bernoulli'_two]
  norm_num [Polynomial.bernoulli, Finset.sum_range_succ, hb] at h1 h2
  rw [h1,h2]
  ring

theorem a4_chiFive_LSeries_two :
    LSeries (fun n : ℕ => a4ChiFive n) 2 =
      (4:ℂ) * Real.pi ^ 2 / (25 * (Real.sqrt 5 : ℂ)) := by
  have h1 := HurwitzZeta.LSeriesHasSum_cos (1/5) (s := (2:ℂ)) (by norm_num)
  have h2 := HurwitzZeta.LSeriesHasSum_cos (2/5) (s := (2:ℂ)) (by norm_num)
  have h := (h1.sub h2).smul (2 / (Real.sqrt 5 : ℂ))
  have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 5))
  have hf : (2 / (Real.sqrt 5 : ℂ)) •
      ((fun n : ℕ => (Real.cos (2 * Real.pi * (1/5) * n) : ℂ)) -
       (fun n : ℕ => (Real.cos (2 * Real.pi * (2/5) * n) : ℂ))) =
      (fun n : ℕ => a4ChiFive n) := by
    funext n
    change (2 / (Real.sqrt 5 : ℂ)) *
      ((Real.cos (2 * Real.pi * (1/5) * n) : ℂ) -
       (Real.cos (2 * Real.pi * (2/5) * n) : ℂ)) = _
    rw [← Complex.ofReal_sub]
    change (2 / (Real.sqrt 5 : ℂ)) * (a4CosineDifference n : ℂ) = _
    rw [a4CosineDifference_character, a4ChiFive_apply]
    push_cast
    field_simp
  rw [hf, a4_cosZeta_difference] at h
  have ht := h.tsum_eq
  change LSeries (fun n : ℕ => a4ChiFive n) 2 = _ at ht
  rw [ht]
  ring

theorem a4_jacobi_finite_table : ∀ n : Fin 320, Nat.Coprime n.val 320 →
    jacobiSym 80 n.val = a4ChiFiveValue n.val := by decide +kernel

theorem a4_character_changeLevel :
    PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletCharacter a4.latticeOfPolarForm 2 =
      DirichletCharacter.changeLevel
        (show 5 ∣ PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2 by
          rw [a4_latticeOfPolarForm_characterModulus]; decide) a4ChiFive := by
  letI : NeZero (PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2) :=
    ⟨by rw [a4_latticeOfPolarForm_characterModulus]; decide⟩
  apply MulChar.ext
  intro u
  rw [PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletCharacter, dif_pos (by decide),
    PositiveDefiniteIntegralLattice.goodPrimeEvenJacobiDirichletCharacter_apply_unit,
    DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulChar.coe_toUnitHom,
    ZMod.unitsMap_val, ZMod.cast_eq_val, a4ChiFive_apply]
  have ht := a4_jacobi_finite_table
    ⟨(u : ZMod (PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2)).val, by simpa only [a4_latticeOfPolarForm_characterModulus] using ZMod.val_lt (u : ZMod (PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2))⟩
    (by simpa only [a4_latticeOfPolarForm_characterModulus] using ZMod.val_coe_unit_coprime u)
  rw [a4_latticeOfPolarForm_characterDiscriminant]
  exact_mod_cast ht

theorem a4_retained_LSeries_two :
    LSeries (fun n : ℕ =>
      PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletCharacter a4.latticeOfPolarForm 2 n) 2 =
      (Real.pi : ℂ)^2 / (5 * (Real.sqrt 5 : ℂ)) := by
  letI : NeZero (PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2) :=
    ⟨by rw [a4_latticeOfPolarForm_characterModulus]; decide⟩
  rw [a4_character_changeLevel]
  have h := DirichletCharacter.LSeries_changeLevel
    (show 5 ∣ PositiveDefiniteIntegralLattice.goodPrimeEvenDirichletModulus a4.latticeOfPolarForm 2 by
      rw [a4_latticeOfPolarForm_characterModulus]; decide) a4ChiFive (s := (2:ℂ)) (by norm_num)
  change LSeries (fun n : ℕ => _) 2 = _ at h
  rw [h, a4_chiFive_LSeries_two, a4_latticeOfPolarForm_characterModulus]
  have hp : (320:ℕ).primeFactors = {2,5} := by
    rw [show (320:ℕ) = 2^6 * 5 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow 2 (by decide)]
    norm_num
  rw [hp]
  have hv2 : a4ChiFive (2:ZMod 5) = -1 := by
    rw [a4ChiFive_apply, show a4ChiFiveValue 2 = -1 by decide]
    norm_num
  have hv5 : a4ChiFive (5:ZMod 5) = 0 := by
    rw [a4ChiFive_apply, show a4ChiFiveValue 5 = 0 by decide]
    norm_num
  norm_num [hv2, hv5, Complex.cpow_neg, Complex.cpow_ofNat]
  ring

end MassFormulaReleaseExamples
