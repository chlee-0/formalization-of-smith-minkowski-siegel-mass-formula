import SMSFormula.Applications.Examples.A2LocalFactors
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The A2 field residue through the existing analytic class-number formula

The discriminant bound proves principality. Finite integer norm equations count
order units; no enumeration of lattice genus classes is assumed.
-/

noncomputable section

namespace MassFormulaReleaseExamples

open BinaryNormIdeal PositiveDefiniteIntegralLattice

local notation "O" => DiscriminantOrder a2.latticeOfPolarForm.binaryPrimitiveDiscriminant
local notation "E" => FractionRing O
local notation "bD" => a2.latticeOfPolarForm.binaryPrimitiveDiscriminant % 2
local notation "cD" => ((a2.latticeOfPolarForm.binaryPrimitiveDiscriminant % 2)^2 -
  a2.latticeOfPolarForm.binaryPrimitiveDiscriminant) / 4

theorem a2_integerRing_isPrincipal :
    letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
    letI := a2.latticeOfPolarForm.binaryFractionNumberField
    IsPrincipalIdealRing (NumberField.RingOfIntegers E) := by
  letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
  letI := a2.latticeOfPolarForm.binaryFractionNumberField
  apply _root_.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [a2_fieldDiscriminant, a2.latticeOfPolarForm.binaryFraction_nrComplexPlaces_one,
    a2.latticeOfPolarForm.binaryFractionField_finrank_two]
  norm_num
  nlinarith [Real.pi_gt_three]

def a2_integerNormOnePairs : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-1) 1).product (Finset.Icc (-1) 1)).filter
    (fun z => z.1^2 + z.1*z.2 + z.2^2 = 1)

theorem a2_integerNormOnePairs_card : a2_integerNormOnePairs.card = 6 := by decide

theorem a2_integerNormOne_bounds (a b : ℤ) (h : a^2 + a*b + b^2 = 1) :
    (-1 ≤ a ∧ a ≤ 1) ∧ (-1 ≤ b ∧ b ≤ 1) := by
  have ha : 3*a^2 ≤ 4 := by nlinarith [sq_nonneg (a+2*b)]
  have hb : 3*b^2 ≤ 4 := by nlinarith [sq_nonneg (2*a+b)]
  have ha' : a^2 ≤ 1 := by omega
  have hb' : b^2 ≤ 1 := by omega
  constructor
  · constructor <;> nlinarith [sq_nonneg (a-2), sq_nonneg (a+2)]
  · constructor <;> nlinarith [sq_nonneg (b-2), sq_nonneg (b+2)]

def a2_orderUnitsEquivNormPairs :
    (CoefficientOrder 1 1 1)ˣ ≃ {z // z ∈ a2_integerNormOnePairs} where
  toFun u := ⟨(u.val.re, u.val.im), by
    have h := norm_coefficientOrder_unit 1 1 1 (by norm_num) u
    have hn : u.val.re^2 + u.val.re*u.val.im + u.val.im^2 = 1 := by
      rw [QuadraticAlgebra.norm_def] at h
      norm_num at h
      nlinarith
    have hb := a2_integerNormOne_bounds _ _ hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr hb.1, Finset.mem_Icc.mpr hb.2⟩, hn⟩⟩
  invFun z := unitOfNormOne 1 1 1 ⟨z.val.1, z.val.2⟩ (by
    have h := (Finset.mem_filter.mp z.prop).2
    rw [QuadraticAlgebra.norm_def]
    norm_num
    nlinarith)
  left_inv u := by
    apply Units.ext
    exact QuadraticAlgebra.ext rfl rfl
  right_inv z := by apply Subtype.ext; rfl

theorem a2_orderUnits_card : Nat.card Oˣ = 6 := by
  rw [a2_latticeOfPolarForm_binaryPrimitiveDiscriminant]
  change Nat.card (CoefficientOrder 1 1 1)ˣ = 6
  rw [Nat.card_congr a2_orderUnitsEquivNormPairs]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using a2_integerNormOnePairs_card

theorem a2_orderToIntegers_surjective :
    letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
    Function.Surjective (orderToRingOfIntegers 1 bD cD) := by
  letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
  have hc : Nat.card (NumberField.RingOfIntegers E ⧸ orderImage 1 bD cD) = 1 := a2_orderIndex
  letI : Subsingleton (NumberField.RingOfIntegers E ⧸ orderImage 1 bD cD) :=
    (Nat.card_eq_one_iff_unique.mp hc).1
  intro x
  have hx : (Submodule.Quotient.mk x : NumberField.RingOfIntegers E ⧸ orderImage 1 bD cD) = 0 :=
    Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero _).mp hx

theorem a2_integerUnits_card :
    letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
    Nat.card (NumberField.RingOfIntegers E)ˣ = 6 := by
  letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
  let e := RingEquiv.ofBijective (orderToRingOfIntegers 1 bD cD).toRingHom
    ⟨orderToRingOfIntegers_injective 1 bD cD, a2_orderToIntegers_surjective⟩
  rw [← Nat.card_congr (Units.mapEquiv e.toMulEquiv).toEquiv]
  exact a2_orderUnits_card

theorem a2_maximalClassGroup_card :
    letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
    letI := a2.latticeOfPolarForm.binaryFractionNumberField
    Nat.card (ClassGroup (NumberField.RingOfIntegers E)) = 1 := by
  letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
  letI := a2.latticeOfPolarForm.binaryFractionNumberField
  have h := (NumberField.classNumber_eq_one_iff).mpr a2_integerRing_isPrincipal
  simpa only [NumberField.classNumber, Nat.card_eq_fintype_card] using h

theorem a2_dedekindResidue :
    letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
    letI := a2.latticeOfPolarForm.binaryFractionNumberField
    NumberField.dedekindZeta_residue E = Real.pi / (3 * Real.sqrt 3) := by
  letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
  letI := a2.latticeOfPolarForm.binaryFractionNumberField
  have h := fraction_dedekindZeta_residue_eq 1 bD cD
    a2.latticeOfPolarForm.binaryDiscriminantOrder_discriminant_neg
  dsimp only at h
  rw [a2_maximalClassGroup_card, a2_integerUnits_card, a2_fieldDiscriminant] at h
  norm_num at h
  rw [h]
  ring

theorem a2_orderedProduct_value :
    a2.latticeOfPolarForm.massLocalInverseProductTendsTo (Real.pi / 24) := by
  letI := a2.latticeOfPolarForm.binaryDiscriminantOrder_isDomain
  letI := a2.latticeOfPolarForm.binaryFractionNumberField
  have h := a2.latticeOfPolarForm.massLocalInverseProductTendsTo_binaryResidue_mul_badDensity
  rw [a2_dedekindResidue, a2_badDensityCorrection] at h
  have hs : Real.pi / (3 * Real.sqrt 3) * (Real.sqrt 3 / 8) = Real.pi / 24 := by
    (field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]; ring)
  rwa [hs] at h

/-- Ordinary full-O genus mass of the `2Q` integral model.
The module `A2Intrinsic` proves the intrinsic version
`a2_intrinsic_ordinaryGenusMass`. -/
theorem a2_latticeOfPolarForm_ordinaryGenusMass : a2.latticeOfPolarForm.ordinaryGenusMass = (1/12 : ℚ) := by
  obtain ⟨P, _, hconv, hmass⟩ := a2_actual_massFormula
  have hP : P = Real.pi / 24 := tendsto_nhds_unique hconv a2_orderedProduct_value
  have hr : ((a2.latticeOfPolarForm.ordinaryGenusMass : ℚ) : ℝ) = (1/12 : ℝ) := by
    rw [hmass, hP]
    (field_simp [Real.pi_ne_zero]; ring)
  apply Rat.cast_injective (α := ℝ)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  exact hr

end MassFormulaReleaseExamples
