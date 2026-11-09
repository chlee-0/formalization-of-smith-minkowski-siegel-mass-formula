import SMSFormula.BinaryNormIdeal

/-!
# A common integral order presentation for each primitive discriminant

The trace parameter is r=D%2. The generator satisfies ω²=rω-(r²-D)/4.
Coefficient orders of the same discriminant are integrally isomorphic by
translation of the generator. The maps preserve norm. No maximal-order or
fundamental-discriminant condition is used.
-/

namespace BinaryNormIdeal

open scoped QuadraticAlgebra

/-- Translate the generator by an integer while keeping its orientation. -/
def coefficientOrderEquivOfShift (a b c a' b' c' k : ℤ)
    (hb : b = b' + 2 * k) (hac : a * c = a' * c' + b' * k + k ^ 2) :
    CoefficientOrder a b c ≃ₐ[ℤ] CoefficientOrder a' b' c' where
  toFun z := ⟨z.re + k * z.im, z.im⟩
  invFun z := ⟨z.re - k * z.im, z.im⟩
  left_inv z := by apply QuadraticAlgebra.ext <;> simp
  right_inv z := by apply QuadraticAlgebra.ext <;> simp
  map_add' z w := by
    apply QuadraticAlgebra.ext
    · simp; ring
    · simp
  map_mul' z w := by
    apply QuadraticAlgebra.ext
    · change (z * w).re + k * (z * w).im = _
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
      linear_combination (k * z.im * w.im) * hb - (z.im * w.im) * hac
    · change (z * w).im = _
      simp only [QuadraticAlgebra.im_mul]
      linear_combination (z.im * w.im) * hb
  commutes' r := by apply QuadraticAlgebra.ext <;> simp

/-- This translation preserves the norm in the original integral rings. -/
lemma norm_coefficientOrderEquivOfShift (a b c a' b' c' k : ℤ)
    (hb : b = b' + 2 * k) (hac : a * c = a' * c' + b' * k + k ^ 2)
    (z : CoefficientOrder a b c) :
    (coefficientOrderEquivOfShift a b c a' b' c' k hb hac z).norm = z.norm := by
  change (z.re + k * z.im) * (z.re + k * z.im) +
    b' * (z.re + k * z.im) * z.im - (-a' * c') * z.im * z.im = _
  rw [QuadraticAlgebra.norm_def]
  linear_combination -(z.re * z.im) * hb - (z.im ^ 2) * hac

private lemma two_dvd_trace_sub (a b c a' b' c' : ℤ)
    (hD : b ^ 2 - 4 * a * c = b' ^ 2 - 4 * a' * c') : 2 ∣ b - b' := by
  have h := congrArg (Int.castRingHom (ZMod 2)) hD
  have hh : (b : ZMod 2) ^ 2 = (b' : ZMod 2) ^ 2 := by
    have hn : (4 : ZMod 2) = 0 := by decide
    simpa [hn] using h
  have hs (x : ZMod 2) : x ^ 2 = x := by fin_cases x <;> decide
  rw [hs, hs] at hh
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub b' b 2).mp hh.symm

/-- Equal polynomial discriminants identify the coefficient orders integrally. -/
def coefficientOrderEquivOfDiscriminant (a b c a' b' c' : ℤ)
    (hD : b ^ 2 - 4 * a * c = b' ^ 2 - 4 * a' * c') :
    CoefficientOrder a b c ≃ₐ[ℤ] CoefficientOrder a' b' c' := by
  let k := (b - b') / 2
  have hdiv := Int.mul_ediv_cancel' (two_dvd_trace_sub a b c a' b' c' hD)
  have hb : b = b' + 2 * k := by dsimp only [k]; omega
  have hac : a * c = a' * c' + b' * k + k ^ 2 := by rw [hb] at hD; nlinarith
  exact coefficientOrderEquivOfShift a b c a' b' c' k hb hac

lemma norm_coefficientOrderEquivOfDiscriminant (a b c a' b' c' : ℤ)
    (hD : b ^ 2 - 4 * a * c = b' ^ 2 - 4 * a' * c') (z : CoefficientOrder a b c) :
    (coefficientOrderEquivOfDiscriminant a b c a' b' c' hD z).norm = z.norm := by
  unfold coefficientOrderEquivOfDiscriminant
  apply norm_coefficientOrderEquivOfShift

/-- A single integral ring presentation for a discriminant D. -/
abbrev DiscriminantOrder (D : ℤ) := CoefficientOrder 1 (D % 2) (((D % 2) ^ 2 - D) / 4)

/-- The defining polynomial has exactly discriminant D, including at 2. -/
lemma discriminantOrder_coefficients (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (D % 2) ^ 2 - 4 * 1 * (((D % 2) ^ 2 - D) / 4) = D := by
  have hdiv : (4 : ℤ) ∣ (D % 2) ^ 2 - D := by
    rcases hD with h | h
    · have hr : D % 2 = 0 := by omega
      rw [hr]
      simp only [zero_pow (by decide : 2 ≠ 0), zero_sub]
      exact dvd_neg.mpr (Int.dvd_of_emod_eq_zero h)
    · have hr : D % 2 = 1 := by omega
      rw [hr]
      norm_num
      exact Int.dvd_of_emod_eq_zero (by omega)
  have h := Int.mul_ediv_cancel' hdiv
  omega

/-- Every valid discriminant gives the common integral order, with norm preserved. -/
def coefficientOrderEquivDiscriminantOrder (a b c : ℤ) (D : ℤ)
    (hres : D % 4 = 0 ∨ D % 4 = 1) (hD : b ^ 2 - 4 * a * c = D) :
    CoefficientOrder a b c ≃ₐ[ℤ] DiscriminantOrder D :=
  coefficientOrderEquivOfDiscriminant a b c 1 (D % 2) (((D % 2) ^ 2 - D) / 4)
    (hD.trans (discriminantOrder_coefficients D hres).symm)

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

/-- The actual lattice's coefficient order maps to the order fixed by its
primitive discriminant, rather than an unspecified maximal order. -/
def binaryCoefficientOrderEquivDiscriminantOrder (K : PositiveDefiniteIntegralLattice 2) :
    K.binaryCoefficientOrder ≃ₐ[ℤ] BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant :=
  BinaryNormIdeal.coefficientOrderEquivDiscriminantOrder _ _ _ _
    K.binaryPrimitiveDiscriminant_mod_four rfl

lemma norm_binaryCoefficientOrderEquivDiscriminantOrder (K : PositiveDefiniteIntegralLattice 2)
    (z : K.binaryCoefficientOrder) :
    (K.binaryCoefficientOrderEquivDiscriminantOrder z).norm = z.norm := by
  unfold binaryCoefficientOrderEquivDiscriminantOrder BinaryNormIdeal.coefficientOrderEquivDiscriminantOrder
  apply BinaryNormIdeal.norm_coefficientOrderEquivOfDiscriminant

/-- The primitive norm ideal in the ring determined only by the discriminant. -/
def binaryDiscriminantNormIdeal (K : PositiveDefiniteIntegralLattice 2) :
    Ideal (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant) :=
  K.binaryNormIdeal.comap K.binaryCoefficientOrderEquivDiscriminantOrder.symm.toRingHom

/-- Exact original coordinates on the ideal in the common discriminant order. -/
noncomputable def binaryDiscriminantNormIdealCoordinates (K : PositiveDefiniteIntegralLattice 2) :
    (Fin 2 → ℤ) ≃ₗ[ℤ] K.binaryDiscriminantNormIdeal where
  toFun x := ⟨K.binaryCoefficientOrderEquivDiscriminantOrder
    (K.binaryNormIdealCoordinates x).val, by
      change K.binaryCoefficientOrderEquivDiscriminantOrder.symm
        (K.binaryCoefficientOrderEquivDiscriminantOrder (K.binaryNormIdealCoordinates x).val) ∈ K.binaryNormIdeal
      rw [AlgEquiv.symm_apply_apply]
      exact (K.binaryNormIdealCoordinates x).prop⟩
  invFun z := K.binaryNormIdealCoordinates.symm
    ⟨K.binaryCoefficientOrderEquivDiscriminantOrder.symm z.val, z.prop⟩
  left_inv x := by simp
  right_inv z := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    change K.binaryCoefficientOrderEquivDiscriminantOrder (K.binaryNormIdealCoordinates (r • x)).val =
      r • K.binaryCoefficientOrderEquivDiscriminantOrder (K.binaryNormIdealCoordinates x).val
    rw [map_smul]
    exact K.binaryCoefficientOrderEquivDiscriminantOrder.toLinearEquiv.map_smul r _

/-- Transport to the common order keeps the literal norm scale A Q. -/
theorem norm_binaryDiscriminantNormIdealCoordinates (K : PositiveDefiniteIntegralLattice 2) (x : Fin 2 → ℤ) :
    (K.binaryDiscriminantNormIdealCoordinates x).val.norm =
      (K.pairingMatrix 0 0 / (K.binaryContent : ℤ)) * K.binaryPrimitivePolynomial x := by
  change (K.binaryCoefficientOrderEquivDiscriminantOrder (K.binaryNormIdealCoordinates x).val).norm = _
  rw [norm_binaryCoefficientOrderEquivDiscriminantOrder, norm_binaryNormIdealCoordinates]

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.coefficientOrderEquivOfShift
#assert_standard_axioms BinaryNormIdeal.norm_coefficientOrderEquivOfShift
#assert_standard_axioms BinaryNormIdeal.coefficientOrderEquivOfDiscriminant
#assert_standard_axioms BinaryNormIdeal.norm_coefficientOrderEquivOfDiscriminant
#assert_standard_axioms BinaryNormIdeal.DiscriminantOrder
#assert_standard_axioms BinaryNormIdeal.discriminantOrder_coefficients
#assert_standard_axioms BinaryNormIdeal.coefficientOrderEquivDiscriminantOrder
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryCoefficientOrderEquivDiscriminantOrder
#assert_standard_axioms PositiveDefiniteIntegralLattice.norm_binaryCoefficientOrderEquivDiscriminantOrder
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDiscriminantNormIdeal
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDiscriminantNormIdealCoordinates
#assert_standard_axioms PositiveDefiniteIntegralLattice.norm_binaryDiscriminantNormIdealCoordinates
