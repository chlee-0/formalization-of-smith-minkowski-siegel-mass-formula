import SMSFormula.BinaryLocalPrimitive

/-!
# Primitive binary discriminants and integral reconstruction

The discriminant belongs to the primitive norm polynomial, not to the polar
Gram matrix. Its exact scale is g² D = -4 det(F). The original lattice model
requires an even scaled mixed coefficient; it does not require B itself even.
-/

open Matrix

namespace PositiveDefiniteIntegralLattice

/-- Discriminant of the content-divided binary norm polynomial. -/
def binaryPrimitiveDiscriminant (K : PositiveDefiniteIntegralLattice 2) : ℤ :=
  ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ)) ^ 2 -
    4 * (K.pairingMatrix 0 0 / (K.binaryContent : ℤ)) *
      (K.pairingMatrix 1 1 / (K.binaryContent : ℤ))

/-- The primitive discriminant has the exact quadratic-matrix normalization. -/
theorem binaryContent_sq_mul_binaryPrimitiveDiscriminant (K : PositiveDefiniteIntegralLattice 2) :
    (K.binaryContent : ℤ) ^ 2 * K.binaryPrimitiveDiscriminant =
      -4 * K.pairingDeterminant := by
  have hd := (dvd_binaryContent_iff K K.binaryContent).mp (dvd_refl _)
  have ha := Int.mul_ediv_cancel' hd.1
  have hb := Int.mul_ediv_cancel' hd.2.1
  have hc := Int.mul_ediv_cancel' hd.2.2
  unfold binaryPrimitiveDiscriminant pairingDeterminant
  rw [Matrix.det_fin_two, K.form_symm.apply 0 1]
  calc
    _ = ((K.binaryContent : ℤ) * ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ))) ^ 2 -
        4 * ((K.binaryContent : ℤ) * (K.pairingMatrix 0 0 / (K.binaryContent : ℤ))) *
          ((K.binaryContent : ℤ) * (K.pairingMatrix 1 1 / (K.binaryContent : ℤ))) := by ring
    _ = _ := by rw [ha, hb, hc]; ring

theorem binaryPrimitiveDiscriminant_neg (K : PositiveDefiniteIntegralLattice 2) :
    K.binaryPrimitiveDiscriminant < 0 := by
  have hg : (0 : ℤ) < K.binaryContent := by exact_mod_cast K.binaryContent_pos
  have hdet := K.pairingDeterminant_pos
  have heq := K.binaryContent_sq_mul_binaryPrimitiveDiscriminant
  have hs : (0 : ℤ) < (K.binaryContent : ℤ) ^ 2 := sq_pos_of_pos hg
  nlinarith

private lemma sq_emod_four (b : ℤ) : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
  have hb : 0 ≤ b % 4 ∧ b % 4 < 4 := ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  have hcases : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  rcases hcases with h | h | h | h <;>
    rw [pow_two, Int.mul_emod, h] <;> norm_num

/-- The primitive polynomial has a quadratic-order discriminant residue. -/
theorem binaryPrimitiveDiscriminant_mod_four (K : PositiveDefiniteIntegralLattice 2) :
    K.binaryPrimitiveDiscriminant % 4 = 0 ∨ K.binaryPrimitiveDiscriminant % 4 = 1 := by
  simpa [binaryPrimitiveDiscriminant, Int.sub_emod, Int.mul_emod] using
    sq_emod_four ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ))

/-- Actual genus equality fixes the primitive discriminant, with no conductor restriction. -/
theorem IsSameGenus.binaryPrimitiveDiscriminant_eq {K L : PositiveDefiniteIntegralLattice 2}
    (h : K.IsSameGenus L) : K.binaryPrimitiveDiscriminant = L.binaryPrimitiveDiscriminant := by
  have hK := K.binaryContent_sq_mul_binaryPrimitiveDiscriminant
  have hL := L.binaryContent_sq_mul_binaryPrimitiveDiscriminant
  rw [← h.binaryContent_eq, ← pairingDeterminant_eq_of_isSameGenus K L h] at hL
  have hgne : (K.binaryContent : ℤ) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (ne_of_gt K.binaryContent_pos))
  exact mul_left_cancel₀ hgne (hK.trans hL.symm)

/-- The leading coefficient is positive after content division. -/
lemma binaryPrimitivePolynomial_leading_pos (K : PositiveDefiniteIntegralLattice 2) :
    0 < K.pairingMatrix 0 0 / (K.binaryContent : ℤ) := by
  simpa [binaryPrimitivePolynomial_apply] using
    K.binaryPrimitivePolynomial_posDef ![1, 0] (by decide)

/-- Matching the original scaled discriminant forces the required integral
mixed entry. This permits an odd primitive mixed coefficient when g is even. -/
lemma binary_scaled_mixed_even_of_discriminant (K : PositiveDefiniteIntegralLattice 2)
    (a b c : ℤ) (hD : b ^ 2 - 4 * a * c = K.binaryPrimitiveDiscriminant) :
    2 ∣ (K.binaryContent : ℤ) * b := by
  have heq := K.binaryContent_sq_mul_binaryPrimitiveDiscriminant
  rw [← hD] at heq
  have hsq : ((K.binaryContent : ℤ) * b) ^ 2 =
      4 * ((K.binaryContent : ℤ) ^ 2 * a * c - K.pairingDeterminant) := by
    linear_combination heq
  have hm : (((K.binaryContent : ℤ) * b) ^ 2) % 4 = 0 := by rw [hsq]; omega
  simp only [pow_two] at hm
  have hrem : ((K.binaryContent : ℤ) * b) % 2 = 0 := by
    have hpow := Int.mul_emod ((K.binaryContent : ℤ) * b) ((K.binaryContent : ℤ) * b) 4
    have hcases : ((K.binaryContent : ℤ) * b) % 4 = 0 ∨
        ((K.binaryContent : ℤ) * b) % 4 = 1 ∨
        ((K.binaryContent : ℤ) * b) % 4 = 2 ∨
        ((K.binaryContent : ℤ) * b) % 4 = 3 := by omega
    rcases hcases with h | h | h | h <;> norm_num [h] at hpow <;> omega
  exact Int.dvd_of_emod_eq_zero hrem

/-- The symmetric integral matrix reconstructed from a scaled norm polynomial.
Integrality uses 2 ∣ gB, rather than requiring B even or dividing F by g. -/
def binaryReconstructionMatrix (g : ℕ) (a b c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(g : ℤ) * a, (g : ℤ) * b / 2; (g : ℤ) * b / 2, (g : ℤ) * c]

lemma binaryReconstructionMatrix_isSymm (g : ℕ) (a b c : ℤ) :
    (binaryReconstructionMatrix g a b c).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The reconstructed matrix has precisely the requested scaled norm. -/
lemma binaryReconstructionMatrix_norm (g : ℕ) (a b c : ℤ)
    (heven : (2 : ℤ) ∣ (g : ℤ) * b)
    {R : Type*} [CommRing R] (x : Fin 2 → R) :
    dotProduct x (((binaryReconstructionMatrix g a b c).map (Int.cast : ℤ → R)).mulVec x) =
      (g : R) * ((a : R) * x 0 ^ 2 + (b : R) * x 0 * x 1 + (c : R) * x 1 ^ 2) := by
  have hs : ((binaryReconstructionMatrix g a b c).map (Int.cast : ℤ → R)).IsSymm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  apply Matrix.dotProduct_mulVec_fin_two_eq_scalar_polynomial _ hs
  · simp [binaryReconstructionMatrix]
  · have h := congrArg (Int.castRingHom R) (Int.mul_ediv_cancel' heven)
    simpa [binaryReconstructionMatrix] using h
  · simp [binaryReconstructionMatrix]

private lemma real_binary_polynomial_pos (a b c : ℝ) (ha : 0 < a)
    (hD : b ^ 2 - 4 * a * c < 0) (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    0 < a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2 := by
  by_cases hy : x 1 = 0
  · have hxn : x 0 ≠ 0 := by
      intro h
      apply hx
      ext i
      fin_cases i <;> simp [h, hy]
    simpa [hy] using mul_pos ha (sq_pos_of_ne_zero hxn)
  · have hterm : 0 < (4 * a * c - b ^ 2) * x 1 ^ 2 :=
      mul_pos (by linarith) (sq_pos_of_ne_zero hy)
    have hid : 4 * a * (a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) =
        (2 * a * x 0 + b * x 1) ^ 2 + (4 * a * c - b ^ 2) * x 1 ^ 2 := by ring
    have hp : 0 < 4 * a * (a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) := by
      rw [hid]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) hterm
    exact (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < 4 * a)).mp hp

/-- Every positive binary polynomial with an integral scaled mixed entry gives
an actual lattice in the original symmetric integral-matrix model. -/
def binaryLatticeOfCoefficients (g : ℕ) (hg : 0 < g) (a b c : ℤ)
    (ha : 0 < a) (hD : b ^ 2 - 4 * a * c < 0)
    (heven : (2 : ℤ) ∣ (g : ℤ) * b) : PositiveDefiniteIntegralLattice 2 where
  pairingMatrix := binaryReconstructionMatrix g a b c
  form_symm := binaryReconstructionMatrix_isSymm g a b c
  form_posDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [binaryReconstructionMatrix]
    · intro x hx
      simp only [star_trivial]
      rw [binaryReconstructionMatrix_norm g a b c heven]
      exact mul_pos (by exact_mod_cast hg)
        (real_binary_polynomial_pos a b c (by exact_mod_cast ha) (by exact_mod_cast hD) x hx)

/-- Primitive coefficient gcd makes the reconstructed lattice's actual content g. -/
theorem binaryLatticeOfCoefficients_content (g : ℕ) (hg : 0 < g) (a b c : ℤ)
    (ha : 0 < a) (hD : b ^ 2 - 4 * a * c < 0)
    (heven : (2 : ℤ) ∣ (g : ℤ) * b) (hprim : Int.gcd a (Int.gcd b c : ℤ) = 1) :
    (binaryLatticeOfCoefficients g hg a b c ha hD heven).binaryContent = g := by
  have hb := Int.mul_ediv_cancel' heven
  change Int.gcd ((g : ℤ) * a) (Int.gcd (2 * ((g : ℤ) * b / 2)) ((g : ℤ) * c) : ℤ) = g
  rw [hb, Int.gcd_mul_left]
  simp only [Int.natAbs_natCast, Nat.cast_mul]
  rw [Int.gcd_mul_left, hprim]
  simp

/-- The primitive polynomial of the reconstructed lattice has the exact
three original coefficients, on the same integer coordinate carrier. -/
theorem binaryLatticeOfCoefficients_primitive_apply (g : ℕ) (hg : 0 < g) (a b c : ℤ)
    (ha : 0 < a) (hD : b ^ 2 - 4 * a * c < 0)
    (heven : (2 : ℤ) ∣ (g : ℤ) * b) (hprim : Int.gcd a (Int.gcd b c : ℤ) = 1)
    (x : Fin 2 → ℤ) :
    (binaryLatticeOfCoefficients g hg a b c ha hD heven).binaryPrimitivePolynomial x =
      a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2 := by
  have hgne : (g : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hg)
  have hn := binaryReconstructionMatrix_norm g a b c heven (R := ℤ) x
  have hq := quadForm_eq_binaryContent_mul_binaryPrimitivePolynomial
    (binaryLatticeOfCoefficients g hg a b c ha hD heven) x
  rw [quadForm_eq_dotProduct, binaryLatticeOfCoefficients_content g hg a b c ha hD heven hprim] at hq
  have hn' : dotProduct x ((binaryReconstructionMatrix g a b c).mulVec x) =
      (g : ℤ) * (a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) := by simpa using hn
  exact mul_left_cancel₀ hgne (hq.symm.trans hn')

/-- Reconstruction recovers all three divided coefficients exactly. -/
theorem binaryLatticeOfCoefficients_coefficients (g : ℕ) (hg : 0 < g) (a b c : ℤ)
    (ha : 0 < a) (hD : b ^ 2 - 4 * a * c < 0)
    (heven : (2 : ℤ) ∣ (g : ℤ) * b) (hprim : Int.gcd a (Int.gcd b c : ℤ) = 1) :
    let L := binaryLatticeOfCoefficients g hg a b c ha hD heven
    L.pairingMatrix 0 0 / (L.binaryContent : ℤ) = a ∧
      (2 * L.pairingMatrix 0 1) / (L.binaryContent : ℤ) = b ∧
      L.pairingMatrix 1 1 / (L.binaryContent : ℤ) = c := by
  dsimp only
  rw [binaryLatticeOfCoefficients_content g hg a b c ha hD heven hprim]
  have hgne : (g : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hg)
  change ((g : ℤ) * a) / (g : ℤ) = a ∧
    (2 * ((g : ℤ) * b / 2)) / (g : ℤ) = b ∧ ((g : ℤ) * c) / (g : ℤ) = c
  rw [Int.mul_ediv_cancel' heven]
  simp [Int.mul_ediv_cancel_left _ hgne]

/-- Reconstruction preserves the requested primitive discriminant. -/
theorem binaryLatticeOfCoefficients_discriminant (g : ℕ) (hg : 0 < g) (a b c : ℤ)
    (ha : 0 < a) (hD : b ^ 2 - 4 * a * c < 0)
    (heven : (2 : ℤ) ∣ (g : ℤ) * b) (hprim : Int.gcd a (Int.gcd b c : ℤ) = 1) :
    (binaryLatticeOfCoefficients g hg a b c ha hD heven).binaryPrimitiveDiscriminant =
      b ^ 2 - 4 * a * c := by
  obtain ⟨hA, hB, hC⟩ := binaryLatticeOfCoefficients_coefficients g hg a b c ha hD heven hprim
  unfold binaryPrimitiveDiscriminant
  rw [hA, hB, hC]

/-- Every primitive positive binary polynomial with the same discriminant is
realized at the original content. No parity hypothesis is left to the caller.
Discriminant equality alone does not assert membership in the original genus. -/
theorem exists_binaryLattice_of_primitive_discriminant (K : PositiveDefiniteIntegralLattice 2)
    (a b c : ℤ) (ha : 0 < a) (hD : b ^ 2 - 4 * a * c = K.binaryPrimitiveDiscriminant)
    (hprim : Int.gcd a (Int.gcd b c : ℤ) = 1) :
    ∃ L : PositiveDefiniteIntegralLattice 2, L.binaryContent = K.binaryContent ∧
      L.binaryPrimitiveDiscriminant = K.binaryPrimitiveDiscriminant ∧
      ∀ x : Fin 2 → ℤ, L.binaryPrimitivePolynomial x =
        a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2 := by
  have hneg : b ^ 2 - 4 * a * c < 0 := by rw [hD]; exact K.binaryPrimitiveDiscriminant_neg
  have heven := binary_scaled_mixed_even_of_discriminant K a b c hD
  refine ⟨binaryLatticeOfCoefficients K.binaryContent K.binaryContent_pos a b c ha hneg heven,
    binaryLatticeOfCoefficients_content _ _ _ _ _ _ _ _ hprim, ?_,
    binaryLatticeOfCoefficients_primitive_apply _ _ _ _ _ _ _ _ hprim⟩
  exact (binaryLatticeOfCoefficients_discriminant _ _ _ _ _ _ _ _ hprim).trans hD

/-- Starting from an actual lattice, reconstruction recovers its original
matrix on the same coordinates, not merely an isometry class. -/
theorem binaryReconstructionMatrix_of_lattice (K : PositiveDefiniteIntegralLattice 2) :
    binaryReconstructionMatrix K.binaryContent
      (K.pairingMatrix 0 0 / (K.binaryContent : ℤ))
      ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ))
      (K.pairingMatrix 1 1 / (K.binaryContent : ℤ)) = K.pairingMatrix := by
  have hd := (dvd_binaryContent_iff K K.binaryContent).mp (dvd_refl _)
  have ha := Int.mul_ediv_cancel' hd.1
  have hb := Int.mul_ediv_cancel' hd.2.1
  have hc := Int.mul_ediv_cancel' hd.2.2
  ext i j
  fin_cases i <;> fin_cases j
  · exact ha
  · change (K.binaryContent : ℤ) * ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ)) / 2 = _
    rw [hb, Int.mul_ediv_cancel_left _ (by decide : (2 : ℤ) ≠ 0)]
    rfl
  · change (K.binaryContent : ℤ) * ((2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ)) / 2 = _
    rw [hb, Int.mul_ediv_cancel_left _ (by decide : (2 : ℤ) ≠ 0)]
    exact (K.form_symm.apply 0 1).symm
  · exact hc

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitiveDiscriminant
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryContent_sq_mul_binaryPrimitiveDiscriminant
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitiveDiscriminant_neg
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitiveDiscriminant_mod_four
#assert_standard_axioms PositiveDefiniteIntegralLattice.IsSameGenus.binaryPrimitiveDiscriminant_eq
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePolynomial_leading_pos
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_scaled_mixed_even_of_discriminant
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryReconstructionMatrix
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryReconstructionMatrix_isSymm
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryReconstructionMatrix_norm
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLatticeOfCoefficients
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLatticeOfCoefficients_content
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLatticeOfCoefficients_primitive_apply
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLatticeOfCoefficients_coefficients
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLatticeOfCoefficients_discriminant
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryLattice_of_primitive_discriminant
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryReconstructionMatrix_of_lattice
