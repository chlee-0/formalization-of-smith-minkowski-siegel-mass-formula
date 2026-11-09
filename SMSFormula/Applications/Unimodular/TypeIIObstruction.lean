import SMSFormula.Applications.Unimodular.Gram
import SMSFormula.RationalAdeleVectorComplexGaussianTheta
import SMSFormula.StandardAxiomsGuard

/-!
# Gaussian-theta connectors for the Type II rank obstruction

This file continues the Gaussian-theta route:
it specializes the existing finite-dimensional complex Gaussian theta theorem to
classically unimodular integral lattices by reindexing the inverse theta series
through the stored determinant-one form matrix.

The final scalar endgame, which extracts `8 ∣ n` from the resulting
`(1 + i)` comparison for Type II lattices, is intentionally left to subsequent
lemmas.  The statements here introduce no mass-formula or classification
assumption.
-/

noncomputable section

open Matrix BigOperators

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A classically unimodular stored form matrix is invertible over `ℝ` in the
ordinary matrix-inverse sense.  This cancellation form is convenient for the
quadratic-value calculation used in inverse-theta reindexing. -/
theorem real_pairingMatrix_mul_inv_of_isUnimodular
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) :
    (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) *
      (L.pairingMatrix.map (Int.cast : ℤ → ℝ))⁻¹ = 1 := by
  let S : Matrix (Fin n) (Fin n) ℝ := L.pairingMatrix.map (Int.cast : ℤ → ℝ)
  have hdetZ : L.pairingMatrix.det = 1 := by
    simpa [IsUnimodular, pairingDeterminant] using hU
  have hdet : S.det = 1 := by
    calc
      S.det = ((Int.castRingHom ℝ).mapMatrix L.pairingMatrix).det := by rfl
      _ = ((L.pairingMatrix.det : ℤ) : ℝ) := by
          rw [← RingHom.map_det]
          simp
      _ = 1 := by simp [hdetZ]
  exact Matrix.mul_nonsing_inv S (by simp [hdet])

/-- The real cast of the stored form matrix remains symmetric. -/
theorem real_pairingMatrix_isSymm (L : PositiveDefiniteIntegralLattice n) :
    (L.pairingMatrix.map (Int.cast : ℤ → ℝ)).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp [L.form_symm.apply i j]

/-- Integer multiplication by the stored form matrix commutes with casting the
coordinate vector to real coordinates. -/
theorem integerVectorReal_pairingMatrix_mulVec
    (L : PositiveDefiniteIntegralLattice n) (z : Fin n → ℤ) :
    integerVectorReal (L.pairingMatrix.mulVec z) =
      (L.pairingMatrix.map (Int.cast : ℤ → ℝ)).mulVec (integerVectorReal z) := by
  ext i
  simp [integerVectorReal, Matrix.mulVec, dotProduct]

/-- If a symmetric real matrix has a left inverse given by its ordinary inverse,
then the quadratic value after the map `x ↦ Sx` against `S⁻¹` is the original
quadratic value against `S`. -/
theorem dotProduct_mulVec_inv_mulVec_mulVec_eq
    {S : Matrix (Fin n) (Fin n) ℝ}
    (hleft : S * S⁻¹ = 1) (hsymm : S.IsSymm) (x : Fin n → ℝ) :
    S.mulVec x ⬝ᵥ (S⁻¹.mulVec (S.mulVec x)) = x ⬝ᵥ S.mulVec x := by
  calc
    S.mulVec x ⬝ᵥ (S⁻¹.mulVec (S.mulVec x)) =
        ((S.mulVec x) ᵥ* S⁻¹) ⬝ᵥ (S.mulVec x) := by
          rw [Matrix.dotProduct_mulVec]
    _ = ((x ᵥ* S.transpose) ᵥ* S⁻¹) ⬝ᵥ (S.mulVec x) := by
          rw [Matrix.vecMul_transpose]
    _ = (x ᵥ* (S.transpose * S⁻¹)) ⬝ᵥ (S.mulVec x) := by
          simp
    _ = (x ᵥ* (S * S⁻¹)) ⬝ᵥ (S.mulVec x) := by
          have hst : S.transpose = S := hsymm
          rw [hst]
    _ = x ⬝ᵥ S.mulVec x := by
          rw [hleft]
          simp

/-- Pointwise reindexing of the inverse Gaussian summand by the determinant-one
stored form matrix. -/
theorem shiftedMatrixGaussianSummand_pairingMatrix_inv_mulVec_eq
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (b : ℂ) (z : Fin n → ℤ) :
    shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))⁻¹ b 0
        (L.pairingMatrix.mulVec z) =
      shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) b 0 z := by
  let S : Matrix (Fin n) (Fin n) ℝ := L.pairingMatrix.map (Int.cast : ℤ → ℝ)
  have hvec := integerVectorReal_pairingMatrix_mulVec L z
  have hquad :
      integerVectorReal (L.pairingMatrix.mulVec z) ⬝ᵥ
          (S⁻¹.mulVec (integerVectorReal (L.pairingMatrix.mulVec z))) =
        integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z) := by
    rw [hvec]
    exact dotProduct_mulVec_inv_mulVec_mulVec_eq (S := S)
      (real_pairingMatrix_mul_inv_of_isUnimodular L hU)
      (real_pairingMatrix_isSymm L) (integerVectorReal z)
  rw [shiftedMatrixGaussianSummand, shiftedMatrixGaussianSummand]
  simp [S, hquad]

/-- The inverse theta series of a classically unimodular stored form matrix
reindexes to the original theta series at the same complex scale. -/
theorem tsum_shiftedMatrixGaussianSummand_pairingMatrix_inv_eq_self
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (b : ℂ) :
    (∑' y : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))⁻¹ b 0 y) =
      ∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) b 0 z := by
  have hdet : L.pairingMatrix.det = 1 := by
    simpa [IsUnimodular, pairingDeterminant] using hU
  let f : (Fin n → ℤ) → ℂ :=
    shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))⁻¹ b 0
  have hreindex := tsum_comp_integerMatrix_mulVec_of_det_eq_one L.pairingMatrix hdet f
  calc
    (∑' y : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))⁻¹ b 0 y) =
        ∑' z : Fin n → ℤ, f (L.pairingMatrix.mulVec z) := by
          simpa [f] using hreindex.symm
    _ = ∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) b 0 z := by
          apply tsum_congr
          intro z
          exact shiftedMatrixGaussianSummand_pairingMatrix_inv_mulVec_eq L hU b z


/-- Complex exponential periodicity in the form used by Type II parity: the
negative integral `2πi` phase is trivial. -/
theorem exp_neg_two_pi_I_intCast (m : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ))) = 1 := by
  rw [Complex.exp_eq_one_iff]
  exact ⟨-m, by
    norm_num
    ring⟩

/-- If an integer quadratic value is even, then the extra `(1+i)` imaginary
phase is trivial. -/
theorem exp_neg_pi_mul_one_add_I_int_of_even {q : ℤ} (hq : Even q) :
    Complex.exp (-Real.pi * (1 + Complex.I) * (q : ℂ)) =
      Complex.exp (-Real.pi * (q : ℂ)) := by
  rcases hq with ⟨m, hm⟩
  rw [hm]
  rw [show -Real.pi * (1 + Complex.I) * (((m + m : ℤ) : ℂ)) =
      -Real.pi * (((m + m : ℤ) : ℂ)) + -(2 * Real.pi * Complex.I * (m : ℂ)) by
    push_cast
    ring_nf]
  rw [Complex.exp_add, exp_neg_two_pi_I_intCast]
  simp

/-- Type II parity identifies the `(1+i)` Gaussian summand with the real
positive Gaussian summand at scale `1`. -/
theorem shiftedMatrixGaussianSummand_one_add_I_eq_real_of_isTypeII
    (L : PositiveDefiniteIntegralLattice n) (hII : L.HasEvenNorms) (z : Fin n → ℤ) :
    shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
        (1 + Complex.I) 0 z =
      shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
        1 0 z := by
  have hq :
      integerVectorReal z ⬝ᵥ
          (L.pairingMatrix.map (Int.cast : ℤ → ℝ)).mulVec (integerVectorReal z) =
        (L.quadForm z : ℝ) := by
    simp [L.quadForm_eq_dotProduct, integerVectorReal, Matrix.mulVec, dotProduct]
  rw [shiftedMatrixGaussianSummand, shiftedMatrixGaussianSummand]
  rw [hq]
  simpa using exp_neg_pi_mul_one_add_I_int_of_even (hII z)

/-- Summed form of `shiftedMatrixGaussianSummand_one_add_I_eq_real_of_isTypeII`. -/
theorem theta_one_add_I_eq_real_of_isTypeII
    (L : PositiveDefiniteIntegralLattice n) (hII : L.HasEvenNorms) :
    (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
          (1 + Complex.I) 0 z) =
      ∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
          1 0 z := by
  apply tsum_congr
  intro z
  exact shiftedMatrixGaussianSummand_one_add_I_eq_real_of_isTypeII L hII z

/-- The sine term in `exp (π i m)` vanishes for integral `m`. -/
theorem complex_sin_pi_intCast (m : ℤ) :
    Complex.sin (Real.pi * (m : ℂ)) = 0 := by
  rw [← Complex.ofReal_intCast m]
  rw [← Complex.ofReal_mul]
  rw [show Real.pi * (m : ℝ) = (m : ℝ) * Real.pi by ring]
  rw [← Complex.ofReal_sin]
  simp [Real.sin_int_mul_pi]

/-- The cosine term in `exp (π i m)` is real for integral `m`. -/
theorem complex_cos_pi_intCast_im_zero (m : ℤ) :
    (Complex.cos (Real.pi * (m : ℂ))).im = 0 := by
  rw [show Real.pi * (m : ℂ) = (((m : ℝ) * Real.pi : ℝ) : ℂ) by
    rw [← Complex.ofReal_intCast m]
    rw [show (Real.pi : ℂ) * ((m : ℝ) : ℂ) = (((Real.pi * (m : ℝ) : ℝ)) : ℂ) by
      rw [Complex.ofReal_mul]]
    congr 1
    ring]
  rw [← Complex.ofReal_cos]
  exact Complex.ofReal_im (Real.cos ((m : ℝ) * Real.pi))

/-- A real exponential has zero imaginary part after embedding into `ℂ`. -/
theorem exp_ofReal_im_zero (x : ℝ) :
    (Complex.exp (x : ℂ)).im = 0 := by
  rw [← Complex.ofReal_exp]
  simp

/-- The phase `exp (π i m)` is real for integral `m`. -/
theorem exp_pi_I_intCast_im_zero (m : ℤ) :
    (Complex.exp (Real.pi * Complex.I * (m : ℂ))).im = 0 := by
  rw [show Real.pi * Complex.I * (m : ℂ) = (Real.pi * (m : ℂ)) * Complex.I by ring]
  rw [Complex.exp_mul_I]
  rw [complex_sin_pi_intCast m]
  simpa using complex_cos_pi_intCast_im_zero m

/-- Type II parity makes each half-scale inverse-theta summand real. -/
theorem shiftedMatrixGaussianSummand_half_one_sub_I_im_eq_zero_of_isTypeII
    (L : PositiveDefiniteIntegralLattice n) (hII : L.HasEvenNorms) (z : Fin n → ℤ) :
    (shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
        ((1 - Complex.I) / 2) 0 z).im = 0 := by
  have hq :
      integerVectorReal z ⬝ᵥ
          (L.pairingMatrix.map (Int.cast : ℤ → ℝ)).mulVec (integerVectorReal z) =
        (L.quadForm z : ℝ) := by
    simp [L.quadForm_eq_dotProduct, integerVectorReal, Matrix.mulVec, dotProduct]
  rcases hII z with ⟨m, hm⟩
  rw [shiftedMatrixGaussianSummand]
  rw [hq, hm]
  simp only [Pi.zero_apply]
  rw [show -Real.pi * ((1 - Complex.I) / 2) * ((((m + m : ℤ) : ℝ) : ℂ)) +
        2 * Real.pi * ∑ i : Fin n, 0 * (z i : ℂ) =
      ((-Real.pi * (m : ℝ) : ℝ) : ℂ) + Real.pi * Complex.I * (m : ℂ) by
    simp
    ring]
  rw [Complex.exp_add]
  rw [Complex.mul_im]
  rw [exp_ofReal_im_zero, exp_pi_I_intCast_im_zero]
  ring

/-- Summed form: the half-scale theta on the right side of the Poisson bridge
has zero imaginary part for Type II lattices. -/
theorem theta_half_one_sub_I_im_eq_zero_of_isTypeII
    (L : PositiveDefiniteIntegralLattice n) (hII : L.HasEvenNorms) :
    (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
          ((1 - Complex.I) / 2) 0 z).im = 0 := by
  let f : (Fin n → ℤ) → ℂ := fun z =>
    shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
      ((1 - Complex.I) / 2) 0 z
  have hzero : pureImaginaryLinear (0 : Fin n → ℝ) = 0 := by
    funext i
    simp [pureImaginaryLinear]
  have hsum : Summable f := by
    have hs := summable_shiftedMatrixGaussianSummand_complex_pureImaginaryLinear
      (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) L.form_posDef
      (b := (1 - Complex.I) / 2) (by norm_num) (0 : Fin n → ℝ)
    simpa [f, hzero] using hs
  have hmap := (Complex.imCLM).map_tsum hsum
  rw [show (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
          ((1 - Complex.I) / 2) 0 z).im =
      ∑' z : Fin n → ℤ, (f z).im by
    simpa [f] using hmap]
  simp [f, shiftedMatrixGaussianSummand_half_one_sub_I_im_eq_zero_of_isTypeII L hII]

/-- Every positive real-width Gaussian summand has positive real part. -/
theorem shiftedMatrixGaussianSummand_one_re_pos
    (L : PositiveDefiniteIntegralLattice n) (z : Fin n → ℤ) :
    0 < (shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
        1 0 z).re := by
  rw [shiftedMatrixGaussianSummand]
  simp only [Pi.zero_apply, MulZeroClass.zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  rw [show -↑Real.pi * 1 * ↑(integerVectorReal z ⬝ᵥ L.pairingMatrix.map Int.cast *ᵥ integerVectorReal z) =
      ((-Real.pi * (integerVectorReal z ⬝ᵥ L.pairingMatrix.map Int.cast *ᵥ integerVectorReal z) : ℝ) : ℂ) by
    simp]
  rw [← Complex.ofReal_exp]
  exact Real.exp_pos _

/-- Every positive real-width Gaussian summand is real. -/
theorem shiftedMatrixGaussianSummand_one_im_eq_zero
    (L : PositiveDefiniteIntegralLattice n) (z : Fin n → ℤ) :
    (shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
        1 0 z).im = 0 := by
  rw [shiftedMatrixGaussianSummand]
  simp only [Pi.zero_apply, MulZeroClass.zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  rw [show -↑Real.pi * 1 * ↑(integerVectorReal z ⬝ᵥ L.pairingMatrix.map Int.cast *ᵥ integerVectorReal z) =
      ((-Real.pi * (integerVectorReal z ⬝ᵥ L.pairingMatrix.map Int.cast *ᵥ integerVectorReal z) : ℝ) : ℂ) by
    simp]
  rw [← Complex.ofReal_exp]
  exact Complex.ofReal_im _

/-- The positive real-width theta sum has positive real part, hence is nonzero. -/
theorem theta_one_re_pos (L : PositiveDefiniteIntegralLattice n) :
    0 < (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
          1 0 z).re := by
  let f : (Fin n → ℤ) → ℂ := fun z =>
    shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) 1 0 z
  have hsum : Summable f := by
    simpa [f] using summable_shiftedMatrixGaussianSummand_zero_fintype
      (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) L.form_posDef (a := 1) (by norm_num)
  have hsumre : Summable (fun z => (f z).re) := by
    simpa using (Complex.reCLM).summable hsum
  rw [show (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
          1 0 z).re = ∑' z : Fin n → ℤ, (f z).re by
    simpa [f] using (Complex.reCLM).map_tsum hsum]
  exact hsumre.tsum_pos
    (fun z => le_of_lt (by simpa [f] using shiftedMatrixGaussianSummand_one_re_pos L z))
    0 (by simpa [f] using shiftedMatrixGaussianSummand_one_re_pos L (0 : Fin n → ℤ))

/-- The positive real-width theta sum has zero imaginary part. -/
theorem theta_one_im_eq_zero (L : PositiveDefiniteIntegralLattice n) :
    (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
          1 0 z).im = 0 := by
  let f : (Fin n → ℤ) → ℂ := fun z =>
    shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) 1 0 z
  have hsum : Summable f := by
    simpa [f] using summable_shiftedMatrixGaussianSummand_zero_fintype
      (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) L.form_posDef (a := 1) (by norm_num)
  have hmap := (Complex.imCLM).map_tsum hsum
  rw [show (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
          1 0 z).im = ∑' z : Fin n → ℤ, (f z).im by
    simpa [f] using hmap]
  simp [f, shiftedMatrixGaussianSummand_one_im_eq_zero L]

/-- The positive real-width theta sum is nonzero. -/
theorem theta_one_ne_zero (L : PositiveDefiniteIntegralLattice n) :
    (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
          1 0 z) ≠ 0 := by
  intro h
  have hpos := theta_one_re_pos L
  rw [h] at hpos
  norm_num at hpos

/-- The `b = 1 + i` theta identity for a classically unimodular lattice, after
reindexing the inverse theta through the integral determinant-one form matrix.
This is the analytic bridge before the Type II scalar endgame. -/
theorem theta_one_add_I_eq_normalization_mul_theta_half_one_sub_I
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) :
    (∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
          (1 + Complex.I) 0 z) =
      complexShiftedMatrixThetaNormalization
          (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) (1 + Complex.I) *
        ∑' z : Fin n → ℤ,
          shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
            ((1 - Complex.I) / 2) 0 z := by
  have htheta := tsum_shiftedMatrixGaussianSummand_complex_zero_eq_inv_one_add_I
    n (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) L.form_posDef
  have hreindex := tsum_shiftedMatrixGaussianSummand_pairingMatrix_inv_eq_self
    L hU ((1 - Complex.I) / 2)
  simpa [hreindex] using htheta

/-- For a Type II classically unimodular lattice, the normalization factor
forced by the `b = 1 + i` theta bridge is real. -/
theorem complexShiftedMatrixThetaNormalization_one_add_I_im_eq_zero_of_isTypeII
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hII : L.HasEvenNorms) :
    (complexShiftedMatrixThetaNormalization
        (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) (1 + Complex.I)).im = 0 := by
  let N : ℂ := complexShiftedMatrixThetaNormalization
        (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) (1 + Complex.I)
  let T : ℂ := ∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ))
          ((1 - Complex.I) / 2) 0 z
  let R : ℂ := ∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand (L.pairingMatrix.map (Int.cast : ℤ → ℝ)) 1 0 z
  have hbridge := theta_one_add_I_eq_normalization_mul_theta_half_one_sub_I L hU
  have hparity := theta_one_add_I_eq_real_of_isTypeII L hII
  have hNT_eq_R : N * T = R := by
    dsimp [N, T, R]
    rw [← hparity]
    exact hbridge.symm
  have hT_im : T.im = 0 := by
    dsimp [T]
    exact theta_half_one_sub_I_im_eq_zero_of_isTypeII L hII
  have hR_im : R.im = 0 := by
    dsimp [R]
    exact theta_one_im_eq_zero L
  have hR_ne : R ≠ 0 := by
    dsimp [R]
    exact theta_one_ne_zero L
  have hT_ne : T ≠ 0 := by
    intro hTzero
    apply hR_ne
    rw [← hNT_eq_R, hTzero, mul_zero]
  have hT_re_ne : T.re ≠ 0 := by
    intro hT_re_zero
    apply hT_ne
    rw [Complex.ext_iff]
    exact ⟨by simpa using hT_re_zero, by simpa using hT_im⟩
  have hmul_im : (N * T).im = 0 := by
    rw [hNT_eq_R, hR_im]
  rw [Complex.mul_im, hT_im, mul_zero, zero_add] at hmul_im
  exact (mul_eq_zero.mp hmul_im).resolve_right hT_re_ne

/-- Algebraic phase extraction: if `(1+i)^m` is real, then `i^m = 1`. -/
theorem complex_I_pow_of_one_add_I_pow_im_zero {m : ℕ}
    (h : ((1 + Complex.I) ^ m).im = 0) :
    Complex.I ^ m = 1 := by
  let z : ℂ := 1 + Complex.I
  have hconj_pow : (starRingEnd ℂ) (z ^ m) = z ^ m := by
    rw [Complex.conj_eq_iff_im]
    simpa [z] using h
  have hzstar : (starRingEnd ℂ) z = 1 - Complex.I := by
    simp [z]
    ring_nf
  have hpow_conj : (1 - Complex.I) ^ m = (1 + Complex.I) ^ m := by
    calc
      (1 - Complex.I) ^ m = ((starRingEnd ℂ) z) ^ m := by
        rw [hzstar]
      _ = (starRingEnd ℂ) (z ^ m) := by
        rw [map_pow]
      _ = z ^ m := hconj_pow
      _ = (1 + Complex.I) ^ m := by rfl
  have hmain : (2 : ℂ) ^ m * Complex.I ^ m = (2 : ℂ) ^ m := by
    calc
      (2 : ℂ) ^ m * Complex.I ^ m = (2 * Complex.I : ℂ) ^ m := by
        rw [mul_pow]
      _ = ((1 + Complex.I) ^ 2) ^ m := by
        congr 1
        norm_num [Complex.ext_iff, pow_two, Complex.I_mul_I]
      _ = (1 + Complex.I) ^ (2 * m) := by
        rw [pow_mul]
      _ = (1 + Complex.I) ^ (m + m) := by
        congr 1
        omega
      _ = (1 + Complex.I) ^ m * (1 + Complex.I) ^ m := by
        rw [pow_add]
      _ = (1 + Complex.I) ^ m * (1 - Complex.I) ^ m := by
        rw [← hpow_conj]
      _ = ((1 + Complex.I) * (1 - Complex.I)) ^ m := by
        rw [mul_pow]
      _ = (2 : ℂ) ^ m := by
        congr 1
        norm_num [Complex.ext_iff, Complex.I_mul_I]
  have htwo : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hmain' : (2 : ℂ) ^ m * Complex.I ^ m = (2 : ℂ) ^ m * 1 := by
    simpa [mul_one] using hmain
  exact mul_left_cancel₀ htwo hmain'

/-- If the inverse of `(1+i)^m` is real, then `(1+i)^m` is real. -/
theorem one_add_I_pow_im_zero_of_inv_im_zero {m : ℕ}
    (h : (((1 + Complex.I) ^ m)⁻¹).im = 0) :
    ((1 + Complex.I) ^ m).im = 0 := by
  rw [Complex.inv_im] at h
  have hnorm_ne : Complex.normSq ((1 + Complex.I) ^ m) ≠ 0 := by
    have hz : (1 + Complex.I : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by
      norm_num [Complex.ext_iff])
    exact (Complex.normSq_pos.mpr hz).ne'
  rw [div_eq_zero_iff] at h
  rcases h with hneg | hnorm
  · exact neg_eq_zero.mp hneg
  · exact False.elim (hnorm_ne hnorm)

/-- The scalar phase extracted from the Type II theta comparison in even rank. -/
theorem complex_I_pow_half_eq_one_of_isTypeII_even
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hII : L.HasEvenNorms)
    (hn : Even n) :
    Complex.I ^ (n / 2) = 1 := by
  rcases hn with ⟨m, hm⟩
  let S : Matrix (Fin n) (Fin n) ℝ := L.pairingMatrix.map (Int.cast : ℤ → ℝ)
  let r : ℂ := (1 + Complex.I) ^ (1 / 2 : ℂ)
  have hdetZ : L.pairingMatrix.det = 1 := by
    simpa [IsUnimodular, pairingDeterminant] using hU
  have hdetS : S.det = 1 := by
    calc
      S.det = ((Int.castRingHom ℝ).mapMatrix L.pairingMatrix).det := by rfl
      _ = ((L.pairingMatrix.det : ℤ) : ℝ) := by
          rw [← RingHom.map_det]
          simp
      _ = 1 := by simp [hdetZ]
  have hNim := complexShiftedMatrixThetaNormalization_one_add_I_im_eq_zero_of_isTypeII L hU hII
  have hInv_rn : ((r ^ n)⁻¹).im = 0 := by
    simpa [complexShiftedMatrixThetaNormalization, S, r, hdetS] using hNim
  have hr2_raw := Complex.cpow_nat_inv_pow (1 + Complex.I) (n := 2) two_ne_zero
  have hr2 : r ^ 2 = 1 + Complex.I := by
    change ((1 + Complex.I) ^ (1 / 2 : ℂ)) ^ 2 = 1 + Complex.I
    convert hr2_raw using 2
    norm_num
  have hrpow : r ^ n = (1 + Complex.I) ^ m := by
    rw [hm]
    calc
      r ^ (m + m) = r ^ m * r ^ m := by rw [pow_add]
      _ = (r * r) ^ m := by rw [mul_pow]
      _ = (r ^ 2) ^ m := by simp [pow_two]
      _ = (1 + Complex.I) ^ m := by rw [hr2]
  have hInv : (((1 + Complex.I) ^ m)⁻¹).im = 0 := by
    rwa [hrpow] at hInv_rn
  have hpow_im : ((1 + Complex.I) ^ m).im = 0 :=
    one_add_I_pow_im_zero_of_inv_im_zero hInv
  have hhalf : n / 2 = m := by omega
  rw [hhalf]
  exact complex_I_pow_of_one_add_I_pow_im_zero hpow_im

/-- General Type II rank obstruction for classically unimodular positive-definite
integral lattices. -/
theorem eight_dvd_rank_of_isUnimodular_isTypeII
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hII : L.HasEvenNorms) :
    8 ∣ n := by
  have hnEven : Even n := by
    rw [← Nat.not_odd_iff_even]
    intro hnOdd
    exact (L.not_hasEvenNorms_of_isUnimodular_odd_rank hnOdd hU) hII
  exact eight_dvd_of_even_complex_I_pow_half_eq_one hnEven
    (complex_I_pow_half_eq_one_of_isTypeII_even L hU hII hnEven)

/-- Negated form of the general Type II rank obstruction. -/
theorem not_hasEvenNorms_of_isUnimodular_not_dvd_eight
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hn : ¬ 8 ∣ n) :
    ¬ L.HasEvenNorms := by
  intro hII
  exact hn (eight_dvd_rank_of_isUnimodular_isTypeII L hU hII)

/-- Outside ranks divisible by eight, every classically unimodular lattice is Type I. -/
theorem hasOddNorm_of_isUnimodular_not_dvd_eight
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hn : ¬ 8 ∣ n) :
    L.HasOddNorm := by
  rw [← L.not_hasEvenNorms_iff_hasOddNorm]
  exact L.not_hasEvenNorms_of_isUnimodular_not_dvd_eight hU hn


#assert_standard_axioms real_pairingMatrix_mul_inv_of_isUnimodular
#assert_standard_axioms real_pairingMatrix_isSymm
#assert_standard_axioms integerVectorReal_pairingMatrix_mulVec
#assert_standard_axioms dotProduct_mulVec_inv_mulVec_mulVec_eq
#assert_standard_axioms shiftedMatrixGaussianSummand_pairingMatrix_inv_mulVec_eq
#assert_standard_axioms tsum_shiftedMatrixGaussianSummand_pairingMatrix_inv_eq_self
#assert_standard_axioms theta_one_add_I_eq_normalization_mul_theta_half_one_sub_I
#assert_standard_axioms exp_neg_two_pi_I_intCast
#assert_standard_axioms exp_neg_pi_mul_one_add_I_int_of_even
#assert_standard_axioms shiftedMatrixGaussianSummand_one_add_I_eq_real_of_isTypeII
#assert_standard_axioms theta_one_add_I_eq_real_of_isTypeII
#assert_standard_axioms complex_sin_pi_intCast
#assert_standard_axioms complex_cos_pi_intCast_im_zero
#assert_standard_axioms exp_ofReal_im_zero
#assert_standard_axioms exp_pi_I_intCast_im_zero
#assert_standard_axioms shiftedMatrixGaussianSummand_half_one_sub_I_im_eq_zero_of_isTypeII
#assert_standard_axioms theta_half_one_sub_I_im_eq_zero_of_isTypeII
#assert_standard_axioms shiftedMatrixGaussianSummand_one_re_pos
#assert_standard_axioms shiftedMatrixGaussianSummand_one_im_eq_zero
#assert_standard_axioms theta_one_re_pos
#assert_standard_axioms theta_one_im_eq_zero
#assert_standard_axioms theta_one_ne_zero
#assert_standard_axioms complexShiftedMatrixThetaNormalization_one_add_I_im_eq_zero_of_isTypeII
#assert_standard_axioms complex_I_pow_of_one_add_I_pow_im_zero
#assert_standard_axioms one_add_I_pow_im_zero_of_inv_im_zero
#assert_standard_axioms complex_I_pow_half_eq_one_of_isTypeII_even
#assert_standard_axioms eight_dvd_rank_of_isUnimodular_isTypeII
#assert_standard_axioms not_hasEvenNorms_of_isUnimodular_not_dvd_eight
#assert_standard_axioms hasOddNorm_of_isUnimodular_not_dvd_eight

end PositiveDefiniteIntegralLattice
