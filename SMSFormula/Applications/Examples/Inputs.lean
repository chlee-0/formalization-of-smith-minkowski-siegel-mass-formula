import SMSFormula.IntegralQuadraticFormBridge

/-!
# Concrete inputs for the three worked examples

These declarations fix the input forms and the `Q`/`2Q` crosswalk. They do not
assert numerical genus masses. The second example has two proposed genus
representatives, not two separate examples.
-/

open Matrix

noncomputable section

namespace MassFormulaReleaseExamples

def a2Polar : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 2]

def ternaryOnePolar : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, 0, 0; 0, 4, 0; 0, 0, 22]

def ternaryTwoPolar : Matrix (Fin 3) (Fin 3) ℤ :=
  !![4, 0, 0; 0, 6, 2; 0, 2, 8]

def a4Polar : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2]

theorem a2Polar_posDef : (a2Polar.map (Int.cast : ℤ → ℝ)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [a2Polar]
  · intro x hx
    simp only [star_trivial]
    have h0 := sq_nonneg (x 0)
    have h1 := sq_nonneg (x 1)
    have h01 := sq_nonneg (x 0 + x 1)
    have hp : 0 < x 0 ^ 2 ∨ 0 < x 1 ^ 2 := by
      by_contra h
      push Not at h
      apply hx
      ext i
      fin_cases i <;> simp <;> nlinarith
    simp [a2Polar, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    rcases hp with hp | hp <;> nlinarith

theorem ternaryOnePolar_posDef :
    (ternaryOnePolar.map (Int.cast : ℤ → ℝ)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [ternaryOnePolar]
  · intro x hx
    simp only [star_trivial]
    have h0 := sq_nonneg (x 0)
    have h1 := sq_nonneg (x 1)
    have h2 := sq_nonneg (x 2)
    have hp : 0 < x 0 ^ 2 ∨ 0 < x 1 ^ 2 ∨ 0 < x 2 ^ 2 := by
      by_contra h
      push Not at h
      apply hx
      ext i
      fin_cases i <;> simp <;> nlinarith
    simp [ternaryOnePolar, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    rcases hp with hp | hp | hp <;> nlinarith

theorem ternaryTwoPolar_posDef :
    (ternaryTwoPolar.map (Int.cast : ℤ → ℝ)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [ternaryTwoPolar]
  · intro x hx
    simp only [star_trivial]
    have h0 := sq_nonneg (x 0)
    have h1 := sq_nonneg (x 1)
    have h2 := sq_nonneg (x 2)
    have h12 := sq_nonneg (x 1 + x 2)
    have hp : 0 < x 0 ^ 2 ∨ 0 < x 1 ^ 2 ∨ 0 < x 2 ^ 2 := by
      by_contra h
      push Not at h
      apply hx
      ext i
      fin_cases i <;> simp <;> nlinarith
    simp [ternaryTwoPolar, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    rcases hp with hp | hp | hp <;> nlinarith

theorem a4Polar_posDef : (a4Polar.map (Int.cast : ℤ → ℝ)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [a4Polar]
  · intro x hx
    simp only [star_trivial]
    have h0 := sq_nonneg (x 0)
    have h01 := sq_nonneg (x 0 - x 1)
    have h12 := sq_nonneg (x 1 - x 2)
    have h23 := sq_nonneg (x 2 - x 3)
    have h3 := sq_nonneg (x 3)
    simp [a4Polar, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    by_contra h
    push Not at h
    have hx0 : x 0 = 0 := by nlinarith
    have hx1 : x 1 = 0 := by nlinarith
    have hx2 : x 2 = 0 := by nlinarith
    have hx3 : x 3 = 0 := by nlinarith
    apply hx
    ext i
    fin_cases i <;> simp [hx0, hx1, hx2, hx3]

def a2 : PositiveDefiniteIntegralQuadraticForm 2 where
  polarGramMatrix := a2Polar
  polarGram_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [a2Polar]
  polarGram_even_diag := by intro i; fin_cases i <;> norm_num [a2Polar]
  polarGram_posDef := a2Polar_posDef

def ternaryOne : PositiveDefiniteIntegralQuadraticForm 3 where
  polarGramMatrix := ternaryOnePolar
  polarGram_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [ternaryOnePolar]
  polarGram_even_diag := by
    intro i
    fin_cases i
    · exact ⟨1, by norm_num [ternaryOnePolar]⟩
    · exact ⟨2, by norm_num [ternaryOnePolar]⟩
    · exact ⟨11, by norm_num [ternaryOnePolar]⟩
  polarGram_posDef := ternaryOnePolar_posDef

def ternaryTwo : PositiveDefiniteIntegralQuadraticForm 3 where
  polarGramMatrix := ternaryTwoPolar
  polarGram_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [ternaryTwoPolar]
  polarGram_even_diag := by
    intro i
    fin_cases i
    · exact ⟨2, by norm_num [ternaryTwoPolar]⟩
    · exact ⟨3, by norm_num [ternaryTwoPolar]⟩
    · exact ⟨4, by norm_num [ternaryTwoPolar]⟩
  polarGram_posDef := ternaryTwoPolar_posDef

def a4 : PositiveDefiniteIntegralQuadraticForm 4 where
  polarGramMatrix := a4Polar
  polarGram_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [a4Polar]
  polarGram_even_diag := by intro i; fin_cases i <;> norm_num [a4Polar]
  polarGram_posDef := a4Polar_posDef

theorem a2_quadForm (x y : ℤ) : a2.quadForm ![x, y] = x^2 + x*y + y^2 := by
  have h := a2.two_mul_quadForm_eq_polarGram ![x, y]
  norm_num [a2, a2Polar, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h ⊢
  nlinarith

theorem ternaryOne_quadForm (x y z : ℤ) :
    ternaryOne.quadForm ![x, y, z] = x^2 + 2*y^2 + 11*z^2 := by
  have h := ternaryOne.two_mul_quadForm_eq_polarGram ![x, y, z]
  norm_num [ternaryOne, ternaryOnePolar, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at h ⊢
  nlinarith

theorem ternaryTwo_quadForm (x y z : ℤ) :
    ternaryTwo.quadForm ![x, y, z] = 2*x^2 + 3*y^2 + 4*z^2 + 2*y*z := by
  have h := ternaryTwo.two_mul_quadForm_eq_polarGram ![x, y, z]
  norm_num [ternaryTwo, ternaryTwoPolar, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at h ⊢
  nlinarith

theorem a4_quadForm (w x y z : ℤ) :
    a4.quadForm ![w, x, y, z] = w^2 + x^2 + y^2 + z^2 - w*x - x*y - y*z := by
  have h := a4.two_mul_quadForm_eq_polarGram ![w, x, y, z]
  norm_num [a4, a4Polar, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h ⊢
  nlinarith

theorem a2_quadraticMatrix_offDiagonal : a2.quadraticMatrix 0 1 = (1/2 : ℚ) := by
  norm_num [a2, a2Polar, PositiveDefiniteIntegralQuadraticForm.quadraticMatrix]

theorem a4_quadraticMatrix_offDiagonal : a4.quadraticMatrix 0 1 = -(1/2 : ℚ) := by
  norm_num [a4, a4Polar, PositiveDefiniteIntegralQuadraticForm.quadraticMatrix]

theorem a2_latticeOfPolarForm_quadForm (x y : ℤ) :
    a2.latticeOfPolarForm.quadForm ![x, y] = 2 * (x^2 + x*y + y^2) := by
  rw [PositiveDefiniteIntegralQuadraticForm.latticeOfPolarForm_quadForm, a2_quadForm]

theorem a4_latticeOfPolarForm_quadForm (w x y z : ℤ) :
    a4.latticeOfPolarForm.quadForm ![w, x, y, z] =
      2 * (w^2 + x^2 + y^2 + z^2 - w*x - x*y - y*z) := by
  rw [PositiveDefiniteIntegralQuadraticForm.latticeOfPolarForm_quadForm, a4_quadForm]

theorem a2_polarDeterminant : a2.polarDeterminant = 3 := by decide

theorem ternaryOne_polarDeterminant : ternaryOne.polarDeterminant = 176 := by decide

theorem ternaryTwo_polarDeterminant : ternaryTwo.polarDeterminant = 176 := by decide

theorem a4_polarDeterminant : a4.polarDeterminant = 5 := by decide

theorem a2_quadraticDeterminant : a2.quadraticDeterminant = (3/4 : ℚ) := by
  have h := a2.polarDeterminant_cast_eq_two_pow_mul_quadraticDeterminant
  rw [a2_polarDeterminant] at h
  norm_num at h
  linarith

theorem ternaryOne_quadraticDeterminant : ternaryOne.quadraticDeterminant = 22 := by
  have h := ternaryOne.polarDeterminant_cast_eq_two_pow_mul_quadraticDeterminant
  rw [ternaryOne_polarDeterminant] at h
  norm_num at h
  linarith

theorem ternaryTwo_quadraticDeterminant : ternaryTwo.quadraticDeterminant = 22 := by
  have h := ternaryTwo.polarDeterminant_cast_eq_two_pow_mul_quadraticDeterminant
  rw [ternaryTwo_polarDeterminant] at h
  norm_num at h
  linarith

theorem a4_quadraticDeterminant : a4.quadraticDeterminant = (5/16 : ℚ) := by
  have h := a4.polarDeterminant_cast_eq_two_pow_mul_quadraticDeterminant
  rw [a4_polarDeterminant] at h
  norm_num at h
  linarith

/-- The second example also has an integral `F`, so it can use the
ordinary-genus-mass API directly without replacing `Q1` by `2Q1`. -/
def ternaryLattice : PositiveDefiniteIntegralLattice 3 where
  pairingMatrix := !![1, 0, 0; 0, 2, 0; 0, 0, 11]
  form_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  form_posDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    · intro x hx
      have h := ternaryOnePolar_posDef.dotProduct_mulVec_pos hx
      simp [ternaryOnePolar, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h ⊢
      nlinarith

theorem ternaryLattice_quadForm (x y z : ℤ) :
    ternaryLattice.quadForm ![x, y, z] = x^2 + 2*y^2 + 11*z^2 := by
  rw [PositiveDefiniteIntegralLattice.quadForm_eq_dotProduct]
  simp [ternaryLattice, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem ternaryLattice_pairingDeterminant : ternaryLattice.pairingDeterminant = 22 := by
  decide

theorem ternaryLattice_polarDeterminant : ternaryLattice.polarDeterminant = 176 := by
  decide

end MassFormulaReleaseExamples
