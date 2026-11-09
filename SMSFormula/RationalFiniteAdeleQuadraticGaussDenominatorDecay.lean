import SMSFormula.RationalFiniteAdeleQuadraticGaussAnnihilatorContainment

/-!
# Denominator decay of the finite quadratic Gauss integral

This file takes the real square root of the exact determinant-corrected
annihilator-mass bound.  It first keeps the factor
`gcd(t.den, |polarDeterminant L|)`, then bounds that gcd by the fixed lattice discriminant.
The resulting denominator factor is `(sqrt t.den)⁻ⁿ`, i.e. the required
`t.den ^ (-n/2)` decay, without introducing real powers or local factors.
-/

noncomputable section

open Matrix MeasureTheory RationalQuadraticSpaceMatrix Set

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private theorem sqrt_nat_pow_mul_inv_sqrt_nat_pow_sq
    (a b n : ℕ) :
    ((Real.sqrt (a : ℝ)) ^ n * (Real.sqrt (b : ℝ))⁻¹ ^ n) ^ 2 =
      (((a : ℝ) / (b : ℝ)) ^ n) := by
  rw [← mul_pow]
  change ((Real.sqrt (a : ℝ) / Real.sqrt (b : ℝ)) ^ n) ^ 2 = _
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  congr 1
  rw [div_pow]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

/-- Exact square-root bound retaining the full denominator--discriminant gcd. -/
theorem norm_quadraticGaussIntegral_le_gcd_sqrt_pow_mul_inv_den_sqrt_pow
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t‖ ≤
      (Real.sqrt (Nat.gcd t.den L.polarDeterminant.natAbs : ℝ)) ^ n *
        (Real.sqrt (t.den : ℝ))⁻¹ ^ n := by
  let d := L.polarDeterminant.natAbs
  let g := Nat.gcd t.den d
  let m := L.finiteQuadraticGaussDenominatorDilation t
  have hmpos : 0 < m := Nat.pos_of_ne_zero
    (L.finiteQuadraticGaussDenominatorDilation_ne_zero t)
  have hgm : g * m = t.den := by
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left t.den d)
  have hinv_m : ((m : ℝ)⁻¹) = (g : ℝ) / (t.den : ℝ) := by
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hmpos)
    have hdenR : (t.den : ℝ) ≠ 0 := by exact_mod_cast t.den_nz
    field_simp
    exact_mod_cast (by simpa [mul_comm] using hgm.symm)
  have hsq := L.norm_quadraticGaussIntegral_sq_le_denominatorDilation t
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_natCast] at hsq
  rw [show L.finiteQuadraticGaussDenominatorDilation t = m by rfl,
    hinv_m] at hsq
  have hsq' :
      ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t‖ ^ 2 ≤
        (((g : ℝ) / (t.den : ℝ)) ^ n) := hsq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [sqrt_nat_pow_mul_inv_sqrt_nat_pow_sq]
  exact hsq'

/-- Uniform denominator decay with all bad and dyadic loss contained in the
fixed lattice discriminant. -/
theorem norm_quadraticGaussIntegral_le_polarDeterminant_sqrt_pow_mul_inv_den_sqrt_pow
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t‖ ≤
      (Real.sqrt (L.polarDeterminant.natAbs : ℝ)) ^ n *
        (Real.sqrt (t.den : ℝ))⁻¹ ^ n := by
  calc
    ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t‖ ≤
        (Real.sqrt (Nat.gcd t.den L.polarDeterminant.natAbs : ℝ)) ^ n *
          (Real.sqrt (t.den : ℝ))⁻¹ ^ n :=
      L.norm_quadraticGaussIntegral_le_gcd_sqrt_pow_mul_inv_den_sqrt_pow t
    _ ≤ (Real.sqrt (L.polarDeterminant.natAbs : ℝ)) ^ n *
          (Real.sqrt (t.den : ℝ))⁻¹ ^ n := by
      apply mul_le_mul_of_nonneg_right
      · apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
        · exact Real.sqrt_le_sqrt (by
            exact_mod_cast Nat.gcd_le_right t.den
              (Int.natAbs_pos.mpr (ne_of_gt L.polarDeterminant_pos)))
      · positivity

end PositiveDefiniteIntegralLattice

end
