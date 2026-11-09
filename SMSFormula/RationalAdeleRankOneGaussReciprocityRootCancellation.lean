import SMSFormula.RationalAdeleRankOneWeylBruhatAnalyticReduction
import SMSFormula.RationalFiniteAdeleQuadraticGaussDualQuotient

/-!
# Principal-root cancellation in the nonzero rank-one Bruhat relation

The finite quadratic Gauss reciprocity formula carries the principal factor
`(-t * I)^(1/2)`.  This file proves that this factor cancels exactly against
the two real Gaussian half-powers occurring in the already reduced nonzero
Bruhat relation.  Both signs of the nonzero rational parameter are handled by
checking the principal-argument interval explicitly.

The final theorem is conditional on the one remaining finite Gauss
reciprocity equality.  Thus no finite Gauss value, Weil index, generic Weil
representation, or analytic Bruhat relation is assumed or asserted
unconditionally here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

private theorem cpow_half_mul_of_arg_add_mem
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (harg : x.arg + y.arg ∈ Set.Ioc (-Real.pi) Real.pi) :
    x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) =
      (x * y) ^ (1 / 2 : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero hx,
    Complex.cpow_def_of_ne_zero hy,
    Complex.cpow_def_of_ne_zero (mul_ne_zero hx hy),
    Complex.log_mul hx hy harg, add_mul, Complex.exp_add]

/-- Exact principal-half-power identity for the real factors on the two sides
of the nonzero rational Bruhat relation.  The negative Fourier-kernel sign
appears as the explicit factor `-t * I`. -/
theorem principalHalfPower_bruhat
    {a : ℝ} (ha : 0 < a) {t : ℚ} (ht : t ≠ 0) :
    (Real.sqrt a : ℂ) *
        (((a : ℂ)⁻¹ - (t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) =
      (-(t : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
        ((a : ℂ) + (t⁻¹ : ℂ) * Complex.I) ^ (1 / 2 : ℂ) := by
  let b₁ : ℂ := (a : ℂ)⁻¹ - (t : ℂ) * Complex.I
  let b₂ : ℂ := (a : ℂ) + (t⁻¹ : ℂ) * Complex.I
  let c : ℂ := -(t : ℂ) * Complex.I
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb₁re : 0 < b₁.re := by
    simp [b₁, Complex.inv_re, ha]
  have hb₂re : 0 < b₂.re := by simp [b₂, ha]
  have hb₁ : b₁ ≠ 0 := by
    intro h
    rw [h] at hb₁re
    exact (lt_irrefl 0) hb₁re
  have hb₂ : b₂ ≠ 0 := by
    intro h
    rw [h] at hb₂re
    exact (lt_irrefl 0) hb₂re
  have hc : c ≠ 0 := by
    simp [c, ht]
  have hb₁arg : |b₁.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb₁re)
  have hb₂arg : |b₂.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb₂re)
  have hleftArg : (a : ℂ).arg + b₁.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ha.le]
    rw [Set.mem_Ioc]
    have hb := abs_lt.mp hb₁arg
    constructor <;> linarith [Real.pi_pos]
  have hcarg : c.arg = if 0 < t then -(Real.pi / 2) else Real.pi / 2 := by
    split_ifs with htpos
    · rw [Complex.arg_eq_neg_pi_div_two_iff]
      simp [c, htpos]
    · rw [Complex.arg_eq_pi_div_two_iff]
      have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht
      simp [c, htneg]
  have hrightArg : c.arg + b₂.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [hcarg, Set.mem_Ioc]
    have hb := abs_lt.mp hb₂arg
    split_ifs <;> constructor <;> linarith [Real.pi_pos]
  have hprod : (a : ℂ) * b₁ = c * b₂ := by
    dsimp [b₁, b₂, c]
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    field_simp [haC, ht0]
    ring_nf
    simp [sub_eq_add_neg, add_comm]
  have hsqrt : ((a : ℂ) ^ (1 / 2 : ℂ)) = (Real.sqrt a : ℂ) := by
    simpa using cpow_half_ofReal_mul_eq_sqrt ha
      (show 0 < (1 : ℝ) by norm_num)
  change (Real.sqrt a : ℂ) * b₁ ^ (1 / 2 : ℂ) =
    c ^ (1 / 2 : ℂ) * b₂ ^ (1 / 2 : ℂ)
  rw [← hsqrt]
  rw [cpow_half_mul_of_arg_add_mem haC hb₁ hleftArg]
  rw [hprod]
  exact (cpow_half_mul_of_arg_add_mem hc hb₂ hrightArg).symm

/-- The exact finite Gauss reciprocity factor implies the real--finite product
identity on which the nonzero Bruhat reduction rests. -/
theorem rationalAdeleRankOne_real_finite_identity_of_quadraticGaussReciprocity
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    {t : ℚ} (ht : t ≠ 0)
    (hrec :
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t =
        (L.polarRealDeterminantScale : ℂ) *
          ((-(t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
            (-t⁻¹)) :
    (((L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / (Real.sqrt a : ℂ)) ^ n) *
          polarRealGaussianFourierProduct L
            ((a : ℂ)⁻¹ - (t : ℂ) * Complex.I) 0) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t =
      polarRealGaussianFourierProduct L
          ((a : ℂ) + (t⁻¹ : ℂ) * Complex.I) 0 *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
          (-t⁻¹) := by
  rw [polarRealGaussianFourierProduct_zero,
    polarRealGaussianFourierProduct_zero, hrec]
  have hd : (L.polarRealDeterminantScale : ℂ) ≠ 0 := by
    exact_mod_cast L.polarRealDeterminantScale_ne_zero
  have hsqrt : (Real.sqrt a : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  have hb₁ :
      ((a : ℂ)⁻¹ - (t : ℂ) * Complex.I) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    intro h
    have hpos :
        0 < (((a : ℂ)⁻¹ - (t : ℂ) * Complex.I).re) := by
      simp [Complex.inv_re, ha]
    rw [h] at hpos
    exact (lt_irrefl 0) hpos
  have hcroot :
      (-(t : ℂ) * Complex.I) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    simp [ht]
  have hroot := principalHalfPower_bruhat ha ht
  have hrootDiv :
      ((-(t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) /
          ((Real.sqrt a : ℂ) *
            (((a : ℂ)⁻¹ - (t : ℂ) * Complex.I) ^ (1 / 2 : ℂ))) =
        1 / (((a : ℂ) + (t⁻¹ : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) := by
    rw [hroot]
    rw [div_mul_eq_div_mul_one_div, div_self hcroot]
    simp
  calc
    _ = (L.polarRealDeterminantScale : ℂ)⁻¹ *
          ((((-(t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) /
            ((Real.sqrt a : ℂ) *
              (((a : ℂ)⁻¹ - (t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)))) ^ n) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
            (-t⁻¹) := by
        field_simp [hd, hsqrt, hb₁, hcroot]
        ring
    _ = _ := by rw [hrootDiv]

/-- Conditional closure of the concrete nonzero analytic Bruhat relation.
The only premise not already proved in the repository is the displayed exact
finite quadratic Gauss reciprocity identity. -/
theorem rationalAdeleRankOne_nonzeroBruhatAnalyticRelation_of_quadraticGaussReciprocity
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    {t : ℚ} (ht : t ≠ 0)
    (hrec :
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t =
        (L.polarRealDeterminantScale : ℂ) *
          ((-(t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
            (-t⁻¹)) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator
          (algebraMap ℚ RationalAdele t)
          (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
            (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)))) 0 =
      L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator
        (algebraMap ℚ RationalAdele (-t⁻¹))
        (rationalAdeleRankOneDilationOperator (-t⁻¹)
          (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
            (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator
              (algebraMap ℚ RationalAdele (-t⁻¹))
              (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))))) 0 := by
  rw [rationalAdeleRankOne_nonzeroBruhatAnalyticRelation_iff_real_finite L ha ht]
  exact rationalAdeleRankOne_real_finite_identity_of_quadraticGaussReciprocity
    L ha ht hrec

end RationalQuadraticSpaceMatrix
