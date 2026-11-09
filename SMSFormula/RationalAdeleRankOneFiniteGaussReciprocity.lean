import SMSFormula.RationalAdeleRankOneGaussReciprocityBoundary
import SMSFormula.RationalAdeleRankOneGaussReciprocityRootCancellation

/-!
# Finite quadratic Gauss reciprocity at the rational theta boundary

The right-half-plane matrix-theta identity is evaluated along the rational
boundary studied in `RationalAdeleRankOneGaussReciprocityBoundary`.  Its two
determinant-normalized sides converge to the
standard and polar-dual finite-adelic Gauss integrals.  This file
computes the remaining principal-root ratio and uses uniqueness of limits to
prove the exact reciprocity identity.

No Gauss sum is divided out.  Even denominators and primes dividing the
discriminant remain inside the two finite integrals, and no local
Weil index or generic representation theorem is used.
-/

noncomputable section

open Filter Matrix Topology RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

/-- The scalar left after putting the two determinant-normalized boundary
theta families on the same side of the complex matrix-theta identity. -/
def rationalGaussBoundaryRootFactor (t ρ : ℝ) : ℂ :=
  (Real.sqrt ((ρ ^ 2 + t⁻¹ ^ 2)⁻¹) : ℝ) *
    (rationalGaussBoundaryParameter t ρ) ^ (1 / 2 : ℂ)

private theorem cpow_half_mul_posReal_of_ne_zero
    (b : ℂ) (hb : b ≠ 0) (s : ℝ) (hs : 0 < s) :
    (b * (s : ℂ)) ^ (1 / 2 : ℂ) =
      b ^ (1 / 2 : ℂ) * (Real.sqrt s : ℂ) := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hb hs0),
    Complex.cpow_def_of_ne_zero hb,
    Complex.log_mul_ofReal s hs b hb, add_mul, Complex.exp_add]
  calc
    Complex.exp (↑(Real.log s) * (1 / 2)) *
          Complex.exp (Complex.log b * (1 / 2)) =
        Complex.exp (Complex.log b * (1 / 2)) *
          Complex.exp (↑(Real.log s) * (1 / 2)) := mul_comm _ _
    _ = Complex.exp (Complex.log b * (1 / 2)) *
          (Real.sqrt s : ℂ) := by
      congr 1
      simp [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hs]

private theorem principalHalfPower_rationalBoundary
    {t : ℝ} (ht : t ≠ 0) :
    (Real.sqrt (t ^ 2) : ℂ) *
        ((-(t⁻¹ : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) =
      ((-(t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) := by
  have hbase : (-(t⁻¹ : ℂ) * Complex.I) ≠ 0 := by simp [ht]
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have hprod :
      (-(t⁻¹ : ℂ) * Complex.I) * ((t ^ 2 : ℝ) : ℂ) =
        -(t : ℂ) * Complex.I := by
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    push_cast
    field_simp [htC]
  have hroot := cpow_half_mul_posReal_of_ne_zero
    (-(t⁻¹ : ℂ) * Complex.I) hbase (t ^ 2) ht2
  rw [hprod] at hroot
  rw [hroot]
  ring

/-- The exact boundary root ratio tends to the principal half-power required
by finite quadratic Gauss reciprocity. -/
theorem tendsto_rationalGaussBoundaryRootFactor
    {t : ℝ} (ht : t ≠ 0) :
    Tendsto (rationalGaussBoundaryRootFactor t) (𝓝[>] 0)
      (𝓝 ((-(t : ℂ) * Complex.I) ^ (1 / 2 : ℂ))) := by
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := inf_le_left
  have hrho : Tendsto (fun ρ : ℝ ↦ ρ) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.mono_left hle
  have hden : Tendsto (fun ρ : ℝ ↦ ρ ^ 2 + t⁻¹ ^ 2) (𝓝[>] 0)
      (𝓝 (t⁻¹ ^ 2)) := by
    simpa using (hrho.pow 2).add tendsto_const_nhds
  have hinv : Tendsto (fun ρ : ℝ ↦ (ρ ^ 2 + t⁻¹ ^ 2)⁻¹) (𝓝[>] 0)
      (𝓝 (t ^ 2)) := by
    have h := hden.inv₀ (pow_ne_zero 2 (inv_ne_zero ht))
    convert h using 1
    field_simp [ht]
  have hsqrt : Tendsto (fun ρ : ℝ ↦ Real.sqrt ((ρ ^ 2 + t⁻¹ ^ 2)⁻¹))
      (𝓝[>] 0) (𝓝 (Real.sqrt (t ^ 2))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hinv
  have hb : Tendsto (rationalGaussBoundaryParameter t) (𝓝[>] 0)
      (𝓝 (-(t⁻¹ : ℂ) * Complex.I)) := by
    have hc : Tendsto (fun _ : ℝ ↦ (t⁻¹ : ℂ) * Complex.I)
        (𝓝[>] 0) (𝓝 ((t⁻¹ : ℂ) * Complex.I)) := tendsto_const_nhds
    have h := hrho.ofReal.sub hc
    simpa [rationalGaussBoundaryParameter] using h
  have hbmem : (-(t⁻¹ : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    right
    simp [ht]
  have hhalf : Tendsto (fun _ : ℝ ↦ (1 / 2 : ℂ)) (𝓝[>] 0)
      (𝓝 (1 / 2 : ℂ)) := tendsto_const_nhds
  have hroot := hb.cpow hhalf hbmem
  have hmul := hsqrt.ofReal.mul hroot
  rw [principalHalfPower_rationalBoundary ht] at hmul
  simpa only [rationalGaussBoundaryRootFactor] using hmul

private theorem sqrt_pow_of_nonneg (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt (a ^ n) = Real.sqrt a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg ha n), ih, pow_succ]

/-- After determinant normalization, the complex matrix-theta identity says
pointwise that the reciprocal boundary family is the direct boundary family
times the visible determinant and principal-root factor. -/
theorem polarDeterminant_mul_normalized_boundaryInvTheta_eq_rootFactor_mul_boundaryTheta
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) {t : ℚ} (ht : t ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (L.polarDeterminant.natAbs : ℂ) *
        ((Real.sqrt
          ((rationalGaussDualRealScale (t : ℝ) ρ) ^ n *
            L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹.det) : ℂ) *
          ∑' z : Fin n → ℤ,
            shiftedMatrixGaussianSummand
              L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
              ((rationalGaussBoundaryParameter (t : ℝ) ρ)⁻¹) 0 z) =
      (L.polarRealDeterminantScale : ℂ) *
        (rationalGaussBoundaryRootFactor (t : ℝ) ρ) ^ n *
          ((Real.sqrt
            (ρ ^ n *
              L.rationalQuadraticSpaceMatrix.realPolarMatrix.det) : ℂ) *
            ∑' z : Fin n → ℤ,
              shiftedMatrixGaussianSummand
                L.rationalQuadraticSpaceMatrix.realPolarMatrix
                (rationalGaussBoundaryParameter (t : ℝ) ρ) 0 z) := by
  let C := L.rationalQuadraticSpaceMatrix.realPolarMatrix
  let b := rationalGaussBoundaryParameter (t : ℝ) ρ
  let δ := rationalGaussDualRealScale (t : ℝ) ρ
  let Θ := ∑' z : Fin n → ℤ, shiftedMatrixGaussianSummand C b 0 z
  let Θi := ∑' z : Fin n → ℤ, shiftedMatrixGaussianSummand C⁻¹ b⁻¹ 0 z
  have hb : 0 < b.re := by simpa [b] using hρ
  have htheta : Θ = complexShiftedMatrixThetaNormalization C b * Θi :=
    tsum_shiftedMatrixGaussianSummand_complex_zero_eq_inv
      n C L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef hb
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
  have hbroot : b ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hb0]
    exact Complex.exp_ne_zero _
  have hCdet : 0 < C.det :=
    L.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos
  have hsqrtC : (Real.sqrt C.det : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hCdet
  have htheta' :
      Θi = (b ^ (1 / 2 : ℂ)) ^ n * (Real.sqrt C.det : ℂ) * Θ := by
    rw [htheta, complexShiftedMatrixThetaNormalization]
    simp only [Fintype.card_fin]
    field_simp [hbroot]
    rw [mul_div_cancel_right₀ _ (pow_ne_zero n hbroot)]
  have hδ : 0 < δ :=
    rationalGaussDualRealScale_pos (by exact_mod_cast ht) hρ
  have hdetinv : C⁻¹.det = C.det⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hsqrtDual :
      Real.sqrt (δ ^ n * C⁻¹.det) =
        Real.sqrt δ ^ n * (Real.sqrt C.det)⁻¹ := by
    rw [hdetinv, Real.sqrt_mul (pow_nonneg hδ.le n),
      sqrt_pow_of_nonneg δ hδ.le n, Real.sqrt_inv]
  have hsqrtPrimal :
      Real.sqrt (ρ ^ n * C.det) =
        Real.sqrt ρ ^ n * Real.sqrt C.det := by
    rw [Real.sqrt_mul (pow_nonneg hρ.le n),
      sqrt_pow_of_nonneg ρ hρ.le n]
  have hdiscReal : (L.polarDeterminant.natAbs : ℝ) = C.det := by
    change (L.polarDeterminant.natAbs : ℝ) =
      L.rationalQuadraticSpaceMatrix.realPolarMatrix.det
    rw [L.rationalQuadraticSpaceMatrix_realPolarMatrix_det,
      Nat.cast_natAbs, abs_of_pos]
    exact_mod_cast L.polarDeterminant_pos
  have hdeltaSqrt :
      Real.sqrt δ = Real.sqrt ρ *
        Real.sqrt ((ρ ^ 2 + ((t : ℝ)⁻¹) ^ 2)⁻¹) := by
    rw [show δ = ρ * (ρ ^ 2 + ((t : ℝ)⁻¹) ^ 2)⁻¹ by
      simp [δ, rationalGaussDualRealScale, div_eq_mul_inv]]
    rw [Real.sqrt_mul hρ.le]
  change
    (L.polarDeterminant.natAbs : ℂ) *
        ((Real.sqrt (δ ^ n * C⁻¹.det) : ℂ) * Θi) =
      (L.polarRealDeterminantScale : ℂ) *
        (rationalGaussBoundaryRootFactor (t : ℝ) ρ) ^ n *
          ((Real.sqrt (ρ ^ n * C.det) : ℂ) * Θ)
  rw [htheta', hsqrtDual, hsqrtPrimal, hdeltaSqrt]
  rw [show (L.polarRealDeterminantScale : ℂ) =
      (Real.sqrt C.det : ℂ) by rfl]
  rw [show (L.polarDeterminant.natAbs : ℂ) = (C.det : ℂ) by exact_mod_cast hdiscReal]
  simp only [rationalGaussBoundaryRootFactor, b, mul_pow]
  push_cast
  have hsqrtSq : Real.sqrt C.det ^ 2 = C.det :=
    Real.sq_sqrt hCdet.le
  field_simp [hsqrtC]
  rw [← hsqrtSq]
  simp [Real.sqrt_sq (Real.sqrt_nonneg _)]
  left
  left
  ring

/-- Exact finite quadratic Gauss reciprocity for the literal standard and
polar-dual finite-adelic integrals.  The equality is forced by the complex
matrix-theta identity and the two independently proved Abel limits. -/
theorem rationalFiniteAdeleQuadraticGaussReciprocity
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hn : n ≠ 0)
    {t : ℚ} (ht : t ≠ 0) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t =
      (L.polarRealDeterminantScale : ℂ) *
        ((-((t : ℝ) : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
            (-t⁻¹) := by
  have hA :=
    tendsto_normalized_rationalGaussBoundaryTheta_eq_standardGauss L t
  have hB :=
    tendsto_polarDeterminant_mul_normalized_rationalGaussBoundaryInvTheta_eq_dualGauss
      L hn ht
  have hK := tendsto_rationalGaussBoundaryRootFactor
    (t := (t : ℝ)) (by exact_mod_cast ht)
  have hR :=
    ((hK.pow n).const_mul (L.polarRealDeterminantScale : ℂ)).mul hA
  have hBR : Tendsto
      (fun ρ : ℝ ↦
        (L.polarRealDeterminantScale : ℂ) *
          (rationalGaussBoundaryRootFactor (t : ℝ) ρ) ^ n *
            ((Real.sqrt
              (ρ ^ n *
                L.rationalQuadraticSpaceMatrix.realPolarMatrix.det) : ℂ) *
              ∑' z : Fin n → ℤ,
                shiftedMatrixGaussianSummand
                  L.rationalQuadraticSpaceMatrix.realPolarMatrix
                  (rationalGaussBoundaryParameter (t : ℝ) ρ) 0 z))
      (𝓝[>] 0)
      (𝓝
        (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral
          t)) := by
    apply hB.congr'
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    exact
      polarDeterminant_mul_normalized_boundaryInvTheta_eq_rootFactor_mul_boundaryTheta
        L ht hρ
  exact tendsto_nhds_unique hBR hR

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

open PositiveDefiniteIntegralLattice

/-- Unconditional closure of the nonzero zero-frequency Bruhat relation on
the concrete polar Gaussian--lattice orbit. -/
theorem rationalAdeleRankOne_nonzeroBruhatAnalyticRelation
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hn : n ≠ 0)
    {a : ℝ} (ha : 0 < a) {t : ℚ} (ht : t ≠ 0) :
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
  exact
    rationalAdeleRankOne_nonzeroBruhatAnalyticRelation_of_quadraticGaussReciprocity
      L ha ht (L.rationalFiniteAdeleQuadraticGaussReciprocity hn ht)

end RationalQuadraticSpaceMatrix
