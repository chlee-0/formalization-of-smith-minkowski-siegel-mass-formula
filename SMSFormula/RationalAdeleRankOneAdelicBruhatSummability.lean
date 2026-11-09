import SMSFormula.RationalFiniteAdeleQuadraticGaussStrongApproximation
import SMSFormula.RationalAdeleRankOneBruhatSummability

/-!
# Summability along every adelic unipotent translate

The finite-only dilation orbit of a rational Bruhat family leaves the rational
diagonal.  This file proves convergence on that actual orbit, and in fact for
every fixed adelic unipotent parameter.  Finite strong approximation supplies
one existential rational translate of the old Gauss family.  The real
component differs from that translate by a fixed real number, whose inverse
square-root factor is uniformly bounded by a literal constant.  The resulting
majorant is a translated copy of the already summable rational-height kernel.

The strong-approximation rational is used only inside the proof.  No selector,
quotient section, adelic parameter sum, Eisenstein extension, or shell
comparison is defined.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix MeasureTheory RationalQuadraticSpaceMatrix

namespace RationalQuadraticSpaceMatrix

/-- The real coordinate of an adelic parameter plus a rational diagonal is
the corresponding ordinary real translate. -/
theorem rationalAdeleRealScalar_add_rationalDiagonal
    (u : RationalAdele) (t : ℚ) :
    rationalAdeleRealScalar (u + algebraMap ℚ RationalAdele t) =
      rationalAdeleRealScalar u + (t : ℝ) := by
  change rationalInfiniteAdeleContinuousAddEquivReal
      (u.1 + algebraMap ℚ RationalInfiniteAdele t) = _
  rw [map_add, rationalInfiniteAdeleContinuousAddEquivReal_algebraMap]
  have ht : algebraMap ℚ ℝ t = (t : ℝ) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℝ) t
  simp only [ht, rationalAdeleRealScalar]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Shifting the imaginary coordinate of a right-half-plane parameter by a
fixed real number costs only the displayed scale-independent factor. -/
theorem norm_bruhat_parameter_le_mul_norm_translated
    {a delta : ℝ} (ha : 0 < a) (t : ℚ) :
    ‖(a : ℂ) - (t : ℂ) * Complex.I‖ ≤
      (1 + |delta| / a) *
        ‖(a : ℂ) - ((t : ℝ) + delta : ℂ) * Complex.I‖ := by
  let z : ℂ := (a : ℂ) - ((t : ℝ) + delta : ℂ) * Complex.I
  have hza : a ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    simpa [z, abs_of_pos ha, Complex.mul_re] using h
  have hdelta : |delta| ≤ (|delta| / a) * ‖z‖ := by
    calc
      |delta| = (|delta| / a) * a := by field_simp
      _ ≤ (|delta| / a) * ‖z‖ := by gcongr
  have heq :
      (a : ℂ) - (t : ℂ) * Complex.I =
        z + (delta : ℂ) * Complex.I := by
    dsimp [z]
    ring
  rw [heq]
  calc
    ‖z + (delta : ℂ) * Complex.I‖ ≤
        ‖z‖ + ‖(delta : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = ‖z‖ + |delta| := by simp [Real.norm_eq_abs]
    _ ≤ ‖z‖ + (|delta| / a) * ‖z‖ := by gcongr
    _ = (1 + |delta| / a) * ‖z‖ := by ring

/-- The inverse square-root real Bruhat factor at a fixed translate is
bounded uniformly by the unshifted factor. -/
theorem inv_sqrt_norm_translated_bruhat_parameter_le
    {a delta : ℝ} (ha : 0 < a) (t : ℚ) :
    (Real.sqrt ‖(a : ℂ) -
        ((t : ℝ) + delta : ℂ) * Complex.I‖)⁻¹ ≤
      Real.sqrt (1 + |delta| / a) *
        (Real.sqrt ‖(a : ℂ) - (t : ℂ) * Complex.I‖)⁻¹ := by
  let oldNorm := ‖(a : ℂ) - (t : ℂ) * Complex.I‖
  let newNorm :=
    ‖(a : ℂ) - ((t : ℝ) + delta : ℂ) * Complex.I‖
  let C := 1 + |delta| / a
  have hold : 0 < oldNorm := by
    have h := Complex.abs_re_le_norm
      ((a : ℂ) - (t : ℂ) * Complex.I)
    have h' : a ≤ oldNorm := by
      simpa [oldNorm, abs_of_pos ha, Complex.mul_re] using h
    exact ha.trans_le h'
  have hnew : 0 < newNorm := by
    have h := Complex.abs_re_le_norm
      ((a : ℂ) - ((t : ℝ) + delta : ℂ) * Complex.I)
    have h' : a ≤ newNorm := by
      simpa [newNorm, abs_of_pos ha, Complex.mul_re] using h
    exact ha.trans_le h'
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hcomp : oldNorm ≤ C * newNorm := by
    simpa only [oldNorm, newNorm, C] using
      norm_bruhat_parameter_le_mul_norm_translated ha t
  have hsqrt : Real.sqrt oldNorm ≤
      Real.sqrt C * Real.sqrt newNorm := by
    rw [← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt hcomp
  change (Real.sqrt newNorm)⁻¹ ≤
    Real.sqrt C * (Real.sqrt oldNorm)⁻¹
  rw [inv_eq_one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (Real.sqrt_pos.2 hnew)
    (Real.sqrt_pos.2 hold)).2 (by simpa using hsqrt)

/-- Exact norm of the explicit real factor at an arbitrary real Bruhat
parameter. -/
theorem norm_polarRealGaussian_explicit_real_bruhat_factor
    (L : PositiveDefiniteIntegralLattice n) (a s : ℝ) :
    ‖(L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / ((a : ℂ) - (s : ℂ) * Complex.I) ^
          (1 / 2 : ℂ)) ^ n‖ =
      (L.polarRealDeterminantScale : ℝ)⁻¹ *
        (Real.sqrt ‖(a : ℂ) - (s : ℂ) * Complex.I‖)⁻¹ ^ n := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg
    (by exact_mod_cast L.polarRealDeterminantScale_pos.le)]
  rw [norm_pow, norm_div, norm_one,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_real]
  simp only [one_div, Real.sqrt_eq_rpow]

/-- For rank at least five, the concrete Bruhat family is summable along
every fixed adelic unipotent translate.  This covers the genuinely adelic
families produced by finite-only dilation, without reindexing them as rational
parameters. -/
theorem summable_rationalAdeleRankOneAdelicBruhatCoefficient_add_diagonal_polarGaussianLattice_of_rankAtLeastFive
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (hn : 5 ≤ n)
    (u : RationalAdele) :
    Summable (fun t : ℚ =>
      L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneAdelicBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))
        (u + algebraMap ℚ RationalAdele t)) := by
  obtain ⟨q, hq⟩ :=
    RationalQuadraticSpaceMatrix.exists_rational_rationalFiniteAdeleQuadraticGaussIntegralAt_add_diagonal_eq
      L u.2
  let delta : ℝ := rationalAdeleRealScalar u - (q : ℝ)
  let K : ℝ :=
    Real.sqrt (1 + |delta| / a) ^ n *
      ((L.polarRealDeterminantScale : ℝ)⁻¹ *
        (Real.sqrt (L.polarDeterminant.natAbs : ℝ)) ^ n *
        (Real.sqrt (min a 1))⁻¹ ^ n)
  have hkernel : Summable (fun t : ℚ =>
      (Real.sqrt (rationalRankOneBruhatHeight (t + q)))⁻¹ ^ n) :=
    (summable_inv_sqrt_rationalRankOneBruhatHeight_pow hn).comp_injective
      (fun _ _ h ↦ add_right_cancel h)
  apply Summable.of_norm_bounded (hkernel.mul_left K)
  intro t
  rw [rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice_eq_explicit_real_mul_finiteAt
    L (by simpa using ha)]
  rw [norm_mul, norm_polarRealGaussian_explicit_real_bruhat_factor]
  have hfinite :
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt
          (u + algebraMap ℚ RationalAdele t).2 =
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
          (t + q) := by
    simpa using hq t
  rw [hfinite]
  have hreal : rationalAdeleRealScalar
      (u + algebraMap ℚ RationalAdele t) =
        ((t + q : ℚ) : ℝ) + delta := by
    rw [rationalAdeleRealScalar_add_rationalDiagonal]
    dsimp [delta]
    push_cast
    ring
  rw [hreal]
  have hshift :=
    inv_sqrt_norm_translated_bruhat_parameter_le
      (delta := delta) ha (t + q)
  norm_cast at hshift
  calc
    (L.polarRealDeterminantScale : ℝ)⁻¹ *
          (Real.sqrt ‖(a : ℂ) -
            ((((t + q : ℚ) : ℝ) + delta : ℝ) : ℂ) * Complex.I‖)⁻¹ ^ n *
        ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
          (t + q)‖ ≤
      (L.polarRealDeterminantScale : ℝ)⁻¹ *
          (Real.sqrt (1 + |delta| / a) *
            (Real.sqrt ‖(a : ℂ) - ((t + q : ℚ) : ℂ) * Complex.I‖)⁻¹) ^ n *
        ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral
          (t + q)‖ := by
            gcongr
    _ = Real.sqrt (1 + |delta| / a) ^ n *
        ‖L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) (t + q)‖ := by
            rw [rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_eq_explicit_real_mul_finite
              L (by simpa using ha)]
            rw [norm_mul,
              norm_polarRealGaussian_explicit_bruhat_factor]
            ring
    _ ≤ K *
        (Real.sqrt (rationalRankOneBruhatHeight (t + q)))⁻¹ ^ n := by
      dsimp [K]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (L.norm_rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_le_height
          ha (t + q)) (by positivity)

end PositiveDefiniteIntegralLattice

end
