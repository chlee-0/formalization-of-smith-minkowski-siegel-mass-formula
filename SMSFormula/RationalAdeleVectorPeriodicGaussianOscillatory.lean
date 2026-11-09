import SMSFormula.RationalAdeleVectorPeriodicGaussianAbel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Oscillatory perturbations of periodic Gaussian Abel limits

The direct matrix Landsberg--Schaar argument approaches a rational quadratic
phase through complex Gaussian parameters.  After the limiting periodic phase
has been separated, the remaining imaginary parameter `eta(a)` is smaller
than the positive Gaussian scale `a`.

This file proves that such an `o(a)` quadratic phase does not change the
periodic Gaussian Abel limit.  The proof uses the pointwise circle estimate
`|exp(i x)-1| <= |x|` and a first Gaussian-moment bound obtained by domination
with the same Gaussian at half scale.  Absolute summability is established
before every `tsum` comparison.

No complex matrix-theta transformation, finite Gauss value, reciprocity
identity, or Weil index is asserted.
-/

noncomputable section

open Filter Matrix Topology

namespace PositiveDefiniteIntegralLattice

/-- The real quadratic value of an integer vector for a matrix `S`. -/
def integerVectorMatrixQuadraticValue
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℤ) : ℝ :=
  integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z)

/-- The unit-modulus quadratic phase used for the small imaginary
perturbation. -/
def quadraticOscillation
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) (z : Fin n → ℤ) : ℂ :=
  Complex.exp
    (Complex.I * (-Real.pi * η * integerVectorMatrixQuadraticValue S z : ℝ))

@[simp]
theorem norm_quadraticOscillation
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) (z : Fin n → ℤ) :
    ‖quadraticOscillation S η z‖ = 1 := by
  rw [quadraticOscillation, Complex.norm_exp]
  simp [Complex.mul_re]

theorem norm_quadraticOscillation_sub_one_le
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) (z : Fin n → ℤ) :
    ‖quadraticOscillation S η z - 1‖ ≤
      Real.pi * |η| * |integerVectorMatrixQuadraticValue S z| := by
  rw [quadraticOscillation]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := -Real.pi * η * integerVectorMatrixQuadraticValue S z)).trans_eq ?_
  simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos Real.pi_pos]

/-- The product of the positive Gaussian and the small quadratic oscillation
is exactly the matrix Gaussian with complex scale `a + eta*I`. -/
theorem quadraticOscillation_mul_centeredGaussian_eq_shifted
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (a η : ℝ) (z : Fin n → ℤ) :
    quadraticOscillation S η z *
        centeredMatrixGaussianSummand S a 0 z =
      shiftedMatrixGaussianSummand S
        ((a : ℂ) + (η : ℂ) * Complex.I) 0 z := by
  rw [quadraticOscillation, centeredMatrixGaussianSummand,
    shiftedMatrixGaussianSummand, ← Complex.exp_add]
  simp only [Pi.zero_apply, sub_zero]
  rw [show (fun i ↦ (z i : ℝ)) = integerVectorReal z by rfl]
  dsimp [integerVectorMatrixQuadraticValue]
  push_cast
  ring_nf
  simp

/-- A periodically weighted positive Gaussian remains summable after any
real quadratic phase perturbation. -/
theorem summable_periodicWeight_mul_quadraticOscillation_mul_centeredGaussian
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) (η : ℝ)
    (weight : (Fin n → ZMod m) → ℂ) :
    Summable (fun z : Fin n → ℤ ↦
      weight (fun i ↦ (z i : ZMod m)) * quadraticOscillation S η z *
        centeredMatrixGaussianSummand S a 0 z) := by
  have hbase :=
    (summable_periodicWeight_mul_centeredMatrixGaussianSummand
      S hS ha weight).norm
  apply Summable.of_norm_bounded hbase
  intro z
  simp

private theorem quadraticValue_nonneg
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (z : Fin n → ℤ) :
    0 ≤ integerVectorMatrixQuadraticValue S z := by
  exact hS.posSemidef.dotProduct_mulVec_nonneg (integerVectorReal z)

/-- At zero center a real-scale centered Gaussian is the complex coercion of
its norm. -/
theorem centeredMatrixGaussianSummand_zero_eq_ofReal_norm
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (a : ℝ)
    (z : Fin n → ℤ) :
    centeredMatrixGaussianSummand S a 0 z =
      (‖centeredMatrixGaussianSummand S a 0 z‖ : ℂ) := by
  rw [centeredMatrixGaussianSummand]
  simp only [Pi.zero_apply, sub_zero]
  rw [show (fun i ↦ (z i : ℝ)) = integerVectorReal z by rfl]
  let q : ℝ := integerVectorReal z ⬝ᵥ S.mulVec (integerVectorReal z)
  change Complex.exp
      (-(Real.pi : ℂ) * (a : ℂ) * (q : ℂ)) =
    (‖Complex.exp
      (-(Real.pi : ℂ) * (a : ℂ) * (q : ℂ))‖ : ℂ)
  apply Complex.ext
  · rw [Complex.norm_exp]
    simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  · simp [Complex.exp_im, Complex.mul_im]

/-- The square-root normalization at scale `a` is the fixed factor
`sqrt(2^n)` times the normalization at half scale. -/
theorem sqrt_gaussianNormalization_eq_sqrt_two_pow_mul_halfScale
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) :
    Real.sqrt (a ^ n * S.det) =
      Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt ((a / 2) ^ n * S.det) := by
  have harg : a ^ n * S.det =
      (2 : ℝ) ^ n * ((a / 2) ^ n * S.det) := by
    rw [div_pow]
    field_simp
  rw [harg, Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ n)]

/-- The determinant-normalized sum of Gaussian norms at half scale has a
finite explicit limit. -/
theorem tendsto_sqrt_det_mul_tsum_norm_centered_halfScale_nhdsGT_zero
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) :
    Tendsto
      (fun a : ℝ ↦ Real.sqrt (a ^ n * S.det) *
        ∑' z : Fin n → ℤ,
          ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖)
      (𝓝[>] 0) (𝓝 (Real.sqrt ((2 : ℝ) ^ n))) := by
  have hcomplex :=
    tendsto_sqrt_det_mul_tsum_centered_mul_nhdsGT_zero
      S hS 0 (by norm_num : (0 : ℝ) < 1 / 2)
  have hreal :
      Tendsto
        (fun a : ℝ ↦ Real.sqrt ((a / 2) ^ n * S.det) *
          ∑' z : Fin n → ℤ,
            ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖)
        (𝓝[>] 0) (𝓝 1) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
    apply hre.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    simp only [Function.comp_apply]
    rw [show a * (1 / 2 : ℝ) = a / 2 by ring]
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    have hsum :=
      summable_centeredMatrixGaussianSummand S hS (half_pos ha) 0
    calc
      (∑' z : Fin n → ℤ,
          centeredMatrixGaussianSummand S (a / 2) 0 z).re =
          ∑' z : Fin n → ℤ,
            (centeredMatrixGaussianSummand S (a / 2) 0 z).re :=
        (Complex.hasSum_re hsum.hasSum).tsum_eq.symm
      _ = ∑' z : Fin n → ℤ,
          ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖ := by
        apply tsum_congr
        intro z
        have hz := congrArg Complex.re
          (centeredMatrixGaussianSummand_zero_eq_ofReal_norm
            S (a / 2) z)
        simpa using hz
  have hscaled := hreal.const_mul (Real.sqrt ((2 : ℝ) ^ n))
  have hscaled' :
      Tendsto
        (fun a : ℝ ↦ Real.sqrt ((2 : ℝ) ^ n) *
          (Real.sqrt ((a / 2) ^ n * S.det) *
            ∑' z : Fin n → ℤ,
              ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖))
        (𝓝[>] 0) (𝓝 (Real.sqrt ((2 : ℝ) ^ n))) := by
    simpa using hscaled
  apply hscaled'.congr'
  apply Filter.Eventually.of_forall
  intro a
  change Real.sqrt ((2 : ℝ) ^ n) *
      (Real.sqrt ((a / 2) ^ n * S.det) *
        ∑' z : Fin n → ℤ,
          ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖) =
    Real.sqrt (a ^ n * S.det) *
      ∑' z : Fin n → ℤ,
        ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖
  calc
    Real.sqrt ((2 : ℝ) ^ n) *
        (Real.sqrt ((a / 2) ^ n * S.det) *
          ∑' z : Fin n → ℤ,
            ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖) =
      (Real.sqrt ((2 : ℝ) ^ n) *
        Real.sqrt ((a / 2) ^ n * S.det)) *
          ∑' z : Fin n → ℤ,
            ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖ := by ring
    _ = Real.sqrt (a ^ n * S.det) *
          ∑' z : Fin n → ℤ,
            ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖ := by
      rw [← sqrt_gaussianNormalization_eq_sqrt_two_pow_mul_halfScale S a]

/-- The first quadratic moment of a positive matrix Gaussian is dominated by
the half-scale Gaussian with a literal `a⁻¹` coefficient. -/
theorem quadraticValue_mul_norm_centeredGaussian_le_halfScale
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) (z : Fin n → ℤ) :
    integerVectorMatrixQuadraticValue S z *
        ‖centeredMatrixGaussianSummand S a 0 z‖ ≤
      (2 * Real.exp (-1) / (Real.pi * a)) *
        ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖ := by
  let q := integerVectorMatrixQuadraticValue S z
  let y := Real.pi * a * q / 2
  have hq : 0 ≤ q := quadraticValue_nonneg S hS z
  have hpa : 0 < Real.pi * a := mul_pos Real.pi_pos ha
  have hpa0 : Real.pi * a ≠ 0 := hpa.ne'
  have hy : y = Real.pi * a * q / 2 := rfl
  have hmoment := Real.mul_exp_neg_le_exp_neg_one y
  have hgauss :
      ‖centeredMatrixGaussianSummand S a 0 z‖ =
        Real.exp (-Real.pi * a * q) := by
    rw [centeredMatrixGaussianSummand, Complex.norm_exp]
    congr 1
    simp only [Pi.zero_apply, sub_zero, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    dsimp [q, integerVectorMatrixQuadraticValue, integerVectorReal]
    rw [show (fun i ↦ (z i : ℝ)) = integerVectorReal z by rfl]
  have hhalf :
      ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖ =
        Real.exp (-y) := by
    rw [centeredMatrixGaussianSummand, Complex.norm_exp]
    congr 1
    simp only [Pi.zero_apply, sub_zero, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    dsimp [q, y, integerVectorMatrixQuadraticValue, integerVectorReal]
    rw [show (fun i ↦ (z i : ℝ)) = integerVectorReal z by rfl]
    ring
  rw [hgauss, hhalf]
  have hfactor : 0 ≤ 2 / (Real.pi * a) * Real.exp (-y) := by positivity
  have hrewrite :
      q * Real.exp (-Real.pi * a * q) =
        (2 / (Real.pi * a) * Real.exp (-y)) *
          (y * Real.exp (-y)) := by
    have hexp :
        Real.exp (-Real.pi * a * q) =
          Real.exp (-y) * Real.exp (-y) := by
      rw [← Real.exp_add]
      congr 1
      rw [hy]
      ring
    have hyq : 2 / (Real.pi * a) * y = q := by
      rw [hy]
      field_simp [hpa0]
    rw [hexp, ← hyq]
    ring
  rw [hrewrite]
  calc
    (2 / (Real.pi * a) * Real.exp (-y)) *
        (y * Real.exp (-y)) ≤
      (2 / (Real.pi * a) * Real.exp (-y)) * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left hmoment hfactor
    _ = (2 * Real.exp (-1) / (Real.pi * a)) * Real.exp (-y) := by ring

/-- Pointwise domination of the periodically weighted oscillatory error by
the half-scale positive Gaussian. -/
theorem norm_periodicQuadraticOscillation_error_le_halfScale
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) (η : ℝ)
    (weight : (Fin n → ZMod m) → ℂ) (z : Fin n → ℤ) :
      ‖weight (fun i ↦ (z i : ZMod m)) *
          (quadraticOscillation S η z - 1) *
          centeredMatrixGaussianSummand S a 0 z‖ ≤
        ((∑ r : Fin n → ZMod m, ‖weight r‖) * (Real.pi * |η|) *
          (2 * Real.exp (-1) / (Real.pi * a))) *
          ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖ := by
  let C : ℝ := ∑ r : Fin n → ZMod m, ‖weight r‖
  have hC : ∀ r, ‖weight r‖ ≤ C := by
    intro r
    exact Finset.single_le_sum
      (fun i _hi ↦ norm_nonneg (weight i)) (Finset.mem_univ r)
  have hq := quadraticValue_nonneg S hS z
  have hphase := norm_quadraticOscillation_sub_one_le S η z
  rw [norm_mul, norm_mul]
  change _ ≤ (C * (Real.pi * |η|) *
    (2 * Real.exp (-1) / (Real.pi * a))) * _
  calc
    ‖weight (fun i ↦ (z i : ZMod m))‖ *
          ‖quadraticOscillation S η z - 1‖ *
          ‖centeredMatrixGaussianSummand S a 0 z‖ ≤
        ‖weight (fun i ↦ (z i : ZMod m))‖ *
            (Real.pi * |η| * integerVectorMatrixQuadraticValue S z) *
          ‖centeredMatrixGaussianSummand S a 0 z‖ := by
      gcongr
      simpa [abs_of_nonneg hq] using hphase
    _ ≤ C * (Real.pi * |η| * integerVectorMatrixQuadraticValue S z) *
          ‖centeredMatrixGaussianSummand S a 0 z‖ := by
      gcongr
      exact hC (fun i ↦ (z i : ZMod m))
    _ ≤ C * (Real.pi * |η|) *
          ((2 * Real.exp (-1) / (Real.pi * a)) *
            ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖) := by
      have hm := quadraticValue_mul_norm_centeredGaussian_le_halfScale
        S hS ha z
      have hnonneg : 0 ≤ C * (Real.pi * |η|) := by
        dsimp [C]
        positivity
      calc
        C * (Real.pi * |η| * integerVectorMatrixQuadraticValue S z) *
            ‖centeredMatrixGaussianSummand S a 0 z‖ =
          (C * (Real.pi * |η|)) *
            (integerVectorMatrixQuadraticValue S z *
              ‖centeredMatrixGaussianSummand S a 0 z‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hm hnonneg
    _ = (C * (Real.pi * |η|) *
          (2 * Real.exp (-1) / (Real.pi * a))) *
          ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖ := by ring

/-- The norm of the periodically weighted oscillatory error is summable at
every positive Gaussian scale. -/
theorem summable_norm_periodicQuadraticOscillation_error
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    {a : ℝ} (ha : 0 < a) (η : ℝ)
    (weight : (Fin n → ZMod m) → ℂ) :
    Summable (fun z : Fin n → ℤ ↦
      ‖weight (fun i ↦ (z i : ZMod m)) *
          (quadraticOscillation S η z - 1) *
          centeredMatrixGaussianSummand S a 0 z‖) := by
  let C : ℝ := ∑ r : Fin n → ZMod m, ‖weight r‖
  let K : ℝ := C * (Real.pi * |η|) *
    (2 * Real.exp (-1) / (Real.pi * a))
  have hhalf :=
    (summable_centeredMatrixGaussianSummand S hS (half_pos ha) 0).norm
  apply Summable.of_norm_bounded (hhalf.mul_left K)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_periodicQuadraticOscillation_error_le_halfScale
    S hS ha η weight z

/-- After determinant normalization, an `o(a)` imaginary quadratic
perturbation contributes zero in the positive Abel limit. -/
theorem tendsto_normalized_periodicQuadraticOscillation_error_nhdsGT_zero
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (weight : (Fin n → ZMod m) → ℂ) (η : ℝ → ℝ)
    (hη : Tendsto (fun a ↦ η a / a) (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun a : ℝ ↦ (Real.sqrt (a ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ,
          weight (fun i ↦ (z i : ZMod m)) *
            (quadraticOscillation S (η a) z - 1) *
            centeredMatrixGaussianSummand S a 0 z)
      (𝓝[>] 0) (𝓝 0) := by
  let C : ℝ := ∑ r : Fin n → ZMod m, ‖weight r‖
  let B : ℝ → ℝ := fun a ↦ Real.sqrt (a ^ n * S.det) *
    ∑' z : Fin n → ℤ,
      ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖
  let R : ℝ → ℝ := fun a ↦
    (C * 2 * Real.exp (-1)) * |η a / a| * B a
  have hηabs : Tendsto (fun a ↦ |η a / a|) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.norm_eq_abs, abs_div] using hη.norm
  have hB : Tendsto B (𝓝[>] 0)
      (𝓝 (Real.sqrt ((2 : ℝ) ^ n))) := by
    exact tendsto_sqrt_det_mul_tsum_norm_centered_halfScale_nhdsGT_zero S hS
  have hR : Tendsto R (𝓝[>] 0) (𝓝 0) := by
    have hprod := hηabs.mul hB
    have hscaled := hprod.const_mul (C * 2 * Real.exp (-1))
    simpa only [R, mul_assoc, zero_mul, mul_zero] using hscaled
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with a ha
    let K : ℝ := C * (Real.pi * |η a|) *
      (2 * Real.exp (-1) / (Real.pi * a))
    let error : (Fin n → ℤ) → ℂ := fun z ↦
      weight (fun i ↦ (z i : ZMod m)) *
        (quadraticOscillation S (η a) z - 1) *
        centeredMatrixGaussianSummand S a 0 z
    let halfGaussian : (Fin n → ℤ) → ℝ := fun z ↦
      ‖centeredMatrixGaussianSummand S (a / 2) 0 z‖
    have herrorNorm : Summable (fun z ↦ ‖error z‖) := by
      exact summable_norm_periodicQuadraticOscillation_error
        S hS ha (η a) weight
    have hhalf : Summable halfGaussian := by
      exact (summable_centeredMatrixGaussianSummand
        S hS (half_pos ha) 0).norm
    have hpoint : ∀ z, ‖error z‖ ≤ K * halfGaussian z := by
      intro z
      exact norm_periodicQuadraticOscillation_error_le_halfScale
        S hS ha (η a) weight z
    have hsum : ‖∑' z, error z‖ ≤ K * ∑' z, halfGaussian z := by
      calc
        ‖∑' z, error z‖ ≤ ∑' z, ‖error z‖ :=
          norm_tsum_le_tsum_norm herrorNorm
        _ ≤ ∑' z, K * halfGaussian z :=
          herrorNorm.tsum_le_tsum hpoint (hhalf.mul_left K)
        _ = K * ∑' z, halfGaussian z := tsum_mul_left
    change ‖(Real.sqrt (a ^ n * S.det) : ℂ) * ∑' z, error z‖ ≤ R a
    rw [norm_mul]
    have hsqrtNorm :
        ‖(Real.sqrt (a ^ n * S.det) : ℂ)‖ =
          Real.sqrt (a ^ n * S.det) := by
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hsqrtNorm]
    calc
      Real.sqrt (a ^ n * S.det) * ‖∑' z, error z‖ ≤
          Real.sqrt (a ^ n * S.det) *
            (K * ∑' z, halfGaussian z) :=
        mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
      _ = R a := by
        have ha' : 0 < a := ha
        dsimp [R, B, K, C, halfGaussian]
        rw [abs_div, show |a| = a from abs_of_pos ha']
        field_simp [Real.pi_ne_zero, ha'.ne']
  · exact hR

/-- Periodic Gaussian Abel limit with a quadratic imaginary perturbation
`eta(a)=o(a)`.  The limit is the same literal uniform residue average as in
the positive theorem. -/
theorem tendsto_periodicGaussianAbel_of_quadraticOscillation_isLittleO
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (weight : (Fin n → ZMod m) → ℂ) (η : ℝ → ℝ)
    (hη : Tendsto (fun a ↦ η a / a) (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun a : ℝ ↦ (Real.sqrt (a ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ,
          weight (fun i ↦ (z i : ZMod m)) *
            quadraticOscillation S (η a) z *
            centeredMatrixGaussianSummand S a 0 z)
      (𝓝[>] 0)
      (𝓝 ((((m : ℝ) ^ n : ℂ)⁻¹) * ∑ r, weight r)) := by
  have hpositive := tendsto_periodicGaussianAbel_nhdsGT_zero S hS weight
  have herror :=
    tendsto_normalized_periodicQuadraticOscillation_error_nhdsGT_zero
      S hS weight η hη
  have hcombined := hpositive.add herror
  have hcombined' :
      Tendsto
        (fun a : ℝ ↦
          (Real.sqrt (a ^ n * S.det) : ℂ) *
              ∑' z : Fin n → ℤ,
                weight (fun i ↦ (z i : ZMod m)) *
                  centeredMatrixGaussianSummand S a 0 z +
            (Real.sqrt (a ^ n * S.det) : ℂ) *
              ∑' z : Fin n → ℤ,
                weight (fun i ↦ (z i : ZMod m)) *
                  (quadraticOscillation S (η a) z - 1) *
                  centeredMatrixGaussianSummand S a 0 z)
        (𝓝[>] 0)
        (𝓝 ((((m : ℝ) ^ n : ℂ)⁻¹) * ∑ r, weight r)) := by
    simpa only [add_zero] using hcombined
  apply hcombined'.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  let base : (Fin n → ℤ) → ℂ := fun z ↦
    weight (fun i ↦ (z i : ZMod m)) *
      centeredMatrixGaussianSummand S a 0 z
  let err : (Fin n → ℤ) → ℂ := fun z ↦
    weight (fun i ↦ (z i : ZMod m)) *
      (quadraticOscillation S (η a) z - 1) *
      centeredMatrixGaussianSummand S a 0 z
  let perturbed : (Fin n → ℤ) → ℂ := fun z ↦
    weight (fun i ↦ (z i : ZMod m)) *
      quadraticOscillation S (η a) z *
      centeredMatrixGaussianSummand S a 0 z
  have hbase : Summable base := by
    exact summable_periodicWeight_mul_centeredMatrixGaussianSummand
      S hS ha weight
  have herrorNorm : Summable (fun z ↦ ‖err z‖) := by
    exact summable_norm_periodicQuadraticOscillation_error
      S hS ha (η a) weight
  have herr : Summable err := herrorNorm.of_norm
  change
    (Real.sqrt (a ^ n * S.det) : ℂ) * ∑' z, base z +
        (Real.sqrt (a ^ n * S.det) : ℂ) * ∑' z, err z =
      (Real.sqrt (a ^ n * S.det) : ℂ) * ∑' z, perturbed z
  calc
    (Real.sqrt (a ^ n * S.det) : ℂ) * ∑' z, base z +
          (Real.sqrt (a ^ n * S.det) : ℂ) * ∑' z, err z =
        (Real.sqrt (a ^ n * S.det) : ℂ) *
          ((∑' z, base z) + ∑' z, err z) := by ring
    _ = (Real.sqrt (a ^ n * S.det) : ℂ) *
          (∑' z : Fin n → ℤ, (base z + err z)) := by
      rw [(hbase.hasSum.add herr.hasSum).tsum_eq]
    _ = (Real.sqrt (a ^ n * S.det) : ℂ) *
          (∑' z : Fin n → ℤ, perturbed z) := by
      congr 1
      apply tsum_congr
      intro z
      dsimp [base, err, perturbed]
      ring

/-- Equivalent complex-scale form of the oscillatory periodic Abel theorem.
This is the form used by the boundary approach in the matrix
Landsberg--Schaar argument. -/
theorem tendsto_periodicShiftedMatrixGaussian_of_imaginaryError_isLittleO
    {n m : ℕ} [NeZero m]
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (weight : (Fin n → ZMod m) → ℂ) (η : ℝ → ℝ)
    (hη : Tendsto (fun a ↦ η a / a) (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun a : ℝ ↦ (Real.sqrt (a ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ,
          weight (fun i ↦ (z i : ZMod m)) *
            shiftedMatrixGaussianSummand S
              ((a : ℂ) + (η a : ℂ) * Complex.I) 0 z)
      (𝓝[>] 0)
      (𝓝 ((((m : ℝ) ^ n : ℂ)⁻¹) * ∑ r, weight r)) := by
  have h := tendsto_periodicGaussianAbel_of_quadraticOscillation_isLittleO
    S hS weight η hη
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro a
  change
    (Real.sqrt (a ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ,
          weight (fun i ↦ (z i : ZMod m)) *
            quadraticOscillation S (η a) z *
            centeredMatrixGaussianSummand S a 0 z =
      (Real.sqrt (a ^ n * S.det) : ℂ) *
        ∑' z : Fin n → ℤ,
          weight (fun i ↦ (z i : ZMod m)) *
            shiftedMatrixGaussianSummand S
              ((a : ℂ) + (η a : ℂ) * Complex.I) 0 z
  congr 1
  apply tsum_congr
  intro z
  calc
    weight (fun i ↦ (z i : ZMod m)) * quadraticOscillation S (η a) z *
        centeredMatrixGaussianSummand S a 0 z =
      weight (fun i ↦ (z i : ZMod m)) *
        (quadraticOscillation S (η a) z *
          centeredMatrixGaussianSummand S a 0 z) := by ring
    _ = _ := by rw [quadraticOscillation_mul_centeredGaussian_eq_shifted]

end PositiveDefiniteIntegralLattice
