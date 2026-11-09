import Mathlib.Analysis.Fourier.PoissonSummation
import SMSFormula.RationalFiniteAdeleIntegralCosetDecomposition
import SMSFormula.RationalAdeleZeroFrequencyVanishing
import SMSFormula.RationalAdeleBruhatIntegralLocalProduct
import SMSFormula.RationalAdeleRankOneEisensteinFourierDensity

/-!
# Rank-one adelic Poisson summation for the Eisenstein aggregate at the identity

For the polar Gaussian--lattice test `Φ` at positive scale `c` and rank at least five, the
convergent rank-one Eisenstein--Siegel functional is

`E(Φ) = Φ(0) + ∑_{b ∈ ℚ} d_Φ(b)`,

with `d_Φ` the complex value Fourier density.  The proof is a Poisson summation for
the Bruhat family `B(t) = A(t) G(t)` (`A` the archimedean factor, `G` the finite Gauss
integral):

* `ℚ ≃ (ℚ ∩ [0,1)) × ℤ` by the canonical fractional part and floor, and `G` is `ℤ`-periodic;
* Mathlib's real Poisson summation `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable` for
  `A`, whose Fourier transform is the closed-form archimedean local integral (zero at
  nonpositive frequency, `k^{n/2-1} e^{-2π c k}` at positive frequency, hence summable);
* the finite coset decomposition turns `∑_r e(k r) G(r)` into the finite local integral;
* the local product factorization identifies `𝓕A(k) · (finite)(-k)` with `d_Φ(k)`, and the
  non-integral vanishing extends the integer sum to all of `ℚ`.

The double series is absolutely convergent (`∑_r ‖G(r)‖ < ∞` from integrability of `G`), so the
two summations can be interchanged.
-/

noncomputable section

open MeasureTheory Filter Asymptotics
open scoped FourierTransform Real

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The archimedean Bruhat factor of the polar Gaussian at scale `c`, as a function on `ℝ`. -/
def polarArchimedeanBruhatFactor (L : PositiveDefiniteIntegralLattice n) (c : ℝ) (v : ℝ) : ℂ :=
  (L.polarRealDeterminantScale : ℂ)⁻¹ * (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n

theorem continuous_polarArchimedeanBruhatFactor (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c) :
    Continuous (L.polarArchimedeanBruhatFactor c) :=
  L.continuous_archimedeanBruhatFactor hc

/-- The archimedean factor decays like `|v|^{-n/2}`. -/
theorem polarArchimedeanBruhatFactor_isBigO (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c)
    (hn : 3 ≤ n) :
    L.polarArchimedeanBruhatFactor c =O[cocompact ℝ] (|·| ^ (-((n : ℝ) / 2))) := by
  refine Asymptotics.IsBigO.of_bound
    ((L.polarRealDeterminantScale : ℝ)⁻¹ * (min c 1 / 2) ^ (-((n : ℝ) / 2))) ?_
  filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with w hw
  have hw0 : w ≠ 0 := hw
  have hwpos : 0 < |w| := abs_pos.2 hw0
  rw [polarArchimedeanBruhatFactor, norm_archimedeanBruhatFactor,
    Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg w) _)]
  have hbound := archimedeanBound_le (n := n) hc hn w
  have hmono : (1 + ‖w‖) ^ (-((n : ℝ) / 2)) ≤ |w| ^ (-((n : ℝ) / 2)) := by
    refine Real.rpow_le_rpow_of_nonpos hwpos ?_ ?_
    · rw [Real.norm_eq_abs]; linarith
    · have : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
      linarith
  have hdet : 0 ≤ (L.polarRealDeterminantScale : ℝ)⁻¹ :=
    inv_nonneg.2 L.polarRealDeterminantScale_pos.le
  have hK : 0 ≤ (min c 1 / 2) ^ (-((n : ℝ) / 2)) := by
    have : 0 < min c 1 / 2 := by
      have := lt_min hc zero_lt_one
      linarith
    positivity
  calc (L.polarRealDeterminantScale : ℝ)⁻¹ *
        (Real.sqrt ‖(c : ℂ) - (w : ℂ) * Complex.I‖)⁻¹ ^ n
      ≤ (L.polarRealDeterminantScale : ℝ)⁻¹ *
          ((min c 1 / 2) ^ (-((n : ℝ) / 2)) * (1 + ‖w‖) ^ (-((n : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left hbound hdet
    _ ≤ (L.polarRealDeterminantScale : ℝ)⁻¹ *
          ((min c 1 / 2) ^ (-((n : ℝ) / 2)) * |w| ^ (-((n : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hK) hdet
    _ = _ := by ring

/-- The Fourier transform of the archimedean factor is the archimedean local integral at the
opposite frequency. -/
theorem fourier_polarArchimedeanBruhatFactor_eq_integral (L : PositiveDefiniteIntegralLattice n) (c w : ℝ) :
    𝓕 (L.polarArchimedeanBruhatFactor c) w =
      ∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * ((-w : ℝ) : ℂ) * (v : ℂ)) *
        ((L.polarRealDeterminantScale : ℂ)⁻¹ *
          (1 / ((c : ℂ) - (v : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) ^ n) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
  simp only [smul_eq_mul, polarArchimedeanBruhatFactor]
  congr 2
  push_cast
  ring

/-- At positive frequency the Fourier transform is the closed-form value. -/
theorem fourier_polarArchimedeanBruhatFactor_of_pos (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c)
    (hn : 3 ≤ n) {w : ℝ} (hw : 0 < w) :
    𝓕 (L.polarArchimedeanBruhatFactor c) w =
      (((L.polarRealDeterminantScale : ℝ)⁻¹ *
        ((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) *
        w ^ ((n : ℝ) / 2 - 1) * Real.exp (-(2 * Real.pi * c) * w) : ℝ) : ℂ) := by
  rw [fourier_polarArchimedeanBruhatFactor_eq_integral,
    L.integral_archimedeanBruhatFactor_eq_value hc hn (t := -w) (by linarith), neg_neg]

/-- At nonpositive frequency the Fourier transform vanishes (vanishing at positive parameter
and zero-parameter vanishing). -/
theorem fourier_polarArchimedeanBruhatFactor_of_nonpos (L : PositiveDefiniteIntegralLattice n) {c : ℝ}
    (hc : 0 < c) (hn : 3 ≤ n) {w : ℝ} (hw : w ≤ 0) :
    𝓕 (L.polarArchimedeanBruhatFactor c) w = 0 := by
  rw [fourier_polarArchimedeanBruhatFactor_eq_integral]
  rcases hw.lt_or_eq with hlt | heq
  · exact L.integral_archimedeanBruhatFactor_eq_zero hc hn (by linarith)
  · rw [heq, neg_zero]
    exact L.integral_archimedeanBruhatFactor_zero_eq_zero hc hn

/-- The Fourier transform of the archimedean factor is absolutely summable on `ℤ`. -/
theorem summable_norm_fourier_polarArchimedeanBruhatFactor (L : PositiveDefiniteIntegralLattice n) {c : ℝ}
    (hc : 0 < c) (hn : 3 ≤ n) :
    Summable fun k : ℤ ↦ ‖𝓕 (L.polarArchimedeanBruhatFactor c) k‖ := by
  set K : ℝ := (L.polarRealDeterminantScale : ℝ)⁻¹ *
    ((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) with hKdef
  have hK : 0 ≤ K := by
    have hdet : 0 ≤ (L.polarRealDeterminantScale : ℝ)⁻¹ :=
      inv_nonneg.2 L.polarRealDeterminantScale_pos.le
    have hΓ : 0 < Real.Gamma ((n : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  have ha : 0 < 2 * Real.pi * c := by positivity
  refine Summable.of_nat_of_neg ?_ ?_
  · refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
      ((Real.summable_pow_mul_exp_neg_nat_mul n ha).mul_left K)
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [Int.cast_natCast, Nat.cast_zero,
        L.fourier_polarArchimedeanBruhatFactor_of_nonpos hc hn le_rfl, norm_zero]
      positivity
    · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      rw [Int.cast_natCast, L.fourier_polarArchimedeanBruhatFactor_of_pos hc hn hmpos,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hpow : (m : ℝ) ^ ((n : ℝ) / 2 - 1) ≤ (m : ℝ) ^ n := by
        rw [← Real.rpow_natCast]
        refine Real.rpow_le_rpow_of_exponent_le hm1 ?_
        have : (0 : ℝ) ≤ (n : ℝ) := by positivity
        linarith
      calc K * (m : ℝ) ^ ((n : ℝ) / 2 - 1) * Real.exp (-(2 * Real.pi * c) * m)
          ≤ K * (m : ℝ) ^ n * Real.exp (-(2 * Real.pi * c) * m) := by
            gcongr
        _ = K * ((m : ℝ) ^ n * Real.exp (-(2 * Real.pi * c) * m)) := by ring
  · have hzero : (fun m : ℕ ↦ ‖𝓕 (L.polarArchimedeanBruhatFactor c) ((-(m : ℤ) : ℤ) : ℝ)‖) =
        fun _ ↦ 0 := by
      funext m
      have hm : ((-(m : ℤ) : ℤ) : ℝ) ≤ 0 := by
        push_cast
        exact neg_nonpos.2 (Nat.cast_nonneg m)
      rw [L.fourier_polarArchimedeanBruhatFactor_of_nonpos hc hn hm, norm_zero]
    rw [hzero]
    exact summable_zero

/-- Real Poisson summation for the archimedean factor (Mathlib), at every real translate. -/
theorem tsum_polarArchimedeanBruhatFactor_add_int (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c)
    (hn : 3 ≤ n) (x : ℝ) :
    ∑' m : ℤ, L.polarArchimedeanBruhatFactor c (x + m) =
      ∑' k : ℤ, 𝓕 (L.polarArchimedeanBruhatFactor c) k * fourier k (x : UnitAddCircle) := by
  have hb : 1 < (n : ℝ) / 2 := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (L.continuous_polarArchimedeanBruhatFactor hc) hb (L.polarArchimedeanBruhatFactor_isBigO hc hn)
    (L.summable_norm_fourier_polarArchimedeanBruhatFactor hc hn).of_norm x

/-! ## The canonical splitting `ℚ ≃ (ℚ ∩ [0,1)) × ℤ` -/

/-- The canonical fractional-part/floor splitting of `ℚ`. -/
def rationalFractFloorEquiv : ℚ ≃ RationalFractionalRep × ℤ where
  toFun t := (⟨Int.fract t, Int.fract_fract t⟩, ⌊t⌋)
  invFun p := p.1.1 + p.2
  left_inv t := Int.fract_add_floor t
  right_inv := by
    rintro ⟨⟨r, hr⟩, m⟩
    have h0 : ⌊r⌋ = 0 := by
      have h := hr
      rw [Int.fract] at h
      exact_mod_cast (show ((⌊r⌋ : ℤ) : ℚ) = 0 by linarith)
    refine Prod.ext (Subtype.ext ?_) ?_
    · change Int.fract (r + (m : ℚ)) = r
      rw [Int.fract_add_intCast, hr]
    · change ⌊r + (m : ℚ)⌋ = m
      rw [Int.floor_add_intCast, h0, zero_add]

@[simp]
theorem rationalFractFloorEquiv_symm_apply (p : RationalFractionalRep × ℤ) :
    rationalFractFloorEquiv.symm p = p.1.1 + p.2 :=
  rfl

/-- The finite character at a rational point, as the Poisson exponential. -/
theorem fourier_coe_eq_fourierChar_inv (k : ℤ) (r : ℚ) :
    fourier k ((r : ℝ) : UnitAddCircle) =
      (((Real.fourierChar ((-(k : ℚ) * r : ℚ) : ℝ))⁻¹ : Circle) : ℂ) := by
  rw [fourier_coe_apply, Circle.coe_inv, Real.fourierChar_apply, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-! ## The Eisenstein aggregate at the identity -/

/-- The Bruhat family factors as archimedean factor times finite Gauss integral. -/
theorem rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_eq_archimedean_mul
    (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ)) t =
      L.polarArchimedeanBruhatFactor c (t : ℝ) *
        L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t := by
  rw [RationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_eq_real_mul_finite
      L (by simpa using hc) t,
    RationalQuadraticSpaceMatrix.polarRealGaussianFourierProduct_zero, polarArchimedeanBruhatFactor,
    Complex.ofReal_ratCast]

/-- The value density at an integer frequency is the archimedean Fourier transform times the
finite character sum. -/
theorem complexValueFourierDensity_polarGaussianLattice_intCast_eq (L : PositiveDefiniteIntegralLattice n)
    {c : ℝ} (hc : 0 < c) (hrank : 5 ≤ n) (k : ℤ) :
    L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ))
        (algebraMap ℚ RationalAdele (k : ℚ)) =
      𝓕 (L.polarArchimedeanBruhatFactor c) k *
        ∑' r : RationalFractionalRep,
          fourier k ((r.1 : ℝ) : UnitAddCircle) *
            L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral r.1 := by
  rw [← RationalQuadraticSpaceMatrix.integral_scaledFourierChar_mul_bruhat_eq_complexValueFourierDensity,
    L.integral_scaledChar_mul_adelicBruhat_eq_real_mul_finite (by simpa using hc) (-(k : ℚ)),
    L.integral_finiteLocal_eq_tsum_of_int hrank ⟨-k, by push_cast; rfl⟩,
    integral_archimedeanLocal_eq_real, fourier_polarArchimedeanBruhatFactor_eq_integral]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
    push_cast
    rfl
  · refine tsum_congr fun r ↦ ?_
    rw [fourier_coe_eq_fourierChar_inv]

/-- The value density vanishes at every non-integral rational frequency. -/
theorem complexValueFourierDensity_polarGaussianLattice_eq_zero_of_not_int
    (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c) {b : ℚ} (hb : b ∉ (algebraMap ℤ ℚ).range) :
    L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ))
        (algebraMap ℚ RationalAdele b) = 0 := by
  rw [← RationalQuadraticSpaceMatrix.integral_scaledFourierChar_mul_bruhat_eq_complexValueFourierDensity,
    L.integral_scaledChar_mul_adelicBruhat_eq_real_mul_finite (by simpa using hc) (-b),
    L.integral_finiteLocal_eq_zero_of_not_int hb, mul_zero]

set_option maxHeartbeats 1000000 in
/-- Rank-one adelic Poisson summation for the Bruhat family:
`∑_{t ∈ ℚ} B_Φ(t) = ∑_{k ∈ ℤ} d_Φ(k)`, absolutely convergent on the right. -/
theorem tsum_bruhat_polarGaussianLattice_eq_tsum_int_density (L : PositiveDefiniteIntegralLattice n) {c : ℝ}
    (hc : 0 < c) (hrank : 5 ≤ n) :
    (∑' t : ℚ, L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ)) t) =
      ∑' k : ℤ, L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ))
        (algebraMap ℚ RationalAdele (k : ℚ)) := by
  have hn3 : 3 ≤ n := by omega
  set A := L.polarArchimedeanBruhatFactor c with hAdef
  set G : ℚ → ℂ := fun t ↦
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t with hGdef
  set B : ℚ → ℂ := fun t ↦ L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
    (rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ)) t with hBdef
  have hB : ∀ t, B t = A (t : ℝ) * G t := fun t ↦
    L.rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_eq_archimedean_mul hc t
  have hsumB : Summable B :=
    L.summable_rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_of_rankAtLeastFive hc
      hrank
  have hsumG := L.summable_norm_finiteGaussIntegral_fractionalRep hrank
  have hsumF := L.summable_norm_fourier_polarArchimedeanBruhatFactor hc hn3
  -- split `ℚ` canonically
  have hsplit : ∑' t : ℚ, B t = ∑' r : RationalFractionalRep, ∑' m : ℤ, B (r.1 + m) := by
    rw [← rationalFractFloorEquiv.symm.tsum_eq B]
    have hsum' : Summable fun p : RationalFractionalRep × ℤ ↦ B (rationalFractFloorEquiv.symm p) :=
      (rationalFractFloorEquiv.symm.summable_iff).2 hsumB
    exact hsum'.tsum_prod
  -- periodicity of `G` and real Poisson
  have hinner : ∀ r : RationalFractionalRep, ∑' m : ℤ, B (r.1 + m) =
      ∑' k : ℤ, 𝓕 A k * fourier k ((r.1 : ℝ) : UnitAddCircle) * G r.1 := by
    intro r
    have hper : ∀ m : ℤ, B (r.1 + m) = A ((r.1 : ℝ) + m) * G r.1 := by
      intro m
      rw [hB]
      congr 1
      · push_cast; rfl
      · exact RationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral_add_intCast
          L r.1 m
    simp_rw [hper]
    rw [tsum_mul_right, L.tsum_polarArchimedeanBruhatFactor_add_int hc hn3, tsum_mul_right]
  rw [hsplit, tsum_congr hinner]
  -- absolute convergence of the double series and interchange
  have hnorm : ∀ (r : RationalFractionalRep) (k : ℤ),
      ‖𝓕 A k * fourier k ((r.1 : ℝ) : UnitAddCircle) * G r.1‖ = ‖G r.1‖ * ‖𝓕 A k‖ := by
    intro r k
    rw [norm_mul, norm_mul, fourier_coe_eq_fourierChar_inv, Circle.norm_coe, mul_one, mul_comm]
  have hsum2 : Summable (Function.uncurry fun (r : RationalFractionalRep) (k : ℤ) ↦
      𝓕 A k * fourier k ((r.1 : ℝ) : UnitAddCircle) * G r.1) := by
    refine Summable.of_norm_bounded
      (hsumG.mul_of_nonneg hsumF (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)) ?_
    rintro ⟨r, k⟩
    exact le_of_eq (hnorm r k)
  rw [← hsum2.tsum_comm]
  refine tsum_congr fun k ↦ ?_
  rw [L.complexValueFourierDensity_polarGaussianLattice_intCast_eq hc hrank k, ← tsum_mul_left]
  refine tsum_congr fun r ↦ ?_
  ring

/-- The value densities are absolutely summable over `ℚ`. -/
theorem summable_norm_complexValueFourierDensity_polarGaussianLattice (L : PositiveDefiniteIntegralLattice n)
    {c : ℝ} (hc : 0 < c) (hrank : 5 ≤ n) :
    Summable fun b : ℚ ↦ ‖L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ))
        (algebraMap ℚ RationalAdele b)‖ := by
  have hn3 : 3 ≤ n := by omega
  have hsumG := L.summable_norm_finiteGaussIntegral_fractionalRep hrank
  have hsumF := L.summable_norm_fourier_polarArchimedeanBruhatFactor hc hn3
  have hint : Summable fun k : ℤ ↦ ‖L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
      (rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ))
      (algebraMap ℚ RationalAdele (k : ℚ))‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
      (hsumF.mul_right (∑' r : RationalFractionalRep,
        ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral r.1‖))
    rw [L.complexValueFourierDensity_polarGaussianLattice_intCast_eq hc hrank k, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hterm : ∀ r : RationalFractionalRep,
        ‖fourier k ((r.1 : ℝ) : UnitAddCircle) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral r.1‖ =
        ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral r.1‖ := by
      intro r
      rw [norm_mul, fourier_coe_eq_fourierChar_inv, Circle.norm_coe, one_mul]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hterm))
    exact hsumG.congr fun r ↦ (hterm r).symm
  refine (Int.cast_injective (α := ℚ)).summable_iff ?_ |>.1 hint
  intro b hb
  have hb' : b ∉ (algebraMap ℤ ℚ).range := by
    rintro ⟨k, rfl⟩
    exact hb ⟨k, rfl⟩
  rw [L.complexValueFourierDensity_polarGaussianLattice_eq_zero_of_not_int hc hb', norm_zero]

/-- The Eisenstein aggregate at the identity: for the polar Gaussian--lattice test at positive
scale and rank at least five, `E(Φ) = Φ(0) + ∑_{b ∈ ℚ} d_Φ(b)`. -/
theorem rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice_eq_zero_add_tsum_density
    (L : PositiveDefiniteIntegralLattice n) {c : ℝ} (hc : 0 < c) (hrank : 5 ≤ n) :
    L.rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice hc hrank =
      rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ) 0 +
        ∑' b : ℚ, L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
          (rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ))
          (algebraMap ℚ RationalAdele b) := by
  rw [L.rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice_eq_infinity_add_tsum,
    L.tsum_bruhat_polarGaussianLattice_eq_tsum_int_density hc hrank]
  congr 1
  set D : ℚ → ℂ := fun b ↦ L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
    (rationalAdeleVectorPolarGaussianLatticeTest L (c : ℂ)) (algebraMap ℚ RationalAdele b)
    with hDdef
  change ∑' k : ℤ, D (k : ℚ) = ∑' b : ℚ, D b
  refine Function.Injective.tsum_eq (g := fun k : ℤ ↦ (k : ℚ)) Int.cast_injective ?_
  intro b hb
  by_contra hnot
  have hb' : b ∉ (algebraMap ℤ ℚ).range := by
    rintro ⟨k, rfl⟩
    exact hnot ⟨k, rfl⟩
  exact hb (L.complexValueFourierDensity_polarGaussianLattice_eq_zero_of_not_int hc hb')

end PositiveDefiniteIntegralLattice
