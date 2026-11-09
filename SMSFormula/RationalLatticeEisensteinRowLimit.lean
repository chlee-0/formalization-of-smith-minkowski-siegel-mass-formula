import SMSFormula.RationalLatticeEisensteinRowFourier
import SMSFormula.RationalLatticeCosetGroupedBound
import SMSFormula.RationalLatticeRowKernelZero
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The row limit `H_s → E_row` and its holomorphy

This file supplies the analytic input of the boundary reduction `tendsto_gaussBoundaryAnomaly_and_sLaw`:
`H_s = E_s - y^{-1-s} W_s` converges on the upper half-plane to a holomorphic `E₀`.

* The coset target: `q(adj(S) u) + D² λ = D² (q(ν) + λ)` (`cosetStandardTarget_cast`).
* The row coefficients at a nonzero frequency `m = k + q(ν)` are summable over the rows, with
  `Σ_c ‖B_{c,[u]}(m)‖ ≤ K' √|m|` (`summable_norm_gaussRowCoefficient`), from the sharp coset estimate.
* The dominating function `[m ≠ 0] C |m|⁻² ‖B_{c,[u]}(m)‖` is summable over `(c, k)`.
Nothing is chosen.
-/

noncomputable section

open Matrix Complex Filter Topology SMSFormula.WeightTwoConstantTerm SMSFormula.RowKernel Finset
open scoped FourierTransform

namespace PositiveDefiniteIntegralLattice

/-! ## The coset target -/

section Target

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

theorem polarDualNorm_zero : L.polarDualNorm 0 = 0 := by
  simp [polarDualNorm]

theorem polarDualNorm_gram_mulVec (y : Fin n → ℤ) :
    L.polarDualNorm (L.polarGramMatrix *ᵥ y) = (L.quadForm y : ℝ) := by
  have h := L.polarDualNorm_add_gram 0 y
  rw [zero_add, L.polarDualNorm_zero, zero_add] at h
  rw [h]
  simp

theorem polarDualNorm_smul (a : ℤ) (u : Fin n → ℤ) :
    L.polarDualNorm (a • u) = (a : ℝ) ^ 2 * L.polarDualNorm u := by
  unfold polarDualNorm
  have h : integerVectorReal (a • u) = (a : ℝ) • integerVectorReal u := by
    funext i; simp [integerVectorReal]
  rw [h, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/-- The coset target: `q(adj(S) u) + D² λ = D² (q(ν) + λ)`. -/
theorem cosetStandardTarget_cast (u : Fin n → ℤ) (lam : ℤ) :
    ((L.cosetStandardTarget u lam : ℤ) : ℝ) =
      ((L.polarGramMatrix.det : ℤ) : ℝ) ^ 2 * (L.polarDualNorm u + lam) := by
  unfold cosetStandardTarget
  have hq : ((L.quadForm (L.polarGramMatrix.adjugate *ᵥ u) : ℤ) : ℝ) =
      ((L.polarGramMatrix.det : ℤ) : ℝ) ^ 2 * L.polarDualNorm u := by
    rw [← L.polarDualNorm_gram_mulVec, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, L.polarDualNorm_smul]
  rw [Int.cast_add, Int.cast_mul, Int.cast_pow, hq]
  ring

end Target

variable (L : PositiveDefiniteIntegralLattice 4)

/-! ## The row coefficients at a nonzero frequency -/

/-- `B_{c,[u]}(k + r) = -κ A^{cos}_c(u, k)` for `c ≥ 1`. -/
theorem gaussRowCoefficient_eq_cosetGRCoeff (c : ℕ) [NeZero c] (u : Fin 4 → ℤ) (k : ℤ) :
    L.gaussRowCoefficient c (u : L.PolarDiscriminantGroup) (k + L.polarDualNorm u) =
      -(L.polarKappa : ℂ) * L.cosetGRCoeff u k c := by
  rw [show ((k : ℤ) : ℝ) + L.polarDualNorm u = L.polarDualNorm u + ((k : ℤ) : ℝ) from add_comm _ _,
    L.gaussRowCoefficient_eq c u k, L.cosetGRCoeff_eq_cosetGaussRamanujanCoefficient]

theorem cosetStandardTarget_ne_zero (u : Fin 4 → ℤ) (k : ℤ) (hm : (k : ℝ) + L.polarDualNorm u ≠ 0) :
    L.cosetStandardTarget u k ≠ 0 := by
  have hD : ((L.polarGramMatrix.det : ℤ) : ℝ) ≠ 0 := by exact_mod_cast L.polarGramMatrix_det_ne_zero
  intro h
  have h1 := L.cosetStandardTarget_cast u k
  rw [h, Int.cast_zero] at h1
  have h2 : ((L.polarGramMatrix.det : ℤ) : ℝ) ^ 2 * (L.polarDualNorm u + k) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hD) (by rw [add_comm]; exact hm)
  exact h2 h1.symm

theorem sqrt_natAbs_cosetStandardTarget (u : Fin 4 → ℤ) (k : ℤ) :
    Real.sqrt ((L.cosetStandardTarget u k).natAbs : ℝ) =
      |((L.polarGramMatrix.det : ℤ) : ℝ)| * Real.sqrt |(k : ℝ) + L.polarDualNorm u| := by
  have h1 : ((L.cosetStandardTarget u k).natAbs : ℝ) = |((L.cosetStandardTarget u k : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h1, L.cosetStandardTarget_cast, abs_mul, abs_pow, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (abs_nonneg _), add_comm (L.polarDualNorm u)]

theorem norm_gaussRowCoefficient_succ (u : Fin 4 → ℤ) (k : ℤ) (j : ℕ) :
    ‖L.gaussRowCoefficient (j + 1) (u : L.PolarDiscriminantGroup) (k + L.polarDualNorm u)‖ =
      L.polarKappa * ‖L.cosetGRCoeff u k (j + 1)‖ := by
  rw [L.gaussRowCoefficient_eq_cosetGRCoeff (j + 1) u k, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg L.polarKappa_pos.le]

/-- The row sum at a nonzero frequency: `Σ_{c ≥ 1} ‖B_{c,[u]}(m)‖ ≤ K' √|m|`. -/
theorem exists_summable_norm_gaussRowCoefficient :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ (u : Fin 4 → ℤ) (k : ℤ), (k : ℝ) + L.polarDualNorm u ≠ 0 →
      Summable (fun j : ℕ ↦ ‖L.gaussRowCoefficient (j + 1) (u : L.PolarDiscriminantGroup)
        (k + L.polarDualNorm u)‖) ∧
      ∑' j : ℕ, ‖L.gaussRowCoefficient (j + 1) (u : L.PolarDiscriminantGroup) (k + L.polarDualNorm u)‖ ≤
        K' * Real.sqrt |(k : ℝ) + L.polarDualNorm u| := by
  obtain ⟨K, hK0, hK⟩ := L.exists_summable_norm_cosetGRCoeff_le_sqrt
  have hκ := L.polarKappa_pos
  refine ⟨L.polarKappa * K * |((L.polarGramMatrix.det : ℤ) : ℝ)|,
    mul_nonneg (mul_nonneg hκ.le hK0.le) (abs_nonneg _), fun u k hm ↦ ?_⟩
  have hM := L.cosetStandardTarget_ne_zero u k hm
  have hs := (hK u k hM).1
  have hle := (hK u k hM).2
  have hs1 : Summable fun j : ℕ ↦ ‖L.cosetGRCoeff u k (j + 1)‖ :=
    (summable_nat_add_iff (f := fun c ↦ ‖L.cosetGRCoeff u k c‖) 1).2 hs
  have hle1 : ∑' j : ℕ, ‖L.cosetGRCoeff u k (j + 1)‖ ≤ ∑' c : ℕ, ‖L.cosetGRCoeff u k c‖ := by
    rw [hs.tsum_eq_zero_add, L.cosetGRCoeff_zero u k, norm_zero, zero_add]
  simp_rw [L.norm_gaussRowCoefficient_succ u k]
  refine ⟨hs1.mul_left _, ?_⟩
  rw [tsum_mul_left]
  calc L.polarKappa * ∑' j : ℕ, ‖L.cosetGRCoeff u k (j + 1)‖
      ≤ L.polarKappa * (K * Real.sqrt ((L.cosetStandardTarget u k).natAbs : ℝ)) :=
        mul_le_mul_of_nonneg_left (hle1.trans hle) hκ.le
    _ = _ := by rw [L.sqrt_natAbs_cosetStandardTarget]; ring

/-! ## The dominating function -/

/-- The dominating function `G(j, k) = [m ≠ 0] C |m|⁻² ‖B_{j+1,[u]}(m)‖`, `m = k + q(ν)`. -/
def rowMajorant (C : ℝ) (u : Fin 4 → ℤ) (p : ℕ × ℤ) : ℝ :=
  if (p.2 : ℝ) + L.polarDualNorm u = 0 then 0 else
    C / |(p.2 : ℝ) + L.polarDualNorm u| ^ 2 *
      ‖L.gaussRowCoefficient (p.1 + 1) (u : L.PolarDiscriminantGroup) (p.2 + L.polarDualNorm u)‖

theorem rowMajorant_nonneg {C : ℝ} (hC : 0 ≤ C) (u : Fin 4 → ℤ) (p : ℕ × ℤ) :
    0 ≤ L.rowMajorant C u p := by
  unfold rowMajorant
  split_ifs
  · exact le_rfl
  · positivity

theorem sqrt_div_sq_eq {m : ℝ} (hm : m ≠ 0) :
    Real.sqrt |m| / |m| ^ 2 = 1 / |m| ^ (3 / 2 : ℝ) := by
  have hpos : 0 < |m| := abs_pos.2 hm
  rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_sub hpos,
    show (1 / 2 : ℝ) - 2 = -(3 / 2) by norm_num, Real.rpow_neg hpos.le, one_div]

/-- The dominating function is summable over `(row, frequency)`. -/
theorem summable_rowMajorant {C : ℝ} (hC : 0 ≤ C) (u : Fin 4 → ℤ) :
    Summable (L.rowMajorant C u) := by
  obtain ⟨K', hK'0, hK'⟩ := L.exists_summable_norm_gaussRowCoefficient
  set r := L.polarDualNorm u with hr
  rw [← (Equiv.prodComm ℤ ℕ).summable_iff]
  have hnn : 0 ≤ L.rowMajorant C u ∘ (Equiv.prodComm ℤ ℕ) :=
    fun p ↦ L.rowMajorant_nonneg hC u _
  refine (summable_prod_of_nonneg hnn).2 ⟨fun k ↦ ?_, ?_⟩
  · by_cases hm : (k : ℝ) + r = 0
    · simp only [Function.comp_def, Equiv.prodComm_apply, Prod.swap_prod_mk, rowMajorant, hr] at hm ⊢
      simp only [hm, if_true]
      exact summable_zero
    · simp only [Function.comp_def, Equiv.prodComm_apply, Prod.swap_prod_mk, rowMajorant]
      rw [← hr]
      simp only [hm, if_false]
      exact ((hK' u k hm).1).mul_left _
  · refine Summable.of_nonneg_of_le (fun k ↦ tsum_nonneg fun j ↦ hnn (k, j)) (fun k ↦ ?_)
      (((Real.summable_one_div_int_add_rpow r (3 / 2)).2 (by norm_num)).mul_left (C * K'))
    by_cases hm : (k : ℝ) + r = 0
    · simp only [Function.comp_def, Equiv.prodComm_apply, Prod.swap_prod_mk, rowMajorant]
      rw [← hr]
      simp only [hm, if_true, tsum_zero]
      positivity
    · simp only [Function.comp_def, Equiv.prodComm_apply, Prod.swap_prod_mk, rowMajorant]
      rw [← hr]
      simp only [hm, if_false]
      rw [tsum_mul_left]
      calc C / |(k : ℝ) + r| ^ 2 * ∑' j : ℕ, ‖L.gaussRowCoefficient (j + 1)
            (u : L.PolarDiscriminantGroup) (k + r)‖
          ≤ C / |(k : ℝ) + r| ^ 2 * (K' * Real.sqrt |(k : ℝ) + r|) :=
            mul_le_mul_of_nonneg_left ((hK' u k hm).2) (by positivity)
        _ = C * K' * (1 / |(k : ℝ) + r| ^ (3 / 2 : ℝ)) := by
            rw [← sqrt_div_sq_eq hm]; ring

/-! ## Coordinates of the rows, the zero mode and the anomaly -/

theorem summable_regEisRow_succ {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ upperHalfSet) :
    Summable fun n : ℕ ↦ L.regEisRow s z ((n : ℤ) + 1) :=
  (L.summable_regEisSummand_prod hs hz).prod.comp_injective fun a b h ↦ by simpa using h

/-- `‖B_{c,a}(m)‖ ≤ 1` for `c ≥ 1`. -/
theorem norm_gaussRowCoefficient_le_one (c : ℕ) [NeZero c] (a : L.PolarDiscriminantGroup) (m : ℝ) :
    ‖L.gaussRowCoefficient c a m‖ ≤ 1 := by
  have hc : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  unfold gaussRowCoefficient
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hsum : ‖∑ j ∈ (range c).filter (fun j ↦ c.Coprime j),
      L.gaussColumn (c : ℤ) j a * exp (2 * Real.pi * I * (m : ℂ) * (j : ℂ) / (c : ℂ))‖ ≤ c.totient := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ (range c).filter (fun j ↦ c.Coprime j),
          ‖L.gaussColumn (c : ℤ) j a * exp (2 * Real.pi * I * (m : ℂ) * (j : ℂ) / (c : ℂ))‖
        ≤ ∑ j ∈ (range c).filter (fun j ↦ c.Coprime j), (1 : ℝ) := by
          refine sum_le_sum fun j hj ↦ ?_
          rw [norm_mul]
          have h1 := L.norm_gaussColumn_apply_le (Nat.isCoprime_iff_coprime.2 (mem_filter.1 hj).2) a
          have h2 : ‖exp (2 * Real.pi * I * (m : ℂ) * (j : ℂ) / (c : ℂ))‖ = 1 := by
            rw [show 2 * (Real.pi : ℂ) * I * (m : ℂ) * (j : ℂ) / (c : ℂ) =
              2 * Real.pi * I * ((m * j / c : ℝ) : ℂ) by push_cast; ring]
            exact norm_exp_two_pi_I_mul_real _
          rw [h2, mul_one]
          exact h1
      _ = c.totient := by rw [sum_const, nsmul_eq_mul, mul_one, Nat.totient_eq_card_coprime]
  have htot : (c.totient : ℝ) ≤ c := by exact_mod_cast Nat.totient_le c
  calc ((c : ℝ) ^ 2)⁻¹ * _ ≤ ((c : ℝ) ^ 2)⁻¹ * (c.totient : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((c : ℝ) ^ 2)⁻¹ * (c : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (htot.trans ?_) (by positivity)
        nlinarith [show (1 : ℝ) ≤ c by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)]
    _ = 1 := inv_mul_cancel₀ (by positivity)

/-- The zero frequency of the kernel: `ĥ_{s,y}(0) = -κ(s) y^{-1-2s}`. -/
theorem fourier_rowKernel_zero_freq {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) :
    𝓕 (rowKernel s y) 0 = -((zeroModeKappa s : ℝ) : ℂ) * ((y ^ (-1 - 2 * s) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
  exact integral_rowKernel hs hy

/-- The zero frequency occurs exactly when `e(q(ν)) = 1`. -/
theorem tsum_ite_zero_freq (u : Fin 4 → ℤ) (G : ℝ → ℂ) :
    ∑' k : ℤ, (if (k : ℝ) + L.polarDualNorm u = 0 then G ((k : ℝ) + L.polarDualNorm u) else 0) =
      if L.polarDiscNormChar (u : L.PolarDiscriminantGroup) = 1 then G 0 else 0 := by
  rw [polarDiscNormChar_coe]
  split_ifs with h
  · obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
    have hr : L.polarDualNorm u = n := by
      have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      have : ((L.polarDualNorm u : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
        apply mul_left_cancel₀ hpi
        rw [hn]; push_cast; ring
      exact_mod_cast this
    have hiff : ∀ k : ℤ, ((k : ℝ) + L.polarDualNorm u = 0) ↔ k = -n := by
      intro k
      rw [hr]
      constructor
      · intro h'; have : ((k + n : ℤ) : ℝ) = 0 := by push_cast; exact h'
        have := Int.cast_eq_zero.1 this; omega
      · rintro rfl; push_cast; ring
    have hG : ∀ k : ℤ, (if (k : ℝ) + L.polarDualNorm u = 0 then G ((k : ℝ) + L.polarDualNorm u) else 0) =
        if k = -n then G 0 else 0 := by
      intro k
      by_cases hk : k = -n
      · rw [if_pos ((hiff k).2 hk), if_pos hk, (hiff k).2 hk]
      · rw [if_neg (fun h' ↦ hk ((hiff k).1 h')), if_neg hk]
    simp_rw [hG]
    exact tsum_ite_eq (-n) (fun _ : ℤ ↦ G 0)
  · have hne : ∀ k : ℤ, (k : ℝ) + L.polarDualNorm u ≠ 0 := by
      intro k hk
      apply h
      have hr : L.polarDualNorm u = ((-k : ℤ) : ℝ) := by push_cast; linarith
      rw [hr, Complex.ofReal_intCast]
      exact exp_two_pi_I_intCast (-k)
    simp only [hne, if_false, tsum_zero]

/-- `b_c[u] = [e(q(ν)) = 1] B_{c,[u]}(0)`. -/
theorem gaussBoundaryRowVector_apply (c : ℕ) (u : Fin 4 → ℤ) :
    L.gaussBoundaryRowVector c (u : L.PolarDiscriminantGroup) =
      if L.polarDiscNormChar (u : L.PolarDiscriminantGroup) = 1 then
        L.gaussRowCoefficient c (u : L.PolarDiscriminantGroup) 0 else 0 := by
  unfold gaussBoundaryRowVector gaussRowCoefficient
  rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  unfold gaussPi0
  split_ifs with h
  · congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    simp
  · simp

/-- `W_s[u] = -κ(s) Σ_{n ≥ 0} (n+1)^{-2s} b_{n+1}[u]`. -/
theorem gaussBoundaryAnomaly_apply {s : ℝ} (hs : 0 < s) (u : Fin 4 → ℤ) :
    L.gaussBoundaryAnomaly s (u : L.PolarDiscriminantGroup) =
      -((zeroModeKappa s : ℝ) : ℂ) * ∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) ^ (-2 * s) : ℝ) : ℂ) *
        L.gaussBoundaryRowVector (n + 1) (u : L.PolarDiscriminantGroup) := by
  unfold gaussBoundaryAnomaly
  have hsum := L.summable_anomalyTerm hs
  rw [Pi.smul_apply, smul_eq_mul, tsum_apply hsum]
  have hsum' : Summable fun c : ℕ ↦ ((((c : ℝ) ^ (-2 * s) : ℝ) : ℂ) • L.gaussBoundaryRowVector c)
      (u : L.PolarDiscriminantGroup) := Pi.summable.1 hsum _
  rw [hsum'.tsum_eq_zero_add]
  have h0 : L.gaussBoundaryRowVector 0 = 0 := by simp [gaussBoundaryRowVector]
  simp only [h0, Pi.zero_apply, mul_zero, zero_add, Pi.smul_apply, smul_eq_mul]

/-! ## The regularized coordinate as a double series -/

/-- The row term `f_s(n, k) = y^s (n+1)^{-2s} [m ≠ 0] ĥ_{s,y}(m) e(mx) B_{n+1,[u]}(m)`, `m = k + q(ν)`. -/
def rowTerm (s : ℝ) (z : ℂ) (u : Fin 4 → ℤ) (p : ℕ × ℤ) : ℂ :=
  ((z.im ^ s * (((p.1 + 1 : ℕ) : ℝ) ^ 2) ^ (-s) : ℝ) : ℂ) *
    (if (p.2 : ℝ) + L.polarDualNorm u = 0 then 0 else
      𝓕 (rowKernel s z.im) (p.2 + L.polarDualNorm u) *
        exp (2 * Real.pi * I * ((p.2 + L.polarDualNorm u : ℝ) : ℂ) * z.re) *
        L.gaussRowCoefficient (p.1 + 1) (u : L.PolarDiscriminantGroup) (p.2 + L.polarDualNorm u))

theorem norm_exp_two_pi_I_mul_mul_real (a b : ℝ) :
    ‖exp (2 * Real.pi * I * (a : ℂ) * (b : ℂ))‖ = 1 := by
  rw [show 2 * (Real.pi : ℂ) * I * (a : ℂ) * (b : ℂ) = 2 * Real.pi * I * ((a * b : ℝ) : ℂ) by
    push_cast; ring]
  exact norm_exp_two_pi_I_mul_real _

theorem rowKernelDecay_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ rowKernelDecay y := by
  unfold rowKernelDecay
  have : 0 ≤ ∫ t : ℝ, (t ^ 2 + y ^ 2)⁻¹ :=
    MeasureTheory.integral_nonneg fun t ↦ inv_nonneg.2 (sq_add_sq_pos hy t).le
  positivity

/-- The domination `‖f_s(n,k)‖ ≤ (1 + y) G(n,k)` for `0 ≤ s ≤ 1`, with `C = K_y/(4π²)`. -/
theorem norm_rowTerm_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z : ℂ} (hz : z ∈ upperHalfSet)
    (u : Fin 4 → ℤ) (p : ℕ × ℤ) :
    ‖L.rowTerm s z u p‖ ≤
      (1 + z.im) * L.rowMajorant (rowKernelDecay z.im / (4 * Real.pi ^ 2)) u p := by
  have hy : 0 < z.im := hz
  unfold rowTerm rowMajorant
  have hys : z.im ^ s ≤ 1 + z.im := rpow_le_one_add hy.le hs0 hs1
  have hcs : (((p.1 + 1 : ℕ) : ℝ) ^ 2) ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; nlinarith [Nat.zero_le p.1]) (by linarith)
  have hα0 : 0 ≤ z.im ^ s * (((p.1 + 1 : ℕ) : ℝ) ^ 2) ^ (-s) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hα0]
  split_ifs with hm
  · rw [norm_zero, mul_zero, mul_zero]
  · rw [norm_mul, norm_mul, norm_exp_two_pi_I_mul_mul_real, mul_one]
    have hF := norm_fourier_rowKernel_le_of_ne hs0 hs1 hy hm
    rw [Real.rpow_two] at hF
    have hB := norm_nonneg (L.gaussRowCoefficient (p.1 + 1) (u : L.PolarDiscriminantGroup)
      (p.2 + L.polarDualNorm u))
    calc z.im ^ s * (((p.1 + 1 : ℕ) : ℝ) ^ 2) ^ (-s) *
          (‖𝓕 (rowKernel s z.im) (p.2 + L.polarDualNorm u)‖ *
            ‖L.gaussRowCoefficient (p.1 + 1) (u : L.PolarDiscriminantGroup) (p.2 + L.polarDualNorm u)‖)
        ≤ (1 + z.im) * 1 * (rowKernelDecay z.im / (4 * Real.pi ^ 2) *
            (1 / |(p.2 : ℝ) + L.polarDualNorm u| ^ 2) *
            ‖L.gaussRowCoefficient (p.1 + 1) (u : L.PolarDiscriminantGroup) (p.2 + L.polarDualNorm u)‖) := by
          gcongr
      _ = _ := by ring

theorem summable_rowTerm {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z : ℂ} (hz : z ∈ upperHalfSet)
    (u : Fin 4 → ℤ) : Summable (L.rowTerm s z u) := by
  have hy : 0 < z.im := hz
  have hK : 0 ≤ rowKernelDecay z.im / (4 * Real.pi ^ 2) :=
    div_nonneg (rowKernelDecay_nonneg hy) (by positivity)
  exact Summable.of_norm_bounded ((L.summable_rowMajorant hK u).mul_left (1 + z.im))
    (L.norm_rowTerm_le hs0 hs1 hz u)

/-- The row `n + 1` in the coordinate `[u]`. -/
theorem regEisRow_succ_apply {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {z : ℂ} (hz : z ∈ upperHalfSet)
    (n : ℕ) (u : Fin 4 → ℤ) :
    L.regEisRow s z ((n : ℤ) + 1) (u : L.PolarDiscriminantGroup) =
      ((z.im ^ s * (((n + 1 : ℕ) : ℝ) ^ 2) ^ (-s) : ℝ) : ℂ) *
        ∑' k : ℤ, 𝓕 (rowKernel s z.im) (k + L.polarDualNorm u) *
          exp (2 * Real.pi * I * ((k + L.polarDualNorm u : ℝ) : ℂ) * z.re) *
          L.gaussRowCoefficient (n + 1) (u : L.PolarDiscriminantGroup) (k + L.polarDualNorm u) := by
  rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring]
  exact L.regEisRow_apply_fourier hs hs1 hz (n + 1) u

/-- The frequency series of a row splits into the nonzero frequencies and the zero mode. -/
theorem tsum_rowFourier_split {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z : ℂ} (hz : z ∈ upperHalfSet)
    (n : ℕ) (u : Fin 4 → ℤ) :
    ∑' k : ℤ, 𝓕 (rowKernel s z.im) (k + L.polarDualNorm u) *
        exp (2 * Real.pi * I * ((k + L.polarDualNorm u : ℝ) : ℂ) * z.re) *
        L.gaussRowCoefficient (n + 1) (u : L.PolarDiscriminantGroup) (k + L.polarDualNorm u) =
      ∑' k : ℤ, (if (k : ℝ) + L.polarDualNorm u = 0 then 0 else
        𝓕 (rowKernel s z.im) (k + L.polarDualNorm u) *
          exp (2 * Real.pi * I * ((k + L.polarDualNorm u : ℝ) : ℂ) * z.re) *
          L.gaussRowCoefficient (n + 1) (u : L.PolarDiscriminantGroup) (k + L.polarDualNorm u)) +
      𝓕 (rowKernel s z.im) 0 * L.gaussBoundaryRowVector (n + 1) (u : L.PolarDiscriminantGroup) := by
  have hy : 0 < z.im := hz
  set r := L.polarDualNorm u with hr
  set G : ℝ → ℂ := fun m ↦ 𝓕 (rowKernel s z.im) m * exp (2 * Real.pi * I * (m : ℂ) * z.re) *
    L.gaussRowCoefficient (n + 1) (u : L.PolarDiscriminantGroup) m with hG
  have hT : ∀ k : ℤ, 𝓕 (rowKernel s z.im) (k + r) *
      exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * z.re) *
      L.gaussRowCoefficient (n + 1) (u : L.PolarDiscriminantGroup) (k + r) = G ((k : ℝ) + r) := fun k ↦ rfl
  simp_rw [hT]
  have hnormG : ∀ k : ℤ, ‖G ((k : ℝ) + r)‖ ≤ ‖𝓕 (rowKernel s z.im) (k + r)‖ := by
    intro k
    rw [hG]
    simp only
    rw [norm_mul, norm_mul, norm_exp_two_pi_I_mul_mul_real, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (L.norm_gaussRowCoefficient_le_one (n + 1) _ _)
  have hsumG : Summable fun k : ℤ ↦ G ((k : ℝ) + r) :=
    Summable.of_norm_bounded (summable_norm_fourier_rowKernel_add hs0 hs1 hy r) hnormG
  have h1 : Summable fun k : ℤ ↦ (if (k : ℝ) + r = 0 then 0 else G ((k : ℝ) + r)) :=
    Summable.of_norm_bounded (summable_norm_fourier_rowKernel_add hs0 hs1 hy r) fun k ↦ by
      split_ifs
      · rw [norm_zero]; exact norm_nonneg _
      · exact hnormG k
  have h2 : Summable fun k : ℤ ↦ (if (k : ℝ) + r = 0 then G ((k : ℝ) + r) else 0) :=
    Summable.of_norm_bounded (summable_norm_fourier_rowKernel_add hs0 hs1 hy r) fun k ↦ by
      split_ifs
      · exact hnormG k
      · rw [norm_zero]; exact norm_nonneg _
  have hsplit : ∀ k : ℤ, G ((k : ℝ) + r) = (if (k : ℝ) + r = 0 then 0 else G ((k : ℝ) + r)) +
      (if (k : ℝ) + r = 0 then G ((k : ℝ) + r) else 0) := by
    intro k; split_ifs <;> simp
  rw [tsum_congr hsplit, h1.tsum_add h2, hr, L.tsum_ite_zero_freq u G, ← hr]
  congr 1
  rw [L.gaussBoundaryRowVector_apply]
  split_ifs
  · rw [hG]; simp
  · rw [mul_zero]

/-- The regularized coordinate as a double series:
`(E_s - y^{-1-s} W_s)(z)_{[u]} = y^s e₀[u] + Σ_{(n,k)} f_s(n,k)`. -/
theorem regEisenstein_sub_anomaly_apply {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {z : ℂ}
    (hz : z ∈ upperHalfSet) (u : Fin 4 → ℤ) :
    (L.regEisenstein s z - (((z.im ^ (-1 - s) : ℝ)) : ℂ) • L.gaussBoundaryAnomaly s)
        (u : L.PolarDiscriminantGroup) =
      ((z.im ^ s : ℝ) : ℂ) * L.gaussE0 (u : L.PolarDiscriminantGroup) + ∑' p, L.rowTerm s z u p := by
  have hy : 0 < z.im := hz
  set r := L.polarDualNorm u with hr
  rw [Pi.sub_apply, L.regEisenstein_eq_rows hs hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    tsum_apply (L.summable_regEisRow_succ hs hz), Pi.smul_apply, smul_eq_mul,
    L.gaussBoundaryAnomaly_apply hs]
  simp_rw [L.regEisRow_succ_apply hs hs1 hz, L.tsum_rowFourier_split hs.le hs1 hz, mul_add]
  -- the zero modes reassemble `y^{-1-s} W_s`
  have hzero : ∀ n : ℕ, ((z.im ^ s * (((n + 1 : ℕ) : ℝ) ^ 2) ^ (-s) : ℝ) : ℂ) *
      (𝓕 (rowKernel s z.im) 0 * L.gaussBoundaryRowVector (n + 1) (u : L.PolarDiscriminantGroup)) =
      ((z.im ^ (-1 - s) : ℝ) : ℂ) * (-((zeroModeKappa s : ℝ) : ℂ)) *
        (((((n + 1 : ℕ) : ℝ) ^ (-2 * s) : ℝ) : ℂ) *
          L.gaussBoundaryRowVector (n + 1) (u : L.PolarDiscriminantGroup)) := by
    intro n
    rw [fourier_rowKernel_zero_freq hs.le hy]
    have hc : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (((n + 1 : ℕ) : ℝ) ^ 2) ^ (-s) = ((n + 1 : ℕ) : ℝ) ^ (-2 * s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc]; ring_nf
    have h2 : z.im ^ s * z.im ^ (-1 - 2 * s) = z.im ^ (-1 - s) := by
      rw [← Real.rpow_add hy]; ring_nf
    rw [h1]
    have h3 : ((z.im ^ s * ((n + 1 : ℕ) : ℝ) ^ (-2 * s) : ℝ) : ℂ) * ((z.im ^ (-1 - 2 * s) : ℝ) : ℂ) =
        ((z.im ^ (-1 - s) : ℝ) : ℂ) * ((((n + 1 : ℕ) : ℝ) ^ (-2 * s) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← h2]; ring_nf
    linear_combination (-((zeroModeKappa s : ℝ) : ℂ) *
      L.gaussBoundaryRowVector (n + 1) (u : L.PolarDiscriminantGroup)) * h3
  simp_rw [hzero]
  have hsA : Summable fun n : ℕ ↦ ((z.im ^ s * (((n + 1 : ℕ) : ℝ) ^ 2) ^ (-s) : ℝ) : ℂ) *
      ∑' k : ℤ, (if (k : ℝ) + r = 0 then 0 else
        𝓕 (rowKernel s z.im) (k + r) * exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * z.re) *
          L.gaussRowCoefficient (n + 1) (u : L.PolarDiscriminantGroup) (k + r)) := by
    have := (L.summable_rowTerm hs.le hs1 hz u).prod
    refine this.congr fun n ↦ ?_
    unfold rowTerm
    dsimp only
    rw [tsum_mul_left]
  have hsW : Summable fun n : ℕ ↦ ((z.im ^ (-1 - s) : ℝ) : ℂ) * (-((zeroModeKappa s : ℝ) : ℂ)) *
      (((((n + 1 : ℕ) : ℝ) ^ (-2 * s) : ℝ) : ℂ) *
        L.gaussBoundaryRowVector (n + 1) (u : L.PolarDiscriminantGroup)) := by
    have h := Pi.summable.1 (L.summable_anomalyTerm hs) (u : L.PolarDiscriminantGroup)
    have h' := (summable_nat_add_iff (f := fun c : ℕ ↦ ((((c : ℝ) ^ (-2 * s) : ℝ) : ℂ) •
      L.gaussBoundaryRowVector c) (u : L.PolarDiscriminantGroup)) 1).2 h
    refine (h'.mul_left (((z.im ^ (-1 - s) : ℝ) : ℂ) * (-((zeroModeKappa s : ℝ) : ℂ)))).congr fun n ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsA.tsum_add hsW, tsum_mul_left]
  have hrow : ∑' n : ℕ, ((z.im ^ s * (((n + 1 : ℕ) : ℝ) ^ 2) ^ (-s) : ℝ) : ℂ) *
      ∑' k : ℤ, (if (k : ℝ) + r = 0 then 0 else
        𝓕 (rowKernel s z.im) (k + r) * exp (2 * Real.pi * I * ((k + r : ℝ) : ℂ) * z.re) *
          L.gaussRowCoefficient (n + 1) (u : L.PolarDiscriminantGroup) (k + r)) =
      ∑' p, L.rowTerm s z u p := by
    rw [(L.summable_rowTerm hs.le hs1 hz u).tsum_prod]
    refine tsum_congr fun n ↦ ?_
    unfold rowTerm
    dsimp only
    rw [tsum_mul_left]
  rw [hrow]
  ring

/-! ## The limit `s → 0⁺` -/

theorem tendsto_rpow_const_nhdsGT {a : ℝ} (ha : 0 < a) :
    Tendsto (fun s : ℝ ↦ a ^ s) (𝓝[>] 0) (𝓝 1) := by
  have h := ((Real.continuousAt_const_rpow ha.ne' (b := 0)).tendsto).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa using h

theorem tendsto_rpow_neg_const_nhdsGT {a : ℝ} (ha : 0 < a) :
    Tendsto (fun s : ℝ ↦ a ^ (-s)) (𝓝[>] 0) (𝓝 1) := by
  have hn : Tendsto (fun s : ℝ ↦ -s) (𝓝 0) (𝓝 0) := by simpa using (continuous_neg.tendsto (0 : ℝ))
  have h := ((Real.continuousAt_const_rpow ha.ne' (b := 0)).tendsto.comp hn).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa [Function.comp_def] using h

/-- Each row term converges as `s → 0⁺`. -/
theorem tendsto_rowTerm {z : ℂ} (hz : z ∈ upperHalfSet) (u : Fin 4 → ℤ) (p : ℕ × ℤ) :
    Tendsto (fun s ↦ L.rowTerm s z u p) (𝓝[>] 0) (𝓝 (L.rowTerm 0 z u p)) := by
  have hy : 0 < z.im := hz
  unfold rowTerm
  have hα : Tendsto (fun s : ℝ ↦ ((z.im ^ s * (((p.1 + 1 : ℕ) : ℝ) ^ 2) ^ (-s) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((z.im ^ (0 : ℝ) * (((p.1 + 1 : ℕ) : ℝ) ^ 2) ^ (-(0 : ℝ)) : ℝ) : ℂ)) := by
    have h1 := tendsto_rpow_const_nhdsGT hy
    have h2 := tendsto_rpow_neg_const_nhdsGT (a := (((p.1 + 1 : ℕ) : ℝ) ^ 2)) (by positivity)
    have h3 := (Complex.continuous_ofReal.tendsto _).comp (h1.mul h2)
    simpa [Function.comp_def] using h3
  refine hα.mul ?_
  split_ifs with hm
  · exact tendsto_const_nhds
  · exact ((tendsto_fourier_rowKernel hy _).mul_const _).mul_const _

/-- The limit `s → 0⁺` of the regularized coordinate. -/
theorem tendsto_regEisenstein_sub_anomaly_apply {z : ℂ} (hz : z ∈ upperHalfSet) (u : Fin 4 → ℤ) :
    Tendsto (fun s ↦ (L.regEisenstein s z - (((z.im ^ (-1 - s) : ℝ)) : ℂ) • L.gaussBoundaryAnomaly s)
        (u : L.PolarDiscriminantGroup)) (𝓝[>] 0)
      (𝓝 (L.gaussE0 (u : L.PolarDiscriminantGroup) + ∑' p, L.rowTerm 0 z u p)) := by
  have hy : 0 < z.im := hz
  have hK : 0 ≤ rowKernelDecay z.im / (4 * Real.pi ^ 2) :=
    div_nonneg (rowKernelDecay_nonneg hy) (by positivity)
  have hT : Tendsto (fun s ↦ ∑' p, L.rowTerm s z u p) (𝓝[>] 0) (𝓝 (∑' p, L.rowTerm 0 z u p)) := by
    refine tendsto_tsum_of_dominated_convergence ((L.summable_rowMajorant hK u).mul_left (1 + z.im))
      (L.tendsto_rowTerm hz u) ?_
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
    exact L.norm_rowTerm_le hs.1.le hs.2.le hz u
  have hE : Tendsto (fun s : ℝ ↦ ((z.im ^ s : ℝ) : ℂ) * L.gaussE0 (u : L.PolarDiscriminantGroup)) (𝓝[>] 0)
      (𝓝 (L.gaussE0 (u : L.PolarDiscriminantGroup))) := by
    have h := ((Complex.continuous_ofReal.tendsto _).comp (tendsto_rpow_const_nhdsGT hy)).mul_const
      (L.gaussE0 (u : L.PolarDiscriminantGroup))
    simpa [Function.comp_def] using h
  refine (hE.add hT).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
  exact (L.regEisenstein_sub_anomaly_apply hs.1 hs.2.le hz u).symm

/-! ## The explicit q-expansion of the limit and its holomorphy -/

/-- The limit term `[m > 0] (-4π² m) e(mz) B_{n+1,[u]}(m)`, `m = k + q(ν)`. -/
def rowLimitTerm (u : Fin 4 → ℤ) (z : ℂ) (p : ℕ × ℤ) : ℂ :=
  if 0 < (p.2 : ℝ) + L.polarDualNorm u then
    -(4 * Real.pi ^ 2 * (((p.2 : ℝ) + L.polarDualNorm u : ℝ) : ℂ)) *
      exp (2 * Real.pi * I * (((p.2 : ℝ) + L.polarDualNorm u : ℝ) : ℂ) * z) *
      L.gaussRowCoefficient (p.1 + 1) (u : L.PolarDiscriminantGroup) (p.2 + L.polarDualNorm u)
  else 0

theorem rowTerm_zero_eq_rowLimitTerm {z : ℂ} (hz : z ∈ upperHalfSet) (u : Fin 4 → ℤ) (p : ℕ × ℤ) :
    L.rowTerm 0 z u p = L.rowLimitTerm u z p := by
  have hy : 0 < z.im := hz
  unfold rowTerm rowLimitTerm
  simp only [Real.rpow_zero, neg_zero, mul_one, Complex.ofReal_one, one_mul]
  set m : ℝ := (p.2 : ℝ) + L.polarDualNorm u with hm
  rcases lt_trichotomy m 0 with h | h | h
  · rw [if_neg h.ne, if_neg (not_lt.2 h.le), L.fourier_rowKernel_zero_of_nonpos hy h.le]
    ring
  · rw [if_pos h, if_neg (lt_irrefl _ |> fun h' ↦ by rw [h]; exact h')]
  · rw [if_neg h.ne', if_pos h]
    have := L.fourier_rowKernel_zero_mul_exp_of_pos hy h z.re
    rw [Complex.re_add_im] at this
    rw [this]

theorem norm_rowLimitTerm_le {y₀ : ℝ} (hy₀ : 0 < y₀) (u : Fin 4 → ℤ) {z : ℂ} (hz : y₀ < z.im)
    (p : ℕ × ℤ) :
    ‖L.rowLimitTerm u z p‖ ≤ L.rowMajorant (rowKernelDecay y₀ / (4 * Real.pi ^ 2)) u p := by
  unfold rowLimitTerm rowMajorant
  set m : ℝ := (p.2 : ℝ) + L.polarDualNorm u with hm
  split_ifs with hpos hzero hzero
  · exact absurd hzero hpos.ne'
  · have hF := L.fourier_rowKernel_zero_of_pos hy₀ hpos
    have hdec := norm_fourier_rowKernel_le_of_ne le_rfl zero_le_one hy₀ hpos.ne'
    rw [hF, norm_neg, Complex.norm_real, Real.rpow_two] at hdec
    rw [norm_mul, norm_mul, norm_neg]
    have hexp : ‖exp (2 * Real.pi * I * (m : ℂ) * z)‖ = Real.exp (-(2 * Real.pi * m) * z.im) := by
      rw [Complex.norm_exp]
      congr 1
      simp [mul_re, mul_im]
    rw [hexp]
    have hmono : Real.exp (-(2 * Real.pi * m) * z.im) ≤ Real.exp (-(2 * Real.pi * y₀) * m) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hz.le (by positivity : (0 : ℝ) ≤ 2 * Real.pi * m)
      linarith
    have h4 : ‖(4 * (Real.pi : ℂ) ^ 2 * (m : ℂ))‖ = 4 * Real.pi ^ 2 * m := by
      rw [show (4 * (Real.pi : ℂ) ^ 2 * (m : ℂ)) = ((4 * Real.pi ^ 2 * m : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h4]
    have hB := norm_nonneg (L.gaussRowCoefficient (p.1 + 1) (u : L.PolarDiscriminantGroup) m)
    rw [Real.norm_of_nonneg (by positivity)] at hdec
    calc 4 * Real.pi ^ 2 * m * Real.exp (-(2 * Real.pi * m) * z.im) *
          ‖L.gaussRowCoefficient (p.1 + 1) (u : L.PolarDiscriminantGroup) m‖
        ≤ 4 * Real.pi ^ 2 * m * Real.exp (-(2 * Real.pi * y₀) * m) *
          ‖L.gaussRowCoefficient (p.1 + 1) (u : L.PolarDiscriminantGroup) m‖ := by gcongr
      _ ≤ rowKernelDecay y₀ / (4 * Real.pi ^ 2) * (1 / |m| ^ 2) *
          ‖L.gaussRowCoefficient (p.1 + 1) (u : L.PolarDiscriminantGroup) m‖ := by gcongr
      _ = _ := by ring
  · rw [norm_zero]
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (div_nonneg (rowKernelDecay_nonneg hy₀) (by positivity))
      (by positivity)) (norm_nonneg _)

/-- The coordinate q-expansion `E_row(z)_{[u]} = e₀[u] + Σ_{(n,k)} [m > 0] (-4π² m) e(mz) B_{n+1,[u]}(m)` is
holomorphic on the upper half-plane. -/
theorem differentiableOn_rowLimit (u : Fin 4 → ℤ) :
    DifferentiableOn ℂ (fun z ↦ L.gaussE0 (u : L.PolarDiscriminantGroup) + ∑' p, L.rowLimitTerm u z p)
      upperHalfSet := by
  intro z₀ hz₀
  have hy₀ : 0 < z₀.im / 2 := by have : 0 < z₀.im := hz₀; linarith
  set U : Set ℂ := {z | z₀.im / 2 < z.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hz₀U : z₀ ∈ U := by
    change z₀.im / 2 < z₀.im
    have : 0 < z₀.im := hz₀
    linarith
  have hK : 0 ≤ rowKernelDecay (z₀.im / 2) / (4 * Real.pi ^ 2) :=
    div_nonneg (rowKernelDecay_nonneg hy₀) (by positivity)
  have hD : DifferentiableOn ℂ (fun z ↦ ∑' p, L.rowLimitTerm u z p) U := by
    refine differentiableOn_tsum_of_summable_norm (L.summable_rowMajorant hK u) (fun p ↦ ?_) hUo
      (fun p z hz ↦ L.norm_rowLimitTerm_le hy₀ u hz p)
    unfold rowLimitTerm
    split_ifs
    · exact (((differentiable_exp.comp ((differentiable_id.const_mul _))).const_mul _).mul_const
        _).differentiableOn
    · exact differentiableOn_const _
  exact ((hD.const_add _).differentiableAt (hUo.mem_nhds hz₀U)).differentiableWithinAt

/-! ## The boundary row limit and the weight-two S law -/

/-- The row limit `E_row(z) = lim_{s → 0⁺} (E_s(z) - y^{-1-s} W_s)`. -/
def boundaryRowLimit (z : ℂ) : L.PolarDiscriminantGroup → ℂ := fun a ↦
  limUnder (𝓝[>] (0 : ℝ)) fun s ↦
    (L.regEisenstein s z - (((z.im ^ (-1 - s) : ℝ)) : ℂ) • L.gaussBoundaryAnomaly s) a

theorem tendsto_regEisenstein_sub_anomaly_rowLimit {z : ℂ} (hz : z ∈ upperHalfSet) (u : Fin 4 → ℤ) :
    Tendsto (fun s ↦ (L.regEisenstein s z - (((z.im ^ (-1 - s) : ℝ)) : ℂ) • L.gaussBoundaryAnomaly s)
        (u : L.PolarDiscriminantGroup)) (𝓝[>] 0)
      (𝓝 (L.gaussE0 (u : L.PolarDiscriminantGroup) + ∑' p, L.rowLimitTerm u z p)) := by
  have h := L.tendsto_regEisenstein_sub_anomaly_apply hz u
  rwa [tsum_congr (L.rowTerm_zero_eq_rowLimitTerm hz u)] at h

/-- The explicit q-EXPANSION of the row limit (6.6). -/
theorem boundaryRowLimit_apply {z : ℂ} (hz : z ∈ upperHalfSet) (u : Fin 4 → ℤ) :
    L.boundaryRowLimit z (u : L.PolarDiscriminantGroup) =
      L.gaussE0 (u : L.PolarDiscriminantGroup) + ∑' p, L.rowLimitTerm u z p :=
  (L.tendsto_regEisenstein_sub_anomaly_rowLimit hz u).limUnder_eq

theorem tendsto_boundaryRowLimit {z : ℂ} (hz : z ∈ upperHalfSet) :
    Tendsto (fun s ↦ L.regEisenstein s z - (((z.im ^ (-1 - s) : ℝ)) : ℂ) • L.gaussBoundaryAnomaly s)
      (𝓝[>] 0) (𝓝 (L.boundaryRowLimit z)) := by
  refine tendsto_pi_nhds.2 fun a ↦ ?_
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  rw [L.boundaryRowLimit_apply hz u]
  exact L.tendsto_regEisenstein_sub_anomaly_rowLimit hz u

/-- The row limit is holomorphic on the upper half-plane. -/
theorem differentiableOn_boundaryRowLimit :
    DifferentiableOn ℂ L.boundaryRowLimit upperHalfSet := by
  refine differentiableOn_pi.2 fun a ↦ ?_
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  exact (L.differentiableOn_rowLimit u).congr fun z hz ↦ L.boundaryRowLimit_apply hz u

/-- The weight-two boundary: the anomaly vanishes,
`W_s → 0`, and the row limit obeys the exact weight-two S law `E_row(-1/z) = z² U E_row(z)`. -/
theorem tendsto_gaussBoundaryAnomaly_zero_and_boundaryRowLimit_sLaw :
    Tendsto L.gaussBoundaryAnomaly (𝓝[>] 0) (𝓝 0) ∧
      ∀ z ∈ upperHalfSet, L.boundaryRowLimit (-z⁻¹) = z ^ 2 • L.gaussU (L.boundaryRowLimit z) :=
  L.tendsto_gaussBoundaryAnomaly_and_sLaw L.boundaryRowLimit L.differentiableOn_boundaryRowLimit
    fun _ hz ↦ L.tendsto_boundaryRowLimit hz

end PositiveDefiniteIntegralLattice
