import SMSFormula.RationalLatticeEisensteinRowLimit
import SMSFormula.RationalAdeleOrderedStandardAggregate

/-!
# The standard coordinate of the row limit is the standard aggregate

* At the trivial coset `u = 0` the coset coefficients are the Gauss–Ramanujan coefficients
  (`cosetGRCoeff_zero_eq_gaussRamanujanCoefficient`): both have divisor sums equal to the normalized residue
  counts, so Möbius inversion identifies them.
* (8.1), standard part (`boundaryRowLimit_zero_eq_standardAggregate`): for `α > 0`,
  `E_row(iα)_0 = 1 + Σ_k Â_α(k) [k > 0] ∏'_p δ_p(k)`, which is exactly the limit of the ordered standard
  aggregate (`tendsto_orderedStandardAggregate`).  The constants agree because `κ = √det S⁻¹ = |det|^{-1/2}` is the
  inverse of the determinant scale.
* (8.2) `standardAggregate_inv_eq`: the exact weight-two S law at `z = iα`, component `0`, gives
  `E_std(1/α) = α² κ Σ_{ν ∈ A} E_row(iα)_ν`.
Nothing is chosen.
-/

noncomputable section

open Matrix Complex Filter Topology SMSFormula.WeightTwoConstantTerm SMSFormula.RowKernel Finset
open scoped FourierTransform ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace PositiveDefiniteIntegralLattice

/-! ## The trivial coset is the standard lattice -/

section Trivial

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1))

theorem cosetResidueCount_zero (M : ℤ) (N : ℕ) :
    L.cosetResidueCount 0 M N = L.normalizedResidueCount M N := by
  have h : ∀ z : Fin (n + 1) → ZMod N, L.zmodCosetPoly 0 N z = L.zmodQuadForm N z := fun z ↦ by
    simp [zmodCosetPoly]
  unfold cosetResidueCount normalizedResidueCount
  simp only [h]

theorem cosetResidueCountArith_zero (M : ℤ) :
    L.cosetResidueCountArith 0 M = L.normalizedResidueCountArith M := by
  ext N
  simp only [cosetResidueCountArith, normalizedResidueCountArith, ArithmeticFunction.coe_mk,
    L.cosetResidueCount_zero]

/-- At the trivial coset the coset coefficients are the Gauss–Ramanujan coefficients. -/
theorem cosetGRArith_zero (M : ℤ) : L.cosetGRArith 0 M = L.gaussRamanujanArith M := by
  have h1 := L.cosetGRArith_mul_zeta 0 M
  have h2 := L.gaussRamanujanArith_mul_zeta M
  rw [L.cosetResidueCountArith_zero, ← h2] at h1
  have h3 := congrArg (· * (μ : ArithmeticFunction ℂ)) h1
  simp only [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one] at h3
  exact h3

theorem cosetGRCoeff_zero_eq_gaussRamanujanCoefficient (M : ℤ) (c : ℕ) :
    L.cosetGRCoeff 0 M c = L.gaussRamanujanCoefficient c M := by
  have := congrArg (fun f : ArithmeticFunction ℂ ↦ f c) (L.cosetGRArith_zero M)
  simpa using this

end Trivial

variable (L : PositiveDefiniteIntegralLattice 4)

/-! ## The standard coordinate -/

/-- The standard aggregate `E_std(α) = 1 + Σ_k Â_α(k) [k > 0] ∏'_p δ_p(k)`. -/
def standardAggregate (α : ℝ) : ℂ :=
  1 + ∑' k : ℤ, 𝓕 (L.polarArchimedeanBruhatFactor α) k *
    (if 0 < k then ((∏' p : Nat.Primes, L.localResidueDensity k p : ℝ) : ℂ) else 0)

theorem polarKappa_eq_inv_polarRealDeterminantScale :
    L.polarKappa = (L.polarRealDeterminantScale : ℝ)⁻¹ := by
  rw [polarKappa, coe_polarRealDeterminantScale, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    Real.sqrt_inv]

theorem mem_upperHalfSet_mul_I {α : ℝ} (hα : 0 < α) : (α : ℂ) * I ∈ upperHalfSet := by
  simp [upperHalfSet, hα]

/-- The standard coordinate term: `[k > 0] 4π² κ k e^{-2πkα} A_{n+1}(k)`. -/
theorem rowLimitTerm_zero_eq {α : ℝ} (p : ℕ × ℤ) :
    L.rowLimitTerm 0 ((α : ℂ) * I) p =
      if 0 < p.2 then
        ((4 * Real.pi ^ 2 * L.polarKappa * p.2 * Real.exp (-(2 * Real.pi * α) * p.2) : ℝ) : ℂ) *
          L.gaussRamanujanCoefficient (p.1 + 1) p.2
      else 0 := by
  have hN0 : L.polarDualNorm 0 = 0 := L.polarDualNorm_zero
  unfold rowLimitTerm
  simp only [hN0, add_zero]
  by_cases hk : 0 < p.2
  · have hk' : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hk
    rw [if_pos hk', if_pos hk]
    have hB := L.gaussRowCoefficient_eq_cosetGRCoeff (p.1 + 1) 0 p.2
    rw [hN0, add_zero] at hB
    rw [hB, L.cosetGRCoeff_zero_eq_gaussRamanujanCoefficient]
    have hexp : exp (2 * Real.pi * I * ((p.2 : ℝ) : ℂ) * ((α : ℂ) * I)) =
        ((Real.exp (-(2 * Real.pi * α) * p.2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      linear_combination (2 * (Real.pi : ℂ) * (p.2 : ℂ) * α) * I_sq
    rw [hexp]
    push_cast
    ring
  · have hk' : ¬ (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hk
    rw [if_neg hk', if_neg hk]

/-- The standard identification (8.1): `E_row(iα)_0 = E_std(α)`. -/
theorem boundaryRowLimit_zero_eq_standardAggregate {α : ℝ} (hα : 0 < α) :
    L.boundaryRowLimit ((α : ℂ) * I) 0 = L.standardAggregate α := by
  have hz := mem_upperHalfSet_mul_I hα
  have h0 : (0 : L.PolarDiscriminantGroup) = ((0 : Fin 4 → ℤ) : L.PolarDiscriminantGroup) :=
    (QuotientAddGroup.mk_zero _).symm
  rw [h0, L.boundaryRowLimit_apply hz 0, ← h0]
  unfold standardAggregate
  have he : L.gaussE0 0 = 1 := by simp [gaussE0]
  rw [he]
  congr 1
  have hα2 : 0 < α / 2 := by positivity
  have hK : 0 ≤ rowKernelDecay (α / 2) / (4 * Real.pi ^ 2) :=
    div_nonneg (rowKernelDecay_nonneg hα2) (by positivity)
  have hsum : Summable (L.rowLimitTerm 0 ((α : ℂ) * I)) :=
    Summable.of_norm_bounded (L.summable_rowMajorant hK 0) fun p ↦
      L.norm_rowLimitTerm_le hα2 0 (by simp; linarith) p
  have hsum' : Summable fun q : ℤ × ℕ ↦ L.rowLimitTerm 0 ((α : ℂ) * I) (Equiv.prodComm ℤ ℕ q) :=
    (Equiv.prodComm ℤ ℕ).summable_iff.2 hsum
  rw [← (Equiv.prodComm ℤ ℕ).tsum_eq, hsum'.tsum_prod]
  refine tsum_congr fun k ↦ ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, L.rowLimitTerm_zero_eq]
  by_cases hk : 0 < k
  · simp only [if_pos hk]
    rw [tsum_mul_left]
    have hA : ∑' n : ℕ, L.gaussRamanujanCoefficient (n + 1) k =
        ((∏' p : Nat.Primes, L.localResidueDensity k p : ℝ) : ℂ) := by
      have h := L.hasSum_gaussRamanujanCoefficient_tprod_localResidueDensity (n := 3) (by norm_num)
        hk.ne'
      rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
      simp [gaussRamanujanCoefficient]
    rw [hA, L.fourier_polarArchimedeanBruhatFactor_of_pos hα (by norm_num)
      (by exact_mod_cast hk : (0 : ℝ) < (k : ℝ)), L.polarKappa_eq_inv_polarRealDeterminantScale]
    have h2 : ((4 : ℕ) : ℝ) / 2 = 2 := by norm_num
    rw [h2, Real.Gamma_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
    push_cast
    ring
  · simp only [if_neg hk, tsum_zero, mul_zero]

/-- The standard–dual reciprocity (8.2): `E_std(1/α) = α² κ Σ_{ν ∈ A} E_row(iα)_ν`. -/
theorem standardAggregate_inv_eq {α : ℝ} (hα : 0 < α) :
    L.standardAggregate α⁻¹ =
      ((α ^ 2 * L.polarKappa : ℝ) : ℂ) * ∑ a, L.boundaryRowLimit ((α : ℂ) * I) a := by
  have hz := mem_upperHalfSet_mul_I hα
  have hS := congrFun ((L.tendsto_gaussBoundaryAnomaly_zero_and_boundaryRowLimit_sLaw).2 _ hz) 0
  have hinv : -((α : ℂ) * I)⁻¹ = ((α⁻¹ : ℝ) : ℂ) * I := by
    have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
    push_cast
    field_simp
    linear_combination -I_sq
  rw [hinv, L.boundaryRowLimit_zero_eq_standardAggregate (inv_pos.2 hα)] at hS
  rw [hS, Pi.smul_apply, smul_eq_mul]
  have hsum_eq : ∑ a, L.polarDiscPairingChar 0 a * L.boundaryRowLimit ((α : ℂ) * I) a =
      ∑ a, L.boundaryRowLimit ((α : ℂ) * I) a :=
    Finset.sum_congr rfl fun a _ ↦ by rw [polarDiscPairingChar_zero_left, one_mul]
  unfold gaussU
  rw [hsum_eq]
  set S := ∑ a, L.boundaryRowLimit ((α : ℂ) * I) a
  push_cast
  linear_combination (-(L.polarKappa : ℂ) * S * (α : ℂ) ^ 2) * I_sq

end PositiveDefiniteIntegralLattice
