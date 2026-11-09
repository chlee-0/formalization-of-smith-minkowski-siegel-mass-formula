import SMSFormula.RationalSpecialOrthogonalRealPositiveDefiniteMass

/-!
# The real SO mass of a one-line extension over the real SO mass

For a positive-definite rational form `W` of rank `n` and `a > 0`, the evaluated real masses
(`μ_F(SO_F(ℝ)) · SP(k) = |e(F)| · 2^k · √|det F|^{k−1}`) of `W` and of `B = W ⊕ ⟨a⟩` satisfy

`μ_B · |e_W| · Γ((n+1)/2) = μ_W · |e_B| · 2 · √a^n · √|det W| · π^{(n+1)/2}`,

using `SP(n+1) = SP(n) · π^{−(n+1)/2} · Γ((n+1)/2)` and `det B = det W · a`.  Together with the closed
form `d_∞ = detScale⁻¹(2π)^{(n+1)/2}/Γ((n+1)/2)·a^{(n−1)/2}` of the archimedean orbit density this
makes the archimedean factor of the explicit shell weight a Γ- and π-free algebraic quantity.
Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice

/-- `SP(n+1) = SP(n) · π^{−(n+1)/2} · Γ((n+1)/2)`. -/
theorem archimedeanMassFactor_succ (n : ℕ) :
    archimedeanMassFactor (n + 1) =
      archimedeanMassFactor n * Real.pi ^ (-(((n : ℝ) + 1) / 2)) *
        Real.Gamma (((n : ℝ) + 1) / 2) := by
  unfold archimedeanMassFactor
  simp only [Real.rpow_eq_pow]
  rw [Finset.prod_range_succ]
  have hrpow : Real.pi ^ (-(((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) / 4)) =
      Real.pi ^ (-((n : ℝ) * ((n : ℝ) + 1) / 4)) * Real.pi ^ (-(((n : ℝ) + 1) / 2)) := by
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    push_cast
    ring
  rw [hrpow]
  push_cast
  ring

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The real mass ratio of a one-line extension:
`μ_B · |e_W| · Γ((n+1)/2) = μ_W · |e_B| · 2 · √a^n · √|det W| · π^{(n+1)/2}`. -/
theorem realInvariantDifferentialGroupMeasure_nonisotropicLastExtension_mul_eq
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (hW : (W.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) {a : ℚ} (ha : a ≠ 0) (ha0 : 0 < a) :
    (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure Set.univ *
        ENNReal.ofReal (|(Matrix.skewAdjointFixedFormElementaryDetScalar
              W.pairingMatrix W.form_symm W.form_det_ne_zero : ℝ)| *
          Real.Gamma (((n : ℝ) + 1) / 2)) =
      W.realInvariantDifferentialGroupMeasure Set.univ *
        ENNReal.ofReal (|(Matrix.skewAdjointFixedFormElementaryDetScalar
              (W.nonisotropicLastExtension a ha).pairingMatrix
              (W.nonisotropicLastExtension a ha).form_symm
              (W.nonisotropicLastExtension a ha).form_det_ne_zero : ℝ)| *
          2 * Real.sqrt (a : ℝ) ^ n * Real.sqrt |((W.pairingMatrix.det : ℚ) : ℝ)| *
          Real.pi ^ (((n : ℝ) + 1) / 2)) := by
  set B := W.nonisotropicLastExtension a ha
  have hB := B.realInvariantDifferentialGroupMeasure_univ_mul_archimedeanFactor
    (W.posDef_nonisotropicLastExtension_map_real hW ha ha0)
  have hWm := W.realInvariantDifferentialGroupMeasure_univ_mul_archimedeanFactor hW
  set eW := (Matrix.skewAdjointFixedFormElementaryDetScalar W.pairingMatrix W.form_symm
    W.form_det_ne_zero : ℝ)
  set eB := (Matrix.skewAdjointFixedFormElementaryDetScalar B.pairingMatrix B.form_symm
    B.form_det_ne_zero : ℝ)
  set dW : ℝ := ((W.pairingMatrix.det : ℚ) : ℝ)
  set SPn := archimedeanMassFactor n
  have hSPn := archimedeanMassFactor_pos n
  have hSPn1 := archimedeanMassFactor_pos (n + 1)
  have hdetB : ((B.pairingMatrix.det : ℚ) : ℝ) = dW * (a : ℝ) := by
    change ((nonisotropicLastBlockMatrix W.pairingMatrix a).det : ℝ) = _
    rw [nonisotropicLastBlockMatrix_det, Rat.cast_mul]
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha0
  have hΓ : 0 < Real.Gamma (((n : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hπ : 0 < Real.pi ^ (((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  -- cancel `ofReal SP(n+1) * ofReal SP(n)`
  have hne0 : ENNReal.ofReal (archimedeanMassFactor (n + 1)) * ENNReal.ofReal SPn ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hSPn1).ne' (ENNReal.ofReal_pos.mpr hSPn).ne'
  have hnet : ENNReal.ofReal (archimedeanMassFactor (n + 1)) * ENNReal.ofReal SPn ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine (ENNReal.mul_left_inj hne0 hnet).mp ?_
  calc B.realInvariantDifferentialGroupMeasure Set.univ * ENNReal.ofReal (|eW| *
          Real.Gamma (((n : ℝ) + 1) / 2)) *
        (ENNReal.ofReal (archimedeanMassFactor (n + 1)) * ENNReal.ofReal SPn) =
      (B.realInvariantDifferentialGroupMeasure Set.univ *
          ENNReal.ofReal (archimedeanMassFactor (n + 1))) *
        ENNReal.ofReal (|eW| * Real.Gamma (((n : ℝ) + 1) / 2)) * ENNReal.ofReal SPn := by ring
    _ = ENNReal.ofReal (|eB| * ((2 : ℝ) ^ (n + 1) *
            (Real.sqrt |((B.pairingMatrix.det : ℚ) : ℝ)|) ^ (n + 1 - 1))) *
          ENNReal.ofReal (|eW| * Real.Gamma (((n : ℝ) + 1) / 2)) * ENNReal.ofReal SPn := by
        rw [hB]
    _ = ENNReal.ofReal (|eW| * ((2 : ℝ) ^ n * (Real.sqrt |dW|) ^ (n - 1))) *
          ENNReal.ofReal (|eB| * 2 * Real.sqrt (a : ℝ) ^ n * Real.sqrt |dW| *
            Real.pi ^ (((n : ℝ) + 1) / 2)) *
          ENNReal.ofReal (archimedeanMassFactor (n + 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [archimedeanMassFactor_succ, hdetB, abs_mul, abs_of_pos ha',
          Real.sqrt_mul (abs_nonneg _), Nat.add_sub_cancel]
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos
          (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
        have hpn : Real.pi ^ (((((k + 1 : ℕ) : ℝ)) + 1) / 2) *
            Real.pi ^ (-((((k + 1 : ℕ) : ℝ) + 1) / 2)) = 1 := by
          rw [← Real.rpow_add Real.pi_pos, add_neg_cancel, Real.rpow_zero]
        simp only [Nat.add_sub_cancel]
        calc |eB| * (2 ^ (k + 1 + 1) * (Real.sqrt |dW| * Real.sqrt (a : ℝ)) ^ (k + 1)) *
              (|eW| * Real.Gamma ((((k + 1 : ℕ) : ℝ) + 1) / 2)) * SPn =
            |eW| * (2 ^ (k + 1) * Real.sqrt |dW| ^ k) * (|eB| * 2 * Real.sqrt (a : ℝ) ^ (k + 1) *
              Real.sqrt |dW| * Real.pi ^ ((((k + 1 : ℕ) : ℝ) + 1) / 2)) *
              (SPn * Real.pi ^ (-((((k + 1 : ℕ) : ℝ) + 1) / 2)) *
                Real.Gamma ((((k + 1 : ℕ) : ℝ) + 1) / 2)) := by
              have : Real.pi ^ ((((k + 1 : ℕ) : ℝ) + 1) / 2) *
                  Real.pi ^ (-((((k + 1 : ℕ) : ℝ) + 1) / 2)) = 1 := hpn
              linear_combination (-(|eB| * |eW| * 2 ^ (k + 2) * Real.sqrt |dW| ^ (k + 1) *
                Real.sqrt (a : ℝ) ^ (k + 1) * Real.Gamma ((((k + 1 : ℕ) : ℝ) + 1) / 2) * SPn)) * this
          _ = _ := rfl
    _ = W.realInvariantDifferentialGroupMeasure Set.univ * ENNReal.ofReal (|eB| * 2 *
            Real.sqrt (a : ℝ) ^ n * Real.sqrt |dW| * Real.pi ^ (((n : ℝ) + 1) / 2)) *
          (ENNReal.ofReal (archimedeanMassFactor (n + 1)) * ENNReal.ofReal SPn) := by
        rw [← hWm]; ring

end RationalQuadraticSpaceMatrix
