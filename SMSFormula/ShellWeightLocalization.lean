import Mathlib.Data.ENNReal.BigOperators

/-!
# Localizing the explicit shell weight on one finite set of places

A purely algebraic ENNReal lemma.  Suppose the one-shell identity has the shape

`Θ · (∏_T β_W · τ_V · (∏_T s_B · (∏_T s_A)⁻¹) · ∏_T δ · ∏_T vol_W · (∏_T ‖q‖)⁻¹ · ∏_B s_W / (∏_B D · ∏_B s_B))
  = ∏_T β_A · τ_W · d · ∏_T vol_A`

with `β_X = vol_X⁻¹ · (s_X · m)⁻¹` and all local factors positive and finite on `T ⊇ B`.  Then the
ambient data (`vol_A`, `s_A`) and the common conversion `m` cancel place by place, and

`Θ · τ_V · ∏_{v∈T} den_v = τ_W · d · ∏_{v∈T} num_v`,

`den_v = (if v ∈ B then 1 else s_B(v)) · δ_v`,  `num_v = ‖q‖_v · (if v ∈ B then D_v else s_W(v))`.

So the shell-weight constant is `C_a = ∏_{v∈T} num_v / den_v`, a product of local terms.
-/

noncomputable section

open scoped ENNReal

namespace ENNReal

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
private theorem shellWeightLocalization_prod_ne_top {T : Finset ι} {f : ι → ℝ≥0∞}
    (hf : ∀ v ∈ T, f v ≠ ⊤) : ∏ v ∈ T, f v ≠ ⊤ := ENNReal.prod_ne_top hf

omit [DecidableEq ι] in
private theorem shellWeightLocalization_prod_ne_zero {T : Finset ι} {f : ι → ℝ≥0∞}
    (hf : ∀ v ∈ T, f v ≠ 0) : ∏ v ∈ T, f v ≠ 0 := Finset.prod_ne_zero_iff.mpr hf

/-- The shell weight is a product of local terms. -/
theorem shellWeight_localize {T B : Finset ι} (hBT : B ⊆ T)
    {volA volW sA sB sW m nq δ D : ι → ℝ≥0∞}
    (hvolA : ∀ v ∈ T, volA v ≠ 0 ∧ volA v ≠ ⊤) (hvolW : ∀ v ∈ T, volW v ≠ 0 ∧ volW v ≠ ⊤)
    (hsA : ∀ v ∈ T, sA v ≠ 0 ∧ sA v ≠ ⊤) (hsB : ∀ v ∈ T, sB v ≠ 0 ∧ sB v ≠ ⊤)
    (hsW : ∀ v ∈ T, sW v ≠ 0 ∧ sW v ≠ ⊤) (hm : ∀ v ∈ T, m v ≠ 0 ∧ m v ≠ ⊤)
    (hnq : ∀ v ∈ T, nq v ≠ 0 ∧ nq v ≠ ⊤) (hδ : ∀ v ∈ T, δ v ≠ ⊤)
    (hD : ∀ v ∈ B, D v ≠ 0 ∧ D v ≠ ⊤)
    {Θ τV τW d : ℝ≥0∞}
    (h : Θ * ((∏ v ∈ T, (volW v)⁻¹ * (sW v * m v)⁻¹) * τV *
        ((∏ v ∈ T, sB v) * (∏ v ∈ T, sA v)⁻¹) * (∏ v ∈ T, δ v) * (∏ v ∈ T, volW v) *
        (∏ v ∈ T, nq v)⁻¹ * (∏ v ∈ B, sW v) / ((∏ v ∈ B, D v) * ∏ v ∈ B, sB v)) =
      (∏ v ∈ T, (volA v)⁻¹ * (sA v * m v)⁻¹) * τW * d * ∏ v ∈ T, volA v) :
    Θ * τV * ∏ v ∈ T, ((if v ∈ B then 1 else sB v) * δ v) =
      τW * d * ∏ v ∈ T, (nq v * (if v ∈ B then D v else sW v)) := by
  have hDT : ∀ v ∈ T, (if v ∈ B then D v else sW v) ≠ 0 ∧ (if v ∈ B then D v else sW v) ≠ ⊤ := by
    intro v hv
    split_ifs with hvB
    · exact hD v hvB
    · exact hsW v hv
  set P := (∏ v ∈ T, (volW v)⁻¹ * (sW v * m v)⁻¹) *
      ((∏ v ∈ T, sB v) * (∏ v ∈ T, sA v)⁻¹) * (∏ v ∈ T, δ v) * (∏ v ∈ T, volW v) *
      (∏ v ∈ T, nq v)⁻¹ * (∏ v ∈ B, sW v) / ((∏ v ∈ B, D v) * ∏ v ∈ B, sB v) with hP
  set R := (∏ v ∈ T, (volA v)⁻¹ * (sA v * m v)⁻¹) * ∏ v ∈ T, volA v with hRdef
  have hR0 : R ≠ 0 := by
    refine mul_ne_zero (shellWeightLocalization_prod_ne_zero fun v hv ↦ mul_ne_zero
      (ENNReal.inv_ne_zero.mpr (hvolA v hv).2) (ENNReal.inv_ne_zero.mpr
        (ENNReal.mul_ne_top (hsA v hv).2 (hm v hv).2)))
      (shellWeightLocalization_prod_ne_zero fun v hv ↦ (hvolA v hv).1)
  have hRt : R ≠ ⊤ := by
    refine ENNReal.mul_ne_top (shellWeightLocalization_prod_ne_top fun v hv ↦ ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (hvolA v hv).1) (ENNReal.inv_ne_top.mpr
        (mul_ne_zero (hsA v hv).1 (hm v hv).1)))
      (shellWeightLocalization_prod_ne_top fun v hv ↦ (hvolA v hv).2)
  have hPt : P ≠ ⊤ := by
    have hBD : (∏ v ∈ B, D v) * ∏ v ∈ B, sB v ≠ 0 :=
      mul_ne_zero (shellWeightLocalization_prod_ne_zero fun v hv ↦ (hD v hv).1)
        (shellWeightLocalization_prod_ne_zero fun v hv ↦ (hsB v (hBT hv)).1)
    refine ENNReal.div_ne_top ?_ hBD
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ?_ ?_) ?_) ?_) ?_) ?_
    · exact shellWeightLocalization_prod_ne_top fun v hv ↦ ENNReal.mul_ne_top
        (ENNReal.inv_ne_top.mpr (hvolW v hv).1)
        (ENNReal.inv_ne_top.mpr (mul_ne_zero (hsW v hv).1 (hm v hv).1))
    · exact ENNReal.mul_ne_top (shellWeightLocalization_prod_ne_top fun v hv ↦ (hsB v hv).2)
        (ENNReal.inv_ne_top.mpr (shellWeightLocalization_prod_ne_zero fun v hv ↦ (hsA v hv).1))
    · exact shellWeightLocalization_prod_ne_top hδ
    · exact shellWeightLocalization_prod_ne_top fun v hv ↦ (hvolW v hv).2
    · exact ENNReal.inv_ne_top.mpr (shellWeightLocalization_prod_ne_zero fun v hv ↦ (hnq v hv).1)
    · exact shellWeightLocalization_prod_ne_top fun v hv ↦ (hsW v (hBT hv)).2
  have hnumt : ∏ v ∈ T, (nq v * (if v ∈ B then D v else sW v)) ≠ ⊤ :=
    shellWeightLocalization_prod_ne_top fun v hv ↦ ENNReal.mul_ne_top (hnq v hv).2 (hDT v hv).2
  have hdent : ∏ v ∈ T, ((if v ∈ B then 1 else sB v) * δ v) ≠ ⊤ := by
    refine shellWeightLocalization_prod_ne_top fun v hv ↦ ENNReal.mul_ne_top ?_ (hδ v hv)
    split_ifs
    · exact ENNReal.one_ne_top
    · exact (hsB v hv).2
  -- the local cancellation, computed in `ℝ`
  have K : P * ∏ v ∈ T, (nq v * (if v ∈ B then D v else sW v)) =
      (∏ v ∈ T, ((if v ∈ B then 1 else sB v) * δ v)) * R := by
    rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top hPt hnumt) (ENNReal.mul_ne_top hdent hRt)]
    have hBsub : ∀ f : ι → ℝ≥0∞, ∏ v ∈ B, f v = ∏ v ∈ T, (if v ∈ B then f v else 1) := by
      intro f
      rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hBT]
    rw [hP, hRdef, hBsub sW, hBsub D, hBsub sB]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_inv,
      apply_ite ENNReal.toReal, ENNReal.toReal_one, div_eq_mul_inv, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v hv ↦ ?_
    have a1 := ENNReal.toReal_pos (hvolA v hv).1 (hvolA v hv).2
    have a2 := ENNReal.toReal_pos (hvolW v hv).1 (hvolW v hv).2
    have a3 := ENNReal.toReal_pos (hsA v hv).1 (hsA v hv).2
    have a4 := ENNReal.toReal_pos (hsB v hv).1 (hsB v hv).2
    have a5 := ENNReal.toReal_pos (hsW v hv).1 (hsW v hv).2
    have a6 := ENNReal.toReal_pos (hm v hv).1 (hm v hv).2
    have a7 := ENNReal.toReal_pos (hnq v hv).1 (hnq v hv).2
    split_ifs with hvB
    · have a8 := ENNReal.toReal_pos (hD v hvB).1 (hD v hvB).2
      field_simp
    · field_simp
  have h' : Θ * τV * P = R * τW * d := by
    rw [hP, hRdef]
    convert h using 1
    · simp only [div_eq_mul_inv]; ring
    · ring
  have key : R * (Θ * τV * ∏ v ∈ T, ((if v ∈ B then 1 else sB v) * δ v)) =
      R * (τW * d * ∏ v ∈ T, (nq v * (if v ∈ B then D v else sW v))) := by
    calc R * (Θ * τV * ∏ v ∈ T, ((if v ∈ B then 1 else sB v) * δ v)) =
        Θ * τV * ((∏ v ∈ T, ((if v ∈ B then 1 else sB v) * δ v)) * R) := by ring
      _ = Θ * τV * P * ∏ v ∈ T, (nq v * (if v ∈ B then D v else sW v)) := by rw [← K]; ring
      _ = _ := by rw [h']; ring
  exact (ENNReal.mul_right_inj hR0 hRt).mp key

end ENNReal
