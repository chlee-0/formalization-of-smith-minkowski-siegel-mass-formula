import SMSFormula.AdelicGaussianCentralCutoffOrbitRatioValue

/-!
# Cancellation of the local densities in the orbit Riesz ratio

The evaluated orbit Riesz ratio reads

`r = c_G · ((∏_T gR/∏_T gF) · X) / (μ_V ∏_B (s_V c_v) / (μ_W ∏_B s_W))`,

with `T = S ∪ bad` (read through its primes) and `B ⊆ T` the bad places.  The local identities
give `gR · D_v = gF · c_v` at `v ∈ B` (with `D_v = |r| ν(ℤ_p) glue_block(E_v⁻¹ ℤ_p^n)`) and
`gR = gF` at `v ∈ T \ B`.  Then `∏_T gR/∏_T gF = ∏_B c_v/∏_B D_v`, and the local densities
cancel:

`r = c_G · (X · (μ_W ∏_B s_W)) / (∏_B D_v · (μ_V ∏_B s_V))`.

This file proves the three algebraic steps: reindexing a product over the primes of a block of
places, the collapse of the local ratio product, and the final cancellation.  Nothing is chosen.
-/

noncomputable section

open scoped ENNReal
open Rat.HeightOneSpectrum PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase RationalQuadraticSpaceMatrix

/-- A product over the primes of a block of places is the product over the places. -/
theorem prod_placeBlockPrimes_eq {M : Type*} [CommMonoid M]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) (f : ℕ → M) :
    ∏ p ∈ placeBlockPrimes T, f p = ∏ v ∈ T, f (primesEquiv v : ℕ) := by
  unfold placeBlockPrimes
  refine Finset.prod_image fun v _ w _ h ↦ primesEquiv.injective (Subtype.ext h)

/-- The local ratio product collapses: from `gR · D = gF · c` on `B` and `gR = gF` on `T \ B`
(all factors positive and finite), `∏_T gR / ∏_T gF = ∏_B c / ∏_B D`. -/
theorem ENNReal.prod_div_prod_eq_of_local {α : Type*} [DecidableEq α] {T B : Finset α}
    (hBT : B ⊆ T) (gF gR c D : α → ℝ≥0∞)
    (hB : ∀ v ∈ B, gR v * D v = gF v * c v) (hrest : ∀ v ∈ T \ B, gR v = gF v)
    (hgF0 : ∀ v ∈ T, gF v ≠ 0) (hgFt : ∀ v ∈ T, gF v ≠ ⊤)
    (hD0 : ∀ v ∈ B, D v ≠ 0) (hDt : ∀ v ∈ B, D v ≠ ⊤) :
    (∏ v ∈ T, gR v) / (∏ v ∈ T, gF v) = (∏ v ∈ B, c v) / (∏ v ∈ B, D v) := by
  have hprod : (∏ v ∈ T, gR v) * (∏ v ∈ B, D v) = (∏ v ∈ B, c v) * (∏ v ∈ T, gF v) := by
    rw [← Finset.prod_sdiff hBT, ← Finset.prod_sdiff hBT (f := gF),
      Finset.prod_congr rfl hrest]
    calc (∏ v ∈ T \ B, gF v) * (∏ v ∈ B, gR v) * (∏ v ∈ B, D v)
        = (∏ v ∈ T \ B, gF v) * ∏ v ∈ B, (gR v * D v) := by
          rw [mul_assoc, Finset.prod_mul_distrib]
      _ = (∏ v ∈ T \ B, gF v) * ∏ v ∈ B, (gF v * c v) := by
          rw [Finset.prod_congr rfl hB]
      _ = (∏ v ∈ B, c v) * ((∏ v ∈ T \ B, gF v) * ∏ v ∈ B, gF v) := by
          rw [Finset.prod_mul_distrib]; ring
  have hT0 : (∏ v ∈ T, gF v) ≠ 0 := Finset.prod_ne_zero_iff.2 hgF0
  have hTt : (∏ v ∈ T, gF v) ≠ ⊤ := ENNReal.prod_ne_top hgFt
  have hB0 : (∏ v ∈ B, D v) ≠ 0 := Finset.prod_ne_zero_iff.2 hD0
  have hBt : (∏ v ∈ B, D v) ≠ ⊤ := ENNReal.prod_ne_top hDt
  rw [ENNReal.div_eq_div_iff hB0 hBt hT0 hTt]
  calc (∏ v ∈ B, D v) * (∏ v ∈ T, gR v) = (∏ v ∈ T, gR v) * (∏ v ∈ B, D v) := mul_comm _ _
    _ = (∏ v ∈ B, c v) * (∏ v ∈ T, gF v) := hprod
    _ = (∏ v ∈ T, gF v) * (∏ v ∈ B, c v) := mul_comm _ _

/-- The local densities cancel:
`(C/D) · X / (μV · (SV · C) / (μW · SW)) = X · (μW · SW) / (D · (μV · SV))`
for positive finite `C, D, μV, SV, μW, SW`. -/
theorem ENNReal.localDensity_cancel {C D X μV SV μW SW : ℝ≥0∞}
    (hC0 : C ≠ 0) (hCt : C ≠ ⊤) (hD0 : D ≠ 0) (hDt : D ≠ ⊤)
    (hV0 : μV ≠ 0) (hVt : μV ≠ ⊤) (hSV0 : SV ≠ 0) (hSVt : SV ≠ ⊤)
    (hW0 : μW ≠ 0) (hWt : μW ≠ ⊤) (hSW0 : SW ≠ 0) (hSWt : SW ≠ ⊤) :
    (C / D) * X / (μV * (SV * C) / (μW * SW)) = X * (μW * SW) / (D * (μV * SV)) := by
  have hA0 : μW * SW ≠ 0 := mul_ne_zero hW0 hSW0
  have hAt : μW * SW ≠ ⊤ := ENNReal.mul_ne_top hWt hSWt
  have hN0 : μV * (SV * C) ≠ 0 := mul_ne_zero hV0 (mul_ne_zero hSV0 hC0)
  have hNt : μV * (SV * C) ≠ ⊤ := ENNReal.mul_ne_top hVt (ENNReal.mul_ne_top hSVt hCt)
  have hY0 : μV * (SV * C) / (μW * SW) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hN0, hAt⟩
  have hYt : μV * (SV * C) / (μW * SW) ≠ ⊤ := ENNReal.div_ne_top hNt hA0
  have hZ0 : D * (μV * SV) ≠ 0 := mul_ne_zero hD0 (mul_ne_zero hV0 hSV0)
  have hZt : D * (μV * SV) ≠ ⊤ := ENNReal.mul_ne_top hDt (ENNReal.mul_ne_top hVt hSVt)
  rw [ENNReal.div_eq_div_iff hZ0 hZt hY0 hYt]
  have h1 : C / D * D = C := ENNReal.div_mul_cancel hD0 hDt
  have h2 : μV * (SV * C) / (μW * SW) * (μW * SW) = μV * (SV * C) :=
    ENNReal.div_mul_cancel hA0 hAt
  calc D * (μV * SV) * (C / D * X) = (C / D * D) * X * (μV * SV) := by ring
    _ = C * X * (μV * SV) := by rw [h1]
    _ = X * (μV * (SV * C) / (μW * SW) * (μW * SW)) := by rw [h2]; ring
    _ = μV * (SV * C) / (μW * SW) * (X * (μW * SW)) := by ring

/-- The orbit Riesz ratio after cancellation (algebraic form): if
`ρ = c_G · ((∏_T gR/∏_T gF) · X) / (μ_V ∏_B (s_V c) / (μ_W ∏_B s_W))` and the local identities
hold, then `ρ = c_G · (X · (μ_W ∏_B s_W)) / (∏_B D · (μ_V ∏_B s_V))`. -/
theorem ENNReal.orbitRatio_eq_of_local {α : Type*} [DecidableEq α] {T B : Finset α}
    (hBT : B ⊆ T) (gF gR c D sV sW : α → ℝ≥0∞) {ρ cG X μV μW : ℝ≥0∞}
    (hρ : ρ = cG * ((∏ v ∈ T, gR v) / (∏ v ∈ T, gF v) * X /
      (μV * (∏ v ∈ B, sV v * c v) / (μW * ∏ v ∈ B, sW v))))
    (hB : ∀ v ∈ B, gR v * D v = gF v * c v) (hrest : ∀ v ∈ T \ B, gR v = gF v)
    (hgF0 : ∀ v ∈ T, gF v ≠ 0) (hgFt : ∀ v ∈ T, gF v ≠ ⊤)
    (hD0 : ∀ v ∈ B, D v ≠ 0) (hDt : ∀ v ∈ B, D v ≠ ⊤)
    (hc0 : ∀ v ∈ B, c v ≠ 0) (hct : ∀ v ∈ B, c v ≠ ⊤)
    (hsV0 : ∀ v ∈ B, sV v ≠ 0) (hsVt : ∀ v ∈ B, sV v ≠ ⊤)
    (hsW0 : ∀ v ∈ B, sW v ≠ 0) (hsWt : ∀ v ∈ B, sW v ≠ ⊤)
    (hV0 : μV ≠ 0) (hVt : μV ≠ ⊤) (hW0 : μW ≠ 0) (hWt : μW ≠ ⊤) :
    ρ = cG * (X * (μW * ∏ v ∈ B, sW v) / ((∏ v ∈ B, D v) * (μV * ∏ v ∈ B, sV v))) := by
  rw [hρ, ENNReal.prod_div_prod_eq_of_local hBT gF gR c D hB hrest hgF0 hgFt hD0 hDt,
    Finset.prod_mul_distrib]
  congr 1
  exact ENNReal.localDensity_cancel (Finset.prod_ne_zero_iff.2 hc0) (ENNReal.prod_ne_top hct)
    (Finset.prod_ne_zero_iff.2 hD0) (ENNReal.prod_ne_top hDt) hV0 hVt
    (Finset.prod_ne_zero_iff.2 hsV0) (ENNReal.prod_ne_top hsVt) hW0 hWt
    (Finset.prod_ne_zero_iff.2 hsW0) (ENNReal.prod_ne_top hsWt)

/-- The orbit Riesz ratio after cancellation, in the index shapes of the evaluated ratio: local masses
indexed by primes of `T`, local densities indexed by the subtype of `B ⊆ T`. -/
theorem ENNReal.orbitRatio_eq_of_local_places
    [DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ)]
    {T B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)} (hBT : B ⊆ T)
    (gF gR : ℕ → ℝ≥0∞) (c : {v // v ∈ B} → ℝ≥0∞)
    (D sV sW : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞) {ρ cG X μV μW : ℝ≥0∞}
    (hρ : ρ = cG * ((∏ p ∈ placeBlockPrimes T, gR p) / (∏ p ∈ placeBlockPrimes T, gF p) * X /
      (μV * (∏ v : {v // v ∈ B}, sV v.1 * c v) / (μW * ∏ v : {v // v ∈ B}, sW v.1))))
    (hB : ∀ v (h : v ∈ B), gR (primesEquiv v : ℕ) * D v = gF (primesEquiv v : ℕ) * c ⟨v, h⟩)
    (hrest : ∀ v ∈ T \ B, gR (primesEquiv v : ℕ) = gF (primesEquiv v : ℕ))
    (hgF0 : ∀ v ∈ T, gF (primesEquiv v : ℕ) ≠ 0) (hgFt : ∀ v ∈ T, gF (primesEquiv v : ℕ) ≠ ⊤)
    (hD0 : ∀ v ∈ B, D v ≠ 0) (hDt : ∀ v ∈ B, D v ≠ ⊤)
    (hc0 : ∀ v, c v ≠ 0) (hct : ∀ v, c v ≠ ⊤)
    (hsV0 : ∀ v ∈ B, sV v ≠ 0) (hsVt : ∀ v ∈ B, sV v ≠ ⊤)
    (hsW0 : ∀ v ∈ B, sW v ≠ 0) (hsWt : ∀ v ∈ B, sW v ≠ ⊤)
    (hV0 : μV ≠ 0) (hVt : μV ≠ ⊤) (hW0 : μW ≠ 0) (hWt : μW ≠ ⊤) :
    ρ = cG * (X * (μW * ∏ v : {v // v ∈ B}, sW v.1) /
      ((∏ v ∈ B, D v) * (μV * ∏ v : {v // v ∈ B}, sV v.1))) := by
  let c' : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞ := fun v ↦
    if h : v ∈ B then c ⟨v, h⟩ else 1
  have hc' : ∀ v : {v // v ∈ B}, c v = c' v.1 := fun v ↦ by simp [c', v.2]
  have hsc : (∏ v : {v // v ∈ B}, sV v.1 * c v) = ∏ v ∈ B, sV v * c' v := by
    rw [← Finset.prod_coe_sort B]
    exact Fintype.prod_congr _ _ fun v ↦ by rw [hc' v]
  have hsW : (∏ v : {v // v ∈ B}, sW v.1) = ∏ v ∈ B, sW v := Finset.prod_coe_sort B sW
  have hsV : (∏ v : {v // v ∈ B}, sV v.1) = ∏ v ∈ B, sV v := Finset.prod_coe_sort B sV
  rw [prod_placeBlockPrimes_eq, prod_placeBlockPrimes_eq, hsc, hsW] at hρ
  rw [hsW, hsV]
  refine ENNReal.orbitRatio_eq_of_local hBT (fun v ↦ gF (primesEquiv v : ℕ))
    (fun v ↦ gR (primesEquiv v : ℕ)) c' D sV sW hρ (fun v hv ↦ ?_) hrest hgF0 hgFt hD0 hDt
    (fun v hv ↦ by simp only [c', dif_pos hv]; exact hc0 _)
    (fun v hv ↦ by simp only [c', dif_pos hv]; exact hct _) hsV0 hsVt hsW0 hsWt hV0 hVt hW0 hWt
  simp only [c', dif_pos hv]
  exact hB v hv
