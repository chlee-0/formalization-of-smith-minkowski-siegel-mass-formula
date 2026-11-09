import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Exact images of closed balls under near-linear maps, ultrametric case

Over an archimedean field a map close to an invertible linear map `A` only
contains a smaller ball around the image point. With ultrametric norms the image
of a closed ball is exactly the translated `A`-image of the ball, once
`‖A⁻¹‖ * c < 1`. Surjectivity is the Banach fixed point theorem on the complete
closed ball. Consequently the image has Haar measure equal to the Haar modulus
of `A` times the ball's measure: this is the local p-adic change of variables on
balls. No chart, section, baseline or normalization is chosen; the Haar
measures and the linear map are supplied.
-/

noncomputable section

open Metric Set Function
open scoped NNReal ENNReal

namespace ApproximatesLinearOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [IsUltrametricDist E]
    {f : E → F} {A : E ≃L[𝕜] F} {x : E} {ρ : ℝ} {c : ℝ≥0}

omit [IsUltrametricDist E] in
/-- The error term controlled through the inverse `A⁻¹`. -/
private theorem norm_symm_error_le
    (hf : ApproximatesLinearOn f (A : E →L[𝕜] F) (closedBall x ρ) c)
    {y y' : E} (hy : y ∈ closedBall x ρ) (hy' : y' ∈ closedBall x ρ) :
    ‖A.symm (f y - f y' - A (y - y'))‖ ≤ (‖(A.symm : F →L[𝕜] E)‖₊ * c : ℝ≥0) * ‖y - y'‖ := by
  calc ‖A.symm (f y - f y' - A (y - y'))‖
      ≤ ‖(A.symm : F →L[𝕜] E)‖ * ‖f y - f y' - A (y - y')‖ :=
        (A.symm : F →L[𝕜] E).le_opNorm _
    _ ≤ ‖(A.symm : F →L[𝕜] E)‖ * (c * ‖y - y'‖) :=
        mul_le_mul_of_nonneg_left (hf y hy y' hy') (norm_nonneg _)
    _ = _ := by push_cast; ring

/-- Forward inclusion: `A⁻¹(f y - f x)` stays in the closed ball of radius `ρ`. -/
theorem symm_sub_mem_closedBall
    (hf : ApproximatesLinearOn f (A : E →L[𝕜] F) (closedBall x ρ) c)
    (hc : ‖(A.symm : F →L[𝕜] E)‖₊ * c ≤ 1) {y : E} (hy : y ∈ closedBall x ρ) :
    A.symm (f y - f x) ∈ closedBall (0 : E) ρ := by
  have hx : x ∈ closedBall x ρ := mem_closedBall_self (le_trans dist_nonneg hy)
  have he := norm_symm_error_le hf hy hx
  have hyx : ‖y - x‖ ≤ ρ := by simpa [dist_eq_norm] using hy
  have hdecomp : A.symm (f y - f x) = (y - x) + A.symm (f y - f x - A (y - x)) := by
    simp [map_sub]
  rw [mem_closedBall_zero_iff, hdecomp]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hyx ?_)
  calc _ ≤ (‖(A.symm : F →L[𝕜] E)‖₊ * c : ℝ≥0) * ‖y - x‖ := he
    _ ≤ 1 * ‖y - x‖ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (norm_nonneg _)
    _ ≤ ρ := by rw [one_mul]; exact hyx

/-- Reverse inclusion: every translated `A`-image point of the ball is hit, by
the Banach fixed point theorem on the complete closed ball. -/
theorem exists_eq_add_of_mem_closedBall [CompleteSpace E]
    (hf : ApproximatesLinearOn f (A : E →L[𝕜] F) (closedBall x ρ) c)
    (hc : ‖(A.symm : F →L[𝕜] E)‖₊ * c < 1) {u : E} (hu : u ∈ closedBall (0 : E) ρ) :
    ∃ y ∈ closedBall x ρ, f y = f x + A u := by
  have hρ : 0 ≤ ρ := le_trans dist_nonneg hu
  have hx : x ∈ closedBall x ρ := mem_closedBall_self hρ
  have hun : ‖u‖ ≤ ρ := mem_closedBall_zero_iff.mp hu
  set K : ℝ≥0 := ‖(A.symm : F →L[𝕜] E)‖₊ * c with hK
  let T : E → E := fun y ↦ y + A.symm (f x + A u - f y)
  have hTsub : ∀ y, T y - x = u - A.symm (f y - f x - A (y - x)) := by
    intro y
    simp only [T, map_sub, map_add, ContinuousLinearEquiv.symm_apply_apply]
    abel
  have hmaps : MapsTo T (closedBall x ρ) (closedBall x ρ) := by
    intro y hy
    have hyx : ‖y - x‖ ≤ ρ := by simpa [dist_eq_norm] using hy
    rw [mem_closedBall, dist_eq_norm, hTsub, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hun ?_)
    rw [norm_neg]
    calc _ ≤ (K : ℝ) * ‖y - x‖ := norm_symm_error_le hf hy hx
      _ ≤ 1 * ‖y - x‖ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc.le) (norm_nonneg _)
      _ ≤ ρ := by rw [one_mul]; exact hyx
  have hTdiff : ∀ y y', T y - T y' = -A.symm (f y - f y' - A (y - y')) := by
    intro y y'
    simp only [T, map_sub, map_add, ContinuousLinearEquiv.symm_apply_apply]
    abel
  have hcontr : ContractingWith K (hmaps.restrict T (closedBall x ρ) (closedBall x ρ)) := by
    refine ⟨hc, LipschitzWith.of_dist_le_mul fun y y' ↦ ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    change ‖T y - T y'‖ ≤ K * ‖(y : E) - y'‖
    rw [hTdiff, norm_neg]
    exact norm_symm_error_le hf y.2 y'.2
  obtain ⟨y, hy, hfix, -⟩ := hcontr.exists_fixedPoint' isClosed_closedBall.isComplete hmaps hx
    (edist_ne_top _ _)
  refine ⟨y, hy, ?_⟩
  have h0 : A.symm (f x + A u - f y) = 0 := by
    have := hfix
    simp only [IsFixedPt, T] at this
    simpa using this
  have h1 : f x + A u - f y = 0 := by
    simpa using congrArg A h0
  exact (sub_eq_zero.mp h1).symm

/-- Exact image of a closed ball in the ultrametric case. -/
theorem image_closedBall_eq [CompleteSpace E]
    (hf : ApproximatesLinearOn f (A : E →L[𝕜] F) (closedBall x ρ) c)
    (hc : ‖(A.symm : F →L[𝕜] E)‖₊ * c < 1) :
    f '' closedBall x ρ = (fun u ↦ f x + A u) '' closedBall (0 : E) ρ := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨A.symm (f y - f x), hf.symm_sub_mem_closedBall hc.le hy, ?_⟩
    simp
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨y, hy, hfy⟩ := hf.exists_eq_add_of_mem_closedBall hc hu
    exact ⟨y, hy, hfy⟩

/-- Local change of variables on balls: the image of a closed ball has Haar
measure equal to the Haar modulus of `A` times the ball's measure. Both Haar
measures are supplied; the modulus is the scalar factor of `map A⁻¹ ν` against
`μ`, not normalized to one. -/
theorem measure_image_closedBall [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    [LocallyCompactSpace E] [SecondCountableTopology E]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (ν : MeasureTheory.Measure F) [ν.IsAddHaarMeasure] [ν.IsAddLeftInvariant]
    (hf : ApproximatesLinearOn f (A : E →L[𝕜] F) (closedBall x ρ) c)
    (hc : ‖(A.symm : F →L[𝕜] E)‖₊ * c < 1) :
    ν (f '' closedBall x ρ) =
      MeasureTheory.Measure.addHaarScalarFactor (ν.map A.symm) μ * μ (closedBall x ρ) := by
  rw [hf.image_closedBall_eq hc]
  have himage : (fun u ↦ f x + A u) '' closedBall (0 : E) ρ =
      (fun w ↦ f x + w) '' (A.symm ⁻¹' closedBall (0 : E) ρ) := by
    rw [← image_image (fun w ↦ f x + w) A, A.image_eq_preimage_symm]
  rw [himage, image_add_left, MeasureTheory.measure_preimage_add]
  have hmap : ν (A.symm ⁻¹' closedBall (0 : E) ρ) = ν.map A.symm (closedBall (0 : E) ρ) :=
    (MeasureTheory.Measure.map_apply A.symm.continuous.measurable
      isClosed_closedBall.measurableSet).symm
  rw [hmap]
  have h := MeasureTheory.Measure.isAddLeftInvariant_eq_smul (ν.map A.symm) μ
  refine (congrArg (fun m : MeasureTheory.Measure E ↦ m (closedBall (0 : E) ρ)) h).trans ?_
  simp only [MeasureTheory.Measure.smul_apply]
  congr 1
  have hb : closedBall x ρ = (fun h ↦ -x + h) ⁻¹' closedBall (0 : E) ρ := by
    ext y
    simp [mem_closedBall, dist_eq_norm, neg_add_eq_sub]
  rw [hb, MeasureTheory.measure_preimage_add]

end ApproximatesLinearOn

namespace HasStrictFDerivAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [IsUltrametricDist E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    [LocallyCompactSpace E] [SecondCountableTopology E]
    {f : E → F} {A : E ≃L[𝕜] F} {a : E}

/-- Local change of variables from a strict derivative with invertible value,
ultrametric domain: every closed ball inside a fixed neighbourhood of `a` has
image of Haar measure (Haar modulus of `A`) times its own measure. Only the
supplied Haar measures and the strict derivative enter; no chart is chosen. -/
theorem exists_measure_image_closedBall
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (ν : MeasureTheory.Measure F) [ν.IsAddHaarMeasure] [ν.IsAddLeftInvariant]
    (hf : HasStrictFDerivAt f (A : E →L[𝕜] F) a) :
    ∃ δ > 0, ∀ (x : E) (ρ : ℝ), closedBall x ρ ⊆ ball a δ →
      f '' closedBall x ρ = (fun u ↦ f x + A u) '' closedBall (0 : E) ρ ∧
      ν (f '' closedBall x ρ) =
        MeasureTheory.Measure.addHaarScalarFactor (ν.map A.symm) μ * μ (closedBall x ρ) := by
  set c : ℝ≥0 := ‖(A.symm : F →L[𝕜] E)‖₊⁻¹ / 2 with hcdef
  have hc : ‖(A.symm : F →L[𝕜] E)‖₊ * c < 1 := by
    rcases eq_or_ne ‖(A.symm : F →L[𝕜] E)‖₊ 0 with h0 | h0
    · rw [h0, zero_mul]; exact one_pos
    · rw [hcdef, mul_div_assoc', mul_inv_cancel₀ h0]
      exact NNReal.half_lt_self one_ne_zero
  have hc' : Subsingleton E ∨ 0 < c :=
    A.subsingleton_or_nnnorm_symm_pos.imp id fun h ↦ half_pos (inv_pos.2 h)
  obtain ⟨s, hs, happ⟩ := hf.approximates_deriv_on_nhds hc'
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨δ, hδ, fun x ρ hsub ↦ ?_⟩
  have happ' := happ.mono_set (hsub.trans hball)
  exact ⟨happ'.image_closedBall_eq hc, happ'.measure_image_closedBall μ ν hc⟩

end HasStrictFDerivAt
