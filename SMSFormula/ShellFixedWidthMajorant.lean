import SMSFormula.ShellFixedWidthGaussian
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Unit 3, second half: the fixed-width majorant confines the bad set

The trace-positivity lemma consumes a compact set containing the negative part of the test and
missing the fiber. For a compactly supported test that set is immediate, and that case is already
proved. The route's tests are Gaussian and have no compact support, so the compact bad set has to
come from somewhere else -- and it can be found without leaving the fixed width.

The two-centre identity, which is again pure polarization algebra. Shifting the centre by `+v` and
by `-v` and adding gives
`Gamma_(u+v)(x) + Gamma_(u-v)(x) = Gamma_u(x) e^(-bQ(v)) (e^(t) + e^(-t))`, `t = b polar(x-u, v)`.
The bracket is `2 cosh t`, so it grows without bound as `|t|` grows, while every member of the family
at that centre is a fixed multiple of `Gamma_u`.  So a finite sum of such pairs majorizes the
generator by a factor that grows in every direction the polarization sees.

The confinement.  If the test is dominated by `M Gamma_u` and the majorant contains the pair at `v`,
then wherever `Phi + eps Psi` is negative one gets `e^(|b polar(x-u,v)|) < (M/eps) e^(bQ(v))`: the
bad set lies in a slab.  No logarithm is taken and no limit is used -- the amplitude `eps` is the one
fixed in advance by the trace-positivity argument.

And finitely many slabs are bounded.  If the centres `v i` span and the form is positive definite,
the linear map `w |-> (polar(w, v i))_i` is injective, so in finite dimension it is antilipschitz and
pulls bounded sets back to bounded sets.  Hence the bad set is bounded, and being closed by
continuity it is compact.

Negative scope.  This is the archimedean factor.  The finite-adelic indicator is not carried here, so
the product's bad set is not assembled; the domination `|Phi| <= M Gamma_u` is a hypothesis, true for
a single-centre test and needing a finite sum in general; nothing is adelic; and the fiber-avoidance
half of the trace-positivity hypothesis is separate -- this supplies compactness, not disjointness
from the shell.
-/

namespace SMSFormula.ShellFixedWidth

open MeasureTheory Set QuadraticMap SMSFormula.ShiftedGaussian

/-! ## The two-centre identity -/

section Algebra

variable {X E : Type*} [TopologicalSpace X] [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousSub E]

/-- Shifting the centre both ways and adding: the sum is the generator at `u` times a fixed constant
times `e^t + e^(-t)`, with `t` the polarization against the shift. -/
theorem quadraticShiftedGaussian_add_shift (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ)
    (i : C(X, E)) (u v : E) (x : X) :
    quadraticShiftedGaussian Q hQ b i (u + v) x + quadraticShiftedGaussian Q hQ b i (u - v) x =
      quadraticShiftedGaussian Q hQ b i u x * Real.exp (-b * Q v) *
        (Real.exp (b * polar Q (i x - u) v) + Real.exp (-(b * polar Q (i x - u) v))) := by
  have hsub : i x - (u + v) = (i x - u) - v := by abel
  have hadd : i x - (u - v) = (i x - u) + v := by abel
  have h1 : Q ((i x - u) - v) = Q (i x - u) + Q v - polar Q (i x - u) v := quadratic_map_sub Q _ _
  have h2 : Q ((i x - u) + v) = Q (i x - u) + Q v + polar Q (i x - u) v := by
    have : polar Q (i x - u) v = Q ((i x - u) + v) - Q (i x - u) - Q v := rfl
    linarith
  simp only [quadraticShiftedGaussian_apply, hsub, hadd, h1, h2, mul_add, ← Real.exp_add]
  congr 1 <;> ring

/-- The growth: the bracket dominates `e^(|t|)`, so the pair sum grows in the direction `v`. -/
theorem exp_abs_le_exp_add_exp_neg (t : ℝ) : Real.exp |t| ≤ Real.exp t + Real.exp (-t) := by
  rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
    have := (Real.exp_pos (-t)).le
    linarith
  · rw [h]
    have := (Real.exp_pos t).le
    linarith

/-- The pair sum majorizes the generator by a factor growing with the polarization. -/
theorem exp_abs_polar_mul_le (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ) (i : C(X, E))
    (u v : E) (x : X) :
    quadraticShiftedGaussian Q hQ b i u x * Real.exp (-b * Q v) *
        Real.exp |b * polar Q (i x - u) v| ≤
      quadraticShiftedGaussian Q hQ b i (u + v) x + quadraticShiftedGaussian Q hQ b i (u - v) x := by
  rw [quadraticShiftedGaussian_add_shift Q hQ b i u v x]
  refine mul_le_mul_of_nonneg_left (exp_abs_le_exp_add_exp_neg _) ?_
  exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

/-- The confinement, with no logarithm and no limit: where the sum of the test and a fixed multiple
of the majorant is negative, the polarization against `v` is bounded. -/
theorem exp_abs_polar_lt_of_add_neg (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ)
    (i : C(X, E)) (u v : E) {Φ Ψ : X → ℝ} {M ε : ℝ} (hε : 0 < ε)
    (hdom : ∀ y, |Φ y| ≤ M * quadraticShiftedGaussian Q hQ b i u y)
    (hmaj : ∀ y, quadraticShiftedGaussian Q hQ b i (u + v) y +
      quadraticShiftedGaussian Q hQ b i (u - v) y ≤ Ψ y)
    {x : X} (hneg : Φ x + ε * Ψ x < 0) :
    Real.exp (-b * Q v) * Real.exp |b * polar Q (i x - u) v| < M / ε := by
  set G : ℝ := quadraticShiftedGaussian Q hQ b i u x with hG
  set P : ℝ := Real.exp (-b * Q v) * Real.exp |b * polar Q (i x - u) v| with hP
  have hGpos : 0 < G := by
    rw [hG, quadraticShiftedGaussian_apply]
    exact Real.exp_pos _
  have h1 : G * P ≤ Ψ x := by
    rw [hP, ← mul_assoc]
    exact le_trans (exp_abs_polar_mul_le Q hQ b i u v x) (hmaj x)
  have h2 : -(M * G) ≤ Φ x := neg_le_of_abs_le (hdom x)
  have h3 : ε * (G * P) < M * G := by
    have hle : ε * (G * P) ≤ ε * Ψ x := mul_le_mul_of_nonneg_left h1 hε.le
    linarith
  have h4 : G * (ε * P) < G * M := by
    calc G * (ε * P) = ε * (G * P) := by ring
      _ < M * G := h3
      _ = G * M := by ring
  have h5 : ε * P < M := lt_of_mul_lt_mul_left h4 hGpos.le
  rw [lt_div_iff₀ hε]
  linarith

/-- The slab, in the form the boundedness lemma consumes. -/
theorem abs_polar_le_log_of_add_neg (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ)
    (i : C(X, E)) (u v : E) {Φ Ψ : X → ℝ} {M ε : ℝ} (hε : 0 < ε)
    (hdom : ∀ y, |Φ y| ≤ M * quadraticShiftedGaussian Q hQ b i u y)
    (hmaj : ∀ y, quadraticShiftedGaussian Q hQ b i (u + v) y +
      quadraticShiftedGaussian Q hQ b i (u - v) y ≤ Ψ y)
    {x : X} (hneg : Φ x + ε * Ψ x < 0) :
    |b * polar Q (i x - u) v| ≤ Real.log (M / ε * Real.exp (b * Q v)) := by
  have hlt := exp_abs_polar_lt_of_add_neg Q hQ b i u v hε hdom hmaj hneg
  have hEpos : 0 < Real.exp (b * Q v) := Real.exp_pos _
  have hkey : Real.exp |b * polar Q (i x - u) v| ≤ M / ε * Real.exp (b * Q v) := by
    have h := mul_lt_mul_of_pos_right hlt hEpos
    have hcancel : Real.exp (-b * Q v) * Real.exp |b * polar Q (i x - u) v| *
        Real.exp (b * Q v) = Real.exp |b * polar Q (i x - u) v| := by
      rw [mul_right_comm, ← Real.exp_add]
      simp
    rw [hcancel] at h
    exact h.le
  have hCpos : 0 < M / ε * Real.exp (b * Q v) := lt_of_lt_of_le (Real.exp_pos _) hkey
  exact (Real.le_log_iff_exp_le hCpos).mpr hkey

end Algebra

/-! ## Finitely many slabs are bounded -/

section Bounded

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- The polarization coordinates against a family, as a linear map. -/
noncomputable def polarCoords (Q : QuadraticForm ℝ E) (v : ι → E) : E →ₗ[ℝ] (ι → ℝ) where
  toFun w := fun j ↦ polar Q w (v j)
  map_add' w w' := by
    funext j
    exact polar_add_left _ _ _ _
  map_smul' c w := by
    funext j
    exact polar_smul_left _ _ _ _

omit [Fintype ι] in
@[simp]
theorem polarCoords_apply (Q : QuadraticForm ℝ E) (v : ι → E) (w : E) (j : ι) :
    polarCoords Q v w j = polar Q w (v j) := rfl

/-- A positive definite form is nondegenerate, the polarization at a vector against itself being
twice its value. -/
theorem eq_zero_of_polar_eq_zero {Q : QuadraticForm ℝ E} (hpos : Q.PosDef) {w : E}
    (h : polar Q w w = 0) : w = 0 := by
  by_contra hw
  have hQ : 0 < Q w := hpos w hw
  have hdef : polar Q w w = Q (w + w) - Q w - Q w := rfl
  have hsmul : w + w = (2 : ℝ) • w := (two_smul ℝ w).symm
  have hQ2 : Q ((2 : ℝ) • w) = 2 * 2 * Q w := by simpa using Q.map_smul (2 : ℝ) w
  rw [hdef, hsmul, hQ2] at h
  linarith

omit [Fintype ι] in
/-- The coordinates are injective when the family spans and the form is positive definite. -/
theorem injective_polarCoords {Q : QuadraticForm ℝ E} (hpos : Q.PosDef) {v : ι → E}
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) : Function.Injective (polarCoords Q v) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  have hzero : ∀ j, polar Q w (v j) = 0 := by
    intro j
    exact congrFun (LinearMap.mem_ker.mp hw) j
  have hall : ∀ y : E, polar Q w y = 0 := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range v) := by rw [hspan]; trivial
    refine Submodule.span_induction (p := fun (y : E) _ ↦ polar Q w y = 0) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨j, rfl⟩
      exact hzero j
    · exact polar_zero_right _ _
    · intro y₁ y₂ _ _ h₁ h₂
      rw [polar_add_right, h₁, h₂, add_zero]
    · intro c y _ h
      rw [polar_smul_right, h, smul_zero]
  exact eq_zero_of_polar_eq_zero hpos (hall w)

/-- Finitely many slabs are bounded: an injective linear map on a finite-dimensional space is
antilipschitz, so it pulls a bounded set back to a bounded one. -/
theorem isBounded_polarSlab [FiniteDimensional ℝ E] {Q : QuadraticForm ℝ E}
    (hpos : Q.PosDef) {v : ι → E}
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) (R : ℝ) :
    Bornology.IsBounded {w : E | ∀ j, |polar Q w (v j)| ≤ R} := by
  obtain ⟨K, -, hK⟩ := (polarCoords Q v).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr (injective_polarCoords hpos hspan))
  have hsub : {w : E | ∀ j, |polar Q w (v j)| ≤ R} ⊆
      polarCoords Q v ⁻¹' (Metric.closedBall (0 : ι → ℝ) (max R 0)) := by
    intro w hw
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (le_max_right R 0)).mpr fun j ↦ ?_
    simpa using le_trans (hw j) (le_max_left R 0)
  exact (hK.isBounded_preimage Metric.isBounded_closedBall).subset hsub

end Bounded

end SMSFormula.ShellFixedWidth
