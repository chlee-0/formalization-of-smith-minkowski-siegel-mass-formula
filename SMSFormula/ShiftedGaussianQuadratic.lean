import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The shifted Gaussians over a quadratic form

The abstract shifted-Gaussian layer was built over a real inner product space, with the Gaussian
written through the norm, `exp(-b‖x-u‖^2)`.  But the shifted Gaussian family and the repository's
real Gaussian are written through the quadratic form, `exp(-2 pi b Q(x_inf - u))`, and a positive
definite rational form is not presented as a norm.  Instantiating the inner-product layer would
therefore require constructing an inner product space structure from the form.

This file avoids that construction.  Every algebraic fact in the layer holds over an arbitrary
quadratic form, with the polarization taking the place of the inner product:

`b Q(x-u) + c Q(x-v) = (b+c) Q(x-w) + (bc/(b+c)) Q(u-v)`,  `w = (bu+cv)/(b+c)`,

for any quadratic form `Q` whatever -- no positive definiteness, no norm, no inner product.  It is
completing the square, and completing the square never needed a metric.  Positive definiteness is
used at exactly one place, separation, where the exponent must be strictly negative away from
the center; nowhere else.

Consequences.  The product identity, the closure of the all-width family up to a positive constant,
the span being a subalgebra, `Algebra.adjoin` equalling that span, separation, and the determining
core all transfer verbatim.  So the shifted Gaussian family may be recognised directly as the
repository's real Gaussian at a shifted argument, with no inner product instance to build.

Scope: nothing here is adelic, no class membership is checked, and the continuity of the
form is a hypothesis -- a quadratic form on a general topological module need not be continuous.
-/

namespace SMSFormula.ShiftedGaussian

open MeasureTheory Set QuadraticMap

variable {X E : Type*} [TopologicalSpace X] [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousSub E]

/-! ## Completing the square over a quadratic form -/

omit [TopologicalSpace E] [ContinuousSub E] in
/-- The expansion: a difference is expanded by the polarization, which is what replaces the inner
product throughout. -/
theorem quadratic_map_sub (Q : QuadraticForm ℝ E) (x u : E) :
    Q (x - u) = Q x + Q u - polar Q x u := by
  have h : polar Q x (-u) = Q (x + -u) - Q x - Q (-u) := rfl
  rw [polar_neg_right, Q.map_neg] at h
  rw [sub_eq_add_neg]
  linarith

omit [TopologicalSpace E] [ContinuousSub E] in
/-- Completing the square over an arbitrary quadratic form.  No positive definiteness, no norm and
no inner product: only the polarization and its bilinearity. -/
theorem quadratic_combo (Q : QuadraticForm ℝ E) {b c : ℝ} (hs : b + c ≠ 0) (x u v : E) :
    b * Q (x - u) + c * Q (x - v) =
      (b + c) * Q (x - (b + c)⁻¹ • (b • u + c • v)) + (b * c / (b + c)) * Q (u - v) := by
  set w : E := (b + c)⁻¹ • (b • u + c • v) with hw
  have hu := quadratic_map_sub Q x u
  have hv := quadratic_map_sub Q x v
  have hwx := quadratic_map_sub Q x w
  have huv := quadratic_map_sub Q u v
  have hPw : polar Q x w = (b + c)⁻¹ * (b * polar Q x u + c * polar Q x v) := by
    rw [hw, polar_smul_right, polar_add_right, polar_smul_right, polar_smul_right]
    simp [smul_eq_mul, mul_add]
  have hsum : Q (b • u + c • v) = b * b * Q u + c * c * Q v + b * c * polar Q u v := by
    have h : polar Q (b • u) (c • v) = Q (b • u + c • v) - Q (b • u) - Q (c • v) := rfl
    rw [polar_smul_left, polar_smul_right, Q.map_smul, Q.map_smul] at h
    simp only [smul_eq_mul] at h
    linarith
  have hQw : Q w = (b + c)⁻¹ * (b + c)⁻¹ * (b * b * Q u + c * c * Q v + b * c * polar Q u v) := by
    rw [hw, Q.map_smul, hsum]
    simp [smul_eq_mul]
  rw [hu, hv, hwx, huv, hPw, hQw]
  field_simp
  ring

/-! ## The shifted Gaussian of a quadratic form -/

/-- The shifted Gaussian written through a quadratic form, which is the shape the route's family and
the repository's own real Gaussian actually have. -/
noncomputable def quadraticShiftedGaussian (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ)
    (i : C(X, E)) (u : E) : C(X, ℝ) :=
  ⟨fun x ↦ Real.exp (-b * Q (i x - u)),
    Real.continuous_exp.comp
      (continuous_const.mul (hQ.comp (i.continuous.sub continuous_const)))⟩

@[simp]
theorem quadraticShiftedGaussian_apply (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ)
    (i : C(X, E)) (u : E) (x : X) :
    quadraticShiftedGaussian Q hQ b i u x = Real.exp (-b * Q (i x - u)) := rfl

/-- The product identity over a quadratic form: a positive constant times one member at the summed
width, centered at the weighted mean. -/
theorem quadraticShiftedGaussian_mul (Q : QuadraticForm ℝ E) (hQ : Continuous Q) {b c : ℝ}
    (hs : b + c ≠ 0) (i : C(X, E)) (u v : E) :
    quadraticShiftedGaussian Q hQ b i u * quadraticShiftedGaussian Q hQ c i v =
      Real.exp (-(b * c / (b + c)) * Q (u - v)) •
        quadraticShiftedGaussian Q hQ (b + c) i ((b + c)⁻¹ • (b • u + c • v)) := by
  ext x
  simp only [ContinuousMap.mul_apply, quadraticShiftedGaussian_apply, ContinuousMap.smul_apply,
    smul_eq_mul, ← Real.exp_add]
  congr 1
  have h := quadratic_combo Q hs (i x) u v
  linarith

/-- At width zero it is the constant one, so the unit is in the family and is not adjoined. -/
@[simp]
theorem quadraticShiftedGaussian_zero_width (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    (i : C(X, E)) (u : E) : quadraticShiftedGaussian Q hQ 0 i u = 1 := by
  ext x
  rw [quadraticShiftedGaussian_apply, ContinuousMap.one_apply, neg_zero, zero_mul, Real.exp_zero]

/-! ## The all-width family and its span -/

/-- The all-width family over a quadratic form. -/
def quadraticFamily (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (i : C(X, E)) : Set C(X, ℝ) :=
  {f | ∃ b : ℝ, 0 ≤ b ∧ ∃ u : E, f = quadraticShiftedGaussian Q hQ b i u}

theorem quadraticShiftedGaussian_mem_family (Q : QuadraticForm ℝ E) (hQ : Continuous Q) {b : ℝ}
    (hb : 0 ≤ b) (i : C(X, E)) (u : E) :
    quadraticShiftedGaussian Q hQ b i u ∈ quadraticFamily Q hQ i := ⟨b, hb, u, rfl⟩

theorem one_mem_quadraticFamily [Nonempty E] (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    (i : C(X, E)) : (1 : C(X, ℝ)) ∈ quadraticFamily Q hQ i :=
  ⟨0, le_rfl, Classical.arbitrary E, (quadraticShiftedGaussian_zero_width Q hQ i _).symm⟩

/-- Closure under products up to a positive constant, over a quadratic form. -/
theorem mul_mem_span_quadraticFamily (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (i : C(X, E))
    {f g : C(X, ℝ)} (hf : f ∈ quadraticFamily Q hQ i) (hg : g ∈ quadraticFamily Q hQ i) :
    f * g ∈ Submodule.span ℝ (quadraticFamily Q hQ i) := by
  obtain ⟨b, hb, u, rfl⟩ := hf
  obtain ⟨c, hc, v, rfl⟩ := hg
  rcases eq_or_lt_of_le (add_nonneg hb hc) with hzero | hpos
  · have hb0 : b = 0 := le_antisymm (by linarith) hb
    have hc0 : c = 0 := le_antisymm (by linarith) hc
    subst hb0; subst hc0
    simp only [quadraticShiftedGaussian_zero_width, mul_one]
    exact Submodule.subset_span ⟨0, le_rfl, u, (quadraticShiftedGaussian_zero_width Q hQ i u).symm⟩
  · rw [quadraticShiftedGaussian_mul Q hQ hpos.ne' i u v]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (quadraticShiftedGaussian_mem_family Q hQ hpos.le i _))

/-- The span is a subalgebra, over a quadratic form. -/
noncomputable def quadraticSpan [Nonempty E] (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    (i : C(X, E)) : Subalgebra ℝ C(X, ℝ) :=
  (Submodule.span ℝ (quadraticFamily Q hQ i)).toSubalgebra
    (Submodule.subset_span (one_mem_quadraticFamily Q hQ i))
    (fun x y hx hy ↦ by
      refine Submodule.span_induction (p := fun x _ ↦ x * y ∈ Submodule.span ℝ _) ?_ ?_ ?_ ?_ hx
      · intro f hf
        refine Submodule.span_induction (p := fun y _ ↦ f * y ∈ Submodule.span ℝ _) ?_ ?_ ?_ ?_ hy
        · intro g hg; exact mul_mem_span_quadraticFamily Q hQ i hf hg
        · simp
        · intro y₁ y₂ _ _ h₁ h₂; rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
        · intro a y₁ _ h₁; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁
      · simp
      · intro x₁ x₂ _ _ h₁ h₂; rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
      · intro a x₁ _ h₁; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁)

theorem quadraticShiftedGaussian_mem_span [Nonempty E] (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    {b : ℝ} (hb : 0 ≤ b) (i : C(X, E)) (u : E) :
    quadraticShiftedGaussian Q hQ b i u ∈ quadraticSpan Q hQ i :=
  Submodule.subset_span (quadraticShiftedGaussian_mem_family Q hQ hb i u)

/-- The algebra generated is exactly the span, over a quadratic form. -/
theorem adjoin_quadraticFamily_eq_span [Nonempty E] (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    (i : C(X, E)) : Algebra.adjoin ℝ (quadraticFamily Q hQ i) = quadraticSpan Q hQ i :=
  le_antisymm (Algebra.adjoin_le fun _ hf ↦ Submodule.subset_span hf)
    (fun _ hf ↦ Algebra.span_le_adjoin ℝ _ hf)

/-! ## Separation, the one place positive definiteness is used -/

/-- At its own center the member is one. -/
theorem quadraticShiftedGaussian_eq_one (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ)
    (i : C(X, E)) (x : X) : quadraticShiftedGaussian Q hQ b i (i x) x = 1 := by
  simp

/-- Away from its center it is strictly below one -- and this is the only place positive
definiteness enters the whole layer. -/
theorem quadraticShiftedGaussian_lt_one (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    (hpos : Q.PosDef) {b : ℝ} (hb : 0 < b) (i : C(X, E)) {x y : X} (h : i y ≠ i x) :
    quadraticShiftedGaussian Q hQ b i (i x) y < 1 := by
  have hne : i y - i x ≠ 0 := sub_ne_zero.2 h
  have hQpos : 0 < Q (i y - i x) := hpos _ hne
  have : -b * Q (i y - i x) < 0 := by nlinarith
  simpa using Real.exp_lt_one_iff.2 this

/-- The span separates points, for a positive definite form at a positive width. -/
theorem separatesPoints_quadraticSpan [Nonempty E] (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    (hpos : Q.PosDef) {b : ℝ} (hb : 0 < b) {i : C(X, E)} (hi : Function.Injective i) :
    (quadraticSpan Q hQ i).SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨quadraticShiftedGaussian Q hQ b i (i x),
    quadraticShiftedGaussian_mem_span Q hQ hb.le i (i x), rfl⟩, ?_⟩
  show quadraticShiftedGaussian Q hQ b i (i x) x ≠ quadraticShiftedGaussian Q hQ b i (i x) y
  rw [quadraticShiftedGaussian_eq_one]
  exact ne_of_gt (quadraticShiftedGaussian_lt_one Q hQ hpos hb i fun hc ↦ hxy (hi hc).symm)

/-- The bridge, over a quadratic form: any subspace containing every generator contains the whole
algebra, so per-width membership remains sufficient. -/
theorem quadraticSpan_le_of_forall_mem [Nonempty E] (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    {i : C(X, E)} (W : Submodule ℝ C(X, ℝ))
    (hW : ∀ b : ℝ, 0 ≤ b → ∀ u : E, quadraticShiftedGaussian Q hQ b i u ∈ W) :
    ∀ f ∈ quadraticSpan Q hQ i, f ∈ W := by
  intro f hf
  refine Submodule.span_le.2 ?_ hf
  rintro g ⟨b, hb, u, rfl⟩
  exact hW b hb u

end SMSFormula.ShiftedGaussian
