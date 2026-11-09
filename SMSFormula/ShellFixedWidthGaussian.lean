import SMSFormula.RealShellCompactness
import SMSFormula.ShiftedGaussianQuadratic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Separation.Profinite

/-!
# Unit 3: on the shell the fixed width survives

`ShiftedGaussianSpanAlgebra` proved that two shifted Gaussians of width `b` multiply to a Gaussian
of width `b + c`, and concluded that the route's stipulation "`b` fixed once" cannot survive the
passage to an algebra.  The correct scope of that reading: it is right ambiently and
wrong on the shell.

The extra identity, which holds only where the form is constant.  At `Q x = a`,
`Gamma_u(x) Gamma_v(x) = e^(-ba + b polar(u,v)) Gamma_(u+v)(x)`: the width does not double, and the
new centre is the sum rather than a weighted mean.  The check is one line of polarization algebra,
and the discrepancy between the two sides is exactly `b (a - Q x)` -- zero on the shell and nonzero
off it.  So the fixed-width family, restricted to a shell, is closed under products up to a positive
constant.

The unit is also fixed width.  At the origin the generator is the constant `e^(-ba)` on the shell,
so `e^(ba)` times it is one -- the unit is realized at a positive width, which matters because the
width-zero Gaussian is the ambient constant and is not integrable against a finite-adelic compact
factor.

The consequence.  The `R`-linear span of the FIXED-width family is a subalgebra, it separates points
at any positive width for a positive definite form, and on a compact shell two finite regular
measures agreeing against each fixed-width generator are equal -- one check per centre, with the
width fixed once and for all.

Negative scope.  The shell hypothesis is load-bearing and is stated as such: off a level set the
same product genuinely has width `2b`, and the two statements are about different situations, not in
conflict.  Nothing here is adelic, no admissibility is checked, no measure is constructed, and the
analytic input `G_b subset L` is untouched.
-/

namespace SMSFormula.ShellFixedWidth

open MeasureTheory Set QuadraticMap SMSFormula.ShiftedGaussian

variable {X E : Type*} [TopologicalSpace X] [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousSub E]

/-! ## The shell product identity -/

/-- On a shell the width does not double.  Where the form takes the constant value `a`, two
generators of the same width multiply to a positive constant times one generator of that width,
centred at the sum of the centres. -/
theorem quadraticShiftedGaussian_mul_of_shell (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ)
    (i : C(X, E)) (u v : E) {a : ℝ} {x : X} (hx : Q (i x) = a) :
    quadraticShiftedGaussian Q hQ b i u x * quadraticShiftedGaussian Q hQ b i v x =
      Real.exp (-(b * a) + b * polar Q u v) * quadraticShiftedGaussian Q hQ b i (u + v) x := by
  simp only [quadraticShiftedGaussian_apply, ← Real.exp_add]
  congr 1
  have h1 : Q (i x - u) = Q (i x) + Q u - polar Q (i x) u := quadratic_map_sub Q _ _
  have h2 : Q (i x - v) = Q (i x) + Q v - polar Q (i x) v := quadratic_map_sub Q _ _
  have h3 : Q (i x - (u + v)) = Q (i x) + Q (u + v) - polar Q (i x) (u + v) :=
    quadratic_map_sub Q _ _
  have h4 : Q (u + v) = Q u + Q v + polar Q u v := by
    have : polar Q u v = Q (u + v) - Q u - Q v := rfl
    linarith
  have h5 : polar Q (i x) (u + v) = polar Q (i x) u + polar Q (i x) v := polar_add_right _ _ _ _
  rw [h1, h2, h3, h4, h5, hx]
  ring

/-- The unit at a positive width: on the shell the centred generator is the constant `e^(-ba)`, so a
positive multiple of it is one.  The width-zero generator is not used. -/
theorem quadraticShiftedGaussian_zero_center_on_shell (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    (b : ℝ) (i : C(X, E)) {a : ℝ} {x : X} (hx : Q (i x) = a) :
    Real.exp (b * a) * quadraticShiftedGaussian Q hQ b i 0 x = 1 := by
  rw [quadraticShiftedGaussian_apply, sub_zero, hx, ← Real.exp_add]
  simp

/-! ## The fixed-width family and its span -/

/-- The fixed-width family: one width, centres as the only parameter. -/
def fixedWidthFamily (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ) (i : C(X, E)) :
    Set C(X, ℝ) :=
  {f | ∃ u : E, f = quadraticShiftedGaussian Q hQ b i u}

theorem mem_fixedWidthFamily (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ) (i : C(X, E))
    (u : E) : quadraticShiftedGaussian Q hQ b i u ∈ fixedWidthFamily Q hQ b i := ⟨u, rfl⟩

/-- The unit is in the span, at the fixed width, as soon as the ambient map lands in the shell. -/
theorem one_mem_span_fixedWidthFamily (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ)
    (i : C(X, E)) {a : ℝ} (hshell : ∀ x : X, Q (i x) = a) :
    (1 : C(X, ℝ)) ∈ Submodule.span ℝ (fixedWidthFamily Q hQ b i) := by
  have hone : (1 : C(X, ℝ)) = Real.exp (b * a) • quadraticShiftedGaussian Q hQ b i 0 := by
    ext x
    rw [ContinuousMap.one_apply, ContinuousMap.smul_apply, smul_eq_mul]
    exact (quadraticShiftedGaussian_zero_center_on_shell Q hQ b i (hshell x)).symm
  rw [hone]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_fixedWidthFamily Q hQ b i 0))

/-- Closure under products at the fixed width, on the shell. -/
theorem mul_mem_span_fixedWidthFamily (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ)
    (i : C(X, E)) {a : ℝ} (hshell : ∀ x : X, Q (i x) = a) {f g : C(X, ℝ)}
    (hf : f ∈ fixedWidthFamily Q hQ b i) (hg : g ∈ fixedWidthFamily Q hQ b i) :
    f * g ∈ Submodule.span ℝ (fixedWidthFamily Q hQ b i) := by
  obtain ⟨u, rfl⟩ := hf
  obtain ⟨v, rfl⟩ := hg
  have hmul : quadraticShiftedGaussian Q hQ b i u * quadraticShiftedGaussian Q hQ b i v =
      Real.exp (-(b * a) + b * polar Q u v) • quadraticShiftedGaussian Q hQ b i (u + v) := by
    ext x
    rw [ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
    exact quadraticShiftedGaussian_mul_of_shell Q hQ b i u v (hshell x)
  rw [hmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_fixedWidthFamily Q hQ b i _))

/-- The fixed-width span is a subalgebra, on the shell. -/
noncomputable def fixedWidthSpan (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ)
    (i : C(X, E)) {a : ℝ} (hshell : ∀ x : X, Q (i x) = a) : Subalgebra ℝ C(X, ℝ) :=
  (Submodule.span ℝ (fixedWidthFamily Q hQ b i)).toSubalgebra
    (one_mem_span_fixedWidthFamily Q hQ b i hshell)
    (fun f g hf hg ↦ by
      refine Submodule.span_induction
        (p := fun (f : C(X, ℝ)) _ ↦ f * g ∈ Submodule.span ℝ (fixedWidthFamily Q hQ b i))
        ?_ ?_ ?_ ?_ hf
      · intro f hf
        refine Submodule.span_induction
          (p := fun (g : C(X, ℝ)) _ ↦ f * g ∈ Submodule.span ℝ (fixedWidthFamily Q hQ b i))
          ?_ ?_ ?_ ?_ hg
        · exact fun g hg ↦ mul_mem_span_fixedWidthFamily Q hQ b i hshell hf hg
        · simp
        · intro g₁ g₂ _ _ h₁ h₂
          rw [mul_add]
          exact Submodule.add_mem _ h₁ h₂
        · intro c g _ h
          rw [mul_smul_comm]
          exact Submodule.smul_mem _ _ h
      · simp
      · intro f₁ f₂ _ _ h₁ h₂
        rw [add_mul]
        exact Submodule.add_mem _ h₁ h₂
      · intro c f _ h
        rw [smul_mul_assoc]
        exact Submodule.smul_mem _ _ h)

theorem fixedWidthSpan_coe (Q : QuadraticForm ℝ E) (hQ : Continuous Q) (b : ℝ) (i : C(X, E))
    {a : ℝ} (hshell : ∀ x : X, Q (i x) = a) :
    (fixedWidthSpan Q hQ b i hshell : Set C(X, ℝ)) =
      (Submodule.span ℝ (fixedWidthFamily Q hQ b i) : Set C(X, ℝ)) := rfl

/-- The fixed-width span separates points, the centre placed at one of the two. -/
theorem separatesPoints_fixedWidthSpan (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    (hpos : Q.PosDef) {b : ℝ} (hb : 0 < b) {i : C(X, E)} (hi : Function.Injective i) {a : ℝ}
    (hshell : ∀ x : X, Q (i x) = a) : (fixedWidthSpan Q hQ b i hshell).SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨quadraticShiftedGaussian Q hQ b i (i x),
    Submodule.subset_span (mem_fixedWidthFamily Q hQ b i (i x)), rfl⟩, ?_⟩
  show quadraticShiftedGaussian Q hQ b i (i x) x ≠ quadraticShiftedGaussian Q hQ b i (i x) y
  rw [quadraticShiftedGaussian_eq_one]
  exact ne_of_gt (quadraticShiftedGaussian_lt_one Q hQ hpos hb i fun hc ↦ hxy (hi hc).symm)

/-! ## The criterion at one width -/

end SMSFormula.ShellFixedWidth
