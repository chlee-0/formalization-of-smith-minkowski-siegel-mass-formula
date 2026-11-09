import SMSFormula.ShellFixedWidthGaussian
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Unit 4: the local bound, and the extension off the restriction image

The functional is defined on the image of the restriction map -- that is what the trace-positivity
line produces, with no operator extending any function. To reach `C_c(X_a)` it has to be extended,
and what makes that possible is a bound.  This file supplies both.

The local bound is an order argument, not an analytic one.  A positive linear functional applied to
something squeezed between `-c u` and `c u` is squeezed between `-c lam(u)` and `c lam(u)`: apply
positivity to `c u - f` and to `c u + f`.  On a compact space, with `u` at least one everywhere, the
squeeze holds at `c = ‖f‖`, so `|lam f| <= ‖f‖ lam(u)`: the functional is bounded, with the bound
written out as its own value at the unit.  That unit is exactly what the shell supplies -- `e^(ba)`
times the centred fixed-width generator restricts to one on the shell.

The extension is then standard, and mathlib has it: a bounded linear map extends along a dense
uniform embedding, and the extension agrees with the original on the subspace.  The subspace
inclusion is an isometry, hence uniformly inducing, and density is exactly what Stone--Weierstrass
gives for a point-separating subalgebra containing the unit on a compact space.  So the functional
lands on the whole of `C(X, R)` with no choice made anywhere.

Negative scope.  Positivity of the extension is not proved here: the bound and the extension are
metric statements, and recovering the order on the closure is a separate step.  Density is a
hypothesis -- Stone--Weierstrass is not invoked here, only named.  And on a compact space `C_c`
coincides with `C`, so this reaches the route's target only once the shell's compactness is used;
nothing is adelic and no measure is constructed.
-/

namespace SMSFormula.ShellLocalBound

open MeasureTheory Set

variable {X : Type*} [TopologicalSpace X]

/-! ## The order bound -/

/-- The squeeze: a positive linear functional applied to something dominated by `c u` is bounded by
`c lam(u)`.  The whole argument is that positivity is applied twice, to `c u - f` and to `c u + f`. -/
theorem abs_le_of_dominated {V : Submodule ℝ C(X, ℝ)} (lam : V →ₗ[ℝ] ℝ)
    (hpos : ∀ g : V, (∀ x, 0 ≤ (g : C(X, ℝ)) x) → 0 ≤ lam g) (f u : V) {c : ℝ}
    (hdom : ∀ x, |(f : C(X, ℝ)) x| ≤ c * (u : C(X, ℝ)) x) :
    |lam f| ≤ c * lam u := by
  have h1 : 0 ≤ lam (c • u - f) := by
    refine hpos _ fun x ↦ ?_
    have hx := (abs_le.mp (hdom x)).2
    simp only [Submodule.coe_sub, Submodule.coe_smul, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    linarith
  have h2 : 0 ≤ lam (c • u + f) := by
    refine hpos _ fun x ↦ ?_
    have hx := (abs_le.mp (hdom x)).1
    simp only [Submodule.coe_add, Submodule.coe_smul, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    linarith
  rw [map_sub, map_smul, smul_eq_mul] at h1
  rw [map_add, map_smul, smul_eq_mul] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The local bound in sup norm: on a compact space, with a unit at least one everywhere, the
functional is bounded by its own value at that unit. -/
theorem abs_le_norm_mul [CompactSpace X] {V : Submodule ℝ C(X, ℝ)} (lam : V →ₗ[ℝ] ℝ)
    (hpos : ∀ g : V, (∀ x, 0 ≤ (g : C(X, ℝ)) x) → 0 ≤ lam g) (u : V)
    (hu : ∀ x, 1 ≤ (u : C(X, ℝ)) x) (f : V) : |lam f| ≤ ‖f‖ * lam u := by
  refine abs_le_of_dominated lam hpos f u fun x ↦ ?_
  have h1 : |(f : C(X, ℝ)) x| ≤ ‖(f : C(X, ℝ))‖ := by
    simpa [Real.norm_eq_abs] using (f : C(X, ℝ)).norm_coe_le_norm x
  have h2 : ‖(f : C(X, ℝ))‖ = ‖f‖ := rfl
  nlinarith [hu x, norm_nonneg f, h1, h2]

/-! ## The bounded functional and its extension -/

/-- The functional as a continuous linear map, the bound being its own value at the unit. -/
noncomputable def toContinuousLinearMap [CompactSpace X] {V : Submodule ℝ C(X, ℝ)}
    (lam : V →ₗ[ℝ] ℝ) (hpos : ∀ g : V, (∀ x, 0 ≤ (g : C(X, ℝ)) x) → 0 ≤ lam g) (u : V)
    (hu : ∀ x, 1 ≤ (u : C(X, ℝ)) x) : V →L[ℝ] ℝ :=
  lam.mkContinuous (lam u) fun f ↦ by
    rw [Real.norm_eq_abs]
    calc |lam f| ≤ ‖f‖ * lam u := abs_le_norm_mul lam hpos u hu f
      _ = lam u * ‖f‖ := mul_comm _ _

@[simp]
theorem toContinuousLinearMap_apply [CompactSpace X] {V : Submodule ℝ C(X, ℝ)}
    (lam : V →ₗ[ℝ] ℝ) (hpos : ∀ g : V, (∀ x, 0 ≤ (g : C(X, ℝ)) x) → 0 ≤ lam g) (u : V)
    (hu : ∀ x, 1 ≤ (u : C(X, ℝ)) x) (f : V) :
    toContinuousLinearMap lam hpos u hu f = lam f := rfl

/-- The subspace inclusion is uniformly inducing, being an isometry. -/
theorem isUniformInducing_subtypeL (V : Submodule ℝ C(X, ℝ)) [CompactSpace X] :
    IsUniformInducing (V.subtypeL : V → C(X, ℝ)) :=
  (isometry_subtype_coe (s := (V : Set C(X, ℝ)))).isUniformInducing

/-- The extension off the restriction image, along the dense inclusion. -/
noncomputable def extendToAll [CompactSpace X] {V : Submodule ℝ C(X, ℝ)} (lam : V →ₗ[ℝ] ℝ)
    (hpos : ∀ g : V, (∀ x, 0 ≤ (g : C(X, ℝ)) x) → 0 ≤ lam g) (u : V)
    (hu : ∀ x, 1 ≤ (u : C(X, ℝ)) x) : C(X, ℝ) →L[ℝ] ℝ :=
  (toContinuousLinearMap lam hpos u hu).extend V.subtypeL

/-- And it agrees with the original on the subspace, so nothing is redefined. -/
theorem extendToAll_apply [CompactSpace X] {V : Submodule ℝ C(X, ℝ)} (lam : V →ₗ[ℝ] ℝ)
    (hpos : ∀ g : V, (∀ x, 0 ≤ (g : C(X, ℝ)) x) → 0 ≤ lam g) (u : V)
    (hu : ∀ x, 1 ≤ (u : C(X, ℝ)) x) (hdense : Dense (V : Set C(X, ℝ))) (f : V) :
    extendToAll lam hpos u hu (f : C(X, ℝ)) = lam f := by
  have hdr : DenseRange (V.subtypeL : V → C(X, ℝ)) := by
    simpa [DenseRange, Subtype.range_coe] using hdense
  exact ContinuousLinearMap.extend_eq _ hdr (isUniformInducing_subtypeL V) f

end SMSFormula.ShellLocalBound
