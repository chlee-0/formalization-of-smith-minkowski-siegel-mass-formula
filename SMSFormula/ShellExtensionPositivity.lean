import SMSFormula.ShellLocalBoundExtension

/-!
# Unit 4, completed: the density and the positivity of the extension

Two items were left owed. The extension's density hypothesis was named, not supplied; and the
extension itself was a metric construction, so its positivity -- the property the Riesz layer
actually consumes -- was not proved. Both are closed here.

The density is stone--WEIERSTRASS, and the subalgebra is already in hand. On a compact space a
point-separating subalgebra of the real continuous functions is dense, and the fixed-width shell
span was already shown to be a subalgebra separating points at any positive width for a positive
definite form. So the density hypothesis is discharged from what the shell layer had already
proved -- nothing new is constructed.

Positivity of the extension is a one-epsilon argument, no sequences. Given a nonnegative target,
density supplies `g` in the subspace within `eps`; then `g + eps u` is pointwise nonnegative, since
`g` exceeds `f - eps` and the unit is at least one, so positivity on the subspace gives
`lam g >= -eps lam(u)`.  Splitting `Lambda f = Lambda (f - g) + lam g` and bounding the first term
by `‖Lambda‖ eps` leaves `Lambda f >= -eps (lam(u) + ‖Lambda‖)`, and choosing the single `eps`
against the assumed strict negativity contradicts it.  No limit of a sequence is taken and no
compactness beyond the one already used for the sup norm.

The payoff: on a compact space, a positive linear functional on a dense subspace containing a unit
at least one extends to a positive continuous linear functional on all of `C(X, R)` -- which is the
shape mathlib's Riesz layer consumes.

Negative scope.  The unit hypothesis is doing real work in both halves, as the bound and the
nonnegativity of `g + eps u` both use it.  Nothing here constructs the functional itself, exhibits a
measure, or is adelic; and the analytic admissibility `G_b subset L` is not
addressed here.
-/

namespace SMSFormula.ShellLocalBound

open MeasureTheory Set SMSFormula.ShiftedGaussian SMSFormula.ShellFixedWidth

/-! ## The density, from Stone--Weierstrass -/

variable {X : Type*} [TopologicalSpace X]

/-- A point-separating subalgebra is dense on a compact space -- mathlib's Stone--Weierstrass,
restated as the density the extension consumes. -/
theorem dense_of_separatesPoints [CompactSpace X] (A : Subalgebra ℝ C(X, ℝ))
    (hA : A.SeparatesPoints) : Dense (A : Set C(X, ℝ)) := by
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  have hcoe : (closure (A : Set C(X, ℝ))) = (⊤ : Subalgebra ℝ C(X, ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe, htop]
  rw [dense_iff_closure_eq, hcoe]
  rfl

/-- The shell's own fixed-width span is dense, from the separation already proved for it. -/
theorem dense_fixedWidthSpan {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousSub E] [CompactSpace X] (Q : QuadraticForm ℝ E) (hQ : Continuous Q)
    (hposQ : Q.PosDef) {b : ℝ} (hb : 0 < b) {i : C(X, E)} (hi : Function.Injective i) {a : ℝ}
    (hshell : ∀ x : X, Q (i x) = a) :
    Dense ((fixedWidthSpan Q hQ b i hshell : Subalgebra ℝ C(X, ℝ)) : Set C(X, ℝ)) :=
  dense_of_separatesPoints _ (separatesPoints_fixedWidthSpan Q hQ hposQ hb hi hshell)

/-! ## Positivity of the extension -/

/-- The extension is positive.  One `eps` is chosen against the assumed strict negativity; there is
no sequence and no limit.  The unit is used twice: for the bound, and to make `g + eps u`
nonnegative. -/
theorem extendToAll_nonneg [CompactSpace X] {V : Submodule ℝ C(X, ℝ)} (lam : V →ₗ[ℝ] ℝ)
    (hpos : ∀ g : V, (∀ x, 0 ≤ (g : C(X, ℝ)) x) → 0 ≤ lam g) (u : V)
    (hu : ∀ x, 1 ≤ (u : C(X, ℝ)) x) (hdense : Dense (V : Set C(X, ℝ))) (f : C(X, ℝ))
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ extendToAll lam hpos u hu f := by
  set Λ := extendToAll lam hpos u hu with hΛ
  by_contra hneg
  push_neg at hneg
  have hlamu : 0 ≤ lam u := hpos u fun x ↦ le_trans zero_le_one (hu x)
  set C : ℝ := lam u + ‖Λ‖ + 1 with hC
  have hCpos : 0 < C := by
    have := norm_nonneg Λ
    rw [hC]
    linarith
  set ε : ℝ := -(Λ f) / C with hε
  have hεpos : 0 < ε := div_pos (by linarith) hCpos
  obtain ⟨g, hgV, hgd⟩ := hdense.exists_dist_lt f hεpos
  set gv : V := ⟨g, hgV⟩ with hgv
  have hnorm : ‖f - g‖ < ε := by
    rw [← dist_eq_norm]
    exact hgd
  have hptw : ∀ x, |f x - g x| ≤ ‖f - g‖ := fun x ↦ by
    simpa [Real.norm_eq_abs] using (f - g).norm_coe_le_norm x
  have hlamg : -(ε * lam u) ≤ lam gv := by
    have hnn : 0 ≤ lam (ε • u + gv) := by
      refine hpos _ fun x ↦ ?_
      have h1 : |f x - g x| ≤ ‖f - g‖ := hptw x
      have h2 : ε * 1 ≤ ε * (u : C(X, ℝ)) x := mul_le_mul_of_nonneg_left (hu x) hεpos.le
      simp only [Submodule.coe_add, Submodule.coe_smul, ContinuousMap.add_apply,
        ContinuousMap.smul_apply, smul_eq_mul, hgv]
      have h3 : f x - g x ≤ ‖f - g‖ := le_trans (le_abs_self _) h1
      have h4 : 0 ≤ f x := hf x
      linarith
    rw [map_add, map_smul, smul_eq_mul] at hnn
    linarith
  have hsplit : Λ f = Λ (f - g) + lam gv := by
    have hg : Λ g = lam gv := extendToAll_apply lam hpos u hu hdense gv
    have : Λ f = Λ (f - g) + Λ g := by rw [map_sub]; ring
    rw [this, hg]
  have hbound : |Λ (f - g)| ≤ ‖Λ‖ * ε := by
    have h1 : ‖Λ (f - g)‖ ≤ ‖Λ‖ * ‖f - g‖ := Λ.le_opNorm _
    have h2 : ‖Λ‖ * ‖f - g‖ ≤ ‖Λ‖ * ε :=
      mul_le_mul_of_nonneg_left hnorm.le (norm_nonneg Λ)
    rw [Real.norm_eq_abs] at h1
    linarith
  have hlow : -(ε * lam u) - ‖Λ‖ * ε ≤ Λ f := by
    have := (abs_le.mp hbound).1
    linarith [hsplit]
  have hεC : ε * C = -(Λ f) := by
    rw [hε]
    field_simp
  nlinarith [hεpos, hlamu, norm_nonneg Λ, hεC, hlow]

/-- The payoff: on a compact space a positive functional on a dense subspace with a unit at least one
extends to a positive continuous linear functional on the whole of `C(X, R)`. -/
theorem exists_positive_extension [CompactSpace X] {V : Submodule ℝ C(X, ℝ)} (lam : V →ₗ[ℝ] ℝ)
    (hpos : ∀ g : V, (∀ x, 0 ≤ (g : C(X, ℝ)) x) → 0 ≤ lam g) (u : V)
    (hu : ∀ x, 1 ≤ (u : C(X, ℝ)) x) (hdense : Dense (V : Set C(X, ℝ))) :
    ∃ Λ : C(X, ℝ) →L[ℝ] ℝ, (∀ g : V, Λ (g : C(X, ℝ)) = lam g) ∧
      ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Λ f :=
  ⟨extendToAll lam hpos u hu, fun g ↦ extendToAll_apply lam hpos u hu hdense g,
    fun f hf ↦ extendToAll_nonneg lam hpos u hu hdense f hf⟩

end SMSFormula.ShellLocalBound
