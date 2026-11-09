import SMSFormula.QuadraticAnisotropicDecompositionIsometry

/-!
# Base change of quadratic isometries

Mathlib supplies base change for quadratic forms and linear equivalences, but
does not currently package their compatibility as a quadratic isometry
equivalence.  This file proves that compatibility directly on the abstract
tensor-product carriers.

No finite basis or coordinate realization is used.
-/

noncomputable section

namespace QuadraticMap.IsometryEquiv

variable {R A M₁ M₂ : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M₁] [AddCommGroup M₂]
variable [Module R M₁] [Module R M₂]
variable [Invertible (2 : R)] [Invertible (2 : A)]
variable {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- A quadratic isometry equivalence preserves the associated bilinear forms. -/
theorem map_associated (e : Q₁.IsometryEquiv Q₂) (x y : M₁) :
    Q₂.associated (e x) (e y) = Q₁.associated x y := by
  simp only [QuadraticMap.associated_apply]
  rw [← map_add e]
  rw [e.map_app, e.map_app, e.map_app]

/-- Base change of a quadratic isometry equivalence, on the native abstract
tensor-product carriers. -/
def baseChange (e : Q₁.IsometryEquiv Q₂) :
    (Q₁.baseChange A).IsometryEquiv (Q₂.baseChange A) where
  toLinearEquiv := LinearEquiv.baseChange R A M₁ M₂ e.toLinearEquiv
  map_app' z := by
    rw [← (Q₂.baseChange A).associated_eq_self_apply ℕ]
    rw [← (Q₁.baseChange A).associated_eq_self_apply ℕ]
    suffices hbilin : ∀ x y : TensorProduct R A M₁,
        (Q₂.baseChange A).associated
            (LinearEquiv.baseChange R A M₁ M₂ e.toLinearEquiv x)
            (LinearEquiv.baseChange R A M₁ M₂ e.toLinearEquiv y) =
          (Q₁.baseChange A).associated x y by
      exact hbilin z z
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        intro z
        simp only [map_add, LinearMap.add_apply, hx z, hy z]
    | tmul a x =>
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y z hy hz =>
            simp only [map_add, hy, hz]
        | tmul b y =>
            rw [LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul]
            rw [QuadraticForm.associated_baseChange,
              LinearMap.BilinForm.baseChange_tmul]
            rw [QuadraticForm.associated_baseChange,
              LinearMap.BilinForm.baseChange_tmul]
            change Q₂.associated (e x) (e y) • (a * b) =
              Q₁.associated x y • (a * b)
            rw [e.map_associated]

@[simp]
theorem baseChange_tmul (e : Q₁.IsometryEquiv Q₂) (a : A) (x : M₁) :
    e.baseChange (A := A) (a ⊗ₜ[R] x) = a ⊗ₜ[R] e x :=
  LinearEquiv.baseChange_tmul R A M₁ M₂ (e := e.toLinearEquiv) a x

end QuadraticMap.IsometryEquiv
