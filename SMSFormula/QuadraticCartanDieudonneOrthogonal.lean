import SMSFormula.QuadraticCartanDieudonneAlignment

/-!
# Orthogonal-complement reduction for quadratic Cartan--Dieudonne

For an anisotropic vector `x`, this file defines the polar-orthogonal
complement of `K x`, the restricted quadratic form, and the direct-sum
decomposition with the anisotropic line.  A quadratic isometry fixing `x`
restricts to an isometry of this complement.  In finite dimension its
finrank drops by one, and nondegeneracy of the ambient associated bilinear
form passes to the restricted form.

Applied to `reflectionCorrectionAt`, this packages the first genuine
dimension-reduction step of the Cartan--Dieudonne induction.  The induction
and the resulting reflection list remain separate subsequent steps.
-/

noncomputable section

open Module

namespace QuadraticMap

variable {K M : Type*} [Field K] [CharZero K]
variable [AddCommGroup M] [Module K M]
variable (Q : QuadraticForm K M)

/-- The polar-orthogonal complement of the line through `x`. -/
def anisotropicOrthogonal (x : M) : Submodule K M :=
  LinearMap.BilinForm.orthogonal Q.associated (K ∙ x)

theorem mem_anisotropicOrthogonal_iff {x y : M} :
    y ∈ Q.anisotropicOrthogonal x ↔ Q.associated.IsOrtho x y := by
  constructor
  · intro hy
    exact hy x (Submodule.mem_span_singleton_self x)
  · intro hxy z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change Q.associated x y = 0 at hxy
    change Q.associated (a • x) y = 0
    rw [LinearMap.map_smul, LinearMap.smul_apply, hxy, smul_zero]

/-- The quadratic form restricted to the orthogonal complement of `K x`. -/
def orthogonalRestriction (x : M) : QuadraticForm K (Q.anisotropicOrthogonal x) :=
  Q.comp (Q.anisotropicOrthogonal x).subtype

@[simp]
theorem orthogonalRestriction_apply (x : M) (y : Q.anisotropicOrthogonal x) :
    Q.orthogonalRestriction x y = Q y :=
  rfl

theorem associated_orthogonalRestriction (x : M) :
    (Q.orthogonalRestriction x).associated =
      LinearMap.BilinForm.restrict Q.associated (Q.anisotropicOrthogonal x) := by
  rw [orthogonalRestriction, QuadraticMap.associated_comp]
  rfl

theorem not_associated_isOrtho_self (x : M) (hx : Q x ≠ 0) :
    ¬Q.associated.IsOrtho x x := by
  intro h
  apply hx
  rw [← Q.associated_eq_self_apply ℕ x]
  exact h

theorem isCompl_span_anisotropicOrthogonal (x : M) (hx : Q x ≠ 0) :
    IsCompl (K ∙ x) (Q.anisotropicOrthogonal x) :=
  Q.associated.isCompl_span_singleton_orthogonal
    (Q.not_associated_isOrtho_self x hx)

/-- The direct-sum decomposition into the anisotropic line and its
polar-orthogonal complement. -/
def anisotropicDecompositionEquiv (x : M) (hx : Q x ≠ 0) :
    ((K ∙ x) × Q.anisotropicOrthogonal x) ≃ₗ[K] M :=
  Submodule.prodEquivOfIsCompl (K ∙ x) (Q.anisotropicOrthogonal x)
    (Q.isCompl_span_anisotropicOrthogonal x hx)

@[simp]
theorem anisotropicDecompositionEquiv_apply (x : M) (hx : Q x ≠ 0)
    (y : K ∙ x) (z : Q.anisotropicOrthogonal x) :
    Q.anisotropicDecompositionEquiv x hx (y, z) = y + z :=
  rfl

variable [FiniteDimensional K M]

theorem finrank_anisotropicOrthogonal_add_one (x : M) (hx : Q x ≠ 0) :
    finrank K (Q.anisotropicOrthogonal x) + 1 = finrank K M := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ Q.map_zero)
  have h := Submodule.finrank_add_eq_of_isCompl
    (Q.isCompl_span_anisotropicOrthogonal x hx)
  rw [finrank_span_singleton hx0, add_comm] at h
  exact h

omit [FiniteDimensional K M] in
theorem orthogonalRestriction_associated_nondegenerate
    (hQ : Q.associated.Nondegenerate) (x : M) (hx : Q x ≠ 0) :
    (Q.orthogonalRestriction x).associated.Nondegenerate := by
  rw [Q.associated_orthogonalRestriction x]
  exact LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton
    Q.associated hQ
    (QuadraticForm.associated_isSymm K Q).isRefl
    (Q.not_associated_isOrtho_self x hx)

end QuadraticMap

namespace QuadraticMap.IsometryEquiv

variable {K M : Type*} [Field K] [CharZero K]
variable [AddCommGroup M] [Module K M]
variable (Q : QuadraticForm K M)

theorem map_associated_self (g : Q.IsometryEquiv Q) (x y : M) :
    Q.associated (g x) (g y) = Q.associated x y := by
  simp only [QuadraticMap.associated_apply]
  have hsum : g (x + y) = g x + g y := g.toLinearEquiv.map_add x y
  rw [← hsum, g.map_app, g.map_app, g.map_app]

theorem map_associated_eq_zero_of_fixed
    (g : Q.IsometryEquiv Q) (x y : M) (hfix : g x = x)
    (hy : Q.associated.IsOrtho x y) :
    Q.associated.IsOrtho x (g y) := by
  calc
    Q.associated x (g y) = Q.associated (g x) (g y) := by rw [hfix]
    _ = Q.associated x y := g.map_associated_self Q x y
    _ = 0 := hy

def restrictToAnisotropicOrthogonal
    (g : Q.IsometryEquiv Q) (x : M) (hfix : g x = x) :
    Q.anisotropicOrthogonal x ≃ₗ[K] Q.anisotropicOrthogonal x where
  toFun y := ⟨g y, Q.mem_anisotropicOrthogonal_iff.mpr
    (g.map_associated_eq_zero_of_fixed Q x y hfix
      (Q.mem_anisotropicOrthogonal_iff.mp y.property))⟩
  invFun y := ⟨g.symm y, Q.mem_anisotropicOrthogonal_iff.mpr
    (g.symm.map_associated_eq_zero_of_fixed Q x y
      (g.toLinearEquiv.symm_apply_eq.mpr hfix.symm)
      (Q.mem_anisotropicOrthogonal_iff.mp y.property))⟩
  left_inv y := Subtype.ext (g.toLinearEquiv.symm_apply_apply y)
  right_inv y := Subtype.ext (g.toLinearEquiv.apply_symm_apply y)
  map_add' y z := Subtype.ext (g.toLinearEquiv.map_add y z)
  map_smul' a y := Subtype.ext (g.toLinearEquiv.map_smul a y)

@[simp]
theorem coe_restrictToAnisotropicOrthogonal
    (g : Q.IsometryEquiv Q) (x : M) (hfix : g x = x)
    (y : Q.anisotropicOrthogonal x) :
    (g.restrictToAnisotropicOrthogonal Q x hfix y : M) = g y :=
  rfl

def restrictIsometryEquivToAnisotropicOrthogonal
    (g : Q.IsometryEquiv Q) (x : M) (hfix : g x = x) :
    (Q.orthogonalRestriction x).IsometryEquiv (Q.orthogonalRestriction x) where
  toLinearEquiv := g.restrictToAnisotropicOrthogonal Q x hfix
  map_app' y := g.map_app y

def reflectionCorrectionAtOrthogonal
    (g : Q.IsometryEquiv Q) (x : M) (hx : Q x ≠ 0) :
    (Q.orthogonalRestriction x).IsometryEquiv (Q.orthogonalRestriction x) :=
  (g.reflectionCorrectionAt Q x hx).restrictIsometryEquivToAnisotropicOrthogonal
    Q x (g.reflectionCorrectionAt_apply_self Q x hx)

@[simp]
theorem coe_reflectionCorrectionAtOrthogonal
    (g : Q.IsometryEquiv Q) (x : M) (hx : Q x ≠ 0)
    (y : Q.anisotropicOrthogonal x) :
    (g.reflectionCorrectionAtOrthogonal Q x hx y : M) =
      g.reflectionCorrectionAt Q x hx y :=
  rfl

end QuadraticMap.IsometryEquiv
