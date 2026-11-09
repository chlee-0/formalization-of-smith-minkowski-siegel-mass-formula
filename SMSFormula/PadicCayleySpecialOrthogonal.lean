import SMSFormula.PadicCayleyDeterminant
import SMSFormula.SpecialOrthogonalLinearization

/-!
# Algebraic special-orthogonal-valued p-adic Cayley map

For a nonsingular rational form, the p-adic Cayley forward matrix of an
explicit source point is form-preserving and has determinant one. This file
packages those two facts in the special-orthogonal matrix carrier and
records the underlying matrix formula.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The p-adic Cayley forward map from its explicit transported
skew-adjoint source into the special-orthogonal matrix carrier. -/
def skewAdjointPadicCayleySpecialOrthogonal
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) :
    skewAdjointPadicCayleySource F p →
      specialOrthogonalMatrixSet (F.map (algebraMap ℚ ℚ_[p])) :=
  fun X ↦
    ⟨skewAdjointPadicCayleyForwardMatrix F p X.1,
      (formPreservingConstraint_eq_zero_iff _ _).mpr
        (skewAdjointPadicCayleyForwardMatrix_formPreserving F p X.1 X.2),
      skewAdjointPadicCayleyForwardMatrix_det_one F p hF X.1 X.2⟩

@[simp]
theorem coe_skewAdjointPadicCayleySpecialOrthogonal
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) (X : skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicCayleySpecialOrthogonal F p hF X :
        Matrix ι ι ℚ_[p]) =
      (1 + (X.1 : Matrix ι ι ℚ_[p])) *
        (1 - (X.1 : Matrix ι ι ℚ_[p]))⁻¹ :=
  rfl

end Matrix
