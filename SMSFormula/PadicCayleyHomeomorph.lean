import SMSFormula.PadicCayleyContinuity

/-!
# The p-adic Cayley homeomorphism

The algebraic Cayley equivalence between the explicit transported
skew-adjoint source and special-orthogonal inverse domain is a homeomorphism
by the continuity theorems for its forward and inverse maps.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The p-adic Cayley homeomorphism between the explicit transported
skew-adjoint source and the explicit special-orthogonal inverse domain. -/
def skewAdjointPadicCayleyHomeomorphSpecialOrthogonal
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) :
    skewAdjointPadicCayleySource F p ≃ₜ
      padicCayleySpecialOrthogonalInverseDomain F p where
  toEquiv := skewAdjointPadicCayleyEquivSpecialOrthogonal F p hF
  continuous_toFun :=
    continuous_skewAdjointPadicCayleySpecialOrthogonalTarget F p hF
  continuous_invFun :=
    continuous_padicCayleySpecialOrthogonalInverseSource F p

@[simp]
theorem coe_skewAdjointPadicCayleyHomeomorphSpecialOrthogonal_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) (X : skewAdjointPadicCayleySource F p) :
    ((skewAdjointPadicCayleyHomeomorphSpecialOrthogonal F p hF X).1 :
        Matrix ι ι ℚ_[p]) =
      (1 + (X.1 : Matrix ι ι ℚ_[p])) *
        (1 - (X.1 : Matrix ι ι ℚ_[p]))⁻¹ :=
  rfl

@[simp]
theorem coe_skewAdjointPadicCayleyHomeomorphSpecialOrthogonal_symm_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    (((skewAdjointPadicCayleyHomeomorphSpecialOrthogonal
          F p hF).symm g).1 : Matrix ι ι ℚ_[p]) =
      (((g.1 : specialOrthogonalMatrixSet
          (F.map (algebraMap ℚ ℚ_[p]))) : Matrix ι ι ℚ_[p]) + 1)⁻¹ *
        (((g.1 : specialOrthogonalMatrixSet
          (F.map (algebraMap ℚ ℚ_[p]))) : Matrix ι ι ℚ_[p]) - 1) :=
  rfl

end Matrix
