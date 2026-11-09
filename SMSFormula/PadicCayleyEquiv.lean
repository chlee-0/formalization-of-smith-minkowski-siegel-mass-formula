import SMSFormula.PadicCayleyInverseSource

/-!
# Algebraic p-adic Cayley equivalence

For a nonsingular rational form, the explicit transported skew-adjoint Cayley
source is equivalent to the explicit inverse-domain part of the
special-orthogonal matrix carrier. The inverse laws are reduced pointwise to
the ambient matrix identities.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The packaged special-orthogonal Cayley forward image lies in the explicit
inverse domain. -/
theorem skewAdjointPadicCayleySpecialOrthogonal_mem_inverseDomain
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) (X : skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicCayleySpecialOrthogonal F p hF X :
        Matrix ι ι ℚ_[p]) ∈ padicCayleyInverseDomain p := by
  let Xm : Matrix ι ι ℚ_[p] := X.1
  have hX : Xm ∈ padicCayleySource p := X.2
  have htarget := padicCayleyForwardMatrix_mem_inverseDomain p Xm hX
  rw [coe_skewAdjointPadicCayleySpecialOrthogonal]
  change (1 + Xm) * (1 - Xm)⁻¹ ∈ padicCayleyInverseDomain p
  simpa only [padicCayleyForwardMatrix] using htarget

/-- The Cayley forward map, including its explicit special-orthogonal
inverse-domain certificate. -/
def skewAdjointPadicCayleySpecialOrthogonalTarget
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) :
    skewAdjointPadicCayleySource F p →
      padicCayleySpecialOrthogonalInverseDomain F p :=
  fun X ↦
    ⟨skewAdjointPadicCayleySpecialOrthogonal F p hF X,
      skewAdjointPadicCayleySpecialOrthogonal_mem_inverseDomain
        F p hF X⟩

@[simp]
theorem coe_skewAdjointPadicCayleySpecialOrthogonalTarget
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) (X : skewAdjointPadicCayleySource F p) :
    ((skewAdjointPadicCayleySpecialOrthogonalTarget F p hF X).1 :
        Matrix ι ι ℚ_[p]) =
      (1 + (X.1 : Matrix ι ι ℚ_[p])) *
        (1 - (X.1 : Matrix ι ι ℚ_[p]))⁻¹ :=
  rfl

/-- The inverse-source map after the forward-target map recovers the
underlying skew-adjoint matrix. -/
theorem coe_padicCayleySpecialOrthogonalInverseSource_forwardTarget
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) (X : skewAdjointPadicCayleySource F p) :
    ((padicCayleySpecialOrthogonalInverseSource F p
        (skewAdjointPadicCayleySpecialOrthogonalTarget F p hF X)).1 :
      Matrix ι ι ℚ_[p]) =
        (X.1 : Matrix ι ι ℚ_[p]) := by
  let Xm : Matrix ι ι ℚ_[p] := X.1
  have hX : Xm ∈ padicCayleySource p := X.2
  change padicCayleyInverseMatrix p
      (padicCayleyForwardMatrix p Xm) = Xm
  exact padicCayleyInverseMatrix_forward p Xm hX

/-- The forward-target map after the inverse-source map recovers the
underlying special-orthogonal matrix. -/
theorem coe_skewAdjointPadicCayleySpecialOrthogonalTarget_inverseSource
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    ((skewAdjointPadicCayleySpecialOrthogonalTarget F p hF
        (padicCayleySpecialOrthogonalInverseSource F p g)).1 :
      Matrix ι ι ℚ_[p]) =
        (g.1 : Matrix ι ι ℚ_[p]) := by
  let gm : Matrix ι ι ℚ_[p] := g.1
  have hg : gm ∈ padicCayleyInverseDomain p := g.2
  change padicCayleyForwardMatrix p
      (padicCayleyInverseMatrix p gm) = gm
  exact padicCayleyForwardMatrix_inverse p gm hg

/-- The algebraic p-adic Cayley equivalence between the explicit transported
skew-adjoint source and the explicit special-orthogonal inverse domain. -/
def skewAdjointPadicCayleyEquivSpecialOrthogonal
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) :
    skewAdjointPadicCayleySource F p ≃
      padicCayleySpecialOrthogonalInverseDomain F p where
  toFun := skewAdjointPadicCayleySpecialOrthogonalTarget F p hF
  invFun := padicCayleySpecialOrthogonalInverseSource F p
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    exact coe_padicCayleySpecialOrthogonalInverseSource_forwardTarget
      F p hF X
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact coe_skewAdjointPadicCayleySpecialOrthogonalTarget_inverseSource
      F p hF g

end Matrix
