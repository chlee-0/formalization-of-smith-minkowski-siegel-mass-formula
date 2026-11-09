import SMSFormula.PadicCayleyTranslatedChartOverlapAlgebra
import SMSFormula.PadicCayleyPointwiseDifferential
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Differential of translated p-adic Cayley overlap transitions

The ambient inverse Cayley map has derivative

`H ↦ 2(g+1)⁻¹H(g+1)⁻¹`

at every point of its unit domain.  Composing this with left multiplication
by the relative center and the forward Cayley derivative gives the
pointwise chain-rule derivative of a translated-chart overlap transition.

The transition formula is related pointwise to the exact overlap
homeomorphism.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator RightActions Topology

namespace Matrix

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The explicit ambient derivative of inverse Cayley at `g`. -/
def padicCayleyInverseDerivative
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p]) :
    Matrix ι ι ℚ_[p] →L[ℚ_[p]] Matrix ι ι ℚ_[p] :=
  (2 : ℚ_[p]) •
    ContinuousLinearMap.mulLeftRight ℚ_[p] (Matrix ι ι ℚ_[p])
      (g + 1)⁻¹ (g + 1)⁻¹

@[simp]
theorem padicCayleyInverseDerivative_apply
    (p : ℕ) [Fact (Nat.Prime p)] (g H : Matrix ι ι ℚ_[p]) :
    padicCayleyInverseDerivative p g H =
      2 • ((g + 1)⁻¹ * H * (g + 1)⁻¹) :=
  rfl

/-- The direct product-rule derivative before simplifying with the inverse
domain identity. -/
def padicCayleyInverseProductDerivative
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p]) :
    Matrix ι ι ℚ_[p] →L[ℚ_[p]] Matrix ι ι ℚ_[p] :=
  (g + 1)⁻¹ •
      ContinuousLinearMap.id ℚ_[p] (Matrix ι ι ℚ_[p]) +
    ((-ContinuousLinearMap.mulLeftRight ℚ_[p]
      (Matrix ι ι ℚ_[p]) (g + 1)⁻¹ (g + 1)⁻¹).comp
        (ContinuousLinearMap.id ℚ_[p] (Matrix ι ι ℚ_[p]))) <•
      (g - 1)

@[simp]
theorem padicCayleyInverseProductDerivative_apply
    (p : ℕ) [Fact (Nat.Prime p)] (g H : Matrix ι ι ℚ_[p]) :
    padicCayleyInverseProductDerivative p g H =
      (g + 1)⁻¹ * H +
        (-((g + 1)⁻¹ * H * (g + 1)⁻¹)) * (g - 1) :=
  rfl

/-- The inverse Cayley formula has its direct product-rule derivative on the
unit domain. -/
theorem hasFDerivAt_padicCayleyInverseMatrix_product
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p])
    (hg : g ∈ padicCayleyInverseDomain p) :
    HasFDerivAt
      (padicCayleyInverseMatrix (ι := ι) p)
      (padicCayleyInverseProductDerivative p g)
      g := by
  letI : CompleteSpace (Matrix ι ι ℚ_[p]) :=
    FiniteDimensional.complete ℚ_[p] _
  change IsUnit (g + 1) at hg
  let I := ContinuousLinearMap.id ℚ_[p] (Matrix ι ι ℚ_[p])
  have hden :
      HasFDerivAt
        (fun y : Matrix ι ι ℚ_[p] ↦ y + 1) I g := by
    simpa only [I] using
      (hasFDerivAt_id (𝕜 := ℚ_[p]) g).add_const
        (1 : Matrix ι ι ℚ_[p])
  have hnum :
      HasFDerivAt
        (fun y : Matrix ι ι ℚ_[p] ↦ y - 1) I g := by
    simpa only [I] using
      (hasFDerivAt_id (𝕜 := ℚ_[p]) g).sub_const
        (1 : Matrix ι ι ℚ_[p])
  have hinverseAtDenominator :
      HasFDerivAt
        (Ring.inverse :
          Matrix ι ι ℚ_[p] → Matrix ι ι ℚ_[p])
        (-ContinuousLinearMap.mulLeftRight ℚ_[p]
          (Matrix ι ι ℚ_[p]) (g + 1)⁻¹ (g + 1)⁻¹)
        (g + 1) := by
    have hunitInv :
        (↑hg.unit⁻¹ : Matrix ι ι ℚ_[p]) = (g + 1)⁻¹ := by
      rw [Matrix.coe_units_inv, hg.unit_spec]
    simpa only [hg.unit_spec, hunitInv] using
      (hasFDerivAt_ringInverse (𝕜 := ℚ_[p]) hg.unit)
  have hinverse :
      HasFDerivAt
        (fun y : Matrix ι ι ℚ_[p] ↦ Ring.inverse (y + 1))
        ((-ContinuousLinearMap.mulLeftRight ℚ_[p]
          (Matrix ι ι ℚ_[p]) (g + 1)⁻¹ (g + 1)⁻¹).comp I)
        g := by
    simpa only [Function.comp_apply] using
      hinverseAtDenominator.comp g hden
  have hproduct := hinverse.mul' hnum
  change HasFDerivAt
    (fun y : Matrix ι ι ℚ_[p] ↦ (y + 1)⁻¹ * (y - 1))
    (padicCayleyInverseProductDerivative p g)
    g
  simp_rw [nonsing_inv_eq_ringInverse]
  change HasFDerivAt
    (fun y : Matrix ι ι ℚ_[p] ↦
      Ring.inverse (y + 1) * (y - 1))
    _ g at hproduct
  rw [← nonsing_inv_eq_ringInverse] at hproduct
  simpa only [padicCayleyInverseProductDerivative, I] using hproduct

private theorem padicCayleyInverseDerivative_algebra
    (p : ℕ) [Fact (Nat.Prime p)] (A B H T : Matrix ι ι ℚ_[p])
    (hsub : 1 - A * B = A * T)
    (hcomm : Commute T (A * H * A))
    (hsmul : T * (A * H * A) = 2 • (A * H * A)) :
    A * H + (-(A * H * A)) * B = 2 • (A * H * A) := by
  calc
    A * H + (-(A * H * A)) * B =
        (A * H) * (1 - A * B) := by noncomm_ring
    _ = (A * H) * (A * T) := by rw [hsub]
    _ = (A * H * A) * T := by noncomm_ring
    _ = T * (A * H * A) := hcomm.eq.symm
    _ = 2 • (A * H * A) := hsmul

/-- On the inverse domain, the direct product derivative is the closed
two-sided derivative with scalar factor `2`. -/
theorem padicCayleyInverseProductDerivative_eq
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p])
    (hg : g ∈ padicCayleyInverseDomain p) :
    padicCayleyInverseProductDerivative p g =
      padicCayleyInverseDerivative p g := by
  apply ContinuousLinearMap.ext
  intro H
  rw [padicCayleyInverseProductDerivative_apply,
    padicCayleyInverseDerivative_apply]
  have hsub := one_sub_padicCayleyInverseMatrix p g hg
  apply padicCayleyInverseDerivative_algebra p
    (A := (g + 1)⁻¹) (B := g - 1)
    (T := padicCayleyTwoMatrix (ι := ι) p)
  · exact hsub
  · exact Matrix.scalar_commute (n := ι) (2 : ℚ_[p])
      (fun r ↦ mul_comm 2 r) ((g + 1)⁻¹ * H * (g + 1)⁻¹)
  · rw [padicCayleyTwoMatrix, Matrix.scalar_apply]
    exact (Matrix.smul_eq_diagonal_mul
      ((g + 1)⁻¹ * H * (g + 1)⁻¹) (2 : ℚ_[p])).symm

/-- The ambient inverse Cayley map has the explicit two-sided inverse
denominator derivative at every point of its inverse domain. -/
theorem hasFDerivAt_padicCayleyInverseMatrix
    (p : ℕ) [Fact (Nat.Prime p)] (g : Matrix ι ι ℚ_[p])
    (hg : g ∈ padicCayleyInverseDomain p) :
    HasFDerivAt
      (padicCayleyInverseMatrix (ι := ι) p)
      (padicCayleyInverseDerivative p g)
      g :=
  (hasFDerivAt_padicCayleyInverseMatrix_product p g hg).congr_fderiv
    (padicCayleyInverseProductDerivative_eq p g hg)

end Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- The ambient relative overlap transition attached to a matrix `W`. -/
def padicCayleyRelativeTransitionMatrix
    (p : ℕ) [Fact (Nat.Prime p)]
    (W X : Matrix (Fin n) (Fin n) ℚ_[p]) :
    Matrix (Fin n) (Fin n) ℚ_[p] :=
  Matrix.padicCayleyInverseMatrix p
    (W * Matrix.padicCayleyForwardMatrix p X)

@[simp]
theorem padicCayleyRelativeTransitionMatrix_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (W X : Matrix (Fin n) (Fin n) ℚ_[p]) :
    padicCayleyRelativeTransitionMatrix p W X =
      Matrix.padicCayleyInverseMatrix p
        (W * Matrix.padicCayleyForwardMatrix p X) :=
  rfl

/-- The derivative of left multiplication by the relative center `W`. -/
def padicCayleyRelativeLeftDerivative
    (p : ℕ) [Fact (Nat.Prime p)]
    (W : Matrix (Fin n) (Fin n) ℚ_[p]) :
    Matrix (Fin n) (Fin n) ℚ_[p] →L[ℚ_[p]]
      Matrix (Fin n) (Fin n) ℚ_[p] :=
  ContinuousLinearMap.mulLeftRight ℚ_[p]
    (Matrix (Fin n) (Fin n) ℚ_[p]) W 1

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem padicCayleyRelativeLeftDerivative_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (W H : Matrix (Fin n) (Fin n) ℚ_[p]) :
    padicCayleyRelativeLeftDerivative p W H = W * H := by
  change W * H * 1 = W * H
  exact mul_one _

/-- Left multiplication by the relative center has its defining continuous
linear map as derivative. -/
theorem hasFDerivAt_padicCayleyRelativeLeft
    (p : ℕ) [Fact (Nat.Prime p)]
    (W Y : Matrix (Fin n) (Fin n) ℚ_[p]) :
    HasFDerivAt
      (fun Z : Matrix (Fin n) (Fin n) ℚ_[p] ↦ W * Z)
      (padicCayleyRelativeLeftDerivative p W)
      Y := by
  have hfun :
      (fun Z : Matrix (Fin n) (Fin n) ℚ_[p] ↦ W * Z) =
        (padicCayleyRelativeLeftDerivative p W :
          Matrix (Fin n) (Fin n) ℚ_[p] →
            Matrix (Fin n) (Fin n) ℚ_[p]) := by
    funext Z
    exact (padicCayleyRelativeLeftDerivative_apply p W Z).symm
  rw [hfun]
  exact (padicCayleyRelativeLeftDerivative p W).hasFDerivAt

/-- The chain-rule derivative of the ambient relative overlap transition. -/
def padicCayleyRelativeTransitionDerivative
    (p : ℕ) [Fact (Nat.Prime p)]
    (W X : Matrix (Fin n) (Fin n) ℚ_[p]) :
    Matrix (Fin n) (Fin n) ℚ_[p] →L[ℚ_[p]]
      Matrix (Fin n) (Fin n) ℚ_[p] :=
  (Matrix.padicCayleyInverseDerivative p
      (W * Matrix.padicCayleyForwardMatrix p X)).comp
    ((padicCayleyRelativeLeftDerivative p W).comp
      (Matrix.padicCayleyForwardDerivative p X))

/-- The relative target map `X ↦ W * cayley(X)` has the derivative obtained by
left-multiplying the forward Cayley derivative. -/
theorem hasFDerivAt_padicCayleyRelativeTarget
    (p : ℕ) [Fact (Nat.Prime p)]
    (W X : Matrix (Fin n) (Fin n) ℚ_[p])
    (hX : X ∈ Matrix.padicCayleySource p) :
    HasFDerivAt
      (fun Y : Matrix (Fin n) (Fin n) ℚ_[p] ↦
        W * Matrix.padicCayleyForwardMatrix p Y)
      ((padicCayleyRelativeLeftDerivative p W).comp
        (Matrix.padicCayleyForwardDerivative p X))
      X := by
  exact
    (hasFDerivAt_padicCayleyRelativeLeft p W
        (Matrix.padicCayleyForwardMatrix p X)).comp X
      (Matrix.hasFDerivAt_padicCayleyForwardMatrix p X hX)

/-- The ambient relative overlap transition has the chain-rule derivative
obtained from forward Cayley, relative left multiplication, and inverse
Cayley. -/
theorem hasFDerivAt_padicCayleyRelativeTransitionMatrix
    (p : ℕ) [Fact (Nat.Prime p)]
    (W X : Matrix (Fin n) (Fin n) ℚ_[p])
    (hX : X ∈ Matrix.padicCayleySource p)
    (hrelative :
      W * Matrix.padicCayleyForwardMatrix p X ∈
        Matrix.padicCayleyInverseDomain p) :
    HasFDerivAt
      (padicCayleyRelativeTransitionMatrix p W)
      (padicCayleyRelativeTransitionDerivative p W X)
      X := by
  exact
    (Matrix.hasFDerivAt_padicCayleyInverseMatrix p
      (W * Matrix.padicCayleyForwardMatrix p X) hrelative).comp X
        (hasFDerivAt_padicCayleyRelativeTarget p W X hX)

/-- Pointwise action of the ambient relative transition derivative. -/
theorem padicCayleyRelativeTransitionDerivative_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (W X H : Matrix (Fin n) (Fin n) ℚ_[p]) :
    padicCayleyRelativeTransitionDerivative p W X H =
      2 •
        (((W * Matrix.padicCayleyForwardMatrix p X) + 1)⁻¹ *
          (W * (2 •
            ((1 - X)⁻¹ * H * (1 - X)⁻¹))) *
          ((W * Matrix.padicCayleyForwardMatrix p X) + 1)⁻¹) := by
  change
    2 •
        (((W * Matrix.padicCayleyForwardMatrix p X) + 1)⁻¹ *
          (W * (2 •
            ((1 - X)⁻¹ * H * (1 - X)⁻¹)) * 1) *
          ((W * Matrix.padicCayleyForwardMatrix p X) + 1)⁻¹) =
      2 •
        (((W * Matrix.padicCayleyForwardMatrix p X) + 1)⁻¹ *
          (W * (2 •
            ((1 - X)⁻¹ * H * (1 - X)⁻¹))) *
          ((W * Matrix.padicCayleyForwardMatrix p X) + 1)⁻¹)
  rw [mul_one]

/-- Pointwise, the exact forward overlap transition is the ambient relative
transition for the matrix `d⁻¹c`. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_eq_relativeTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1.1 :
          Matrix (Fin n) (Fin n) ℚ_[p]) =
      padicCayleyRelativeTransitionMatrix p
        (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
        (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  exact
    skewAdjointPadicCayleyTranslatedSourceOverlapTransition_eq_inverse_mul_cayley
      F p hF c d X

/-- At every exact forward overlap point, the ambient relative transition for
`d⁻¹c` has the chain-rule derivative. -/
theorem hasFDerivAt_skewAdjointPadicCayleyTranslatedSourceOverlapTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    HasFDerivAt
      (padicCayleyRelativeTransitionMatrix p
        (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])))
      (padicCayleyRelativeTransitionDerivative p
        (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
        (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
      (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  apply hasFDerivAt_padicCayleyRelativeTransitionMatrix
  · exact X.1.2
  · rw [←
      skewAdjointPadicCayleyTranslatedRelativeTargetMatrix_eq_mul_cayley
        F p hF c d X.1]
    exact
      (mem_skewAdjointPadicCayleyTranslatedSourceOverlapSet_iff_relative_inverseDomain
        F p hF c d X.1).mp X.2

/-- Pointwise, the inverse exact overlap transition is the ambient relative
transition for `c⁻¹d`. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_symm_eq_relativeTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF d c) :
    (((skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d).symm X).1.1 :
          Matrix (Fin n) (Fin n) ℚ_[p]) =
      padicCayleyRelativeTransitionMatrix p
        (((c⁻¹ * d).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
        (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  exact
    skewAdjointPadicCayleyTranslatedSourceOverlapTransition_symm_eq_inverse_mul_cayley
      F p hF c d X

/-- At every exact inverse overlap point, the ambient relative transition for
`c⁻¹d` has the chain-rule derivative. -/
theorem hasFDerivAt_skewAdjointPadicCayleyTranslatedSourceOverlapTransition_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF d c) :
    HasFDerivAt
      (padicCayleyRelativeTransitionMatrix p
        (((c⁻¹ * d).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])))
      (padicCayleyRelativeTransitionDerivative p
        (((c⁻¹ * d).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
        (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
      (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  apply hasFDerivAt_padicCayleyRelativeTransitionMatrix
  · exact X.1.2
  · rw [←
      skewAdjointPadicCayleyTranslatedRelativeTargetMatrix_eq_mul_cayley
        F p hF d c X.1]
    exact
      (mem_skewAdjointPadicCayleyTranslatedSourceOverlapSet_iff_relative_inverseDomain
        F p hF d c X.1).mp X.2

end PositiveDefiniteIntegralLattice
