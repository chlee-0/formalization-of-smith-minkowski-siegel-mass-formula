import SMSFormula.PadicCayleyTranslatedChartOverlapDifferential
import SMSFormula.PadicCayleyLeftTrivializedDetNonzero

/-!
# Intrinsic tangent maps for translated p-adic Cayley overlaps

The ambient derivative of a translated Cayley transition preserves the
transported skew-adjoint tangent model.  At corresponding source coordinates
`X` and `Y`, its intrinsic factorization is

`T_Y⁻¹ ∘ T_X`,

where `T_X` and `T_Y` are the left-trivialized Cayley tangent equivalences.
The reverse transition has the inverse factorization.

All exact-chart comparisons are pointwise.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At a Cayley source point, the ambient inverse derivative at the forward
image is a left inverse to the ambient forward derivative. -/
theorem padicCayleyInverseDerivative_comp_forwardDerivative
    (p : ℕ) [Fact (Nat.Prime p)] (X : Matrix ι ι ℚ_[p])
    (hX : X ∈ padicCayleySource p) :
    (padicCayleyInverseDerivative p (padicCayleyForwardMatrix p X)).comp
        (padicCayleyForwardDerivative p X) =
      ContinuousLinearMap.id ℚ_[p] (Matrix ι ι ℚ_[p]) := by
  have hforward :=
    hasFDerivAt_padicCayleyForwardMatrix p X hX
  have hinverse :=
    hasFDerivAt_padicCayleyInverseMatrix p
      (padicCayleyForwardMatrix p X)
      (padicCayleyForwardMatrix_mem_inverseDomain p X hX)
  have hcomp := hinverse.comp X hforward
  have heq :
      (padicCayleyInverseMatrix p ∘ padicCayleyForwardMatrix p) =ᶠ[𝓝 X]
        id := by
    filter_upwards [(isOpen_padicCayleySource p).mem_nhds hX]
      with Y hY
    exact padicCayleyInverseMatrix_forward p Y hY
  exact hcomp.unique
    ((hasFDerivAt_id (𝕜 := ℚ_[p]) X).congr_of_eventuallyEq heq)

set_option backward.isDefEq.respectTransparency false in
/-- The restricted forward derivative is the Cayley image multiplied by its
intrinsic left-trivialized derivative. -/
theorem skewAdjointPadicCayleyForwardDerivative_eq_forward_mul_leftTrivialized
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyForwardDerivative F p X H =
      skewAdjointPadicCayleyForwardMatrix F p X *
        (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX H : Matrix ι ι ℚ_[p]) := by
  let C : Matrix ι ι ℚ_[p] :=
    skewAdjointPadicCayleyForwardMatrix F p X
  let D : Matrix ι ι ℚ_[p] :=
    skewAdjointPadicCayleyForwardDerivative F p X H
  have hCdet : IsUnit C.det := by
    rw [show C.det = 1 by
      exact skewAdjointPadicCayleyForwardMatrix_det_one F p hF X hX]
    exact isUnit_one
  have htrivialized :
      (skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX H : Matrix ι ι ℚ_[p]) =
        C⁻¹ * D := by
    change
      (skewAdjointPadicCayleyLeftTrivializedDerivative F p X H) =
        C⁻¹ * D
    change C⁻¹ * D * 1 = C⁻¹ * D
    exact mul_one _
  change D =
    C * (skewAdjointPadicCayleyLeftTrivializedEndomorphism
      F p X hX H : Matrix ι ι ℚ_[p])
  rw [htrivialized, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv C hCdet, Matrix.one_mul]

end Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- The intrinsic tangent equivalence from a source coordinate `X` to a
corresponding source coordinate `Y`. -/
def skewAdjointPadicCayleyTransitionTangentEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (Matrix.skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv
      F p hF X hX).trans
    (Matrix.skewAdjointPadicCayleyLeftTrivializedContinuousLinearEquiv
      F p hF Y hY).symm

@[simp]
theorem skewAdjointPadicCayleyTransitionTangentEquiv_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X Y H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p) :
    skewAdjointPadicCayleyTransitionTangentEquiv
        F p hF X Y hX hY H =
      Matrix.skewAdjointPadicCayleyLeftTrivializedInverse F p Y
        (Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX H) :=
  rfl

/-- Swapping the two source coordinates gives the inverse intrinsic tangent
equivalence. -/
theorem skewAdjointPadicCayleyTransitionTangentEquiv_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p) :
    (skewAdjointPadicCayleyTransitionTangentEquiv
      F p hF X Y hX hY).symm =
        skewAdjointPadicCayleyTransitionTangentEquiv
          F p hF Y X hY hX := by
  rfl

/-- If the relative target relation is `W * cayley(X) = cayley(Y)`, then the
ambient transition derivative on an intrinsic tangent vector is the ambient
representative of `T_Y⁻¹(T_X(H))`. -/
theorem padicCayleyRelativeTransitionDerivative_skewAdjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (W : Matrix (Fin n) (Fin n) ℚ_[p])
    (X Y H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hrelative :
      W * Matrix.skewAdjointPadicCayleyForwardMatrix F p X =
        Matrix.skewAdjointPadicCayleyForwardMatrix F p Y) :
    padicCayleyRelativeTransitionDerivative p W
        (X : Matrix (Fin n) (Fin n) ℚ_[p])
        (H : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (skewAdjointPadicCayleyTransitionTangentEquiv
        F p hF X Y hX hY H : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  let K :=
    skewAdjointPadicCayleyTransitionTangentEquiv
      F p hF X Y hX hY H
  have htrivialized :
      Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p Y hY K =
        Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X hX H := by
    dsimp [K]
    exact
      Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply_inverse
        F p hF Y
          (Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
            F p X hX H) hY
  have hforward :
      W * Matrix.skewAdjointPadicCayleyForwardDerivative F p X H =
        Matrix.skewAdjointPadicCayleyForwardDerivative F p Y K := by
    rw [
      Matrix.skewAdjointPadicCayleyForwardDerivative_eq_forward_mul_leftTrivialized
        F p hF X H hX,
      Matrix.skewAdjointPadicCayleyForwardDerivative_eq_forward_mul_leftTrivialized
        F p hF Y K hY,
      htrivialized, ← Matrix.mul_assoc, hrelative]
  have hinverse :=
    congrArg
      (fun L :
        Matrix (Fin n) (Fin n) ℚ_[p] →L[ℚ_[p]]
          Matrix (Fin n) (Fin n) ℚ_[p] =>
        L (K : Matrix (Fin n) (Fin n) ℚ_[p]))
      (Matrix.padicCayleyInverseDerivative_comp_forwardDerivative
        p (Y : Matrix (Fin n) (Fin n) ℚ_[p]) hY)
  have hrelative' :
      W * Matrix.padicCayleyForwardMatrix p
          (X : Matrix (Fin n) (Fin n) ℚ_[p]) =
        Matrix.padicCayleyForwardMatrix p
          (Y : Matrix (Fin n) (Fin n) ℚ_[p]) :=
    hrelative
  have hforward' :
      W * Matrix.padicCayleyForwardDerivative p
          (X : Matrix (Fin n) (Fin n) ℚ_[p])
          (H : Matrix (Fin n) (Fin n) ℚ_[p]) =
        Matrix.padicCayleyForwardDerivative p
          (Y : Matrix (Fin n) (Fin n) ℚ_[p])
          (K : Matrix (Fin n) (Fin n) ℚ_[p]) :=
    hforward
  simp only [padicCayleyRelativeTransitionDerivative,
    padicCayleyRelativeLeftDerivative_apply,
    ContinuousLinearMap.comp_apply]
  change
    Matrix.padicCayleyInverseDerivative p
        (W * Matrix.padicCayleyForwardMatrix p
          (X : Matrix (Fin n) (Fin n) ℚ_[p]))
      (W * Matrix.padicCayleyForwardDerivative p
        (X : Matrix (Fin n) (Fin n) ℚ_[p])
        (H : Matrix (Fin n) (Fin n) ℚ_[p])) =
      (K : Matrix (Fin n) (Fin n) ℚ_[p])
  rw [hrelative', hforward']
  simpa [ContinuousLinearMap.comp_apply] using hinverse

/-- The ambient relative transition derivative preserves the transported
skew-adjoint tangent model. -/
theorem padicCayleyRelativeTransitionDerivative_mem_skewAdjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (W : Matrix (Fin n) (Fin n) ℚ_[p])
    (X Y H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hrelative :
      W * Matrix.skewAdjointPadicCayleyForwardMatrix F p X =
        Matrix.skewAdjointPadicCayleyForwardMatrix F p Y) :
    padicCayleyRelativeTransitionDerivative p W
        (X : Matrix (Fin n) (Fin n) ℚ_[p])
        (H : Matrix (Fin n) (Fin n) ℚ_[p]) ∈
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  rw [padicCayleyRelativeTransitionDerivative_skewAdjoint
    F p hF W X Y H hX hY hrelative]
  exact
    (skewAdjointPadicCayleyTransitionTangentEquiv
      F p hF X Y hX hY H).property

/-- The ambient relative transition derivative, codomain-restricted to the
transported skew-adjoint tangent model. -/
def skewAdjointPadicCayleyRelativeTransitionEndomorphism
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (W : Matrix (Fin n) (Fin n) ℚ_[p])
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hrelative :
      W * Matrix.skewAdjointPadicCayleyForwardMatrix F p X =
        Matrix.skewAdjointPadicCayleyForwardMatrix F p Y) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ((padicCayleyRelativeTransitionDerivative p W
      (X : Matrix (Fin n) (Fin n) ℚ_[p])).comp
    (Matrix.skewAdjointPadicAmbientInclusion F p)).codRestrict _
      (fun H =>
        padicCayleyRelativeTransitionDerivative_mem_skewAdjoint
          F p hF W X Y H hX hY hrelative)

/-- The codomain-restricted ambient derivative is the intrinsic transition
tangent equivalence. -/
theorem skewAdjointPadicCayleyRelativeTransitionEndomorphism_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (W : Matrix (Fin n) (Fin n) ℚ_[p])
    (X Y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hY : Y ∈ Matrix.skewAdjointPadicCayleySource F p)
    (hrelative :
      W * Matrix.skewAdjointPadicCayleyForwardMatrix F p X =
        Matrix.skewAdjointPadicCayleyForwardMatrix F p Y) :
    skewAdjointPadicCayleyRelativeTransitionEndomorphism
        F p hF W X Y hX hY hrelative =
      (skewAdjointPadicCayleyTransitionTangentEquiv
        F p hF X Y hX hY).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro H
  apply Subtype.ext
  exact padicCayleyRelativeTransitionDerivative_skewAdjoint
    F p hF W X Y H hX hY hrelative

/-- The relative target at an exact overlap point is the Cayley image of the
transitioned source coordinate. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_forward_relation
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
        Matrix.skewAdjointPadicCayleyForwardMatrix F p X.1 =
      Matrix.skewAdjointPadicCayleyForwardMatrix F p
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X).1 := by
  let W : Matrix (Fin n) (Fin n) ℚ_[p] :=
    ((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])
  let Y :=
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d X).1
  have hdomain :
      W * Matrix.padicCayleyForwardMatrix p
          (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) ∈
        Matrix.padicCayleyInverseDomain p := by
    rw [←
      skewAdjointPadicCayleyTranslatedRelativeTargetMatrix_eq_mul_cayley
        F p hF c d X.1]
    exact
      (mem_skewAdjointPadicCayleyTranslatedSourceOverlapSet_iff_relative_inverseDomain
        F p hF c d X.1).mp X.2
  have hY :
      (Y : Matrix (Fin n) (Fin n) ℚ_[p]) =
        Matrix.padicCayleyInverseMatrix p
          (W * Matrix.padicCayleyForwardMatrix p
            (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) := by
    exact
      skewAdjointPadicCayleyTranslatedSourceOverlapTransition_eq_inverse_mul_cayley
        F p hF c d X
  change
    W * Matrix.padicCayleyForwardMatrix p
        (X.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]) =
      Matrix.padicCayleyForwardMatrix p
        (Y : Matrix (Fin n) (Fin n) ℚ_[p])
  rw [hY, Matrix.padicCayleyForwardMatrix_inverse p _ hdomain]

/-- The pointwise intrinsic tangent equivalence attached to an exact forward
overlap transition. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  skewAdjointPadicCayleyTransitionTangentEquiv F p hF X.1
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d X).1
    X.1.2
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d X).1.2

/-- The exact ambient overlap derivative, restricted to the transported
skew-adjoint tangent model. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  skewAdjointPadicCayleyRelativeTransitionEndomorphism F p hF
    (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
    X.1
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d X).1
    X.1.2
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d X).1.2
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransition_forward_relation
      F p hF c d X)

/-- Pointwise, the restricted exact overlap derivative is its intrinsic
continuous linear equivalence. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
        F p hF c d X =
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X).toContinuousLinearMap := by
  exact skewAdjointPadicCayleyRelativeTransitionEndomorphism_eq
    F p hF
      (((d⁻¹ * c).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
      X.1
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1
      X.1.2
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF c d X).1.2
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransition_forward_relation
        F p hF c d X)

/-- Applying the swapped transition at the corresponding point recovers the
original exact overlap point.  This is stated pointwise. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_swap_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
        F p hF d c
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X) =
      X := by
  exact
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d).symm_apply_apply X

/-- At the corresponding transitioned point, the reverse relative target is
the original Cayley image. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransition_reverse_relation
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (((c⁻¹ * d).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p])) *
        Matrix.skewAdjointPadicCayleyForwardMatrix F p
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
            F p hF c d X).1 =
      Matrix.skewAdjointPadicCayleyForwardMatrix F p X.1 := by
  have h :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransition_forward_relation
      F p hF d c
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X)
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransition_swap_apply
      F p hF c d X] at h
  exact h

/-- The pointwise intrinsic tangent equivalence for the reverse transition at
the corresponding point. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseTangentEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
    F p hF c d X).symm

/-- The ambient derivative of the reverse transition at the corresponding
point, restricted to the transported skew-adjoint tangent model. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  skewAdjointPadicCayleyRelativeTransitionEndomorphism F p hF
    (((c⁻¹ * d).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d X).1
    X.1
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d X).1.2
    X.1.2
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransition_reverse_relation
      F p hF c d X)

/-- The restricted reverse derivative is the inverse intrinsic tangent
equivalence, pointwise at the corresponding overlap coordinate. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
        F p hF c d X =
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseTangentEquiv
        F p hF c d X).toContinuousLinearMap := by
  unfold
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
  rw [
    skewAdjointPadicCayleyRelativeTransitionEndomorphism_eq
      F p hF
        (((c⁻¹ * d).1.1.1 : Matrix (Fin n) (Fin n) ℚ_[p]))
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X).1
        X.1
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X).1.2
        X.1.2
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransition_reverse_relation
          F p hF c d X)]
  unfold
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseTangentEquiv
  exact congrArg ContinuousLinearEquiv.toContinuousLinearMap
    (skewAdjointPadicCayleyTransitionTangentEquiv_symm
      F p hF X.1
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X).1
        X.1.2
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
          F p hF c d X).1.2)

/-- The reverse overlap derivative is a left inverse to the forward overlap
derivative at corresponding source coordinates. -/
@[simp]
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverse_apply_forward
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
        F p hF c d X
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
          F p hF c d X H) =
      H := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_eq,
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism_eq]
  exact
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
      F p hF c d X).symm_apply_apply H

/-- The forward overlap derivative is a left inverse to the reverse overlap
derivative at corresponding source coordinates. -/
@[simp]
theorem skewAdjointPadicCayleyTranslatedSourceOverlapTransitionForward_apply_reverse
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (K : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
        F p hF c d X
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
          F p hF c d X K) =
      K := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_eq,
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism_eq]
  exact
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
      F p hF c d X).apply_symm_apply K

end PositiveDefiniteIntegralLattice
