import SMSFormula.AffinePointGroupScalarTranslation
import SMSFormula.RationalCliffordSpinCandidateInvariantAlgebraicClosureTranslation

/-!
# Ambient algebraic-closure translations for the Spin invariant quotient

The preceding point-level file constructs compatible `Qbar`-valued points of
`SO` and the literal invariant quotient.  Here their left translations are
realized contravariantly as algebra automorphisms of the right scalar-extended
coordinate rings.  Translation by the inverse point supplies the inverse, and
the base-changed invariant comparison intertwines the two automorphisms.

This does not identify the translated principal-open patch or prove that
its translates cover the target.
-/

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 800000

open TensorProduct

namespace RationalQuadraticSpaceMatrix

open RationalTamagawa

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev A := V.specialOrthogonalCoordinateRing
private abbrev C := V.negOneInvariantSubalgebra
private abbrev Qbar := AlgebraicClosure ℚ

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Pullback by left translation on the base-changed `SO` coordinate ring. -/
def specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv
    (φ : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar) :
    V.A ⊗[ℚ] Qbar ≃ₐ[Qbar] V.A ⊗[ℚ] Qbar :=
  V.specialOrthogonalAffinePointGroupData.rightTensorLeftTranslationAlgEquiv
    (algebraicClosureRightTensorPointCoordinateAlgHom φ)

/-- Pullback by left translation on the base-changed invariant-quotient
coordinate ring. -/
def negOneInvariantAlgebraicClosureLeftTranslationAlgEquiv
    (φ : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar) :
    V.C ⊗[ℚ] Qbar ≃ₐ[Qbar] V.C ⊗[ℚ] Qbar :=
  V.negOneInvariantAffinePointGroupData.rightTensorLeftTranslationAlgEquiv
    (algebraicClosureRightTensorPointCoordinateAlgHom φ)

@[simp]
theorem specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv_tmul
    (φ : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar) (a : V.A) (k : Qbar) :
    V.specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv φ
        (a ⊗ₜ[ℚ] k) =
      V.specialOrthogonalAffinePointGroupData.rightTensorLeftTranslatedPoint
          (algebraicClosureRightTensorPointCoordinateAlgHom φ) a *
        Algebra.TensorProduct.includeRight k :=
  V.specialOrthogonalAffinePointGroupData.rightTensorLeftTranslationAlgHom_tmul
    (algebraicClosureRightTensorPointCoordinateAlgHom φ) a k

@[simp]
theorem negOneInvariantAlgebraicClosureLeftTranslationAlgEquiv_tmul
    (φ : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar) (c : V.C) (k : Qbar) :
    V.negOneInvariantAlgebraicClosureLeftTranslationAlgEquiv φ
        (c ⊗ₜ[ℚ] k) =
      V.negOneInvariantAffinePointGroupData.rightTensorLeftTranslatedPoint
          (algebraicClosureRightTensorPointCoordinateAlgHom φ) c *
        Algebra.TensorProduct.includeRight k :=
  V.negOneInvariantAffinePointGroupData.rightTensorLeftTranslationAlgHom_tmul
    (algebraicClosureRightTensorPointCoordinateAlgHom φ) c k

theorem rightTensorLeftTranslatedPoint_comp_invariantComparison
    (φA : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar)
    (φC : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar)
    (hφ : φC.comp
      V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φA) :
    (V.negOneInvariantAffinePointGroupData.rightTensorLeftTranslatedPoint
        (algebraicClosureRightTensorPointCoordinateAlgHom φC)).comp
        V.specialOrthogonalToNegOneInvariantRatAlgHom =
      (V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.restrictScalars ℚ).comp
        (V.specialOrthogonalAffinePointGroupData.rightTensorLeftTranslatedPoint
          (algebraicClosureRightTensorPointCoordinateAlgHom φA)) := by
  let pA := algebraicClosureRightTensorPointCoordinateAlgHom φA
  let pC := algebraicClosureRightTensorPointCoordinateAlgHom φC
  let f := V.specialOrthogonalToNegOneInvariantRatAlgHom
  let fK := V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom
  let uA : V.A →ₐ[ℚ] V.A ⊗[ℚ] Qbar :=
    AffinePointGroupData.rightTensorUniversalPoint
  let uC : V.C →ₐ[ℚ] V.C ⊗[ℚ] Qbar :=
    AffinePointGroupData.rightTensorUniversalPoint
  let cA := V.specialOrthogonalAffinePointGroupData.rightTensorConstantPoint pA
  let cC := V.negOneInvariantAffinePointGroupData.rightTensorConstantPoint pC
  have hp : pC.comp f = pA := by
    exact V.algebraicClosureRightTensorPointCoordinateAlgHom_comp_invariantComparison
      φA φC hφ
  have hc : cC.comp f = (fK.restrictScalars ℚ).comp cA := by
    apply AlgHom.ext
    intro a
    have hpa := DFunLike.congr_fun hp a
    change pC (f a) = pA a at hpa
    simp only [cC, cA, AffinePointGroupData.rightTensorConstantPoint,
      AffinePointGroupData.map_apply, AlgHom.comp_apply]
    rw [hpa]
    simp [fK]
  have hu : uC.comp f = (fK.restrictScalars ℚ).comp uA := by
    apply AlgHom.ext
    intro a
    change V.specialOrthogonalToNegOneInvariantAlgHom a ⊗ₜ[ℚ] (1 : Qbar) =
      fK (a ⊗ₜ[ℚ] (1 : Qbar))
    simp [fK]
  have hpre := map_mul
    (V.negOneInvariantCoordinateAlgHomToSpecialOrthogonal
      (V.C ⊗[ℚ] Qbar)) cC uC
  have hpost := map_mul
    (V.specialOrthogonalAffinePointGroupData.map (fK.restrictScalars ℚ)) cA uA
  change (cC * uC).comp f = cC.comp f * uC.comp f at hpre
  simp only [AffinePointGroupData.map_apply] at hpost
  change (cC * uC).comp f = (fK.restrictScalars ℚ).comp (cA * uA)
  calc
    (cC * uC).comp f = cC.comp f * uC.comp f := hpre
    _ = (fK.restrictScalars ℚ).comp cA *
        (fK.restrictScalars ℚ).comp uA := by rw [hc, hu]
    _ = (fK.restrictScalars ℚ).comp (cA * uA) := hpost.symm

/-- The base-changed invariant comparison intertwines the two ambient
coordinate-ring translations induced by compatible points. -/
theorem algebraicClosureLeftTranslationAlgEquiv_comp_invariantComparison
    (φA : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar)
    (φC : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar)
    (hφ : φC.comp
      V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φA) :
    (V.negOneInvariantAlgebraicClosureLeftTranslationAlgEquiv φC).toAlgHom.comp
        V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom =
      V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.comp
        (V.specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv φA).toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a k =>
      change V.negOneInvariantAffinePointGroupData.rightTensorLeftTranslationAlgHom
          (algebraicClosureRightTensorPointCoordinateAlgHom φC)
          (V.specialOrthogonalToNegOneInvariantAlgHom a ⊗ₜ[ℚ] k) =
        V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom
          (V.specialOrthogonalAffinePointGroupData.rightTensorLeftTranslationAlgHom
            (algebraicClosureRightTensorPointCoordinateAlgHom φA)
            (a ⊗ₜ[ℚ] k))
      rw [V.negOneInvariantAffinePointGroupData.rightTensorLeftTranslationAlgHom_tmul,
        V.specialOrthogonalAffinePointGroupData.rightTensorLeftTranslationAlgHom_tmul,
        map_mul]
      have hpoint := DFunLike.congr_fun
        (V.rightTensorLeftTranslatedPoint_comp_invariantComparison φA φC hφ) a
      change V.negOneInvariantAffinePointGroupData.rightTensorLeftTranslatedPoint
          (algebraicClosureRightTensorPointCoordinateAlgHom φC)
          (V.specialOrthogonalToNegOneInvariantAlgHom a) =
        V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom
          (V.specialOrthogonalAffinePointGroupData.rightTensorLeftTranslatedPoint
            (algebraicClosureRightTensorPointCoordinateAlgHom φA) a) at hpoint
      have hk :
          V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom
              (Algebra.TensorProduct.includeRight k) =
            Algebra.TensorProduct.includeRight k := by
        simpa only [Algebra.TensorProduct.includeRight_apply, map_one] using
          V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom_tmul
            (1 : V.A) k
      rw [hpoint]
      rw [hk]

end RationalQuadraticSpaceMatrix
