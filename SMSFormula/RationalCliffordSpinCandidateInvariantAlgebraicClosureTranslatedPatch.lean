import SMSFormula.PrincipalLocalizationAutomorphismTransport
import SMSFormula.RationalCliffordSpinCandidateInvariantAlgebraicClosureAmbientTranslation

/-!
# Translating the algebraic-closure Spin invariant patch

The base-changed invariant comparison intertwines the coordinate
automorphisms induced by every compatible pair of algebraic-closure points.
Consequently a principal-open isomorphism patch remains an isomorphism after
translation.

Because coordinate rings are contravariant, pullback of `D(d)` by left
translation is `D(τ(d))`, while the geometric image of `D(d)` is
`D(τ⁻¹(d))`.  Both away-map statements are recorded explicitly below.
This file does not prove that translated patches cover the target.
-/

noncomputable section

open TensorProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev A := V.specialOrthogonalCoordinateRing
private abbrev C := V.negOneInvariantSubalgebra
private abbrev Qbar := AlgebraicClosure ℚ

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance translatedSourceTensorCommRing : CommRing (V.A ⊗[ℚ] Qbar) :=
  Algebra.TensorProduct.instCommRing (R := ℚ) (A := V.A) (B := Qbar)

local instance translatedInvariantTensorCommRing : CommRing (V.C ⊗[ℚ] Qbar) :=
  Algebra.TensorProduct.instCommRing (R := ℚ) (A := V.C) (B := Qbar)

local instance translatedSourceTensorCommSemiring : CommSemiring (V.A ⊗[ℚ] Qbar) :=
  (translatedSourceTensorCommRing V).toCommSemiring

local instance translatedInvariantTensorCommSemiring : CommSemiring (V.C ⊗[ℚ] Qbar) :=
  (translatedInvariantTensorCommRing V).toCommSemiring

example : translatedSourceTensorCommSemiring V =
    Algebra.TensorProduct.instCommSemiring (R := ℚ) (A := V.A) (B := Qbar) := rfl

example : translatedInvariantTensorCommSemiring V =
    Algebra.TensorProduct.instCommSemiring (R := ℚ) (A := V.C) (B := Qbar) := rfl

/-- Pullback by compatible left translations preserves a principal-open
isomorphism patch of the base-changed invariant comparison. -/
theorem negOneInvariant_algebraicClosure_awayMap_bijective_leftTranslation
    (d : V.A ⊗[ℚ] Qbar)
    (hbij : Function.Bijective
      (Localization.awayMap
        V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.toRingHom d))
    (φA : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar)
    (φC : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar)
    (hφ : φC.comp
      V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φA) :
    Function.Bijective
      (Localization.awayMap
        V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.toRingHom
        (V.specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv φA d)) := by
  have htransport := Localization.awayMap_bijective_of_intertwining_algEquiv
    (R := Qbar) (A := V.A ⊗[ℚ] Qbar) (B := V.C ⊗[ℚ] Qbar)
    V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom
    (V.specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv φA)
    (V.negOneInvariantAlgebraicClosureLeftTranslationAlgEquiv φC)
    (V.algebraicClosureLeftTranslationAlgEquiv_comp_invariantComparison φA φC hφ)
    d
  exact htransport hbij

/-- The geometric image of a principal patch under compatible left
translations is cut out by the inverse-transformed coordinate, and its away
map is again bijective. -/
theorem negOneInvariant_algebraicClosure_awayMap_bijective_leftTranslation_image
    (d : V.A ⊗[ℚ] Qbar)
    (hbij : Function.Bijective
      (Localization.awayMap
        V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.toRingHom d))
    (φA : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar)
    (φC : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar)
    (hφ : φC.comp
      V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φA) :
    Function.Bijective
      (Localization.awayMap
        V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.toRingHom
        ((V.specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv φA).symm d)) := by
  have htransport := Localization.awayMap_bijective_of_intertwining_algEquiv_symm
    (R := Qbar) (A := V.A ⊗[ℚ] Qbar) (B := V.C ⊗[ℚ] Qbar)
    V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom
    (V.specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv φA)
    (V.negOneInvariantAlgebraicClosureLeftTranslationAlgEquiv φC)
    (V.algebraicClosureLeftTranslationAlgEquiv_comp_invariantComparison φA φC hφ)
    d
  exact htransport hbij

/-- Every minimal component supplies a literal algebraic-closure principal
patch, compatible points in that patch, and the bijective away map for the
geometric translate of the patch by their common group point. -/
theorem exists_negOneInvariant_algebraicClosure_translated_patch_of_mem_minimalPrimes
    (p : Ideal V.A) (hp : p ∈ minimalPrimes V.A) :
    ∃ d : V.A, d ∉ p ∧
      ∃ φA : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar,
        φA (Algebra.TensorProduct.includeLeft
          (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d) ≠ 0 ∧
        ∃ φC : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar,
          φC.comp V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φA ∧
          Function.Bijective
            (Localization.awayMap
              V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.toRingHom
              ((V.specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv φA).symm
                (Algebra.TensorProduct.includeLeft
                  (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d))) := by
  obtain ⟨d, hd, hbij, φA, hφA, φC, hφ⟩ :=
    V.exists_negOneInvariant_algebraicClosure_compatible_points_of_mem_minimalPrimes
      p hp
  refine ⟨d, hd, φA, hφA, φC, hφ, ?_⟩
  exact V.negOneInvariant_algebraicClosure_awayMap_bijective_leftTranslation_image
    (Algebra.TensorProduct.includeLeft
      (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d)
    hbij φA φC hφ

end RationalQuadraticSpaceMatrix
