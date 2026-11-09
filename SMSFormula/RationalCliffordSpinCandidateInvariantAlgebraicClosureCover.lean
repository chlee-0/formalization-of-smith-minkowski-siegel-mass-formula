import SMSFormula.FiniteTypeAlgClosedPrincipalCover
import SMSFormula.RationalCliffordSpinCandidateInvariantAlgebraicClosurePointLift

/-!
# Global algebraic-closure comparison for the Spin invariant quotient

Translations of one nonempty principal isomorphism patch contain every
`AlgebraicClosure Q`-valued point of the base-changed special orthogonal
carrier.  Since that carrier is finite type, the translated denominators
generate the unit ideal.  Localization gluing therefore makes the full
base-changed invariant comparison an algebra isomorphism.
-/

noncomputable section

open TensorProduct

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace RationalQuadraticSpaceMatrix

open RationalTamagawa

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev A := V.specialOrthogonalCoordinateRing
private abbrev C := V.negOneInvariantSubalgebra
private abbrev Qbar := AlgebraicClosure ℚ

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance coverSourceTensorCommRing : CommRing (V.A ⊗[ℚ] Qbar) :=
  Algebra.TensorProduct.instCommRing (R := ℚ) (A := V.A) (B := Qbar)

local instance coverInvariantTensorCommRing : CommRing (V.C ⊗[ℚ] Qbar) :=
  Algebra.TensorProduct.instCommRing (R := ℚ) (A := V.C) (B := Qbar)

local instance coverSourceTensorCommSemiring : CommSemiring (V.A ⊗[ℚ] Qbar) :=
  (coverSourceTensorCommRing V).toCommSemiring

local instance coverInvariantTensorCommSemiring : CommSemiring (V.C ⊗[ℚ] Qbar) :=
  (coverInvariantTensorCommRing V).toCommSemiring

set_option backward.isDefEq.respectTransparency false in
/-- The invariant quotient comparison becomes bijective after scalar
extension from `Q` to its algebraic closure. -/
theorem specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom_bijective :
    Function.Bijective
      V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom := by
  letI : Nontrivial V.A :=
    V.specialOrthogonalCoordinateCounit.toRingHom.domain_nontrivial
  letI : Algebra.FiniteType Qbar (V.A ⊗[ℚ] Qbar) :=
    Algebra.FiniteType.of_surjective
      (Algebra.TensorProduct.commRight ℚ Qbar V.A).toAlgHom
      (Algebra.TensorProduct.commRight ℚ Qbar V.A).surjective
  obtain ⟨⟨p, hp⟩⟩ := Ideal.nonempty_minimalPrimes
    (I := (⊥ : Ideal V.A)) (bot_ne_top : (⊥ : Ideal V.A) ≠ ⊤)
  obtain ⟨d, _, hbij, φ₀A, hφ₀A, φ₀C, hφ₀⟩ :=
    V.exists_negOneInvariant_algebraicClosure_compatible_points_of_mem_minimalPrimes
      p hp
  let dbar : V.A ⊗[ℚ] Qbar :=
    Algebra.TensorProduct.includeLeft
      (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d
  apply Algebra.bijective_of_forall_algHom_exists_awayMap_bijective_apply_ne_zero
    (K := Qbar) (D := V.A ⊗[ℚ] Qbar) (E := V.C ⊗[ℚ] Qbar)
    V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom
  intro φA
  obtain ⟨_, _, φgA, _, _, hbijg, hφA⟩ :=
    V.exists_negOneInvariant_algebraicClosure_translated_patch_containing
      dbar hbij φ₀A hφ₀A φ₀C hφ₀ φA
  exact ⟨
    (V.specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv φgA).symm dbar,
    hbijg, hφA⟩

/-- The base-changed special orthogonal coordinate ring is literally
algebra-equivalent to the base-changed invariant quotient coordinate ring. -/
noncomputable def specialOrthogonalToNegOneInvariantAlgebraicClosureAlgEquiv :
    V.A ⊗[ℚ] Qbar ≃ₐ[Qbar] V.C ⊗[ℚ] Qbar :=
  AlgEquiv.ofBijective
    V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom
    V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom_bijective

@[simp]
theorem specialOrthogonalToNegOneInvariantAlgebraicClosureAlgEquiv_apply
    (x : V.A ⊗[ℚ] Qbar) :
    V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgEquiv x =
      V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom x :=
  rfl

end RationalQuadraticSpaceMatrix
