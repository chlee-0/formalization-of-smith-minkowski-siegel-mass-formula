import SMSFormula.AffinePointGroupScalarTranslationEvaluation
import SMSFormula.RationalCliffordSpinCandidateInvariantAlgebraicClosureTranslatedPatch

/-!
# Lifting arbitrary algebraic-closure points to the Spin invariant quotient

Scheme surjectivity of the original Spin-candidate cover and finite type imply
that every algebraic-closure-valued point of the base-changed `SO` carrier
lifts to the literal invariant quotient.  The proof first lifts the restricted
rational coordinate point through the original affine cover, then extends the
resulting invariant-ring point to the right tensor scalar extension.

This is pointwise surjectivity only over `AlgebraicClosure Q`; it does not
assert pointwise surjectivity over `Q`, `R`, or `Q_p`.
-/

noncomputable section

open TensorProduct

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace RationalQuadraticSpaceMatrix

open RationalTamagawa

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev A := V.specialOrthogonalCoordinateRing
private abbrev B := V.cliffordSpinCandidateCoordinateRing
private abbrev C := V.negOneInvariantSubalgebra
private abbrev Qbar := AlgebraicClosure ℚ

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance pointLiftSourceTensorCommRing : CommRing (V.A ⊗[ℚ] Qbar) :=
  Algebra.TensorProduct.instCommRing (R := ℚ) (A := V.A) (B := Qbar)

local instance pointLiftSourceTensorCommSemiring : CommSemiring (V.A ⊗[ℚ] Qbar) :=
  (pointLiftSourceTensorCommRing V).toCommSemiring

set_option backward.isDefEq.respectTransparency false in
/-- Every algebraic-closure-valued point of the base-changed `SO` carrier
lifts compatibly to the base-changed literal invariant quotient. -/
theorem exists_negOneInvariant_algebraicClosure_point_lift
    (φA : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar) :
    ∃ φC : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar,
      φC.comp V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φA := by
  let φA₀ : V.A →ₐ[ℚ] Qbar :=
    algebraicClosureRightTensorPointCoordinateAlgHom φA
  letI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  letI : Algebra.IsIntegral ℚ Qbar := Algebra.IsAlgebraic.isIntegral
  have hmax : (RingHom.ker φA₀.toRingHom).IsMaximal :=
    Algebra.AlgHom.ker_isMaximal_of_isIntegral φA₀
  letI : Algebra.FiniteType V.A V.B := by
    rw [← RingHom.finiteType_algebraMap]
    exact RingHom.FiniteType.of_finitePresentation
      V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_finitePresentation
  obtain ⟨ψB, hψB⟩ := Algebra.exists_algHom_comp_eq_of_comap_surjective
    V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_comap_surjective
    φA₀ hmax
  letI : IsScalarTower ℚ V.A V.C :=
    IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := V.A) (A := V.C) rfl
  let ψC₀ : V.C →ₐ[ℚ] Qbar :=
    ψB.comp (V.negOneInvariantSubalgebra.val.restrictScalars ℚ)
  have hψC₀ : ψC₀.comp V.specialOrthogonalToNegOneInvariantRatAlgHom = φA₀ := by
    apply AlgHom.ext
    intro a
    change ψB (algebraMap V.A V.B a) = φA₀ a
    exact DFunLike.congr_fun hψB a
  let φC : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar :=
    Algebra.TensorProduct.rightTensorPoint ψC₀
  refine ⟨φC, ?_⟩
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a k =>
      simp only [AlgHom.comp_apply,
        V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom_tmul]
      change ψC₀ (V.specialOrthogonalToNegOneInvariantAlgHom a) * k =
        φA (a ⊗ₜ[ℚ] k)
      have ha := DFunLike.congr_fun hψC₀ a
      change ψC₀ (V.specialOrthogonalToNegOneInvariantAlgHom a) = φA₀ a at ha
      rw [ha]
      change φA (a ⊗ₜ[ℚ] (1 : Qbar)) * k = φA (a ⊗ₜ[ℚ] k)
      have hk := φA.commutes k
      have ht :
          (a ⊗ₜ[ℚ] (1 : Qbar)) * algebraMap Qbar (V.A ⊗[ℚ] Qbar) k =
            a ⊗ₜ[ℚ] k := by
        rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
        simp
      calc
        φA (a ⊗ₜ[ℚ] (1 : Qbar)) * k =
            φA (a ⊗ₜ[ℚ] (1 : Qbar)) *
              φA (algebraMap Qbar (V.A ⊗[ℚ] Qbar) k) :=
          congrArg (fun z => φA (a ⊗ₜ[ℚ] (1 : Qbar)) * z) hk.symm
        _ = φA ((a ⊗ₜ[ℚ] (1 : Qbar)) *
              algebraMap Qbar (V.A ⊗[ℚ] Qbar) k) := (map_mul φA _ _).symm
        _ = φA (a ⊗ₜ[ℚ] k) := congrArg φA ht

/-- Right-tensor extension preserves compatibility with the invariant
comparison. -/
theorem rightTensorPoint_comp_invariantComparison
    (pA : V.A →ₐ[ℚ] Qbar) (pC : V.C →ₐ[ℚ] Qbar)
    (hp : pC.comp V.specialOrthogonalToNegOneInvariantRatAlgHom = pA) :
    (Algebra.TensorProduct.rightTensorPoint pC).comp
        V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom =
      Algebra.TensorProduct.rightTensorPoint pA := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a k =>
      simp only [AlgHom.comp_apply,
        V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom_tmul,
        Algebra.TensorProduct.rightTensorPoint_tmul]
      have ha := DFunLike.congr_fun hp a
      change pC (V.specialOrthogonalToNegOneInvariantAlgHom a) = pA a at ha
      rw [ha]

/-- A fixed nonempty principal isomorphism patch can be translated to contain
any prescribed algebraic-closure-valued point of the base-changed `SO`
carrier.  The translating point lifts compatibly to the invariant quotient,
so the translated away map remains bijective. -/
theorem exists_negOneInvariant_algebraicClosure_translated_patch_containing
    (d : V.A ⊗[ℚ] Qbar)
    (hbij : Function.Bijective
      (Localization.awayMap
        V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.toRingHom d))
    (φ₀A : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar) (hφ₀A : φ₀A d ≠ 0)
    (φ₀C : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar)
    (hφ₀ : φ₀C.comp
      V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φ₀A)
    (φA : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar) :
    ∃ φC : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar,
      φC.comp V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φA ∧
      ∃ φgA : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar,
        ∃ φgC : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar,
          φgC.comp V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φgA ∧
          Function.Bijective
            (Localization.awayMap
              V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.toRingHom
              ((V.specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv φgA).symm d)) ∧
          φA ((V.specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv φgA).symm d) ≠
            0 := by
  obtain ⟨φC, hφ⟩ := V.exists_negOneInvariant_algebraicClosure_point_lift φA
  let p₀A := algebraicClosureRightTensorPointCoordinateAlgHom φ₀A
  let p₀C := algebraicClosureRightTensorPointCoordinateAlgHom φ₀C
  let pA := algebraicClosureRightTensorPointCoordinateAlgHom φA
  let pC := algebraicClosureRightTensorPointCoordinateAlgHom φC
  letI := V.specialOrthogonalAffinePointGroupData.pointGroup Qbar
  letI := V.negOneInvariantAffinePointGroupData.pointGroup Qbar
  let gA : V.A →ₐ[ℚ] Qbar := pA * p₀A⁻¹
  let gC : V.C →ₐ[ℚ] Qbar := pC * p₀C⁻¹
  let φgA : V.A ⊗[ℚ] Qbar →ₐ[Qbar] Qbar :=
    Algebra.TensorProduct.rightTensorPoint gA
  let φgC : V.C ⊗[ℚ] Qbar →ₐ[Qbar] Qbar :=
    Algebra.TensorProduct.rightTensorPoint gC
  have hp₀ : p₀C.comp V.specialOrthogonalToNegOneInvariantRatAlgHom = p₀A :=
    V.algebraicClosureRightTensorPointCoordinateAlgHom_comp_invariantComparison
      φ₀A φ₀C hφ₀
  have hp : pC.comp V.specialOrthogonalToNegOneInvariantRatAlgHom = pA :=
    V.algebraicClosureRightTensorPointCoordinateAlgHom_comp_invariantComparison
      φA φC hφ
  let F := V.negOneInvariantCoordinateAlgHomToSpecialOrthogonal Qbar
  change F p₀C = p₀A at hp₀
  change F pC = pA at hp
  have hg : gC.comp V.specialOrthogonalToNegOneInvariantRatAlgHom = gA := by
    have hmul := map_mul F pC p₀C⁻¹
    have hinv := map_inv F p₀C
    change (pC * p₀C⁻¹).comp V.specialOrthogonalToNegOneInvariantRatAlgHom =
      pA * p₀A⁻¹
    change F (pC * p₀C⁻¹) = pA * p₀A⁻¹
    exact hmul.trans (congrArg₂ (fun left right => left * right) hp
      (hinv.trans (congrArg (fun point => point⁻¹) hp₀)))
  have hφg : φgC.comp
      V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φgA :=
    V.rightTensorPoint_comp_invariantComparison gA gC hg
  have hbijg :=
    V.negOneInvariant_algebraicClosure_awayMap_bijective_leftTranslation_image
      d hbij φgA φgC hφg
  have hresA : algebraicClosureRightTensorPointCoordinateAlgHom φgA = gA := by
    exact Algebra.TensorProduct.rightTensorPoint_comp_includeLeft gA
  have hφreconstruct : Algebra.TensorProduct.rightTensorPoint pA = φA :=
    Algebra.TensorProduct.rightTensorPoint_restrict_eq_self φA
  have hφ₀reconstruct : Algebra.TensorProduct.rightTensorPoint p₀A = φ₀A :=
    Algebra.TensorProduct.rightTensorPoint_restrict_eq_self φ₀A
  have heval :=
    AffinePointGroupData.rightTensorPoint_leftTranslationAlgEquiv_symm_apply
      V.specialOrthogonalAffinePointGroupData p₀A pA d
  change Algebra.TensorProduct.rightTensorPoint pA
      ((V.specialOrthogonalAffinePointGroupData.rightTensorLeftTranslationAlgEquiv
        (pA * p₀A⁻¹)).symm d) =
    Algebra.TensorProduct.rightTensorPoint p₀A d at heval
  have hnonzero : φA
      ((V.specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv φgA).symm d) ≠ 0 := by
    rw [specialOrthogonalAlgebraicClosureLeftTranslationAlgEquiv, hresA,
      ← hφreconstruct, heval, hφ₀reconstruct]
    exact hφ₀A
  exact ⟨φC, hφ, φgA, φgC, hφg, hbijg, hnonzero⟩

end RationalQuadraticSpaceMatrix
