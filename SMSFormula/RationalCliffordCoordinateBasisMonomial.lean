import SMSFormula.RationalCliffordCoordinateBasis
import SMSFormula.CliffordAlgebraChangeFormNaturality
import SMSFormula.RationalCliffordSpinBlockCliffordEmbedding

/-!
# The exterior coordinate basis is the ordered-monomial basis

The `exteriorAlgebraBasis` of `ExteriorAlgebra ℚ (Fin n → ℚ)`, assembled from Mathlib's
exterior-power bases through the exterior grading and reindexed by `Finset (Fin n)`, sends `s`
to the ordered exterior monomial `ιMulti (e ∘ orderEmbOfFin s)` of the standard basis vectors.
-/

noncomputable section

open CliffordAlgebra
open scoped DirectSum

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Mathlib's direct-sum basis evaluates to single-summand basis vectors. -/
theorem dfinsupp_basis_apply {ι R : Type*} [Semiring R] {M : ι → Type*} [DecidableEq ι]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {η : ι → Type*}
    (b : ∀ i, Module.Basis (η i) R (M i)) (i : ι) (x : η i) :
    DFinsupp.basis b ⟨i, x⟩ = DFinsupp.single i (b i x) := by
  rw [← (DFinsupp.basis b).repr_symm_single_one]
  change ((DFinsupp.mapRange.linearEquiv fun i => (b i).repr).trans
    (sigmaFinsuppLequivDFinsupp R).symm).symm (Finsupp.single ⟨i, x⟩ 1) = _
  simp [sigmaFinsuppLequivDFinsupp, sigmaFinsuppEquivDFinsupp_single]

/-- The exterior basis element of `s` is the ordered standard exterior monomial. -/
theorem exteriorAlgebraBasis_apply (s : Finset (Fin n)) :
    exteriorAlgebraBasis (n := n) s =
      ExteriorAlgebra.ιMulti_family ℚ s.card (Pi.basisFun ℚ (Fin n)) ⟨s, rfl⟩ := by
  simp only [exteriorAlgebraBasis, exteriorAlgebraBasisSigma, exteriorDirectSumBasis,
    Module.Basis.reindex_apply, Module.Basis.map_apply]
  erw [dfinsupp_basis_apply]
  erw [DirectSum.decomposeLinearEquiv_symm_apply, DirectSum.decompose_symm_of]
  rw [exteriorPower.basis_apply]
  rfl

/-- Ordered exterior monomials depend only on the underlying subset, not on the cardinality
index. -/
theorem ιMulti_family_congr {M J : Type*} [AddCommGroup M] [Module ℚ M] [LinearOrder J]
    (c : J → M) {k k' : ℕ} (h : k = k') (t : Set.powersetCard J k) (t' : Set.powersetCard J k')
    (hv : t.val = t'.val) :
    ExteriorAlgebra.ιMulti_family ℚ k c t = ExteriorAlgebra.ιMulti_family ℚ k' c t' := by
  subst h
  rw [Subtype.ext hv]

/-- The complement inclusion sends standard basis vectors to their `castSucc` images. -/
theorem nonisotropicLastComplementIncludeLinearMap_basisFun (i : Fin n) :
    nonisotropicLastComplementIncludeLinearMap ℚ (Pi.basisFun ℚ (Fin n) i) =
      Pi.basisFun ℚ (Fin (n + 1)) (Fin.castSuccOrderEmb i) := by
  ext j
  cases j using Fin.lastCases with
  | last =>
    simp [nonisotropicLastComplementIncludeLinearMap, nonisotropicLastComplementInclude,
      Fin.castSucc_ne_last]
  | cast j =>
    simp [nonisotropicLastComplementIncludeLinearMap, nonisotropicLastComplementInclude,
      Pi.single_apply]

/-- Exterior basis naturality: the complement inclusion sends the exterior basis
element of `s` to the exterior basis element of `castSucc(s)`. -/
theorem exteriorMap_complementInclude_exteriorAlgebraBasis (s : Finset (Fin n)) :
    ExteriorAlgebra.map (nonisotropicLastComplementIncludeLinearMap ℚ)
        (exteriorAlgebraBasis (n := n) s) =
      exteriorAlgebraBasis (n := n + 1) (s.map (Fin.castSuccOrderEmb (n := n)).toEmbedding) := by
  rw [exteriorAlgebraBasis_apply, exteriorAlgebraBasis_apply]
  change ExteriorAlgebra.map _ (ExteriorAlgebra.ιMulti ℚ s.card
      (Pi.basisFun ℚ (Fin n) ∘ Set.powersetCard.ofFinEmbEquiv.symm ⟨s, rfl⟩)) = _
  rw [ExteriorAlgebra.map_ιMulti_ofFinEmbEquiv_symm (Fin.castSuccOrderEmb (n := n))
    (Pi.basisFun ℚ (Fin n)) (Pi.basisFun ℚ (Fin (n + 1))) _
    nonisotropicLastComplementIncludeLinearMap_basisFun]
  exact ιMulti_family_congr _ (Finset.card_map _).symm _ _ rfl

/-- At the rational base the scalar-extended form is the rational form. -/
theorem commutativeScalarExtensionQuadraticForm_rat_eq (V : RationalQuadraticSpaceMatrix n) :
    V.commutativeScalarExtensionQuadraticForm ℚ = V.quadraticForm := by
  simp [commutativeScalarExtensionQuadraticForm, commutativeScalarExtensionFormMatrix,
    quadraticForm]

/-- The complement inclusion as a rational isometry of the rational forms. -/
def nonisotropicLastComplementRationalIsometry (W : RationalQuadraticSpaceMatrix n) (a : ℚ)
    (ha : a ≠ 0) : W.quadraticForm →qᵢ (W.nonisotropicLastExtension a ha).quadraticForm where
  toLinearMap := nonisotropicLastComplementIncludeLinearMap ℚ
  map_app' v := by
    have h := W.nonisotropicLastExtension_quadraticForm_complement a ha ℚ v
    rwa [commutativeScalarExtensionQuadraticForm_rat_eq,
      commutativeScalarExtensionQuadraticForm_rat_eq] at h

/-- The Clifford coordinate basis is natural: the Clifford map of the rational complement
isometry sends the coordinate basis element of `s` to that of `castSucc(s)`. -/
theorem map_complementRationalIsometry_cliffordCoordinateBasis (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0) (s : Finset (Fin n)) :
    CliffordAlgebra.map (W.nonisotropicLastComplementRationalIsometry a ha)
        (W.cliffordCoordinateBasis s) =
      (W.nonisotropicLastExtension a ha).cliffordCoordinateBasis
        (s.map (Fin.castSuccOrderEmb (n := n)).toEmbedding) := by
  simp only [cliffordCoordinateBasis, Module.Basis.map_apply]
  rw [CliffordAlgebra.map_equivExterior_symm]
  congr 1
  exact exteriorMap_complementInclude_exteriorAlgebraBasis s

/-- Coordinates are padded: the coordinates of the image of `x` are those of `x` moved to the
`castSucc` index sets. -/
theorem cliffordCoordinateBasis_repr_map_complementRationalIsometry
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) (x : CliffordAlgebra W.quadraticForm) :
    (W.nonisotropicLastExtension a ha).cliffordCoordinateBasis.repr
        (CliffordAlgebra.map (W.nonisotropicLastComplementRationalIsometry a ha) x) =
      Finsupp.mapDomain (fun s ↦ s.map (Fin.castSuccOrderEmb (n := n)).toEmbedding)
        (W.cliffordCoordinateBasis.repr x) := by
  have hlin : ((W.nonisotropicLastExtension a ha).cliffordCoordinateBasis.repr.toLinearMap ∘ₗ
      (CliffordAlgebra.map (W.nonisotropicLastComplementRationalIsometry a ha)).toLinearMap) =
      (Finsupp.lmapDomain ℚ ℚ (fun s ↦ s.map (Fin.castSuccOrderEmb (n := n)).toEmbedding)) ∘ₗ
        W.cliffordCoordinateBasis.repr.toLinearMap := by
    apply W.cliffordCoordinateBasis.ext
    intro s
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_coe, map_complementRationalIsometry_cliffordCoordinateBasis,
      Module.Basis.repr_self, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun hlin x

end RationalQuadraticSpaceMatrix
