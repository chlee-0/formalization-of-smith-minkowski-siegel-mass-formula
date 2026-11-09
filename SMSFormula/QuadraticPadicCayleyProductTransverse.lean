import SMSFormula.QuadraticSquareBranchRelativeTopForm
import SMSFormula.QuadraticPadicCayleyProductDensity

/-! Discharging the transverse Jacobian hypothesis of the full p-adic product
density. The horizontal columns of the actual derivative are already proved
intrinsic; here they are identified with literal shell tangents, and the
transverse determinant is shown to be nonzero exactly when the supplied left
factor is a submersion onto that tangent space. No chart, section, nonlinear
inverse or integrated change of variables is asserted. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice QuadraticMap
open scoped ENNReal NNReal Matrix.Norms.Operator Topology

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hS : HasFDerivAt S dS z)
    (hSO : ∀ᶠ u in 𝓝 z, S u ∈ specialOrthogonalMatrixSet
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)

/-- The actual horizontal derivative column, typed in the literal tangent space
of the shell at the moving orbit point. Its membership is the already proved
polar tangency of the actual orbit derivative, not a new assumption. -/
def lastCayleyProductHorizontalTangent (v : E) :
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).polarBilin
      ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
        lastCoordinateVector)).ker :=
  (W.nonisotropicLastExtension a ha).cayleyOrbitPolarTangentLinearMap p X hX lastCoordinateVector
    (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
    (W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct (0,v))

@[simp] theorem lastCayleyProductHorizontalTangent_coe (v : E) :
    (W.lastCayleyProductHorizontalTangent a ha p S dS z hS hSO Y hY X hX hproduct v).1 =
      dS v *ᵥ lastCoordinateVector :=
  W.lastCayleyProductIntrinsicDerivative_orbit_horizontal a ha p S dS z hS hSO Y hY X hX hproduct v

include hS hSO hY hproduct in
/-- In particular the actual horizontal column is polar-orthogonal to the
moving orbit point: it is a literal shell tangent, not a chosen lift. -/
theorem lastCayleyProduct_horizontal_polar (v : E) :
    ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).polarBilin
      ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX lastCoordinateVector)
      (dS v *ᵥ lastCoordinateVector) = 0 := by
  rw [← W.lastCayleyProductHorizontalTangent_coe a ha p S dS z hS hSO Y hY X hX hproduct v]
  exact (W.lastCayleyProductHorizontalTangent a ha p S dS z hS hSO Y hY X hX hproduct v).2

variable (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
    lastCoordinateVector) (Fin.last n) ≠ 0)

/-- The actual intrinsic derivative read on the lower tangent directions
and the supplied horizontal directions. This is a restriction of the already
computed derivative to a supplied source frame, not a new chart or section. -/
def lastCayleyProductFrameMap (v : Fin n → E) :
    (skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])) →ₗ[ℚ_[p]]
      skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]) :=
  (W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX
    hproduct).toLinearMap.comp
      (LinearMap.prodMap LinearMap.id (Fintype.linearCombination ℚ_[p] v))

theorem lastCayleyProductFrameMap_apply (v : Fin n → E)
    (q : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]) ×
      (Fin n → ℚ_[p])) :
    W.lastCayleyProductFrameMap a ha p S dS z hS hSO Y hY X hX hproduct v q =
      W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct
        (q.1, ∑ i, q.2 i • v i) := rfl

include hs in
/-- The full intrinsic derivative is a linear equivalence on the supplied
frame exactly under the transverse Jacobian hypothesis. This is the linear
isomorphism a p-adic inverse function theorem would consume; no nonlinear
inverse, chart, section or measure transport is asserted here. -/
theorem lastCayleyProductFrameMap_bijective (v : Fin n → E)
    (hv : (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0) :
    Function.Bijective
      (W.lastCayleyProductFrameMap a ha p S dS z hS hSO Y hY X hX hproduct v) := by
  classical
  set D := W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct with hDdef
  set fam : (Fin (Module.finrank ℚ W.skewAdjointTangent) ⊕ Fin n) →
      skewAdjointMatricesLieSubalgebra
        ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]) :=
    Sum.elim (fun i ↦ D (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i, 0))
      (fun j ↦ D (0, v j)) with hfam
  have hne : W.lastOrbitGroupForm a ha ℚ_[p] fam ≠ 0 :=
    W.lastCayleyProduct_frame_ne_zero a ha p S dS z hS hSO Y hY X hX hproduct v hs hv
  have hbasis : LinearIndependent ℚ_[p] (fam ∘ W.lastOrbitIndexEquiv a ha) ∧
      Submodule.span ℚ_[p] (Set.range (fam ∘ W.lastOrbitIndexEquiv a ha)) = ⊤ := by
    refine (Module.Basis.is_basis_iff_det
      (skewAdjointScalarExtensionFinBasis (K := ℚ_[p])
        (W.nonisotropicLastExtension a ha).pairingMatrix)).mpr ?_
    rw [isUnit_iff_ne_zero]
    exact hne
  obtain ⟨hli, hspan⟩ := hbasis
  have hli' : LinearIndependent ℚ_[p] fam := by
    have h := hli.comp _ (W.lastOrbitIndexEquiv a ha).symm.injective
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using h
  have hspan' : Submodule.span ℚ_[p] (Set.range fam) = ⊤ := by
    rwa [Set.range_comp, (W.lastOrbitIndexEquiv a ha).range_eq_univ, Set.image_univ] at hspan
  set C := Module.Basis.mk hli' (le_of_eq hspan'.symm) with hC
  set B := (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix).prod
    (Pi.basisFun ℚ_[p] (Fin n)) with hB
  have hcong : W.lastCayleyProductFrameMap a ha p S dS z hS hSO Y hY X hX hproduct v =
      (B.equiv C (Equiv.refl _)).toLinearMap := by
    refine B.ext (fun i ↦ ?_)
    have hrhs : (B.equiv C (Equiv.refl _)).toLinearMap (B i) = fam i := by
      change B.equiv C (Equiv.refl _) (B i) = fam i
      rw [Module.Basis.equiv_apply, hC, Module.Basis.coe_mk]
      rfl
    rw [hrhs]
    cases i with
    | inl i =>
      have h1 : (B (Sum.inl i)).1 =
          skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i :=
        Module.Basis.prod_apply_inl_fst _ _ i
      have h2 : (B (Sum.inl i)).2 = (0 : Fin n → ℚ_[p]) :=
        Module.Basis.prod_apply_inl_snd _ _ i
      show D ((B (Sum.inl i)).1, ∑ k, (B (Sum.inl i)).2 k • v k) = fam (Sum.inl i)
      rw [h1, h2, hfam]
      simp
    | inr j =>
      have h1 : (B (Sum.inr j)).1 =
          (0 : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p])) :=
        Module.Basis.prod_apply_inr_fst _ _ j
      have h2 : (B (Sum.inr j)).2 = Pi.basisFun ℚ_[p] (Fin n) j :=
        Module.Basis.prod_apply_inr_snd _ _ j
      show D ((B (Sum.inr j)).1, ∑ k, (B (Sum.inr j)).2 k • v k) = fam (Sum.inr j)
      rw [h1, h2, hfam]
      simp [Pi.basisFun_apply, Pi.single_apply]
  rw [hcong]
  exact (B.equiv C (Equiv.refl _)).bijective

end RationalQuadraticSpaceMatrix
