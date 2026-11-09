import SMSFormula.QuadraticPadicCayleyProductTangent

/-! Full density comparison on the derivative of the actual supplied product.
All densities, the rational form ratio and transverse Jacobian remain explicit.
No injectivity or integrated measure comparison is asserted. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice
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


/-- The density law on actual derivative columns, with a locally group-valued
supplied left factor. Horizontal columns are proved intrinsic, not assumed. -/
theorem lastCayleyProduct_density (v : Fin n → E) :
    let D := W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct
    skewAdjointPadicCayleySourceDifferentialDensityENNReal p (n+1)
      (W.nonisotropicLastExtension a ha).pairingMatrix ⟨X,hX⟩ *
      (‖W.lastOrbitGroupForm a ha ℚ_[p]
        (Sum.elim (fun i ↦ D (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i,0))
          (fun j ↦ D (0,v j)))‖₊ : ℝ≥0∞) =
      (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
        skewAdjointPadicCayleySourceDifferentialDensityENNReal p n W.pairingMatrix ⟨Y,hY⟩ *
        (‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
          lastCoordinateVector
          (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
          (fun j ↦ D (0,v j))‖₊ : ℝ≥0∞) := by
  dsimp only
  simp_rw [W.lastCayleyProductIntrinsicDerivative_vertical]
  exact W.lastCayley_density_lower_chart_arbitrary a ha p X hX Y hY _

/-- On the graph overlap, the transverse factor is the determinant of
lower coordinates of dS applied to the fixed vector, with the full relative
coefficient. No basepoint density or arbitrary tangent lift replaces it. -/
theorem lastCayleyProduct_relative_graph (v : Fin n → E)
    (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ≠ 0) :
    let D := W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct
    (W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
      (fun j ↦ D (0,v j)) =
      ((-1 : ℚ_[p])^n / (2 * algebraMap ℚ ℚ_[p] a *
        ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
          lastCoordinateVector) (Fin.last n))) *
      (Pi.basisFun ℚ_[p] (Fin n)).det (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) := by
  dsimp only
  rw [W.lastCayley_relative_graph a ha p X hX hs]
  simp_rw [W.lastCayleyProductIntrinsicDerivative_orbit_horizontal]

/-- The full group-coordinate Jacobian is nonzero when the supplied orbit
coordinates have nonzero transverse Jacobian on the old graph overlap. -/
theorem lastCayleyProduct_frame_ne_zero (v : Fin n → E)
    (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ≠ 0)
    (hv : (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0) :
    let D := W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct
    W.lastOrbitGroupForm a ha ℚ_[p]
      (Sum.elim (fun i ↦ D (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i,0))
        (fun j ↦ D (0,v j))) ≠ 0 := by
  dsimp only
  let D := W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct
  have hr : (W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
      lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
      (fun j ↦ D (0,v j)) ≠ 0 := by
    rw [W.lastCayleyProduct_relative_graph a ha p S dS z hS hSO Y hY X hX hproduct v hs]
    exact mul_ne_zero (div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (mul_ne_zero (mul_ne_zero (by norm_num) ((map_ne_zero _).mpr ha)) hs)) hv
  have hl : skewAdjointPadicCayleySourceDifferentialDensityENNReal p n W.pairingMatrix ⟨Y,hY⟩ ≠ 0 := by
    rw [W.cayleySourceDensity_eq_det p Y hY]
    exact_mod_cast nnnorm_ne_zero_iff.mpr
      (det_skewAdjointPadicCayleyLeftTrivializedEndomorphism_ne_zero W.pairingMatrix p W.form_det_ne_zero Y hY)
  have hg : (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast nnnorm_ne_zero_iff.mpr (W.lastOrbitGaugeRatio_ne_zero a ha ℚ_[p])
  have hf : (‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
      lastCoordinateVector
      (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
      (fun j ↦ D (0,v j))‖₊ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast nnnorm_ne_zero_iff.mpr hr
  have hd := W.lastCayleyProduct_density a ha p S dS z hS hSO Y hY X hX hproduct v
  intro hz
  change _ * (‖W.lastOrbitGroupForm a ha ℚ_[p] _‖₊ : ℝ≥0∞) = _ at hd
  rw [hz] at hd
  simp only [nnnorm_zero, ENNReal.coe_zero, mul_zero] at hd
  exact (mul_ne_zero (mul_ne_zero hg hl) hf) hd.symm

/-- The product determinant law on a supplied square-branch overlap.
Both the full branch density and the transverse determinant appear in it. -/
theorem lastCayleyProduct_density_branch (v : Fin n → E)
    (b : ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberDomain
      p lastCoordinateVector (algebraMap ℚ ℚ_[p] a))
    (hz : (W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX lastCoordinateVector =
      (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap
        p lastCoordinateVector
        (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha)
        (algebraMap ℚ ℚ_[p] a) b).1)
 :
    let D := W.lastCayleyProductIntrinsicDerivative a ha p S dS z hS hSO Y hY X hX hproduct
    skewAdjointPadicCayleySourceDifferentialDensityENNReal p (n+1)
      (W.nonisotropicLastExtension a ha).pairingMatrix ⟨X,hX⟩ *
      (‖W.lastOrbitGroupForm a ha ℚ_[p]
        (Sum.elim (fun i ↦ D (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i,0))
          (fun j ↦ D (0,v j)))‖₊ : ℝ≥0∞) =
      (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
        skewAdjointPadicCayleySourceDifferentialDensityENNReal p n W.pairingMatrix ⟨Y,hY⟩ *
        (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberJacobianInverse
          p lastCoordinateVector (algebraMap ℚ ℚ_[p] a) b.1 *
          (‖(Pi.basisFun ℚ_[p] (Fin n)).det
            (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc)‖₊ : ℝ≥0∞)) := by
  dsimp only
  rw [W.lastCayleyProduct_density a ha p S dS z hS hSO Y hY X hX hproduct v,
    W.lastCayley_relative_eq_branchDensity a ha p X hX b hz]
  simp_rw [W.lastCayleyProductIntrinsicDerivative_orbit_horizontal]

end RationalQuadraticSpaceMatrix
