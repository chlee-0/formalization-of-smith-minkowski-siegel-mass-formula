import SMSFormula.QuadraticPadicCayleyValueBranchComparison

/-! The full density law on arbitrary transverse derivatives. Only the
vertical frame is prescribed. No transverse lifting operator is imposed on a
supplied nonlinear map, and no product chart or integration theorem is asserted. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice QuadraticMap
open scoped ENNReal NNReal Matrix.Norms.Operator

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)

/-- Full signed group/stabilizer/orbit identity for any transverse frame H.
In particular H may be the transverse columns of an actual supplied derivative,
with arbitrary vertical additions. The old basis determinant is retained. -/
theorem lastCayley_group_stabilizer_arbitrary
    (u : Fin (Module.finrank ℚ W.skewAdjointTangent) →
      skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (H : Fin n → skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
    LinearMap.det (skewAdjointPadicCayleyLeftTrivializedEndomorphism
      (W.nonisotropicLastExtension a ha).pairingMatrix p X hX).toLinearMap *
      W.lastOrbitGroupForm a ha ℚ_[p]
        (Sum.elim (fun i ↦ skewAdjointPadicCayleyLeftTrivializedInverse
          (W.nonisotropicLastExtension a ha).pairingMatrix p X
          (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] (u i))) H) =
      W.lastOrbitGaugeRatio a ha ℚ_[p] *
        skewAdjointScalarExtensionDetForm (K := ℚ_[p]) W.pairingMatrix u *
        (W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
          lastCoordinateVector
          (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) H := by
  rw [← W.lastOrbitGroupForm_cayley_apply a ha p X hX,
    (W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm_apply]
  have he : (fun i ↦ skewAdjointPadicCayleyLeftTrivializedEndomorphism
      (W.nonisotropicLastExtension a ha).pairingMatrix p X hX
      (Sum.elim (fun i ↦ skewAdjointPadicCayleyLeftTrivializedInverse
        (W.nonisotropicLastExtension a ha).pairingMatrix p X
        (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] (u i))) H i)) =
      Sum.elim (fun i ↦ W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] (u i))
        (fun j ↦ skewAdjointPadicCayleyLeftTrivializedEndomorphism
          (W.nonisotropicLastExtension a ha).pairingMatrix p X hX (H j)) := by
    funext i
    cases i with
    | inl i =>
      exact skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply_inverse
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero X _ hX
    | inr j => rfl
  rw [he]
  exact W.lastOrbitGroupForm_eq_ratio_mul_orbitRelative a ha ℚ_[p] u _

/-- Both full chart densities on arbitrary transverse columns. The higher
frame determinant remains; this is not an integrated change of variables. -/
theorem lastCayley_density_lower_chart_arbitrary
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (H : Fin n → skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p])) :
    let u := fun i ↦ skewAdjointPadicCayleyLeftTrivializedEndomorphism W.pairingMatrix p Y hY
      (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i)
    skewAdjointPadicCayleySourceDifferentialDensityENNReal p (n+1)
      (W.nonisotropicLastExtension a ha).pairingMatrix ⟨X,hX⟩ *
      (‖W.lastOrbitGroupForm a ha ℚ_[p]
        (Sum.elim (fun i ↦ skewAdjointPadicCayleyLeftTrivializedInverse
          (W.nonisotropicLastExtension a ha).pairingMatrix p X
          (W.nonisotropicLastSkewAdjointEmbed a ha ℚ_[p] (u i))) H)‖₊ : ℝ≥0∞) =
      (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
        skewAdjointPadicCayleySourceDifferentialDensityENNReal p n W.pairingMatrix ⟨Y,hY⟩ *
        (‖(W.nonisotropicLastExtension a ha).cayleyOrbitRelativeTopForm p X hX
          lastCoordinateVector
          (by rw [W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha) H‖₊ : ℝ≥0∞) := by
  dsimp only
  rw [(W.nonisotropicLastExtension a ha).cayleySourceDensity_eq_det p X hX,
    W.cayleySourceDensity_eq_det p Y hY]
  have hf : skewAdjointScalarExtensionDetForm (K := ℚ_[p]) W.pairingMatrix
      (fun i ↦ skewAdjointPadicCayleyLeftTrivializedEndomorphism W.pairingMatrix p Y hY
        (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i)) =
      LinearMap.det (skewAdjointPadicCayleyLeftTrivializedEndomorphism W.pairingMatrix p Y hY).toLinearMap := by
    exact (Module.Basis.det_comp (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix)
      (skewAdjointPadicCayleyLeftTrivializedEndomorphism W.pairingMatrix p Y hY).toLinearMap
      (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix)).trans
        (by rw [Module.Basis.det_self, mul_one])
  have h := W.lastCayley_group_stabilizer_arbitrary a ha p X hX
    (fun i ↦ skewAdjointPadicCayleyLeftTrivializedEndomorphism W.pairingMatrix p Y hY
      (skewAdjointScalarExtensionFinBasis (K := ℚ_[p]) W.pairingMatrix i)) H
  rw [hf] at h
  simpa only [nnnorm_mul, ENNReal.coe_mul] using
    congrArg (fun z : ℚ_[p] ↦ (‖z‖₊ : ℝ≥0∞)) h

end RationalQuadraticSpaceMatrix
