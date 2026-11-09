import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleProductCompositionBasis

/-!
# Relative determinant of the identity north-pole product composition

This file compares the basiswise centered composition with the two
determinants.  It works only with alternating determinants of vector families:
no conjugated carrier endomorphism or full-carrier application equality is
defined.

The result keeps the fixed rational transition scalar explicit.  No `ENNReal`
cancellation, intrinsic density cocycle, nonlinear measure comparison, fiber
identification, or rank recurrence is asserted here.
-/

open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace PositiveDefiniteIntegralLattice

private theorem basis_det_inv
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]
    (A D : Module.Basis ι ℝ E) :
    D.det A = (A.det D)⁻¹ := by
  rw [← Module.Basis.det_basis A D,
    ← Module.Basis.det_basis D A]
  have heq :
      (A.equiv D (Equiv.refl ι)).symm =
        D.equiv A (Equiv.refl ι) := by
    apply LinearEquiv.ext
    intro x
    apply (A.equiv D (Equiv.refl ι)).injective
    simp
  rw [← heq, ← LinearEquiv.coe_det, LinearEquiv.det_symm]
  simp

private theorem basis_det_map_both
    {ι E E' : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup E'] [Module ℝ E']
    (A D : Module.Basis ι ℝ E) (e : E ≃ₗ[ℝ] E') :
    (A.map e).det (D.map e) = A.det D := by
  rw [Module.Basis.det_map]
  congr 1
  ext i
  simp

private theorem basis_det_equiv_apply
    {ι E E' : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup E'] [Module ℝ E']
    (b : Module.Basis ι ℝ E) (b' : Module.Basis ι ℝ E')
    (L : E ≃ₗ[ℝ] E') (v : ι → E) :
    b'.det (fun i => L (v i)) =
      b'.det (b.map L) * b.det v := by
  have hchange :
      b'.det = b'.det (b.map L) • (b.map L).det :=
    AlternatingMap.eq_smul_basis_det (b.map L) b'.det
  calc
    b'.det (fun i => L (v i)) =
        (b'.det (b.map L) • (b.map L).det)
          (fun i => L (v i)) := by
      rw [← hchange]
    _ = b'.det (b.map L) *
        (b.map L).det (fun i => L (v i)) := by
      simp
    _ = b'.det (b.map L) * b.det v := by
      rw [Module.Basis.det_map]
      congr 1
      apply congrArg b.det
      funext i
      simp

/-- The fixed transition source basis, sent forward and then through the
higher tangent split, is the transported mapped/plain source basis. -/
theorem
    identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis_map_higherToMappedSplit
    (n : ℕ) :
    ((identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n).map
      (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv
        n).toLinearEquiv).map
      (identitySpecialOrthogonalNorthPoleProductHigherToMappedSplitEquiv
        n).toLinearEquiv =
      identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n := by
  apply DFunLike.ext _ _
  intro i
  simp [identitySpecialOrthogonalNorthPoleProductMappedSplitBasis,
    identitySpecialOrthogonalNorthPoleProductHigherToMappedSplitEquiv,
    identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv,
    identitySpecialOrthogonalNorthPoleProductSourceContinuousLinearEquiv,
    identitySpecialOrthogonalNorthPoleProductSplitPlainSourceEquiv,
    identitySpecialOrthogonalNorthPoleProductSplitMappedTargetEquiv]
  rfl

/-- The determinant of the fixed higher-to-mapped-split equivalence relative
to the transported source basis is reciprocal to the transition
scalar.  It is recorded as a product identity to avoid introducing an
additional inverse-valued normalization. -/
theorem
    identitySpecialOrthogonalNorthPoleProduct_transitionDetScalar_mul_higherToMappedSplit_basisDet
    (n : ℕ) :
    identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n *
      (identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n).det
        ((identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n).map
          (identitySpecialOrthogonalNorthPoleProductHigherToMappedSplitEquiv
            n).toLinearEquiv) =
      1 := by
  let A :=
    (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis n).map
      (identitySpecialOrthogonalNorthPoleProductTransitionLinearEquiv
        n).toLinearEquiv
  let T :=
    identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n
  let B :=
    identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n
  let R :=
    identitySpecialOrthogonalNorthPoleProductHigherToMappedSplitEquiv n
  have hmap : A.map R.toLinearEquiv = B := by
    exact
      identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis_map_higherToMappedSplit
        n
  have hsecond :
      B.det (T.map R.toLinearEquiv) = A.det T := by
    rw [← hmap]
    exact basis_det_map_both A T R.toLinearEquiv
  change T.det A * B.det (T.map R.toLinearEquiv) = 1
  rw [hsecond, basis_det_inv T A]
  exact mul_inv_cancel₀
    (identitySpecialOrthogonalNorthPoleProductTransitionDetScalar_ne_zero n)

/-- Applying the higher centered endomorphism multiplies the target-basis
determinant of the pointwise transition vectors by its ordinary determinant. -/
theorem
    identitySpecialOrthogonalNorthPoleProductHigherCentered_composition_targetBasis_det
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    (identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n).det
        (fun i =>
          identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
            n p
            (fderiv ℝ
              (identitySpecialOrthogonalNorthPoleProductTransition n) p.1
              (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis
                n i))) =
      LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
            n p).toLinearMap *
        identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar
          n p.1 := by
  rw [show (fun i =>
      identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
        n p
        (fderiv ℝ
          (identitySpecialOrthogonalNorthPoleProductTransition n) p.1
          (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis
            n i))) =
      (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
        n p).toLinearMap ∘
        (fun i =>
          fderiv ℝ
            (identitySpecialOrthogonalNorthPoleProductTransition n) p.1
            (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis
              n i)) by rfl,
    Module.Basis.det_comp]
  rfl

/-- The fixed rational transition scalar times the mapped split determinant
equals the pointwise transition determinant times the higher centered moving
determinant. -/
theorem
    identitySpecialOrthogonalNorthPoleProduct_transitionDetScalar_mul_mappedSplit_det
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n *
        LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
            n p.1
            (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
              n p.2)).toLinearMap =
      identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar
          n p.1 *
        LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
            n p).toLinearMap := by
  rw [
    identitySpecialOrthogonalNorthPoleProductMappedSplit_det_eq_composition_basis_det]
  have hbasisdet :
      (identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n).det
          (fun i =>
            identitySpecialOrthogonalNorthPoleProductHigherToMappedSplitEquiv n
              (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
                n p
                (fderiv ℝ
                  (identitySpecialOrthogonalNorthPoleProductTransition n) p.1
                  (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis
                    n i)))) =
        (identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n).det
            ((identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis
              n).map
              (identitySpecialOrthogonalNorthPoleProductHigherToMappedSplitEquiv
                n).toLinearEquiv) *
          (identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n).det
            (fun i =>
              identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
                n p
                (fderiv ℝ
                  (identitySpecialOrthogonalNorthPoleProductTransition n) p.1
                  (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis
                    n i))) := by
    exact basis_det_equiv_apply
      (identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis n)
      (identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n)
      (identitySpecialOrthogonalNorthPoleProductHigherToMappedSplitEquiv
        n).toLinearEquiv
      (fun i =>
        identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
          n p
          (fderiv ℝ
            (identitySpecialOrthogonalNorthPoleProductTransition n) p.1
            (identitySpecialOrthogonalNorthPoleProductTransitionSourceBasis
              n i)))
  rw [hbasisdet]
  rw [
    identitySpecialOrthogonalNorthPoleProductHigherCentered_composition_targetBasis_det]
  calc
    _ =
        (identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n *
          (identitySpecialOrthogonalNorthPoleProductMappedSplitBasis n).det
            ((identitySpecialOrthogonalNorthPoleProductTransitionTargetBasis
              n).map
              (identitySpecialOrthogonalNorthPoleProductHigherToMappedSplitEquiv
                n).toLinearEquiv)) *
          (LinearMap.det
              (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
                n p).toLinearMap *
            identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar
              n p.1) := by ring
    _ =
        LinearMap.det
            (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
              n p).toLinearMap *
          identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar
            n p.1 := by
      rw [
        identitySpecialOrthogonalNorthPoleProduct_transitionDetScalar_mul_higherToMappedSplit_basisDet,
        one_mul]
    _ = _ := by ring

/-- Absolute-value form of the fixed-scalar composition determinant identity. -/
theorem
    abs_identitySpecialOrthogonalNorthPoleProduct_transitionDetScalar_mul_mappedSplit_det
    (n : ℕ)
    (p : identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet n) :
    |identitySpecialOrthogonalNorthPoleProductTransitionDetScalar n| *
        |LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductMappedSplitDerivative
            n p.1
            (identitySpecialOrthogonalNorthPoleProductHigherChartSourceSet_subset
              n p.2)).toLinearMap| =
      |identitySpecialOrthogonalNorthPoleProductTransitionPointwiseDetScalar
          n p.1| *
        |LinearMap.det
          (identitySpecialOrthogonalNorthPoleProductHigherCenteredMovingDerivative
            n p).toLinearMap| := by
  have h := congrArg abs
    (identitySpecialOrthogonalNorthPoleProduct_transitionDetScalar_mul_mappedSplit_det
      n p)
  simpa only [abs_mul] using h

end PositiveDefiniteIntegralLattice
