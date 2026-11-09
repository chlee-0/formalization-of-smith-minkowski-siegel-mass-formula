import SMSFormula.PadicCayleyTranslatedChartOverlapAmbient
import SMSFormula.SkewAdjointPadicCoordinateBallBasis
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local constancy of the translated p-adic overlap Jacobian

The restricted derivative of an exact translated Cayley overlap
varies continuously in the operator norm.  Its determinant is nonzero because
the derivative is a continuous linear equivalence.  The ultrametric norm on
`ℚ_[p]` is therefore locally constant on these determinants, and so is the
reciprocal `ENNReal` Jacobian density.

The exact overlap is openly embedded in the ambient transported skew-adjoint
carrier.  Every ambient overlap point consequently has a uniform translated
coordinate ball, contained in the overlap, on which the ambient reciprocal
Jacobian density is constant.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- A continuous nowhere-zero p-adic scalar has locally constant nonnegative
norm. -/
theorem isLocallyConstant_nnnorm_of_continuous_ne_zero_padic
    {p : ℕ} [Fact (Nat.Prime p)]
    {X : Type*} [TopologicalSpace X]
    (f : X → ℚ_[p]) (hf : Continuous f)
    (hne : ∀ x, f x ≠ 0) :
    IsLocallyConstant (fun x => ‖f x‖₊) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : 0 < ‖f x‖ := norm_pos_iff.mpr (hne x)
  have hball :
      Metric.ball (f x) ‖f x‖ ∈ 𝓝 (f x) :=
    Metric.ball_mem_nhds _ hpos
  filter_upwards [hf.continuousAt hball] with y hy
  apply NNReal.eq
  exact Padic.norm_eq_of_norm_sub_lt_right
    (by simpa [dist_eq_norm] using hy)

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The explicit inverse left-trivialized Cayley endomorphism varies
continuously with the transported skew-adjoint coordinate. -/
theorem continuous_skewAdjointPadicCayleyLeftTrivializedInverse
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Continuous
      (fun X : (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule =>
        skewAdjointPadicCayleyLeftTrivializedInverse F p X) := by
  letI : NormedSpace ℚ_[p] (Matrix ι ι ℚ_[p]) :=
    Matrix.linftyOpNormedSpace
  let E :=
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
  let inclusion : E →ₗᵢ[ℚ_[p]] Matrix ι ι ℚ_[p] :=
    E.subtypeₗᵢ
  apply
    (((inclusion.postcomp (E := E)).isometry.comp_continuous_iff).mp)
  have hcoe : Continuous (fun X : E => (X : Matrix ι ι ℚ_[p])) :=
    continuous_subtype_val
  have hplus :
      Continuous (fun X : E => 1 + (X : Matrix ι ι ℚ_[p])) :=
    continuous_const.add hcoe
  have hminus :
      Continuous (fun X : E => 1 - (X : Matrix ι ι ℚ_[p])) :=
    continuous_const.sub hcoe
  have hleft :
      Continuous
        (fun X : E =>
          ContinuousLinearMap.mulLeftRight ℚ_[p]
            (Matrix ι ι ℚ_[p])
            (1 + (X : Matrix ι ι ℚ_[p]))) :=
    (ContinuousLinearMap.mulLeftRight ℚ_[p]
      (Matrix ι ι ℚ_[p])).continuous.comp hplus
  have hmul :
      Continuous
        (fun X : E =>
          ContinuousLinearMap.mulLeftRight ℚ_[p]
            (Matrix ι ι ℚ_[p])
            (1 + (X : Matrix ι ι ℚ_[p]))
            (1 - (X : Matrix ι ι ℚ_[p]))) :=
    hleft.clm_apply hminus
  have hambient :
      Continuous
        (fun X : E =>
          skewAdjointPadicCayleyLeftTrivializedInverseAmbient F p X) := by
    simp only [skewAdjointPadicCayleyLeftTrivializedInverseAmbient]
    exact (hmul.clm_comp continuous_const).const_smul ((2 : ℚ_[p])⁻¹)
  exact hambient

/-- On the explicit Cayley source, the intrinsic left-trivialized
endomorphism varies continuously in the operator norm. -/
theorem continuous_skewAdjointPadicCayleyLeftTrivializedEndomorphism
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) :
    Continuous
      (fun X : skewAdjointPadicCayleySource F p =>
        skewAdjointPadicCayleyLeftTrivializedEndomorphism
          F p X.1 X.2) := by
  letI : NormedSpace ℚ_[p] (Matrix ι ι ℚ_[p]) :=
    Matrix.linftyOpNormedSpace
  let E :=
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
  let inclusion : E →ₗᵢ[ℚ_[p]] Matrix ι ι ℚ_[p] :=
    E.subtypeₗᵢ
  apply
    (((inclusion.postcomp (E := E)).isometry.comp_continuous_iff).mp)
  have hcoe :
      Continuous
        (fun X : skewAdjointPadicCayleySource F p =>
          (X.1 : Matrix ι ι ℚ_[p])) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hplus :
      Continuous
        (fun X : skewAdjointPadicCayleySource F p =>
          1 + (X.1 : Matrix ι ι ℚ_[p])) :=
    continuous_const.add hcoe
  have hminus :
      Continuous
        (fun X : skewAdjointPadicCayleySource F p =>
          1 - (X.1 : Matrix ι ι ℚ_[p])) :=
    continuous_const.sub hcoe
  have hplusInv :
      Continuous
        (fun X : skewAdjointPadicCayleySource F p =>
          (1 + (X.1 : Matrix ι ι ℚ_[p]))⁻¹) := by
    exact (continuousOn_padicNonsingInv p).comp_continuous hplus
      (fun X => isUnit_one_add_of_mem_skewAdjointPadicCayleySource
        F p hF X.1 X.2)
  have hminusInv :
      Continuous
        (fun X : skewAdjointPadicCayleySource F p =>
          (1 - (X.1 : Matrix ι ι ℚ_[p]))⁻¹) := by
    exact (continuousOn_padicNonsingInv p).comp_continuous hminus
      (fun X => X.2)
  have hleft :
      Continuous
        (fun X : skewAdjointPadicCayleySource F p =>
          ContinuousLinearMap.mulLeftRight ℚ_[p]
            (Matrix ι ι ℚ_[p])
            (1 + (X.1 : Matrix ι ι ℚ_[p]))⁻¹) :=
    (ContinuousLinearMap.mulLeftRight ℚ_[p]
      (Matrix ι ι ℚ_[p])).continuous.comp hplusInv
  have hmul :
      Continuous
        (fun X : skewAdjointPadicCayleySource F p =>
          ContinuousLinearMap.mulLeftRight ℚ_[p]
            (Matrix ι ι ℚ_[p])
            (1 + (X.1 : Matrix ι ι ℚ_[p]))⁻¹
            (1 - (X.1 : Matrix ι ι ℚ_[p]))⁻¹) :=
    hleft.clm_apply hminusInv
  have hambient :
      Continuous
        (fun X : skewAdjointPadicCayleySource F p =>
          (2 : ℚ_[p]) •
            (ContinuousLinearMap.mulLeftRight ℚ_[p]
              (Matrix ι ι ℚ_[p])
              (1 + (X.1 : Matrix ι ι ℚ_[p]))⁻¹
              (1 - (X.1 : Matrix ι ι ℚ_[p]))⁻¹).comp
                (skewAdjointPadicAmbientInclusion F p)) :=
    continuous_const.smul (hmul.clm_comp continuous_const)
  convert hambient using 1
  funext X
  apply ContinuousLinearMap.ext
  intro H
  change
    (skewAdjointPadicCayleyLeftTrivializedEndomorphism
      F p X.1 X.2 H : Matrix ι ι ℚ_[p]) =
      2 • ((1 + (X.1 : Matrix ι ι ℚ_[p]))⁻¹ *
        (H : Matrix ι ι ℚ_[p]) *
        (1 - (X.1 : Matrix ι ι ℚ_[p]))⁻¹)
  exact
    coe_skewAdjointPadicCayleyLeftTrivializedEndomorphism_apply
      F p X.1 H X.2

end Matrix

/-- The restricted derivative of the exact translated overlap varies
continuously in the operator norm. -/
theorem
    continuous_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Continuous
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
        F p hF c d) := by
  let T :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionHomeomorph
      F p hF c d
  have hforward :
      Continuous
        (fun X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d =>
          Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
            F p X.1 X.1.2) :=
    (Matrix.continuous_skewAdjointPadicCayleyLeftTrivializedEndomorphism
      F p hF).comp continuous_subtype_val
  have hinverse :
      Continuous
        (fun X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d =>
          Matrix.skewAdjointPadicCayleyLeftTrivializedInverse
            F p (T X).1.1) :=
    (Matrix.continuous_skewAdjointPadicCayleyLeftTrivializedInverse
      F p).comp
        (continuous_subtype_val.comp
          (continuous_subtype_val.comp T.continuous))
  have hcomp :
      Continuous
        (fun X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d =>
          (Matrix.skewAdjointPadicCayleyLeftTrivializedInverse
            F p (T X).1.1).comp
              (Matrix.skewAdjointPadicCayleyLeftTrivializedEndomorphism
                F p X.1 X.1.2)) :=
    hinverse.clm_comp hforward
  convert hcomp using 1
  funext X
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_eq]
  rfl

/-- The algebraic determinant of the restricted overlap derivative
is continuous. -/
theorem
    continuous_det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Continuous
      (fun X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d =>
        LinearMap.det
          (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
            F p hF c d X).toLinearMap) :=
  ContinuousLinearMap.continuous_det.comp
    (continuous_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
      F p hF c d)

/-- The determinant of the restricted overlap derivative is
nowhere zero. -/
theorem
    det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    LinearMap.det
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
        F p hF c d X).toLinearMap ≠ 0 := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_eq]
  change
    LinearMap.det
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X).toLinearMap ≠ 0
  rw [← LinearEquiv.coe_det]
  exact Units.ne_zero _

/-- The reciprocal determinant density is locally constant on the exact
translated source overlap. -/
theorem
    isLocallyConstant_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    IsLocallyConstant
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
        p n F hF c d) := by
  have hnorm :
      IsLocallyConstant
        (fun X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d =>
          ‖LinearMap.det
            (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
              F p hF c d X).toLinearMap‖₊) :=
    isLocallyConstant_nnnorm_of_continuous_ne_zero_padic
      _
      (continuous_det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
        F p hF c d)
      (det_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_ne_zero
        F p hF c d)
  have hinv :
      IsLocallyConstant
        (fun X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d =>
          ((‖LinearMap.det
            (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
              F p hF c d X).toLinearMap‖₊ : ENNReal)⁻¹)) :=
    hnorm.comp (fun r : NNReal => ((r : ENNReal)⁻¹))
  simpa only [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse,
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_eq]
    using hinv

/-- Every ambient overlap point is contained in a uniform translated
coordinate ball lying in the overlap on which the ambient reciprocal
Jacobian density is constant. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_ambientOverlap_const_jacobianInverse
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hx :
      x ∈ skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d) :
    ∃ k,
      Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x ⊆
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF c d ∧
      ∀ y ∈ Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x,
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse
            p n F hF c d y =
          skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse
            p n F hF c d x := by
  rcases hx with ⟨X, rfl⟩
  let inclusion :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d
  obtain ⟨V, hVopen, hXV, hconst⟩ :=
    (isLocallyConstant_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionJacobianInverse
      F p hF c d).exists_open X
  have himageOpen : IsOpen (inclusion '' V) :=
    (isOpenEmbedding_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d).isOpenMap V hVopen
  have hXimage : inclusion X ∈ inclusion '' V :=
    ⟨X, hXV, rfl⟩
  obtain ⟨k, hk⟩ :=
    Matrix.exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_mem_nhds
      F p (inclusion X) (himageOpen.mem_nhds hXimage)
  refine ⟨k, ?_, ?_⟩
  · intro y hy
    rcases hk hy with ⟨Y, hYV, rfl⟩
    exact ⟨Y, rfl⟩
  · intro y hy
    rcases hk hy with ⟨Y, hYV, rfl⟩
    rw [
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse_eq,
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse_eq,
      hconst Y hYV]

end PositiveDefiniteIntegralLattice
