import SMSFormula.PadicCayleyTranslatedChartOverlapLocalInversion

/-!
# Exact raw image of a locally normalized p-adic overlap ball

The derivative-normalized overlap transition maps one selected coordinate
ball bijectively onto itself.  This module transports that exact set equality
through the forward tangent equivalence.

The forward image of the level-`k` coordinate subgroup is packaged as an
additive subgroup.  Its affine coset centered at the raw transition of the
source center is clopen.  The raw nonlinear transition maps the selected
source ball exactly onto this target coset.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- The image of the level-`k` coordinate subgroup under the forward tangent
equivalence at an exact translated-overlap point. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (k : ℕ) :
    AddSubgroup
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup F p k).map
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
      F p hF c d X).toLinearEquiv.toAddEquiv.toAddMonoidHom

@[simp]
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup_coe
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (k : ℕ) :
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup
        F p hF c d X k : Set _) =
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X ''
        Matrix.skewAdjointPadicUniformCoordinateBall F p k := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup,
    AddSubgroup.coe_map,
    Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup_coe]
  rfl

/-- The forward tangent image of a coordinate subgroup is clopen. -/
theorem
    isClopen_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (k : ℕ) :
    IsClopen
      (↑(skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup
          F p hF c d X k) :
        Set
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup_coe]
  let A :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
      F p hF c d X
  have himage :
      A '' Matrix.skewAdjointPadicUniformCoordinateBall F p k =
        A.symm ⁻¹' Matrix.skewAdjointPadicUniformCoordinateBall F p k := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨A.symm y, hy, A.apply_symm_apply y⟩
  rw [himage]
  exact IsClopen.preimage
    (Matrix.isClopen_skewAdjointPadicUniformCoordinateBall F p k)
    A.symm.continuous

/-- The affine forward-derivative map centered at the exact overlap point and
its raw transition image. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
        p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
          p n F hF c d X) +
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
      F p hF c d X
      (y -
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
          p n F hF c d X)

/-- The affine target coset obtained from the forward tangent image of the
level-`k` coordinate subgroup. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (k : ℕ) :
    Set
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup
      F p hF c d X k).translatedCoset
    (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF c d X))

/-- The target affine tangent coset is clopen. -/
theorem
    isClopen_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (k : ℕ) :
    IsClopen
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
        F p hF c d X k) := by
  let L :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup
      F p hF c d X k
  let t :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d
      (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
        p n F hF c d X)
  have heq :
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
          F p hF c d X k =
        (Homeomorph.addLeft (-t)) ⁻¹' (L : Set _) := by
    ext y
    change (y - t ∈ L) ↔ (-t + y ∈ L)
    rw [sub_eq_add_neg, add_comm]
  rw [heq]
  exact IsClopen.preimage
    (isClopen_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup
      F p hF c d X k)
    (Homeomorph.addLeft (-t)).continuous

/-- The affine forward tangent map sends the translated source coordinate
ball exactly onto the target affine tangent coset. -/
theorem
    image_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap_coordinateBall
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (k : ℕ) :
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
          F p hF c d X ''
        Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X) =
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
        F p hF c d X k := by
  let x :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X
  let A :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
      F p hF c d X
  let L := Matrix.skewAdjointPadicUniformCoordinateBallAddSubgroup F p k
  let L' :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup
      F p hF c d X k
  let t :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d x
  apply Set.Subset.antisymm
  · rintro w ⟨y, hy, rfl⟩
    have hyL : y - x ∈ L :=
      (Matrix.mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup
        F p k x y).1 hy
    change
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
            F p hF c d X y -
          t ∈
        L'
    have hmap : A (y - x) ∈ L' := by
      dsimp [L']
      rw [
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup,
        AddSubgroup.mem_map]
      exact ⟨y - x, hyL, rfl⟩
    have heq :
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
              F p hF c d X y -
            t =
          A (y - x) := by
      dsimp [
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap,
        x, t, A]
      abel
    rwa [heq]
  · intro w hw
    change w - t ∈ L' at hw
    dsimp [L'] at hw
    rw [
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentImageAddSubgroup,
      AddSubgroup.mem_map] at hw
    obtain ⟨h, hh, hAh⟩ := hw
    let y := x + h
    have hy :
        y ∈ Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x := by
      rw [
        Matrix.mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup]
      have : y - x = h := by
        dsimp [y]
        abel
      rw [this]
      exact hh
    refine ⟨y, hy, ?_⟩
    have hyx : y - x = h := by
      dsimp [y]
      abel
    dsimp [
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap]
    rw [hyx]
    have hAh' : A h = w - t := hAh
    rw [hAh']
    abel

/-- The centered affine forward tangent map is injective. -/
theorem
    injective_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    Function.Injective
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
        F p hF c d X) := by
  intro y z hyz
  have hlinear :
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
            F p hF c d X
            (y -
              skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                p n F hF c d X) =
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
            F p hF c d X
            (z -
              skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                p n F hF c d X) := by
    exact add_left_cancel hyz
  have hsub :
      y -
          skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X =
        z -
          skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X :=
    (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
      F p hF c d X).injective hlinear
  apply sub_eq_zero.mp
  calc
    y - z =
        (y -
            skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X) -
          (z -
            skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X) := by
      abel
    _ = 0 := by rw [hsub, sub_self]

/-- The raw transition factors pointwise through its derivative-normalized
transition followed by the centered affine forward tangent map. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq_tangentAffineMap_normalized
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d)
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
        p n F hF c d y =
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
        F p hF c d X
        (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
          F p hF c d X y) := by
  let x :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X
  let T :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d
  let A :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism
      F p hF c d X
  let R :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
      F p hF c d X
  have hnormalized :
      skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
            F p hF c d X y -
          x =
        R (T y - T x) := by
    dsimp [
      skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition,
      x, T, R]
    abel
  have hcancel : A (R (T y - T x)) = T y - T x := by
    exact
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionForward_apply_reverse
        F p hF c d X (T y - T x)
  have htangent :
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
            F p hF c d X
            (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                F p hF c d X y -
              x) =
        T y - T x := by
    change
      (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
          F p hF c d X).toContinuousLinearMap
          (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
              F p hF c d X y -
            x) =
        T y - T x
    rw [
      ← skewAdjointPadicCayleyTranslatedSourceOverlapTransitionEndomorphism_eq]
    change
      A
          (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
              F p hF c d X y -
            x) =
        T y - T x
    rw [hnormalized, hcancel]
  change T y =
    T x +
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentEquiv
        F p hF c d X
        (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
            F p hF c d X y -
          x)
  rw [htangent]
  abel

/-- At every exact overlap point, one selected coordinate ball has exact raw
transition image equal to the affine forward tangent coset. The source ball
also lies in the overlap, has constant reciprocal density, and the raw
transition is injective on it. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_rawTransition_image_tangentTargetCoset
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ∃ q : ℝ≥0, q < 1 ∧ ∃ k,
      Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X) ⊆
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF c d ∧
      (∀ y ∈
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X),
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse
              p n F hF c d y =
          skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobianInverse
              p n F hF c d
              (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                p n F hF c d X)) ∧
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d ''
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X) =
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
          F p hF c d X k ∧
      Set.InjOn
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d)
        (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X)) := by
  obtain ⟨q, hq, k, hkU, hkconst, hNimage, hNinj⟩ :=
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_derivativeNormalizedTransition_bijective
      F p hF c d X
  refine ⟨q, hq, k, hkU, hkconst, ?_, ?_⟩
  · calc
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
            p n F hF c d ''
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X) =
        (skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
            F p hF c d X ∘
          skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
            F p hF c d X) ''
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X) := by
            apply Set.image_congr
            intro y hy
            exact
              skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq_tangentAffineMap_normalized
                F p hF c d X y
      _ =
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
              F p hF c d X ''
            (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                F p hF c d X ''
              Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
                (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                  p n F hF c d X)) := by
          apply Set.Subset.antisymm
          · rintro w ⟨y, hy, rfl⟩
            exact
              ⟨skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                  F p hF c d X y,
                ⟨y, hy, rfl⟩,
                rfl⟩
          · rintro w ⟨v, ⟨y, hy, rfl⟩, rfl⟩
            exact ⟨y, hy, rfl⟩
      _ =
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
              F p hF c d X ''
            Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
              (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                p n F hF c d X) := by
          rw [hNimage]
      _ =
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentTargetCoset
          F p hF c d X k :=
        image_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap_coordinateBall
          F p hF c d X k
  · intro y hy z hz hyz
    apply hNinj hy hz
    apply
      injective_skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
        F p hF c d X
    calc
      skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
          F p hF c d X
          (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
            F p hF c d X y) =
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d y :=
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq_tangentAffineMap_normalized
          F p hF c d X y).symm
      _ =
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d z := hyz
      _ =
        skewAdjointPadicCayleyTranslatedSourceOverlapTransitionTangentAffineMap
          F p hF c d X
          (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
            F p hF c d X z) :=
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition_eq_tangentAffineMap_normalized
          F p hF c d X z

end PositiveDefiniteIntegralLattice
