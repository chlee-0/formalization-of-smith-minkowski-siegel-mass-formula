import SMSFormula.PadicCayleyTranslatedChartOverlapDeepCoset

/-!
# Basic-ball measure compatibility for a normalized p-adic overlap

The derivative-normalized overlap transition transports every sufficiently
deep coordinate coset exactly to the same-level coset at its image.  Its
selected-ball injectivity therefore identifies the exact restricted preimage
of each such target ball.

Separately, additive translation invariance shows that all same-level
translated coordinate balls have equal coordinate-Haar mass.  These two facts
give equality of the selected-ball pushforward and source restriction when
evaluated on every deeper target ball.

This module does not use measure extensionality, prove equality on all Borel
sets, compose with the affine tangent map, or assert a nonlinear
change-of-variables theorem.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance padicBasicBallMeasureMeasurableSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicBasicBallMeasureBorelSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- Every translated uniform coordinate ball has the same coordinate-Haar
mass as the corresponding zero-centered ball. -/
theorem skewAdjointPadicCoordinateMeasure_translatedUniformCoordinateBall
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicTranslatedUniformCoordinateBall F p k x) =
      skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicUniformCoordinateBall F p k) := by
  let μ := skewAdjointPadicCoordinateMeasure F p
  let translation :
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    fun y => -x + y
  letI : Measure.IsAddHaarMeasure μ :=
    skewAdjointPadicCoordinateMeasure_isAddHaarMeasure F p
  have htranslation : Measurable translation :=
    (continuous_const.add continuous_id).measurable
  have hmap : Measure.map translation μ = μ :=
    Measure.IsAddLeftInvariant.map_add_left_eq_self (-x)
  have happly :=
    congrArg
      (fun ν : Measure
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule =>
        ν (skewAdjointPadicUniformCoordinateBall F p k))
      hmap
  change
    (Measure.map translation μ)
        (skewAdjointPadicUniformCoordinateBall F p k) =
      μ (skewAdjointPadicUniformCoordinateBall F p k) at happly
  rw [Measure.map_apply htranslation
    (isClopen_skewAdjointPadicUniformCoordinateBall F p k).2.measurableSet]
    at happly
  simpa [μ, translation, skewAdjointPadicTranslatedUniformCoordinateBall]
    using happly

/-- Same-level translated coordinate balls have equal coordinate-Haar mass. -/
theorem skewAdjointPadicCoordinateMeasure_translatedUniformCoordinateBall_eq
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicTranslatedUniformCoordinateBall F p k x) =
      skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicTranslatedUniformCoordinateBall F p k y) := by
  rw [
    skewAdjointPadicCoordinateMeasure_translatedUniformCoordinateBall F p k x,
    skewAdjointPadicCoordinateMeasure_translatedUniformCoordinateBall F p k y]

end Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

local instance padicOverlapBasicBallMeasureMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicOverlapBasicBallMeasureBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The derivative-normalized ambient overlap transition is measurable. -/
theorem
    measurable_skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    Measurable
      (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
        F p hF c d X) := by
  let x :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X
  let T :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d
  let R :=
    skewAdjointPadicCayleyTranslatedSourceOverlapTransitionReverseEndomorphism
      F p hF c d X
  have hT : Measurable T :=
    measurable_skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
      p n F hF c d
  have hsub : Measurable (fun y => T y - T x) :=
    (continuous_id.sub continuous_const).measurable.comp hT
  have houter : Continuous (fun z => x + R z) :=
    continuous_const.add R.continuous
  exact houter.measurable.comp hsub

/-- On one selected source ball, the normalized transition has an exact
restricted preimage for every deeper target ball.  Same-level Haar mass
equality then gives equality of the restricted pushforward and source measure
on every such target ball. -/
theorem
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_derivativeNormalizedTransition_basicBallMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (X : skewAdjointPadicCayleyTranslatedSourceOverlap F p hF c d) :
    ∃ k,
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
      skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
          F p hF c d X ''
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X) =
        Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X) ∧
      Set.InjOn
        (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
          F p hF c d X)
        (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
            p n F hF c d X)) ∧
      ∀ l, k ≤ l →
        ∀ y ∈
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
              p n F hF c d X),
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
                (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                  p n F hF c d X) ∩
              skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                  F p hF c d X ⁻¹'
                Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l
                  (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                    F p hF c d X y) =
            Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l y ∧
          Matrix.skewAdjointPadicCoordinateMeasure F p
              (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l y) =
            Matrix.skewAdjointPadicCoordinateMeasure F p
              (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l
                (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                  F p hF c d X y)) ∧
          Measure.map
              (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                F p hF c d X)
              ((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
                (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
                  (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                    p n F hF c d X)))
              (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l
                (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                  F p hF c d X y)) =
            (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
              (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k
                (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
                  p n F hF c d X))
              (Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l
                (skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
                  F p hF c d X y)) := by
  obtain ⟨q, hq, k, hkU, hkconst, -, hdeep⟩ :=
    exists_skewAdjointPadicTranslatedUniformCoordinateBall_derivativeNormalizedTransition_deeper_cosets
      F p hF c d X
  let x :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion
      p n F hF c d X
  let N :=
    skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
      F p hF c d X
  let B := Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k x
  let μ := Matrix.skewAdjointPadicCoordinateMeasure F p
  have hx : x ∈ B := by
    exact Matrix.mem_skewAdjointPadicTranslatedUniformCoordinateBall_self
      F p k x
  obtain ⟨-, hself, hinj⟩ := hdeep k le_rfl x hx
  have hNx : N x = x := by
    exact
      skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition_center
        F p hF c d X
  change N '' B =
    Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p k (N x) at hself
  rw [hNx] at hself
  change N '' B = B at hself
  refine ⟨k, hkU, hkconst, hself, hinj, ?_⟩
  intro l hkl y hy
  obtain ⟨hsourceSubset, himage, -⟩ := hdeep l hkl y hy
  let C := Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l y
  let D :=
    Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p l (N y)
  change N '' C = D at himage
  have hpre : B ∩ N ⁻¹' D = C := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzB, hzD⟩
      change N z ∈ D at hzD
      rw [← himage] at hzD
      obtain ⟨w, hwC, hwz⟩ := hzD
      have hwB : w ∈ B := hsourceSubset hwC
      have hwz' : w = z := hinj hwB hzB hwz
      rwa [← hwz']
    · intro z hzC
      refine ⟨hsourceSubset hzC, ?_⟩
      change N z ∈ D
      rw [← himage]
      exact ⟨z, hzC, rfl⟩
  have hmass : μ C = μ D := by
    exact
      Matrix.skewAdjointPadicCoordinateMeasure_translatedUniformCoordinateBall_eq
        F p l y (N y)
  have hNmeas : Measurable N :=
    measurable_skewAdjointPadicCayleyTranslatedSourceOverlapDerivativeNormalizedTransition
      F p hF c d X
  have hDmeas : MeasurableSet D :=
    (Matrix.isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
      F p l (N y)).2.measurableSet
  have hpreMeas : MeasurableSet (N ⁻¹' D) :=
    hNmeas hDmeas
  have hNy : N y ∈ B := by
    rw [← hself]
    exact ⟨y, hy, rfl⟩
  have htargetSubset : D ⊆ B :=
    Matrix.skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_mem
      F p hkl hNy
  refine ⟨hpre, hmass, ?_⟩
  change Measure.map N (μ.restrict B) D = (μ.restrict B) D
  rw [Measure.map_apply hNmeas hDmeas,
    Measure.restrict_apply hpreMeas,
    Measure.restrict_apply hDmeas]
  rw [Set.inter_comm (N ⁻¹' D) B, hpre, Set.inter_eq_left.mpr htargetSubset]
  exact hmass

end PositiveDefiniteIntegralLattice
