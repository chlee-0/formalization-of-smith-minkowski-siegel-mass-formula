import SMSFormula.RationalSpecialOrthogonalAdelicTangent
import Mathlib.LinearAlgebra.Projection

/-!
# Topology of the full-adelic skew-adjoint tangent carrier

This file proves that the fixed differential coordinates on the full-adelic
skew-adjoint tangent carrier are a homeomorphism for the ambient matrix
subtype topology.  A rational complement supplies an ambient linear
projection.  After scalar extension, its coordinate functionals are written
as finite sums of adelic matrix entries against rational coefficients, so
their continuity uses only the topological-ring structure of the adeles.

Consequently the measurable structure transported through the coordinates is
the ambient Borel structure.  No measure on the adelic special orthogonal group or
Tamagawa-number theorem is introduced.
-/

noncomputable section

open MeasureTheory Set
open scoped Matrix ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- A chosen rational complement to the skew-adjoint tangent subspace. -/
noncomputable def skewAdjointTangentComplement
    (V : RationalQuadraticSpaceMatrix n) :
    Submodule ℚ (Matrix (Fin n) (Fin n) ℚ) :=
  Classical.choose V.skewAdjointTangent.toSubmodule.exists_isCompl

theorem skewAdjointTangent_isCompl_complement
    (V : RationalQuadraticSpaceMatrix n) :
    IsCompl V.skewAdjointTangent.toSubmodule
      V.skewAdjointTangentComplement :=
  Classical.choose_spec V.skewAdjointTangent.toSubmodule.exists_isCompl

/-- The rational ambient projection onto the skew-adjoint tangent subspace. -/
noncomputable def skewAdjointTangentProjection
    (V : RationalQuadraticSpaceMatrix n) :
    Matrix (Fin n) (Fin n) ℚ →ₗ[ℚ] V.skewAdjointTangent :=
  V.skewAdjointTangent.toSubmodule.linearProjOfIsCompl
    V.skewAdjointTangentComplement
    V.skewAdjointTangent_isCompl_complement

@[simp]
theorem skewAdjointTangentProjection_apply_tangent
    (V : RationalQuadraticSpaceMatrix n) (X : V.skewAdjointTangent) :
    V.skewAdjointTangentProjection X = X :=
  Submodule.linearProjOfIsCompl_apply_left
    V.skewAdjointTangent_isCompl_complement X

/-- Rational coordinates obtained by projecting an ambient matrix onto the
skew-adjoint tangent space. -/
noncomputable def skewAdjointAmbientCoordinateLinearMap
    (V : RationalQuadraticSpaceMatrix n) :
    Matrix (Fin n) (Fin n) ℚ →ₗ[ℚ]
      (V.InvariantDifferentialCoordinateIndex → ℚ) :=
  (Matrix.skewAdjointFinBasis V.pairingMatrix).equivFun.toLinearMap.comp
    V.skewAdjointTangentProjection

@[simp]
theorem skewAdjointAmbientCoordinateLinearMap_apply_basis
    (V : RationalQuadraticSpaceMatrix n)
    (k : V.InvariantDifferentialCoordinateIndex) :
    V.skewAdjointAmbientCoordinateLinearMap
        (Matrix.skewAdjointFinBasis V.pairingMatrix k) =
      Pi.single k 1 := by
  change
    (Matrix.skewAdjointFinBasis V.pairingMatrix).equivFun
      (V.skewAdjointTangentProjection
        (Matrix.skewAdjointFinBasis V.pairingMatrix k)) =
      Pi.single k 1
  rw [V.skewAdjointTangentProjection_apply_tangent]
  ext j
  simp [Pi.single_apply, eq_comm]

/-- The rational coefficient of one ambient matrix entry in one projected
skew-adjoint coordinate. -/
noncomputable def skewAdjointAmbientCoordinateCoefficient
    (V : RationalQuadraticSpaceMatrix n)
    (i j : Fin n) (k : V.InvariantDifferentialCoordinateIndex) :
    PositiveDefiniteIntegralLattice.RationalAdele :=
  algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele
    (V.skewAdjointAmbientCoordinateLinearMap
      (Pi.single i (Pi.single j (1 : ℚ)) :
        Matrix (Fin n) (Fin n) ℚ) k)

/-- The full-adelic ambient coordinate extractor.  Its finite matrix formula
is the scalar extension of the rational projection coordinates. -/
noncomputable def fullAdelicSkewAdjointAmbientCoordinateLinearMap
    (V : RationalQuadraticSpaceMatrix n) :
    Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele →ₗ[
      PositiveDefiniteIntegralLattice.RationalAdele]
      (V.InvariantDifferentialCoordinateIndex →
        PositiveDefiniteIntegralLattice.RationalAdele) where
  toFun X k :=
    ∑ i, ∑ j, X i j *
      V.skewAdjointAmbientCoordinateCoefficient i j k
  map_add' X Y := by
    ext k
    simp only [Pi.add_apply, Matrix.add_apply, add_mul,
      Finset.sum_add_distrib]
  map_smul' a X := by
    ext k
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.smul_apply,
      RingHom.id_apply, mul_assoc, Finset.mul_sum]

theorem continuous_fullAdelicSkewAdjointAmbientCoordinateLinearMap
    (V : RationalQuadraticSpaceMatrix n) :
    Continuous V.fullAdelicSkewAdjointAmbientCoordinateLinearMap := by
  have hcontinuous : Continuous
      (fun X : Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele =>
        fun k => ∑ i, ∑ j, X i j *
          V.skewAdjointAmbientCoordinateCoefficient i j k) := by
    rw [continuous_pi_iff]
    intro k
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    have hij : Continuous
        (fun X : Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele =>
          X i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact hij.mul continuous_const
  exact hcontinuous

set_option backward.isDefEq.respectTransparency false in
/-- The explicit ambient extractor commutes with mapping rational matrices
entrywise to the rational adeles. -/
theorem fullAdelicSkewAdjointAmbientCoordinateLinearMap_map
    (V : RationalQuadraticSpaceMatrix n)
    (X : Matrix (Fin n) (Fin n) ℚ) :
    V.fullAdelicSkewAdjointAmbientCoordinateLinearMap
        (X.map (algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele)) =
      fun k =>
        algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele
          (V.skewAdjointAmbientCoordinateLinearMap X k) := by
  have hX :
      X = ∑ i, ∑ j, X i j •
        (Pi.single i (Pi.single j (1 : ℚ)) :
          Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp only [if_pos]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    · intro a _ ha
      simp [ha.symm]
    · simp
  ext k
  have hcoordinate :
      V.skewAdjointAmbientCoordinateLinearMap X k =
        ∑ i, ∑ j, X i j *
          V.skewAdjointAmbientCoordinateLinearMap
            (Pi.single i (Pi.single j (1 : ℚ)) :
              Matrix (Fin n) (Fin n) ℚ) k := by
    conv_lhs => rw [hX]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  change
    (∑ i, ∑ j,
      algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele (X i j) *
        algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele
          (V.skewAdjointAmbientCoordinateLinearMap
            (Pi.single i (Pi.single j (1 : ℚ)) :
              Matrix (Fin n) (Fin n) ℚ) k)) =
      algebraMap ℚ PositiveDefiniteIntegralLattice.RationalAdele
        (V.skewAdjointAmbientCoordinateLinearMap X k)
  rw [hcoordinate, map_sum]
  simp only [map_sum, map_mul]

/-- The ambient adelic coordinate extractor is a left inverse to the fixed
skew-adjoint coordinate map. -/
@[simp]
theorem fullAdelicSkewAdjointAmbientCoordinateLinearMap_coordinate
    (V : RationalQuadraticSpaceMatrix n)
    (x : V.InvariantDifferentialCoordinateIndex →
      PositiveDefiniteIntegralLattice.RationalAdele) :
    V.fullAdelicSkewAdjointAmbientCoordinateLinearMap
        (V.fullAdelicSkewAdjointCoordinateLinearMap x) = x := by
  rw [V.fullAdelicSkewAdjointCoordinateLinearMap_apply, map_sum]
  simp only [map_smul,
    V.fullAdelicSkewAdjointAmbientCoordinateLinearMap_map,
    V.skewAdjointAmbientCoordinateLinearMap_apply_basis]
  ext k
  simp [Pi.single_apply]

/-- On the full skew-adjoint tangent carrier, the ambient extractor is exactly
the inverse of the fixed coordinate equivalence. -/
theorem fullAdelicSkewAdjointAmbientCoordinateLinearMap_apply_tangent
    (V : RationalQuadraticSpaceMatrix n)
    (X : skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :
    V.fullAdelicSkewAdjointAmbientCoordinateLinearMap X =
      V.fullAdelicSkewAdjointTangentCoordinateEquiv.symm X := by
  let x := V.fullAdelicSkewAdjointTangentCoordinateEquiv.symm X
  have hmatrix :
      (X : Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) =
        V.fullAdelicSkewAdjointCoordinateLinearMap x := by
    rw [← V.coe_fullAdelicSkewAdjointTangentCoordinateEquiv_apply]
    exact (congrArg Subtype.val
      (V.fullAdelicSkewAdjointTangentCoordinateEquiv.apply_symm_apply X)).symm
  rw [hmatrix,
    V.fullAdelicSkewAdjointAmbientCoordinateLinearMap_coordinate]

theorem continuous_fullAdelicSkewAdjointTangentCoordinateEquiv_symm
    (V : RationalQuadraticSpaceMatrix n) :
    Continuous V.fullAdelicSkewAdjointTangentCoordinateEquiv.symm := by
  have heq :
      V.fullAdelicSkewAdjointTangentCoordinateEquiv.symm =
        V.fullAdelicSkewAdjointAmbientCoordinateLinearMap ∘
          (Subtype.val :
            skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix →
              Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele) := by
    funext X
    exact
      (V.fullAdelicSkewAdjointAmbientCoordinateLinearMap_apply_tangent X).symm
  rw [heq]
  exact
    V.continuous_fullAdelicSkewAdjointAmbientCoordinateLinearMap.comp
      continuous_subtype_val

/-- Fixed differential coordinates are homeomorphic to the full adelic
skew-adjoint tangent carrier with its ambient matrix subtype topology. -/
noncomputable def fullAdelicSkewAdjointTangentCoordinateHomeomorph
    (V : RationalQuadraticSpaceMatrix n) :
    (V.InvariantDifferentialCoordinateIndex →
        PositiveDefiniteIntegralLattice.RationalAdele) ≃ₜ
      skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix where
  toEquiv := V.fullAdelicSkewAdjointTangentCoordinateEquiv.toEquiv
  continuous_toFun :=
    V.continuous_fullAdelicSkewAdjointTangentCoordinateEquiv
  continuous_invFun :=
    V.continuous_fullAdelicSkewAdjointTangentCoordinateEquiv_symm

/-- The same homeomorphism, retaining its full adelic linear structure. -/
noncomputable def fullAdelicSkewAdjointTangentCoordinateContinuousLinearEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    (V.InvariantDifferentialCoordinateIndex →
        PositiveDefiniteIntegralLattice.RationalAdele) ≃L[PositiveDefiniteIntegralLattice.RationalAdele]
      skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix where
  toLinearEquiv := V.fullAdelicSkewAdjointTangentCoordinateEquiv
  continuous_toFun :=
    V.continuous_fullAdelicSkewAdjointTangentCoordinateEquiv
  continuous_invFun :=
    V.continuous_fullAdelicSkewAdjointTangentCoordinateEquiv_symm

theorem fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv_apply
    (V : RationalQuadraticSpaceMatrix n)
    (x : V.InvariantDifferentialCoordinateIndex →
      PositiveDefiniteIntegralLattice.RationalAdele) :
    V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv x =
      V.fullAdelicSkewAdjointTangentCoordinateHomeomorph x := by
  apply Subtype.ext
  change
    V.fullAdelicSkewAdjointCoordinateLinearMap x =
      (V.fullAdelicSkewAdjointTangentCoordinateEquiv x :
        Matrix (Fin n) (Fin n) PositiveDefiniteIntegralLattice.RationalAdele)
  rw [V.coe_fullAdelicSkewAdjointTangentCoordinateEquiv_apply]

theorem fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv_symm_apply
    (V : RationalQuadraticSpaceMatrix n)
    (X : skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :
    V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.symm X =
      V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.symm X := by
  apply V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.injective
  calc
    V.fullAdelicSkewAdjointTangentCoordinateHomeomorph
        (V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.symm X) =
        V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv
          (V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.symm X) :=
      (V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv_apply _).symm
    _ = X :=
      V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.apply_symm_apply X
    _ = V.fullAdelicSkewAdjointTangentCoordinateHomeomorph
        (V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.symm X) :=
      V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.apply_symm_apply X
        |>.symm

/-- The coordinate-transported measurable structure on the full tangent
carrier is exactly its ambient Borel structure. -/
theorem fullAdelicSkewAdjointTangentMeasurableSpace_eq_borel
    (V : RationalQuadraticSpaceMatrix n) :
    (inferInstance : MeasurableSpace
      (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix)) =
      borel (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) := by
  have hcoordinateBorel :
      PositiveDefiniteIntegralLattice.rationalAdeleCoordinateMeasurableSpace
          (Module.finrank ℚ V.skewAdjointTangent) =
        borel (V.InvariantDifferentialCoordinateIndex →
          PositiveDefiniteIntegralLattice.RationalAdele) :=
    BorelSpace.measurable_eq
  ext s
  constructor
  · intro hs
    have hpre0 :=
      V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.measurable hs
    have hpre :
        MeasurableSet
          (V.fullAdelicSkewAdjointTangentCoordinateHomeomorph ⁻¹' s) := by
      have hset :
          V.fullAdelicSkewAdjointTangentCoordinateHomeomorph ⁻¹' s =
            V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv ⁻¹' s := by
        ext x
        change
          V.fullAdelicSkewAdjointTangentCoordinateHomeomorph x ∈ s ↔
            V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv x ∈ s
        rw [V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv_apply]
      rw [hset]
      exact hpre0
    have hsymmMeasurable :
        @Measurable
          (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix)
          (V.InvariantDifferentialCoordinateIndex →
            PositiveDefiniteIntegralLattice.RationalAdele)
          (borel
            (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix))
          (PositiveDefiniteIntegralLattice.rationalAdeleCoordinateMeasurableSpace
            (Module.finrank ℚ V.skewAdjointTangent))
          V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.symm := by
      exact hcoordinateBorel.symm ▸
        V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.symm.continuous.borel_measurable
    have hs' := hpre.preimage hsymmMeasurable
    have hset :
        V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.symm ⁻¹'
            (V.fullAdelicSkewAdjointTangentCoordinateHomeomorph ⁻¹' s) =
          s := by
      ext X
      simp
    rw [hset] at hs'
    exact hs'
  · intro hs
    have hforwardMeasurable :
        @Measurable
          (V.InvariantDifferentialCoordinateIndex →
            PositiveDefiniteIntegralLattice.RationalAdele)
          (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix)
          (PositiveDefiniteIntegralLattice.rationalAdeleCoordinateMeasurableSpace
            (Module.finrank ℚ V.skewAdjointTangent))
          (borel
            (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix))
          V.fullAdelicSkewAdjointTangentCoordinateHomeomorph := by
      exact hcoordinateBorel.symm ▸
        V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.continuous.borel_measurable
    have hpre :
        MeasurableSet
          (V.fullAdelicSkewAdjointTangentCoordinateHomeomorph ⁻¹' s) :=
      hs.preimage hforwardMeasurable
    have hs' :=
      V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.symm.measurable
        hpre
    have hs'' :
        MeasurableSet
          (V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.symm ⁻¹'
            (V.fullAdelicSkewAdjointTangentCoordinateHomeomorph ⁻¹' s)) := by
      have hset :
          V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.symm ⁻¹'
              (V.fullAdelicSkewAdjointTangentCoordinateHomeomorph ⁻¹' s) =
            V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.symm ⁻¹'
              (V.fullAdelicSkewAdjointTangentCoordinateHomeomorph ⁻¹' s) := by
        ext X
        change
          V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.symm X ∈
              V.fullAdelicSkewAdjointTangentCoordinateHomeomorph ⁻¹' s ↔
            V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv.symm X ∈
              V.fullAdelicSkewAdjointTangentCoordinateHomeomorph ⁻¹' s
        rw [
          V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv_symm_apply]
      rw [hset]
      exact hs'
    have hset :
        V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.symm ⁻¹'
            (V.fullAdelicSkewAdjointTangentCoordinateHomeomorph ⁻¹' s) =
          s := by
      ext X
      simp
    rw [hset] at hs''
    exact hs''

instance fullAdelicSkewAdjointTangentBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :=
  ⟨V.fullAdelicSkewAdjointTangentMeasurableSpace_eq_borel⟩

noncomputable instance fullAdelicSkewAdjointTangentLocallyCompactSpace
    (V : RationalQuadraticSpaceMatrix n) :
    LocallyCompactSpace
      (skewAdjointMatricesLieSubalgebra V.fullAdelicFormMatrix) :=
  V.fullAdelicSkewAdjointTangentCoordinateHomeomorph.locallyCompactSpace_iff.mp
    inferInstance

theorem fullAdelicSkewAdjointTangentCoordinateMeasure_eq_map_continuousLinearEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicSkewAdjointTangentCoordinateMeasure =
      Measure.map
        V.fullAdelicSkewAdjointTangentCoordinateContinuousLinearEquiv
        V.invariantDifferentialAdeleCoordinateNormalization.measure := by
  rw [V.fullAdelicSkewAdjointTangentCoordinateMeasure_eq_map]
  congr 1
  funext x
  exact V.fullAdelicSkewAdjointTangentCoordinateMeasurableEquiv_apply x

end RationalQuadraticSpaceMatrix
