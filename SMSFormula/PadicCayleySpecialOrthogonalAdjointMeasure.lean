import SMSFormula.PadicCayleySpecialOrthogonalAdjoint

/-!
# Adjoint invariance of the p-adic Cayley source measures

The p-adic special-orthogonal adjoint homeomorphism preserves both the
coordinate Haar measure on the exact Cayley source and its reciprocal-Jacobian
differential measure.  The coordinate statement is obtained by embedding the
source into the ambient skew-adjoint space and using the determinant-one
linear transport theorem.  The differential statement then follows from the
pointwise density identity.

No target chart or global group measure is used here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal Topology

namespace Matrix

open PositiveDefiniteIntegralLattice

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyAdjointMeasureMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyAdjointMeasureBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The inverse image of the exact Cayley source under special-orthogonal
adjoint conjugation is the same source. -/
theorem preimage_skewAdjointPadicCayleySource_specialOrthogonalAdjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
        p n F hF hdet g ⁻¹' skewAdjointPadicCayleySource F p =
      skewAdjointPadicCayleySource F p := by
  ext X
  exact skewAdjointPadicSpecialOrthogonalAdjoint_mem_cayleySource_iff
    p n F hF hdet g X

/-- The ambient coordinate Haar measure restricted to the Cayley source is
preserved by special-orthogonal adjoint conjugation. -/
theorem map_restrict_skewAdjointPadicCoordinateMeasure_specialOrthogonalAdjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
          p n F hF hdet g)
        ((skewAdjointPadicCoordinateMeasure F p).restrict
          (skewAdjointPadicCayleySource F p)) =
      (skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleySource F p) := by
  let A := skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
    p n F hF hdet g
  let S := skewAdjointPadicCayleySource F p
  let μ := skewAdjointPadicCoordinateMeasure F p
  have hS : MeasurableSet S :=
    (isOpen_skewAdjointPadicCayleySource F p).measurableSet
  have hpre : A ⁻¹' S = S :=
    preimage_skewAdjointPadicCayleySource_specialOrthogonalAdjoint
      p n F hF hdet g
  change Measure.map A (μ.restrict S) = μ.restrict S
  calc
    Measure.map A (μ.restrict S) =
        Measure.map A (μ.restrict (A ⁻¹' S)) := by rw [hpre]
    _ = (Measure.map A μ).restrict S :=
      (Measure.restrict_map A.continuous.measurable hS).symm
    _ = μ.restrict S := by
      rw [map_skewAdjointPadicCoordinateMeasure_specialOrthogonalAdjoint]

/-- The exact source-subtype coordinate measure is preserved by the
restricted special-orthogonal adjoint homeomorphism. -/
theorem
    map_skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_specialOrthogonalAdjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
          p n F hF hdet g)
        (skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F) =
      skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F := by
  let S := skewAdjointPadicCayleySource F p
  let i : S →
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    Subtype.val
  let A := skewAdjointPadicSpecialOrthogonalAdjointContinuousLinearEquiv
    p n F hF hdet g
  let e := skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
    p n F hF hdet g
  let μ := skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F
  let m := skewAdjointPadicCoordinateMeasure F p
  have hS : MeasurableSet S :=
    (isOpen_skewAdjointPadicCayleySource F p).measurableSet
  apply (MeasurableEmbedding.subtype_coe hS).map_injective
  calc
    Measure.map i (Measure.map e μ) = Measure.map (i ∘ e) μ := by
      rw [Measure.map_map continuous_subtype_val.measurable
        e.continuous.measurable]
    _ = Measure.map (A ∘ i) μ := by
      apply Measure.map_congr
      filter_upwards [] with X
      exact
        coe_skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph_apply
          p n F hF hdet g X
    _ = Measure.map A (Measure.map i μ) := by
      rw [Measure.map_map A.continuous.measurable
        continuous_subtype_val.measurable]
    _ = Measure.map A (m.restrict S) := by
      rw [map_skewAdjointPadicCayleySourceCoordinateSubtypeMeasure]
    _ = m.restrict S :=
      map_restrict_skewAdjointPadicCoordinateMeasure_specialOrthogonalAdjoint
        p n F hF hdet g
    _ = Measure.map i μ := by
      rw [map_skewAdjointPadicCayleySourceCoordinateSubtypeMeasure]

/-- The reciprocal-Jacobian differential measure on the exact p-adic Cayley
source is preserved by special-orthogonal adjoint conjugation. -/
theorem
    map_skewAdjointPadicCayleySourceDifferentialSubtypeMeasure_specialOrthogonalAdjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Measure.map
        (skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
          p n F hF hdet g)
        (skewAdjointPadicCayleySourceDifferentialSubtypeMeasure p n F) =
      skewAdjointPadicCayleySourceDifferentialSubtypeMeasure p n F := by
  let e := skewAdjointPadicCayleySourceSpecialOrthogonalAdjointHomeomorph
    p n F hF hdet g
  let μ := skewAdjointPadicCayleySourceCoordinateSubtypeMeasure p n F
  let d := skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F
  have hd : Measurable d :=
    measurable_skewAdjointPadicCayleySourceDifferentialDensityENNReal p n F
  have hfun : d = d ∘ e := by
    funext X
    exact
      (skewAdjointPadicCayleySourceDifferentialDensityENNReal_adjoint
        p n F hF hdet g X).symm
  change Measure.map e (μ.withDensity d) = μ.withDensity d
  calc
    Measure.map e (μ.withDensity d) =
        Measure.map e (μ.withDensity (d ∘ e)) := by
      exact congrArg (Measure.map e)
        (congrArg (Measure.withDensity μ) hfun)
    _ = (Measure.map e μ).withDensity d :=
      PositiveDefiniteIntegralLattice.map_withDensity_comp_of_measurable
        e μ d e.continuous.measurable hd
    _ = μ.withDensity d := by
      rw [
        map_skewAdjointPadicCayleySourceCoordinateSubtypeMeasure_specialOrthogonalAdjoint
          p n F hF hdet g]

end Matrix
