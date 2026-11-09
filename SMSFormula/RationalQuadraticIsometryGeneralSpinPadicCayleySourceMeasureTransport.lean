import SMSFormula.MeasureSubtypeHomeomorphTransport
import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCayleyDensityTransport
import SMSFormula.PadicCayleyTargetChartMeasureFullSupport

/-!
# P-adic Cayley source measures across anisotropic presentations

The exact presentation source homeomorphism transports the fixed coordinate
measure by the already computed reciprocal local tangent modulus.  Pointwise
covariance of the nonlinear Cayley density then gives the same formula for the
actual Cayley differential source measure.  No selected Spin chart, group
Haar, or finite-adelic cylinder is transported here.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal TensorProduct

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {m : ℕ}
variable {V : RationalQuadraticSpaceMatrix (m + 1)} {x : Fin (m + 1) → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance blockPadicCayleySourceMeasureMeasurableSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance blockPadicCayleySourceMeasureBorelSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance ambientPadicCayleySourceMeasureMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance ambientPadicCayleySourceMeasureBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The source homeomorphism has the ambient presentation tangent map as its
underlying function.  This compact equality is kept opaque for the subsequent
measure specialization. -/
theorem blockToAmbientPadicCayleySourceHomeomorph_val
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Subtype.val ∘ P.blockToAmbientPadicCayleySourceHomeomorph hx p =
      P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p ∘ Subtype.val := by
  funext X
  exact P.blockToAmbientPadicCayleySourceHomeomorph_apply hx p X

/-- The exact p-adic Cayley source-coordinate measure transforms by the
reciprocal local norm of the rational presentation tangent determinant. -/
theorem map_blockToAmbientPadicCayleySourceCoordinateSubtypeMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map (P.blockToAmbientPadicCayleySourceHomeomorph hx p)
        (Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
          p (m + 1) (P.blockSpace hx).pairingMatrix) =
      ‖algebraMap ℚ ℚ_[p]
          (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹ •
        Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
          p (m + 1) V.pairingMatrix := by
  apply Measure.map_comap_subtype_of_map_smul_of_mem_iff
    (Matrix.isOpen_skewAdjointPadicCayleySource
      (P.blockSpace hx).pairingMatrix p).measurableSet
    (Matrix.isOpen_skewAdjointPadicCayleySource V.pairingMatrix p).measurableSet
    (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p)
    (P.blockToAmbientPadicSkewAdjointContinuousLinearEquiv hx p).continuous.measurable
    (P.blockToAmbientPadicCayleySourceHomeomorph hx p).toMeasurableEquiv
    (P.blockToAmbientPadicCayleySourceHomeomorph_val hx p)
    (Matrix.skewAdjointPadicCoordinateMeasure (P.blockSpace hx).pairingMatrix p)
    (Matrix.skewAdjointPadicCoordinateMeasure V.pairingMatrix p)
    ‖algebraMap ℚ ℚ_[p] (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹
    (P.map_blockToAmbientPadicSkewAdjointCoordinateMeasure hx p)
  intro X
  exact P.blockToAmbientPadicCayleySource_iff hx p X

/-- The reciprocal-Jacobian p-adic Cayley differential source measure has the
same reciprocal local presentation modulus as the fixed additive tangent
measure. -/
theorem map_blockToAmbientPadicCayleySourceDifferentialSubtypeMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map (P.blockToAmbientPadicCayleySourceHomeomorph hx p)
        (Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
          p (m + 1) (P.blockSpace hx).pairingMatrix) =
      ‖algebraMap ℚ ℚ_[p]
          (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹ •
        Matrix.skewAdjointPadicCayleySourceDifferentialSubtypeMeasure
          p (m + 1) V.pairingMatrix := by
  let e := P.blockToAmbientPadicCayleySourceHomeomorph hx p
  let μ := Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
    p (m + 1) (P.blockSpace hx).pairingMatrix
  let ν := Matrix.skewAdjointPadicCayleySourceCoordinateSubtypeMeasure
    p (m + 1) V.pairingMatrix
  let dₛ := Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
    p (m + 1) (P.blockSpace hx).pairingMatrix
  let dₜ := Matrix.skewAdjointPadicCayleySourceDifferentialDensityENNReal
    p (m + 1) V.pairingMatrix
  let c := ‖algebraMap ℚ ℚ_[p]
    (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹
  have hdₜ : Measurable dₜ :=
    Matrix.measurable_skewAdjointPadicCayleySourceDifferentialDensityENNReal
      p (m + 1) V.pairingMatrix
  have hdensity : dₛ = dₜ ∘ e := by
    funext X
    exact (P.blockToAmbientPadicCayleySourceDifferentialDensityENNReal
      hx p X).symm
  change Measure.map e (μ.withDensity dₛ) = c • ν.withDensity dₜ
  calc
    Measure.map e (μ.withDensity dₛ) =
        Measure.map e (μ.withDensity (dₜ ∘ e)) := by rw [hdensity]
    _ = (Measure.map e μ).withDensity dₜ :=
      PositiveDefiniteIntegralLattice.map_withDensity_comp_of_measurable
        e μ dₜ e.measurable hdₜ
    _ = (c • ν).withDensity dₜ := by
      rw [P.map_blockToAmbientPadicCayleySourceCoordinateSubtypeMeasure hx p]
    _ = c • ν.withDensity dₜ := by
      ext s hs
      rw [withDensity_apply _ hs, Measure.coe_nnreal_smul_apply,
        withDensity_apply _ hs, Measure.restrict_smul,
        lintegral_smul_measure]
      rfl

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
