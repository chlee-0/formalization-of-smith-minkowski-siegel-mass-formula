import SMSFormula.SkewAdjointPadicMeasureDilation

/-!
# Integral-diagonal-integral p-adic coordinate transport

An integral coordinate automorphism, a signed p-power diagonal dilation, and
a second integral coordinate automorphism scale the normalized skew-adjoint
coordinate Haar measure by the inverse determinant norm. The integral factors
have determinant norm one, so the scale is the diagonal factor
`p ^ (∑ i, z i)`.

This file proves transport for supplied factors. It does not assert a Cartan
or Smith decomposition for an arbitrary element of `GL_d(Q_p)`, and it does
not construct an orthogonal-group measure.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal BigOperators Matrix.Norms.Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance padicCartanSkewMeasurableSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCartanSkewBorelSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

private theorem map_continuousLinearEquiv_trans
    {K X : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup X] [NormedSpace K X]
    [MeasurableSpace X] [BorelSpace X]
    (e f : X ≃L[K] X) (μ : Measure X) :
    Measure.map (e.trans f) μ = Measure.map f (Measure.map e μ) := by
  rw [Measure.map_map f.continuous.measurable e.continuous.measurable]
  rfl

private theorem norm_det_continuousLinearEquiv_trans
    {K X : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup X] [NormedSpace K X] [FiniteDimensional K X]
    (e f : X ≃L[K] X) :
    ‖LinearMap.det (e.trans f).toLinearMap‖ =
      ‖LinearMap.det e.toLinearMap‖ * ‖LinearMap.det f.toLinearMap‖ := by
  change ‖LinearMap.det (f.toLinearMap.comp e.toLinearMap)‖ = _
  rw [LinearMap.det_comp, norm_mul, mul_comm]

/-- Apply `U`, then the signed p-power diagonal coordinate change, then `V`,
all conjugated to the transported p-adic skew-adjoint model. -/
def skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p])
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ)
    (V : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p]) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ((skewAdjointPadicIntegralCoordinateAutomorphism F p U).trans
    (skewAdjointPadicSignedDiagonalDilation F p z)).trans
      (skewAdjointPadicIntegralCoordinateAutomorphism F p V)

private theorem skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism_eq
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p])
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ)
    (V : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p]) :
    skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism F p U z V =
      ((skewAdjointPadicIntegralCoordinateAutomorphism F p U).trans
        (skewAdjointPadicSignedDiagonalDilation F p z)).trans
          (skewAdjointPadicIntegralCoordinateAutomorphism F p V) :=
  rfl

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
theorem map_skewAdjointPadicCoordinateMeasure_integralDiagonalIntegralCoordinateAutomorphism
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U V : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p])
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ) :
    Measure.map
        (skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism
          F p U z V)
        (skewAdjointPadicCoordinateMeasure F p) =
      (p : ℝ≥0) ^ (∑ i, z i) •
        skewAdjointPadicCoordinateMeasure F p := by
  let A := skewAdjointPadicIntegralCoordinateAutomorphism F p U
  let D := skewAdjointPadicSignedDiagonalDilation F p z
  let B := skewAdjointPadicIntegralCoordinateAutomorphism F p V
  let μ := skewAdjointPadicCoordinateMeasure F p
  calc
    Measure.map
        (skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism
          F p U z V) μ =
        Measure.map B (Measure.map (A.trans D) μ) := by
      rw [skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism_eq]
      exact map_continuousLinearEquiv_trans (A.trans D) B μ
    _ = Measure.map B (Measure.map D (Measure.map A μ)) :=
      congrArg (Measure.map B) (map_continuousLinearEquiv_trans A D μ)
    _ = Measure.map B (Measure.map D μ) := by
      rw [show Measure.map A μ = μ by
        exact
          map_skewAdjointPadicCoordinateMeasure_integralCoordinateAutomorphism
            F p U]
    _ = Measure.map B
        ((p : ℝ≥0) ^ (∑ i, z i) • μ) := by
      rw [show Measure.map D μ = (p : ℝ≥0) ^ (∑ i, z i) • μ by
        exact map_skewAdjointPadicCoordinateMeasure_signedDiagonalDilation
          F p z]
    _ = (p : ℝ≥0) ^ (∑ i, z i) • Measure.map B μ :=
      Measure.map_smul _ _ _
    _ = (p : ℝ≥0) ^ (∑ i, z i) • μ := by
      rw [show Measure.map B μ = μ by
        exact
          map_skewAdjointPadicCoordinateMeasure_integralCoordinateAutomorphism
            F p V]
    _ = (p : ℝ≥0) ^ (∑ i, z i) •
        skewAdjointPadicCoordinateMeasure F p := rfl

theorem skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism_det_norm
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U V : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p])
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ) :
    ‖LinearMap.det
      (skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism
        F p U z V).toLinearMap‖ =
      (p : ℝ) ^ (-(∑ i, z i)) := by
  let A := skewAdjointPadicIntegralCoordinateAutomorphism F p U
  let D := skewAdjointPadicSignedDiagonalDilation F p z
  let B := skewAdjointPadicIntegralCoordinateAutomorphism F p V
  calc
    ‖LinearMap.det
      (skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism
        F p U z V).toLinearMap‖ =
        ‖LinearMap.det (A.trans D).toLinearMap‖ *
          ‖LinearMap.det B.toLinearMap‖ := by
      rw [skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism_eq]
      exact norm_det_continuousLinearEquiv_trans (A.trans D) B
    _ = (‖LinearMap.det A.toLinearMap‖ *
        ‖LinearMap.det D.toLinearMap‖) *
          ‖LinearMap.det B.toLinearMap‖ :=
      congrArg (fun r : ℝ => r * ‖LinearMap.det B.toLinearMap‖)
        (norm_det_continuousLinearEquiv_trans A D)
    _ = (p : ℝ) ^ (-(∑ i, z i)) := by
      rw [show ‖LinearMap.det A.toLinearMap‖ = 1 by
        exact skewAdjointPadicIntegralCoordinateAutomorphism_det_norm F p U]
      rw [show ‖LinearMap.det D.toLinearMap‖ =
          (p : ℝ) ^ (-(∑ i, z i)) by
        exact skewAdjointPadicSignedDiagonalDilation_det_norm F p z]
      rw [show ‖LinearMap.det B.toLinearMap‖ = 1 by
        exact skewAdjointPadicIntegralCoordinateAutomorphism_det_norm F p V]
      simp

theorem skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism_inv_nnnorm_det
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U V : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p])
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ) :
    ‖LinearMap.det
      (skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism
        F p U z V).toLinearMap‖₊⁻¹ =
      (p : ℝ≥0) ^ (∑ i, z i) := by
  apply NNReal.eq
  rw [NNReal.coe_inv, coe_nnnorm,
    skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism_det_norm]
  simp [zpow_neg]

theorem map_skewAdjointPadicCoordinateMeasure_integralDiagonalIntegralCoordinateAutomorphism_det
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U V : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p])
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ) :
    Measure.map
        (skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism
          F p U z V)
        (skewAdjointPadicCoordinateMeasure F p) =
      ‖LinearMap.det
        (skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism
          F p U z V).toLinearMap‖₊⁻¹ •
        skewAdjointPadicCoordinateMeasure F p := by
  rw [
    skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism_inv_nnnorm_det]
  exact
    map_skewAdjointPadicCoordinateMeasure_integralDiagonalIntegralCoordinateAutomorphism
      F p U V z

end Matrix
