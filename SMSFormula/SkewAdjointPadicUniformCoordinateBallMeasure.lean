import SMSFormula.SkewAdjointPadicMeasureGeneralTransport
import SMSFormula.PadicCayleyTranslatedChartOverlapBasicBallMeasure

/-!
# Haar mass of uniform transported skew-adjoint coordinate balls

Uniform multiplication by `p ^ k` on the transported p-adic skew-adjoint
carrier has determinant `(p ^ k) ^ d`, where `d` is the fixed rational
skew-adjoint rank.  Applying the intrinsic determinant transport theorem to
the volume-one coordinate lattice gives the exact mass `p ^ (-k d)` of its
image.  Additive translation invariance gives the same mass to every
translated uniform coordinate ball.

No orthogonal-group measure, stabilizer normalization, or reference Haar
comparison occurs here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance padicUniformCoordinateBallMeasureMeasurableSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicUniformCoordinateBallMeasureBorelSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- Uniform multiplication by `p ^ k` has determinant `p ^ (k d)` on the
transported skew-adjoint carrier of rational rank `d`. -/
theorem skewAdjointPadicUniformCoordinateDilation_det
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    LinearMap.det
        (skewAdjointPadicUniformCoordinateDilation F p k).toLinearMap =
      (p : ℚ_[p]) ^
        (k * Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) := by
  change LinearMap.det
      (((p : ℚ_[p]) ^ k) •
        (LinearMap.id :
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule →ₗ[ℚ_[p]]
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)) = _
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one,
    finrank_skewAdjointScalarExtension_padic F p, pow_mul]

/-- The nonnegative determinant norm of uniform multiplication by `p ^ k` is
the reciprocal of `p ^ (k d)`. -/
theorem skewAdjointPadicUniformCoordinateDilation_det_nnnorm
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    ‖LinearMap.det
        (skewAdjointPadicUniformCoordinateDilation F p k).toLinearMap‖₊ =
      ((p : ℝ≥0) ^
        (k * Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))⁻¹ := by
  apply NNReal.eq
  rw [coe_nnnorm, skewAdjointPadicUniformCoordinateDilation_det,
    Padic.norm_p_pow, NNReal.coe_inv, NNReal.coe_pow]
  let d := Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)
  calc
    (p : ℝ) ^ (-((k * d : ℕ) : ℤ)) =
        ((p : ℝ) ^ ((k * d : ℕ) : ℤ))⁻¹ :=
      _root_.zpow_neg (p : ℝ) ((k * d : ℕ) : ℤ)
    _ = ((p : ℝ) ^ (k * d))⁻¹ := by rw [_root_.zpow_natCast]

/-- Uniform multiplication by `p ^ k` pushes the fixed coordinate Haar
measure forward by the scalar `p ^ (k d)`. -/
theorem map_skewAdjointPadicCoordinateMeasure_uniformCoordinateDilation
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    Measure.map (skewAdjointPadicUniformCoordinateDilation F p k)
        (skewAdjointPadicCoordinateMeasure F p) =
      ((p : ℝ≥0) ^
        (k * Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) •
        skewAdjointPadicCoordinateMeasure F p := by
  rw [map_skewAdjointPadicCoordinateMeasure_continuousLinearEquiv_det,
    skewAdjointPadicUniformCoordinateDilation_det_nnnorm, inv_inv]

/-- The level-`k` zero-centered uniform coordinate ball has mass
`p ^ (-k d)`. -/
theorem skewAdjointPadicCoordinateMeasure_uniformCoordinateBall
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicUniformCoordinateBall F p k) =
      ((p : ℝ≥0∞) ^
        (k * Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))⁻¹ := by
  let μ := skewAdjointPadicCoordinateMeasure F p
  let A := skewAdjointPadicUniformCoordinateDilation F p k
  let C := skewAdjointPadicCoordinateLattice F p
  let q : ℝ≥0 :=
    (p : ℝ≥0) ^
      (k * Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))
  have hmap :
      Measure.map A μ = q • μ := by
    exact map_skewAdjointPadicCoordinateMeasure_uniformCoordinateDilation
      F p k
  have happly := congrArg
    (fun ν : Measure
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule =>
      ν (skewAdjointPadicUniformCoordinateBall F p k))
    hmap
  have hpre :
      A ⁻¹' (skewAdjointPadicUniformCoordinateBall F p k) = (C : Set _) := by
    change A ⁻¹' (A '' (C : Set _)) = (C : Set _)
    exact Set.preimage_image_eq _ A.injective
  change
    (Measure.map A μ) (skewAdjointPadicUniformCoordinateBall F p k) =
      (q • μ) (skewAdjointPadicUniformCoordinateBall F p k) at happly
  rw [Measure.map_apply A.continuous.measurable
      (isClopen_skewAdjointPadicUniformCoordinateBall F p k).2.measurableSet,
    hpre, Measure.smul_apply] at happly
  change
    skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicCoordinateLattice F p) =
      (q : ℝ≥0∞) *
      skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicUniformCoordinateBall F p k) at happly
  rw [skewAdjointPadicCoordinateMeasure_lattice] at happly
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by
    simp [q, (Fact.out : Nat.Prime p).ne_zero]
  have hqtop : (q : ℝ≥0∞) ≠ ⊤ := by simp [q]
  calc
    skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicUniformCoordinateBall F p k) =
        1 * skewAdjointPadicCoordinateMeasure F p
          (skewAdjointPadicUniformCoordinateBall F p k) := by rw [one_mul]
    _ = ((q : ℝ≥0∞)⁻¹ * q) *
        skewAdjointPadicCoordinateMeasure F p
          (skewAdjointPadicUniformCoordinateBall F p k) := by
      rw [ENNReal.inv_mul_cancel hq0 hqtop]
    _ = (q : ℝ≥0∞)⁻¹ *
        ((q : ℝ≥0∞) *
          skewAdjointPadicCoordinateMeasure F p
            (skewAdjointPadicUniformCoordinateBall F p k)) := by
      rw [mul_assoc]
    _ = (q : ℝ≥0∞)⁻¹ := by rw [← happly, mul_one]
    _ = ((p : ℝ≥0∞) ^
        (k * Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))⁻¹ := by
      simp [q]

/-- Every translated level-`k` uniform coordinate ball has the same explicit
mass `p ^ (-k d)`. -/
theorem skewAdjointPadicCoordinateMeasure_translatedUniformCoordinateBall_explicit
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicTranslatedUniformCoordinateBall F p k x) =
      ((p : ℝ≥0∞) ^
        (k * Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))⁻¹ := by
  rw [skewAdjointPadicCoordinateMeasure_translatedUniformCoordinateBall,
    skewAdjointPadicCoordinateMeasure_uniformCoordinateBall]

end Matrix
