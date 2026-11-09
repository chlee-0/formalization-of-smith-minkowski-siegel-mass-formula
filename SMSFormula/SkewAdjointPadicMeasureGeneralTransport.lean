import SMSFormula.PadicMatrixIntegralDiagonalIntegralFactorization
import SMSFormula.SkewAdjointPadicMeasureCartan

/-!
# Arbitrary p-adic coordinate transport

Every `Q_p` coordinate automorphism is identified with an
integral--signed-diagonal--integral automorphism by the matrix
decomposition. The normalized skew-adjoint coordinate Haar measure therefore
transforms by the inverse norm of the linear determinant.

No p-adic orthogonal-group chart or stabilizer gauge volume is constructed.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal Matrix.Norms.Operator

namespace Matrix

variable {d : ℕ}

/-- The continuous `Q_p`-linear coordinate automorphism represented by a
general-linear matrix. -/
def padicCoordinateAutomorphism (p : ℕ) [Fact (Nat.Prime p)]
    (W : GL (Fin d) ℚ_[p]) :
    (Fin d → ℚ_[p]) ≃L[ℚ_[p]] (Fin d → ℚ_[p]) :=
  ((GeneralLinearGroup.toLin W).toLinearEquiv).toContinuousLinearEquiv

@[simp]
theorem padicCoordinateAutomorphism_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (W : GL (Fin d) ℚ_[p]) (x : Fin d → ℚ_[p]) :
    padicCoordinateAutomorphism p W x =
      (W : Matrix (Fin d) (Fin d) ℚ_[p]).mulVec x := by
  simp [padicCoordinateAutomorphism]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance skewAdjointPadicGeneralTransportMeasurableSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicGeneralTransportBorelSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- An arbitrary coordinate automorphism conjugated to the transported
p-adic skew-adjoint model. -/
def skewAdjointPadicCoordinateAutomorphism
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (W : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℚ_[p]) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ((skewAdjointPadicCoordinateEquiv F p).trans
    (padicCoordinateAutomorphism p W)).trans
      (skewAdjointPadicCoordinateEquiv F p).symm

theorem skewAdjointPadicCoordinateAutomorphism_coordinate_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (W : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℚ_[p])
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCoordinateEquiv F p
        (skewAdjointPadicCoordinateAutomorphism F p W x) =
      (W : Matrix _ _ ℚ_[p]).mulVec
        (skewAdjointPadicCoordinateEquiv F p x) := by
  simp [skewAdjointPadicCoordinateAutomorphism,
    padicCoordinateAutomorphism]

theorem skewAdjointPadicIntegralCoordinateAutomorphism_coordinate_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (U : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℤ_[p])
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCoordinateEquiv F p
        (skewAdjointPadicIntegralCoordinateAutomorphism F p U x) =
      (GeneralLinearGroup.map PadicInt.Coe.ringHom U :
        Matrix _ _ ℚ_[p]).mulVec
        (skewAdjointPadicCoordinateEquiv F p x) := by
  simp [skewAdjointPadicIntegralCoordinateAutomorphism,
    padicIntegralCoordinateAutomorphism]

set_option maxRecDepth 2048

/-- A factorization package identifies the arbitrary coordinate
automorphism with the composed automorphism. The package's right
factor is applied first. -/
theorem skewAdjointPadicCoordinateAutomorphism_eq_of_factorization
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (W : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℚ_[p])
    (D : PadicIntegralDiagonalIntegralFactorization p
      (W : Matrix _ _ ℚ_[p])) :
    skewAdjointPadicCoordinateAutomorphism F p W =
      skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism
        F p D.right D.exponents D.left := by
  apply ContinuousLinearEquiv.ext
  funext x
  apply (skewAdjointPadicCoordinateEquiv F p).injective
  funext j
  rw [skewAdjointPadicCoordinateAutomorphism_coordinate_apply]
  let c := skewAdjointPadicCoordinateEquiv F p x
  calc
    ((W : Matrix _ _ ℚ_[p]).mulVec c) j =
        (((GeneralLinearGroup.map PadicInt.Coe.ringHom D.left :
            Matrix _ _ ℚ_[p]) *
          padicSignedPrimePowerDiagonalMatrix p D.exponents *
          (GeneralLinearGroup.map PadicInt.Coe.ringHom D.right :
            Matrix _ _ ℚ_[p])).mulVec c) j := by
      exact congrArg (fun y => y j)
        (congrArg (fun M : Matrix _ _ ℚ_[p] => M.mulVec c) D.matrix_eq)
    _ =
        skewAdjointPadicCoordinateEquiv F p
          (skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism
            F p D.right D.exponents D.left x) j := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [skewAdjointPadicIntegralDiagonalIntegralCoordinateAutomorphism]
      change _ =
        skewAdjointPadicCoordinateEquiv F p
          (skewAdjointPadicIntegralCoordinateAutomorphism F p D.left
            (skewAdjointPadicSignedDiagonalDilation F p D.exponents
              (skewAdjointPadicIntegralCoordinateAutomorphism
                F p D.right x))) j
      rw [skewAdjointPadicIntegralCoordinateAutomorphism_coordinate_apply]
      have hdiag :
          skewAdjointPadicCoordinateEquiv F p
              (skewAdjointPadicSignedDiagonalDilation F p D.exponents
                (skewAdjointPadicIntegralCoordinateAutomorphism
                  F p D.right x)) =
            (padicSignedPrimePowerDiagonalMatrix p D.exponents).mulVec
              ((GeneralLinearGroup.map PadicInt.Coe.ringHom D.right :
                Matrix _ _ ℚ_[p]).mulVec c) := by
        funext k
        rw [skewAdjointPadicSignedDiagonalDilation_coordinate_apply,
          skewAdjointPadicIntegralCoordinateAutomorphism_coordinate_apply]
        simp [c, padicSignedPrimePowerDiagonalMatrix,
          Matrix.mulVec_diagonal]
      rw [hdiag]

/-- Arbitrary transported p-adic skew-adjoint coordinate changes scale the
normalized coordinate Haar measure by the inverse determinant norm. -/
theorem map_skewAdjointPadicCoordinateMeasure_coordinateAutomorphism_det
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (W : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℚ_[p]) :
    Measure.map (skewAdjointPadicCoordinateAutomorphism F p W)
        (skewAdjointPadicCoordinateMeasure F p) =
      ‖LinearMap.det
        (skewAdjointPadicCoordinateAutomorphism F p W).toLinearMap‖₊⁻¹ •
        skewAdjointPadicCoordinateMeasure F p := by
  have hW :
      IsUnit (W : Matrix
        (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
        (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℚ_[p]) :=
    Units.isUnit W
  obtain ⟨D⟩ :=
    PadicIntegralDiagonalIntegralFactorization.nonempty_of_isUnit
      (d := Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) p
      (W : Matrix
        (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
        (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℚ_[p])
      hW
  rw [skewAdjointPadicCoordinateAutomorphism_eq_of_factorization F p W D]
  exact
    map_skewAdjointPadicCoordinateMeasure_integralDiagonalIntegralCoordinateAutomorphism_det
      F p D.right D.left D.exponents

/-- Every continuous linear equivalence of the transported p-adic
skew-adjoint carrier scales its fixed coordinate Haar measure by the inverse
norm of its linear determinant. -/
theorem map_skewAdjointPadicCoordinateMeasure_continuousLinearEquiv_det
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (A :
      (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    Measure.map A (skewAdjointPadicCoordinateMeasure F p) =
      ‖LinearMap.det A.toLinearMap‖₊⁻¹ •
        skewAdjointPadicCoordinateMeasure F p := by
  let e := skewAdjointPadicCoordinateEquiv F p
  let C : (Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra F)) → ℚ_[p]) ≃L[ℚ_[p]]
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra F)) → ℚ_[p]) :=
    (e.symm.trans A).trans e
  let M : Matrix
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℚ_[p] :=
    LinearMap.toMatrix' C.toLinearEquiv.toLinearMap
  have hCdet : LinearMap.det C.toLinearEquiv.toLinearMap ≠ 0 := by
    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  have hMdet : M.det ≠ 0 := by
    simpa [M, LinearMap.det_toMatrix'] using hCdet
  let W : GL
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) ℚ_[p] :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet
  have hauto :
      skewAdjointPadicCoordinateAutomorphism F p W = A := by
    apply ContinuousLinearEquiv.ext
    funext Y
    apply e.injective
    rw [skewAdjointPadicCoordinateAutomorphism_coordinate_apply]
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    simp [M, C, e]
  have hmap :=
    map_skewAdjointPadicCoordinateMeasure_coordinateAutomorphism_det
      F p W
  rw [hauto] at hmap
  exact hmap

end Matrix
