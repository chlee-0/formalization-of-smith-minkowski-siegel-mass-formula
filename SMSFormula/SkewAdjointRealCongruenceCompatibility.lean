import SMSFormula.SpecialOrthogonalRealCongruenceChartOverlap

/-!
# Real scalar-extended tangent congruence compatibility

The rational tangent congruence extends to the real skew-adjoint carrier as
the expected ambient matrix conjugation.  The proof checks the fixed
scalar-extension basis and then uses linear extensionality.  This pointwise
bridge is needed before comparing derivatives of cross-form charts.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ContDiff TensorProduct

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Real tangent congruence is the scalar extension of matrix conjugation,
pointwise in ambient matrix coordinates. -/
theorem coe_skewAdjointRealCongruenceContinuousLinearEquiv_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    ((Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W x :
        (skewAdjointMatricesLieSubalgebra
          ((Matrix.skewAdjointCongruenceForm F W).map
            (algebraMap ℚ ℝ))).toSubmodule) :
      Matrix (Fin n) (Fin n) ℝ) =
      (rationalMatrixUnitReal W⁻¹ : Matrix (Fin n) (Fin n) ℝ) *
        (x : Matrix (Fin n) (Fin n) ℝ) *
        (rationalMatrixUnitReal W : Matrix (Fin n) (Fin n) ℝ) := by
  let C :
      Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ)
      (rationalMatrixUnitReal W⁻¹ : Matrix (Fin n) (Fin n) ℝ)
      (rationalMatrixUnitReal W : Matrix (Fin n) (Fin n) ℝ)
  let L :
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
        Matrix (Fin n) (Fin n) ℝ :=
    (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule.subtypeL.comp
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
        F W).toContinuousLinearMap
  let R :
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
        Matrix (Fin n) (Fin n) ℝ :=
    C.comp
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL
  have hLR : L = R := by
    have hlin : L.toLinearMap = R.toLinearMap := by
      apply (Matrix.skewAdjointScalarExtensionFinBasis (K := ℝ) F).ext
      intro i
      change
        ((Matrix.skewAdjointRealCongruenceLinearEquiv F W
          (Matrix.skewAdjointScalarExtensionFinBasis
            (K := ℝ) F i) :
            (skewAdjointMatricesLieSubalgebra
              ((Matrix.skewAdjointCongruenceForm F W).map
                (algebraMap ℚ ℝ))).toSubmodule) :
          Matrix (Fin n) (Fin n) ℝ) =
        C (Matrix.skewAdjointScalarExtensionFinBasis (K := ℝ) F i)
      simp only [Matrix.skewAdjointRealCongruenceLinearEquiv,
        Matrix.skewAdjointScalarExtensionFinBasis,
        Matrix.skewAdjointScalarExtensionBasis,
        Module.Basis.map_apply, Module.Basis.baseChange_apply,
        LinearEquiv.trans_apply]
      let t : ℝ ⊗[ℚ] (skewAdjointMatricesLieSubalgebra F) :=
        (1 : ℝ) ⊗ₜ[ℚ] Matrix.skewAdjointFinBasis F i
      have hcancel :
          (Matrix.skewAdjointScalarExtensionEquiv (K := ℝ) F).symm
              (Matrix.skewAdjointScalarExtensionEquiv (K := ℝ) F t) = t :=
        (Matrix.skewAdjointScalarExtensionEquiv
          (K := ℝ) F).symm_apply_apply t
      have hbase := congrArg
        (LinearEquiv.baseChange ℚ ℝ _
          (skewAdjointMatricesLieSubalgebra
            (Matrix.skewAdjointCongruenceForm F W))
          (Matrix.skewAdjointCongruenceLinearEquiv F W)) hcancel
      dsimp [t] at hbase
      have hout := congrArg
        (fun z =>
          ((Matrix.skewAdjointScalarExtensionEquiv (K := ℝ)
            (Matrix.skewAdjointCongruenceForm F W) z :
              (skewAdjointMatricesLieSubalgebra
                ((Matrix.skewAdjointCongruenceForm F W).map
                  (algebraMap ℚ ℝ))).toSubmodule) :
            Matrix (Fin n) (Fin n) ℝ)) hbase
      calc
        _ = ((Matrix.skewAdjointScalarExtensionEquiv (K := ℝ)
              (Matrix.skewAdjointCongruenceForm F W)
                ((LinearEquiv.baseChange ℚ ℝ _
                  (skewAdjointMatricesLieSubalgebra
                    (Matrix.skewAdjointCongruenceForm F W))
                  (Matrix.skewAdjointCongruenceLinearEquiv F W))
                    ((1 : ℝ) ⊗ₜ[ℚ] Matrix.skewAdjointFinBasis F i)) :
                (skewAdjointMatricesLieSubalgebra
                  ((Matrix.skewAdjointCongruenceForm F W).map
                    (algebraMap ℚ ℝ))).toSubmodule) :
              Matrix (Fin n) (Fin n) ℝ) := hout
        _ = _ := by
          rw [LinearEquiv.baseChange_tmul,
            Matrix.coe_skewAdjointScalarExtensionEquiv_tmul,
            Matrix.coe_skewAdjointCongruenceLinearEquiv_apply,
            Matrix.coe_skewAdjointScalarExtensionEquiv_tmul]
          simp [C] <;> rfl
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun hlin y
  change L x = R x
  exact DFunLike.congr_fun hLR x

end PositiveDefiniteIntegralLattice
