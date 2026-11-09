import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarModulus
import SMSFormula.SpecialOrthogonalRealIdentityTangentMeasure

/-!
# Real tangent Haar transport for an anisotropic presentation

The rational skew-adjoint presentation equivalence is extended to the native
real tangent carriers.  Its action on the fixed scalar-extended rational bases
is computed literally, so the standard basis-Haar change-of-variables theorem
gives the exact reciprocal archimedean norm of the rational presentation
modulus.

This file compares only the additive tangent measures.  It does not
identify the derivative of the nonlinear `GSpin` presentation map, the glued
real group Haar scalar, or any finite-adelic cylinder measure.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped Matrix Matrix.Norms.Operator ENNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance blockRealSkewAdjointMeasurableSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance blockRealSkewAdjointBorelSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance ambientRealSkewAdjointMeasurableSpace :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance ambientRealSkewAdjointBorelSpace :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- Scalar extension of the rational presentation tangent equivalence to the
native real skew-adjoint carriers. -/
def blockToAmbientRealSkewAdjointLinearEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule ≃ₗ[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  (skewAdjointScalarExtensionEquiv (K := ℝ)
      (P.blockSpace hx).pairingMatrix).symm ≪≫ₗ
    LinearEquiv.baseChange ℚ ℝ _ _
      (P.blockToAmbientSkewAdjointLinearEquiv hx) ≪≫ₗ
    skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix

/-- The real scalar extension is a continuous linear equivalence on the
existing finite-dimensional coordinate topologies. -/
def blockToAmbientRealSkewAdjointContinuousLinearEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  (P.blockToAmbientRealSkewAdjointLinearEquiv hx).toContinuousLinearEquiv

/-- On scalar-extended rational tangent vectors, the real presentation map is
literally the scalar extension of the rational presentation map. -/
@[simp]
theorem blockToAmbientRealSkewAdjointLinearEquiv_scalarExtension
    (hx : V.nativeRationalQuadraticForm x ≠ 0) (a : ℝ)
    (X : skewAdjointMatricesLieSubalgebra (P.blockSpace hx).pairingMatrix) :
    P.blockToAmbientRealSkewAdjointLinearEquiv hx
        (skewAdjointScalarExtensionEquiv (K := ℝ)
          (P.blockSpace hx).pairingMatrix (a ⊗ₜ[ℚ] X)) =
      skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
        (a ⊗ₜ[ℚ] P.blockToAmbientSkewAdjointLinearEquiv hx X) := by
  change skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
      (LinearEquiv.baseChange ℚ ℝ _ _
        (P.blockToAmbientSkewAdjointLinearEquiv hx)
        ((skewAdjointScalarExtensionEquiv (K := ℝ)
          (P.blockSpace hx).pairingMatrix).symm
          (skewAdjointScalarExtensionEquiv (K := ℝ)
            (P.blockSpace hx).pairingMatrix (a ⊗ₜ[ℚ] X)))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul]

/-- The fixed block real tangent basis, reindexed by the forced equality with
the ambient tangent dimension. -/
def blockToAmbientRealSkewAdjointSourceBasis
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Module.Basis
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra V.pairingMatrix)))
      ℝ
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  (skewAdjointScalarExtensionFinBasis (K := ℝ)
      (P.blockSpace hx).pairingMatrix).reindex
    (Fin.castOrderIso
      (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq)

/-- Mapping the reindexed block real basis gives the scalar extension of the
rationally transported presentation basis. -/
theorem blockToAmbientRealSkewAdjointSourceBasis_map
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockToAmbientRealSkewAdjointSourceBasis hx).map
        (P.blockToAmbientRealSkewAdjointLinearEquiv hx) =
      skewAdjointScalarExtensionBasis (K := ℝ) V.pairingMatrix
        (P.blockToAmbientSkewAdjointTransportedFinBasis hx) := by
  apply DFunLike.ext _ _
  intro i
  have hsource :
      P.blockToAmbientRealSkewAdjointSourceBasis hx i =
        skewAdjointScalarExtensionEquiv (K := ℝ)
          (P.blockSpace hx).pairingMatrix
          (1 ⊗ₜ[ℚ] Matrix.skewAdjointFinBasis
            (P.blockSpace hx).pairingMatrix
            ((Fin.castOrderIso
              (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq).symm i)) := by
    calc
      P.blockToAmbientRealSkewAdjointSourceBasis hx i =
          skewAdjointScalarExtensionFinBasis (K := ℝ)
            (P.blockSpace hx).pairingMatrix
            ((Fin.castOrderIso
              (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq).symm i) :=
        Module.Basis.reindex_apply _ _ _
      _ = _ := by
        apply Subtype.ext
        rw [skewAdjointScalarExtensionFinBasis,
          coe_skewAdjointScalarExtensionBasis_apply,
          coe_skewAdjointScalarExtensionEquiv_tmul]
        simp
  rw [Module.Basis.map_apply, hsource,
    P.blockToAmbientRealSkewAdjointLinearEquiv_scalarExtension hx]
  calc
    skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
        (1 ⊗ₜ[ℚ]
          P.blockToAmbientSkewAdjointLinearEquiv hx
            (Matrix.skewAdjointFinBasis (P.blockSpace hx).pairingMatrix
              ((Fin.castOrderIso
                (P.blockToAmbientSkewAdjointLinearEquiv hx).finrank_eq).symm i))) =
      skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
        (1 ⊗ₜ[ℚ] P.blockToAmbientSkewAdjointTransportedFinBasis hx i) := by
          congr 2
          simp only [blockToAmbientSkewAdjointTransportedFinBasis,
            Module.Basis.reindex_apply, Module.Basis.map_apply]
          congr 1
    _ = skewAdjointScalarExtensionBasis (K := ℝ) V.pairingMatrix
        (P.blockToAmbientSkewAdjointTransportedFinBasis hx) i := by
          apply Subtype.ext
          rw [coe_skewAdjointScalarExtensionEquiv_tmul,
            coe_skewAdjointScalarExtensionBasis_apply]
          simp

/-- The real determinant of the scalar-extended tangent presentation is the
literal real image of the rational presentation modulus. -/
theorem blockToAmbientRealSkewAdjointDet_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (skewAdjointScalarExtensionFinBasis (K := ℝ) V.pairingMatrix).det
        ((P.blockToAmbientRealSkewAdjointSourceBasis hx).map
          (P.blockToAmbientRealSkewAdjointLinearEquiv hx)) =
      (P.blockToAmbientSkewAdjointDetScalar hx : ℝ) := by
  rw [P.blockToAmbientRealSkewAdjointSourceBasis_map hx]
  rw [blockToAmbientSkewAdjointDetScalar]
  have hpoint (j : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra V.pairingMatrix))) :
      skewAdjointScalarExtensionBasis (K := ℝ) V.pairingMatrix
          (P.blockToAmbientSkewAdjointTransportedFinBasis hx) j =
        skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
          (1 ⊗ₜ[ℚ] P.blockToAmbientSkewAdjointTransportedFinBasis hx j) := by
    apply Subtype.ext
    rw [coe_skewAdjointScalarExtensionBasis_apply (Q := ℚ) (K := ℝ),
      coe_skewAdjointScalarExtensionEquiv_tmul (Q := ℚ) (K := ℝ)]
    simp
  have hdet := skewAdjointScalarExtensionBasis_det_apply (Q := ℚ) (K := ℝ)
      V.pairingMatrix
      (Matrix.skewAdjointFinBasis V.pairingMatrix)
      (P.blockToAmbientSkewAdjointTransportedFinBasis hx)
  change (skewAdjointScalarExtensionFinBasis (K := ℝ) V.pairingMatrix).det
      (fun j => skewAdjointScalarExtensionBasis (K := ℝ) V.pairingMatrix
        (P.blockToAmbientSkewAdjointTransportedFinBasis hx) j) = _
  rw [show
    (fun j => skewAdjointScalarExtensionBasis (K := ℝ) V.pairingMatrix
      (P.blockToAmbientSkewAdjointTransportedFinBasis hx) j) =
    (fun j => skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
      (1 ⊗ₜ[ℚ] P.blockToAmbientSkewAdjointTransportedFinBasis hx j)) by
      funext j
      exact hpoint j]
  exact hdet

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-extended presentation transports the fixed additive real
tangent Haar measure by the reciprocal real norm of the rational modulus. -/
theorem map_blockToAmbientRealSkewAdjointBasisHaarMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure.map (P.blockToAmbientRealSkewAdjointContinuousLinearEquiv hx)
        (Matrix.skewAdjointRealBasisHaarMeasure
          (P.blockSpace hx).pairingMatrix) =
      (Real.toNNReal
        |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)|)⁻¹ •
        Matrix.skewAdjointRealBasisHaarMeasure V.pairingMatrix := by
  letI : MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
    borel _
  letI : BorelSpace
      (skewAdjointMatricesLieSubalgebra
        ((P.blockSpace hx).pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
    ⟨rfl⟩
  letI : MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
    borel _
  letI : BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
    ⟨rfl⟩
  rw [Matrix.skewAdjointRealBasisHaarMeasure,
    Matrix.skewAdjointRealBasisHaarMeasure]
  calc
    Measure.map (P.blockToAmbientRealSkewAdjointContinuousLinearEquiv hx)
        (skewAdjointScalarExtensionFinBasis (K := ℝ)
          (P.blockSpace hx).pairingMatrix).addHaar =
      Measure.map (P.blockToAmbientRealSkewAdjointContinuousLinearEquiv hx)
        (P.blockToAmbientRealSkewAdjointSourceBasis hx).addHaar := by
          rw [blockToAmbientRealSkewAdjointSourceBasis,
            Module.Basis.addHaar_reindex]
    _ = _ := by
      have hmap :=
        Module.Basis.map_addHaar_eq_inv_abs_det_map_smul
          (P.blockToAmbientRealSkewAdjointSourceBasis hx)
          (skewAdjointScalarExtensionFinBasis (K := ℝ) V.pairingMatrix)
          (P.blockToAmbientRealSkewAdjointContinuousLinearEquiv hx)
      change Measure.map
          (P.blockToAmbientRealSkewAdjointContinuousLinearEquiv hx)
          (P.blockToAmbientRealSkewAdjointSourceBasis hx).addHaar =
        (Real.toNNReal
          |(skewAdjointScalarExtensionFinBasis (K := ℝ) V.pairingMatrix).det
            ((P.blockToAmbientRealSkewAdjointSourceBasis hx).map
              (P.blockToAmbientRealSkewAdjointLinearEquiv hx))|)⁻¹ •
          (skewAdjointScalarExtensionFinBasis (K := ℝ)
            V.pairingMatrix).addHaar at hmap
      rw [P.blockToAmbientRealSkewAdjointDet_apply hx] at hmap
      exact hmap

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
