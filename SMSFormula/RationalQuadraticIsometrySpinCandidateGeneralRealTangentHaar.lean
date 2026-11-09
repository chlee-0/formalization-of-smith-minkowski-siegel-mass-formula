import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralHaarModulus
import SMSFormula.SpecialOrthogonalRealIdentityTangentMeasure

/-!
# Real tangent Haar transport under an arbitrary rational isometry

The rational skew-adjoint equivalence attached to an arbitrary supplied
quadratic isometry is extended to the existing native real tangent carriers.
Its determinant in the fixed scalar-extended rational bases is exactly the
real image of the rational modulus, so additive Haar transport has the
reciprocal archimedean factor.

No rank identification, local group chart, group Haar measure, integral
structure, raw normalization certificate, quotient measure, or Tamagawa value
is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped Matrix Matrix.Norms.Operator ENNReal

namespace RationalQuadraticSpaceMatrix

variable {r s : ℕ}
variable (U : RationalQuadraticSpaceMatrix r)
variable (V : RationalQuadraticSpaceMatrix s)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

local instance sourceRealSkewAdjointMeasurableSpace :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance sourceRealSkewAdjointBorelSpace :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

local instance targetRealSkewAdjointMeasurableSpace :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance targetRealSkewAdjointBorelSpace :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- Scalar extension of the rational tangent equivalence to the native real
skew-adjoint carriers. -/
def rationalIsometryRealSkewAdjointLinearEquiv :
    (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule ≃ₗ[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  (skewAdjointScalarExtensionEquiv (K := ℝ) U.pairingMatrix).symm ≪≫ₗ
    LinearEquiv.baseChange ℚ ℝ _ _
      (rationalIsometrySkewAdjointLinearEquiv U V e) ≪≫ₗ
    skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix

/-- The scalar-extended tangent map is a continuous linear equivalence for
the existing finite-dimensional topologies. -/
def rationalIsometryRealSkewAdjointContinuousLinearEquiv :
    (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (V.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  (rationalIsometryRealSkewAdjointLinearEquiv U V e).toContinuousLinearEquiv

/-- On scalar-extended rational tangent vectors, the real map is literally
the scalar extension of the rational conjugation map. -/
@[simp]
theorem rationalIsometryRealSkewAdjointLinearEquiv_scalarExtension
    (a : ℝ) (X : skewAdjointMatricesLieSubalgebra U.pairingMatrix) :
    rationalIsometryRealSkewAdjointLinearEquiv U V e
        (skewAdjointScalarExtensionEquiv (K := ℝ) U.pairingMatrix
          (a ⊗ₜ[ℚ] X)) =
      skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
        (a ⊗ₜ[ℚ] rationalIsometrySkewAdjointLinearEquiv U V e X) := by
  change skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
      (LinearEquiv.baseChange ℚ ℝ _ _
        (rationalIsometrySkewAdjointLinearEquiv U V e)
        ((skewAdjointScalarExtensionEquiv (K := ℝ) U.pairingMatrix).symm
          (skewAdjointScalarExtensionEquiv (K := ℝ) U.pairingMatrix
            (a ⊗ₜ[ℚ] X)))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul]

/-- The fixed source real tangent basis, reindexed by the tangent-dimension
equality furnished by the rational tangent equivalence. -/
def rationalIsometryRealSkewAdjointSourceBasis :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra V.pairingMatrix)))
      ℝ
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
  (skewAdjointScalarExtensionFinBasis (K := ℝ) U.pairingMatrix).reindex
    (Fin.castOrderIso
      (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq)

/-- Mapping the reindexed source basis gives the scalar extension of the
rationally transported basis. -/
theorem rationalIsometryRealSkewAdjointSourceBasis_map :
    (rationalIsometryRealSkewAdjointSourceBasis U V e).map
        (rationalIsometryRealSkewAdjointLinearEquiv U V e) =
      skewAdjointScalarExtensionBasis (K := ℝ) V.pairingMatrix
        (rationalIsometrySkewAdjointTransportedFinBasis U V e) := by
  apply DFunLike.ext _ _
  intro i
  have hsource :
      rationalIsometryRealSkewAdjointSourceBasis U V e i =
        skewAdjointScalarExtensionEquiv (K := ℝ) U.pairingMatrix
          (1 ⊗ₜ[ℚ] Matrix.skewAdjointFinBasis U.pairingMatrix
            ((Fin.castOrderIso
              (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq).symm
                i)) := by
    calc
      rationalIsometryRealSkewAdjointSourceBasis U V e i =
          skewAdjointScalarExtensionFinBasis (K := ℝ) U.pairingMatrix
            ((Fin.castOrderIso
              (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq).symm
                i) :=
        Module.Basis.reindex_apply _ _ _
      _ = _ := by
        apply Subtype.ext
        rw [skewAdjointScalarExtensionFinBasis,
          coe_skewAdjointScalarExtensionBasis_apply,
          coe_skewAdjointScalarExtensionEquiv_tmul]
        simp
  rw [Module.Basis.map_apply, hsource,
    rationalIsometryRealSkewAdjointLinearEquiv_scalarExtension]
  calc
    skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
        (1 ⊗ₜ[ℚ]
          rationalIsometrySkewAdjointLinearEquiv U V e
            (Matrix.skewAdjointFinBasis U.pairingMatrix
              ((Fin.castOrderIso
                (rationalIsometrySkewAdjointLinearEquiv U V e).finrank_eq).symm
                  i))) =
      skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
        (1 ⊗ₜ[ℚ]
          rationalIsometrySkewAdjointTransportedFinBasis U V e i) := by
            congr 2
            simp only [rationalIsometrySkewAdjointTransportedFinBasis,
              Module.Basis.reindex_apply, Module.Basis.map_apply]
            congr 1
    _ = skewAdjointScalarExtensionBasis (K := ℝ) V.pairingMatrix
        (rationalIsometrySkewAdjointTransportedFinBasis U V e) i := by
          apply Subtype.ext
          rw [coe_skewAdjointScalarExtensionEquiv_tmul,
            coe_skewAdjointScalarExtensionBasis_apply]
          simp

/-- The real determinant of the scalar-extended tangent map is exactly the
real image of the rational modulus. -/
theorem rationalIsometryRealSkewAdjointDet_apply :
    (skewAdjointScalarExtensionFinBasis (K := ℝ) V.pairingMatrix).det
        ((rationalIsometryRealSkewAdjointSourceBasis U V e).map
          (rationalIsometryRealSkewAdjointLinearEquiv U V e)) =
      (rationalIsometrySkewAdjointDetScalar U V e : ℝ) := by
  rw [rationalIsometryRealSkewAdjointSourceBasis_map,
    rationalIsometrySkewAdjointDetScalar]
  have hpoint (j : Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra V.pairingMatrix))) :
      skewAdjointScalarExtensionBasis (K := ℝ) V.pairingMatrix
          (rationalIsometrySkewAdjointTransportedFinBasis U V e) j =
        skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
          (1 ⊗ₜ[ℚ]
            rationalIsometrySkewAdjointTransportedFinBasis U V e j) := by
    apply Subtype.ext
    rw [coe_skewAdjointScalarExtensionBasis_apply (Q := ℚ) (K := ℝ),
      coe_skewAdjointScalarExtensionEquiv_tmul (Q := ℚ) (K := ℝ)]
    simp
  have hdet := skewAdjointScalarExtensionBasis_det_apply (Q := ℚ) (K := ℝ)
      V.pairingMatrix (Matrix.skewAdjointFinBasis V.pairingMatrix)
      (rationalIsometrySkewAdjointTransportedFinBasis U V e)
  change (skewAdjointScalarExtensionFinBasis (K := ℝ) V.pairingMatrix).det
      (fun j => skewAdjointScalarExtensionBasis (K := ℝ) V.pairingMatrix
        (rationalIsometrySkewAdjointTransportedFinBasis U V e) j) = _
  rw [show
    (fun j => skewAdjointScalarExtensionBasis (K := ℝ) V.pairingMatrix
      (rationalIsometrySkewAdjointTransportedFinBasis U V e) j) =
    (fun j => skewAdjointScalarExtensionEquiv (K := ℝ) V.pairingMatrix
      (1 ⊗ₜ[ℚ]
        rationalIsometrySkewAdjointTransportedFinBasis U V e j)) by
      funext j
      exact hpoint j]
  exact hdet

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-extended isometry transports the fixed additive real tangent
Haar measure by the reciprocal archimedean norm of the rational modulus. -/
theorem map_rationalIsometryRealSkewAdjointBasisHaarMeasure :
    Measure.map (rationalIsometryRealSkewAdjointContinuousLinearEquiv U V e)
        (Matrix.skewAdjointRealBasisHaarMeasure U.pairingMatrix) =
      (Real.toNNReal
        |((rationalIsometrySkewAdjointDetScalar U V e : ℚ) : ℝ)|)⁻¹ •
        Matrix.skewAdjointRealBasisHaarMeasure V.pairingMatrix := by
  letI : MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
    borel _
  letI : BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (U.pairingMatrix.map (algebraMap ℚ ℝ))).toSubmodule :=
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
    Measure.map (rationalIsometryRealSkewAdjointContinuousLinearEquiv U V e)
        (skewAdjointScalarExtensionFinBasis (K := ℝ) U.pairingMatrix).addHaar =
      Measure.map (rationalIsometryRealSkewAdjointContinuousLinearEquiv U V e)
        (rationalIsometryRealSkewAdjointSourceBasis U V e).addHaar := by
          rw [rationalIsometryRealSkewAdjointSourceBasis,
            Module.Basis.addHaar_reindex]
    _ = _ := by
      have hmap :=
        Module.Basis.map_addHaar_eq_inv_abs_det_map_smul
          (rationalIsometryRealSkewAdjointSourceBasis U V e)
          (skewAdjointScalarExtensionFinBasis (K := ℝ) V.pairingMatrix)
          (rationalIsometryRealSkewAdjointContinuousLinearEquiv U V e)
      change Measure.map
          (rationalIsometryRealSkewAdjointContinuousLinearEquiv U V e)
          (rationalIsometryRealSkewAdjointSourceBasis U V e).addHaar =
        (Real.toNNReal
          |(skewAdjointScalarExtensionFinBasis (K := ℝ) V.pairingMatrix).det
            ((rationalIsometryRealSkewAdjointSourceBasis U V e).map
              (rationalIsometryRealSkewAdjointLinearEquiv U V e))|)⁻¹ •
          (skewAdjointScalarExtensionFinBasis (K := ℝ)
            V.pairingMatrix).addHaar at hmap
      rw [rationalIsometryRealSkewAdjointDet_apply] at hmap
      exact hmap

end RationalQuadraticSpaceMatrix

end
