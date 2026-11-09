import SMSFormula.SkewSymmetricGeneralCongruenceCharacter
import SMSFormula.SpecialOrthogonalRealFormCongruenceHaarScalarCancellation

/-!
# The real special-orthogonal adjoint determinant

Left multiplication by the real form matrix identifies the skew-adjoint Lie
algebra with skew-symmetric matrices.  Under this identification conjugation
by a special-orthogonal point is ordinary congruence.  Its determinant is
therefore `(det g)^(n - 1) = 1`.

The final statements identify the associated explicit self-congruence scalar
and show that it preserves the already constructed real differential measure.
-/

noncomputable section

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator NNReal ENNReal Topology

namespace Matrix

open PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realAdjointGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realAdjointGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

private theorem realForm_det_map_algebraMap_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hdet : F.det ≠ 0) :
    (F.map (algebraMap ℚ ℝ)).det ≠ 0 := by
  have hmap : algebraMap ℚ ℝ F.det ≠ 0 := by
    intro hz
    apply hdet
    apply (algebraMap ℚ ℝ).injective
    simpa using hz
  have heq :
      (F.map (algebraMap ℚ ℝ)).det = algebraMap ℚ ℝ F.det := by
    simpa [RingHom.mapMatrix_apply] using
      ((algebraMap ℚ ℝ).map_det F).symm
  rwa [heq]

/-- Left multiplication by the real form sends skew-adjoint matrices to
skew-symmetric matrices. -/
noncomputable def skewAdjointRealToSkewSymmetricLinearMap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule →ₗ[ℝ]
      skewSymmetricMatricesSubmodule (R := ℝ) (ι := Fin n) where
  toFun H := ⟨F.map (algebraMap ℚ ℝ) *
      (H : Matrix (Fin n) (Fin n) ℝ), by
    let Fr := F.map (algebraMap ℚ ℝ)
    let Hm : Matrix (Fin n) (Fin n) ℝ := H
    have hHker : skewAdjointOperator Fr Hm = 0 := by
      exact LinearMap.mem_ker.mp
        ((mem_ker_skewAdjointOperator_iff Fr Hm).mpr H.property)
    have hHskew : Hmᵀ * Fr = -(Fr * Hm) :=
      eq_neg_of_add_eq_zero_left hHker
    change (Fr * Hm)ᵀ = -(Fr * Hm)
    rw [Matrix.transpose_mul, hF.map (algebraMap ℚ ℝ), hHskew]⟩
  map_add' H K := by
    apply Subtype.ext
    simp [Matrix.mul_add]
  map_smul' c H := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_skewAdjointRealToSkewSymmetricLinearMap_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointRealToSkewSymmetricLinearMap F hF H :
        Matrix (Fin n) (Fin n) ℝ) =
      F.map (algebraMap ℚ ℝ) * (H : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

/-- Left multiplication by the inverse real form sends skew-symmetric
matrices back to skew-adjoint matrices. -/
def skewSymmetricRealToSkewAdjointLinearMap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewSymmetricMatricesSubmodule (R := ℝ) (ι := Fin n) →ₗ[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule where
  toFun Y := ⟨(F.map (algebraMap ℚ ℝ))⁻¹ *
      (Y : Matrix (Fin n) (Fin n) ℝ), by
    let Fr := F.map (algebraMap ℚ ℝ)
    let Ym : Matrix (Fin n) (Fin n) ℝ := Y
    have hFrdet : IsUnit Fr.det :=
      isUnit_iff_ne_zero.mpr (realForm_det_map_algebraMap_ne_zero F hdet)
    have hFrSymm : Fr.IsSymm := hF.map _
    apply (mem_ker_skewAdjointOperator_iff Fr (Fr⁻¹ * Ym)).mp
    rw [LinearMap.mem_ker, skewAdjointOperator_apply, Matrix.transpose_mul,
      Matrix.transpose_nonsing_inv, hFrSymm.eq, Y.property]
    calc
      (-Ym) * Fr⁻¹ * Fr + Fr * (Fr⁻¹ * Ym) =
          -(Ym * (Fr⁻¹ * Fr)) + (Fr * Fr⁻¹) * Ym := by
            noncomm_ring
      _ = 0 := by
        rw [Matrix.nonsing_inv_mul Fr hFrdet,
          Matrix.mul_nonsing_inv Fr hFrdet]
        simp⟩
  map_add' Y Z := by
    apply Subtype.ext
    simp [Matrix.mul_add]
  map_smul' c Y := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_skewSymmetricRealToSkewAdjointLinearMap_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (Y : skewSymmetricMatricesSubmodule (R := ℝ) (ι := Fin n)) :
    (skewSymmetricRealToSkewAdjointLinearMap F hF hdet Y :
        Matrix (Fin n) (Fin n) ℝ) =
      (F.map (algebraMap ℚ ℝ))⁻¹ *
        (Y : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

/-- The real skew-adjoint model is linearly equivalent to skew-symmetric
matrices through `H ↦ F H`. -/
def skewAdjointRealSkewSymmetricLinearEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule ≃ₗ[ℝ]
      skewSymmetricMatricesSubmodule (R := ℝ) (ι := Fin n) := by
  let Fr := F.map (algebraMap ℚ ℝ)
  let hFrdet : IsUnit Fr.det :=
    isUnit_iff_ne_zero.mpr (realForm_det_map_algebraMap_ne_zero F hdet)
  refine LinearEquiv.ofLinear
    (skewAdjointRealToSkewSymmetricLinearMap F hF)
    (skewSymmetricRealToSkewAdjointLinearMap F hF hdet) ?_ ?_
  · apply LinearMap.ext
    intro Y
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.id_apply,
      coe_skewAdjointRealToSkewSymmetricLinearMap_apply,
      coe_skewSymmetricRealToSkewAdjointLinearMap_apply]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv Fr hFrdet,
      Matrix.one_mul]
  · apply LinearMap.ext
    intro H
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.id_apply,
      coe_skewAdjointRealToSkewSymmetricLinearMap_apply,
      coe_skewSymmetricRealToSkewAdjointLinearMap_apply]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Fr hFrdet,
      Matrix.one_mul]

@[simp]
theorem coe_skewAdjointRealSkewSymmetricLinearEquiv_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointRealSkewSymmetricLinearEquiv F hF hdet H :
        Matrix (Fin n) (Fin n) ℝ) =
      F.map (algebraMap ℚ ℝ) * (H : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

/-- The real special-orthogonal adjoint action, using the existing explicit
real form-congruence carrier. -/
def skewAdjointRealSpecialOrthogonalAdjointContinuousLinearEquiv
    (F : Matrix (Fin n) (Fin n) ℚ)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  skewAdjointRealFormCongruenceContinuousLinearEquiv
    (F.map (algebraMap ℚ ℝ)) (F.map (algebraMap ℚ ℝ))
    g.1.1 g.1.2

@[simp]
theorem coe_skewAdjointRealSpecialOrthogonalAdjointContinuousLinearEquiv_apply
    (F : Matrix (Fin n) (Fin n) ℚ)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ)))
    (H : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointRealSpecialOrthogonalAdjointContinuousLinearEquiv
        F g H : Matrix (Fin n) (Fin n) ℝ) =
      (g.1.1.1 : Matrix (Fin n) (Fin n) ℝ)⁻¹ *
        (H : Matrix (Fin n) (Fin n) ℝ) *
          (g.1.1 : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

/-- The special-orthogonal adjoint equivalence is conjugate to ordinary
skew-symmetric congruence. -/
theorem skewAdjointRealSpecialOrthogonalAdjoint_toLinearEquiv_eq_conj
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    (skewAdjointRealSpecialOrthogonalAdjointContinuousLinearEquiv
        F g).toLinearEquiv =
      (skewAdjointRealSkewSymmetricLinearEquiv F hF hdet).trans
        ((skewSymmetricCongruenceLinearEquiv g.1.1).trans
          (skewAdjointRealSkewSymmetricLinearEquiv F hF hdet).symm) := by
  apply LinearEquiv.ext
  intro H
  apply Subtype.ext
  let Fr := F.map (algebraMap ℚ ℝ)
  let W : Matrix (Fin n) (Fin n) ℝ := g.1.1
  have hFrdet : IsUnit Fr.det :=
    isUnit_iff_ne_zero.mpr (realForm_det_map_algebraMap_ne_zero F hdet)
  have htransport : Fr⁻¹ * Wᵀ * Fr = W⁻¹ := by
    have hWdet : IsUnit W.det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g.1.1)
    have hWinv : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv _ hWdet
    calc
      Fr⁻¹ * Wᵀ * Fr = Fr⁻¹ * Wᵀ * Fr * 1 := by rw [Matrix.mul_one]
      _ = Fr⁻¹ * Wᵀ * Fr * (W * W⁻¹) := by rw [hWinv]
      _ = Fr⁻¹ * (Wᵀ * Fr * W) * W⁻¹ := by noncomm_ring
      _ = Fr⁻¹ * Fr * W⁻¹ := by rw [g.1.2]
      _ = W⁻¹ := by rw [Matrix.nonsing_inv_mul Fr hFrdet, Matrix.one_mul]
  change W⁻¹ * (H : Matrix (Fin n) (Fin n) ℝ) * W =
    Fr⁻¹ * (Wᵀ * (Fr * (H : Matrix (Fin n) (Fin n) ℝ)) * W)
  rw [← htransport]
  noncomm_ring

/-- The determinant of the real special-orthogonal adjoint action is one. -/
theorem det_skewAdjointRealSpecialOrthogonalAdjointContinuousLinearEquiv_eq_one
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    LinearMap.det
        (skewAdjointRealSpecialOrthogonalAdjointContinuousLinearEquiv
          F g).toLinearMap = 1 := by
  let E := skewAdjointRealSkewSymmetricLinearEquiv F hF hdet
  let C := skewSymmetricCongruenceLinearEquiv g.1.1
  rw [show
      (skewAdjointRealSpecialOrthogonalAdjointContinuousLinearEquiv
          F g).toLinearEquiv = E.trans (C.trans E.symm) from
    skewAdjointRealSpecialOrthogonalAdjoint_toLinearEquiv_eq_conj
      F hF hdet g]
  have hconj : LinearEquiv.det (E.trans (C.trans E.symm)) =
      LinearEquiv.det C :=
    LinearEquiv.det_conj C E.symm
  have hconj' : LinearMap.det (E.trans (C.trans E.symm)).toLinearMap =
      LinearMap.det C.toLinearMap := by
    have hval := congrArg (fun z : ℝˣ ↦ (z : ℝ)) hconj
    simpa only [LinearEquiv.coe_det] using hval
  rw [hconj']
  change LinearMap.det
      (skewSymmetricCongruenceEndomorphism
        (g.1.1 : Matrix (Fin n) (Fin n) ℝ)) = 1
  rw [det_skewSymmetricCongruenceEndomorphism_eq_det_pow]
  have hgdet : Matrix.det
      (g.1.1 : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (mem_specialFormPreservingMatrixSubgroup_iff
      (F.map (algebraMap ℚ ℝ)) g.1).mp g.2
  rw [hgdet, one_pow]

end Matrix

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

local instance realAdjointDifferentialGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realAdjointDifferentialGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- Conjugation by a real special-orthogonal point as an explicit
self-congruence of the rational form. -/
def specialOrthogonalRealAdjointFormCongruenceData
    (F : Matrix (Fin n) (Fin n) ℚ)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    SpecialOrthogonalRealFormCongruenceData F F where
  unit := g.1.1
  congruence := g.1.2

@[simp]
theorem specialOrthogonalRealAdjointFormCongruenceData_tangentEquiv
    (F : Matrix (Fin n) (Fin n) ℚ)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    (specialOrthogonalRealAdjointFormCongruenceData F g).tangentEquiv =
      Matrix.skewAdjointRealSpecialOrthogonalAdjointContinuousLinearEquiv
        F g :=
  rfl

/-- The absolute explicit self-congruence tangent determinant is one.  The
finite source reindexing may contribute a sign. -/
theorem abs_specialOrthogonalRealAdjointFormCongruenceData_detScalar_eq_one
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    |(specialOrthogonalRealAdjointFormCongruenceData F g).detScalar| = 1 := by
  let A := Matrix.skewAdjointRealSpecialOrthogonalAdjointContinuousLinearEquiv
    F g
  let b := Matrix.skewAdjointScalarExtensionFinBasis (K := ℝ) F
  have hsource : Matrix.skewAdjointRealLinearEquivSourceBasis F F A = b := by
    let h := Matrix.finrank_skewAdjoint_eq_of_real_linearEquiv F F A
    have hp : h = rfl := Subsingleton.elim _ _
    change b.reindex (Fin.castOrderIso h).toEquiv = b
    rw [hp]
    simp
  change |Matrix.skewAdjointRealLinearEquivDetScalar F F A| = 1
  rw [Matrix.skewAdjointRealLinearEquivDetScalar, hsource]
  change |b.det (b.map A.toLinearEquiv)| = 1
  rw [Module.Basis.det_apply]
  have hmatrix : b.toMatrix (b.map A.toLinearEquiv) =
      LinearMap.toMatrix b b A.toLinearMap := by
    ext i j
    simp only [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply,
      Module.Basis.map_apply]
    rfl
  rw [hmatrix, LinearMap.det_toMatrix]
  have hdetA : LinearMap.det A.toLinearMap = 1 := by
    exact
      Matrix.det_skewAdjointRealSpecialOrthogonalAdjointContinuousLinearEquiv_eq_one
        F hF hdet g
  calc
    |LinearMap.det A.toLinearMap| = |(1 : ℝ)| := congrArg abs hdetA
    _ = 1 := abs_one

/-- Conjugation by a real special-orthogonal point preserves the fixed-scale
real differential measure. -/
theorem map_specialFormPreservingSmoothRealDifferentialMeasure_adjoint
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    Measure.map
        (specialOrthogonalRealAdjointFormCongruenceData
          F g).groupEquiv.toHomeomorph
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) =
      specialFormPreservingSmoothRealDifferentialMeasure F hF hdet := by
  rw [map_specialFormPreservingSmoothRealDifferentialMeasure_formCongruence_eq_smul
      F F hF hdet hF hdet
      (specialOrthogonalRealAdjointFormCongruenceData F g),
    specialFormPreservingRealFormCongruenceHaarScalar_eq
      F F hF hdet hF hdet
      (specialOrthogonalRealAdjointFormCongruenceData F g),
    abs_specialOrthogonalRealAdjointFormCongruenceData_detScalar_eq_one
      F hF hdet g]
  norm_num

end PositiveDefiniteIntegralLattice
