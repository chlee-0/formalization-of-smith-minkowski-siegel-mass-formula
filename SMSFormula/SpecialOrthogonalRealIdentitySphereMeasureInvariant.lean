import SMSFormula.SpecialOrthogonalRealIdentityLastColumnMeasure

/-!
# Invariance of the identity-model Euclidean sphere measure

This module realizes the identity special-orthogonal matrix action as a
Euclidean linear isometry and proves that the additive-Haar-induced sphere
measure, and its probability normalization, are invariant. It does not prove
uniqueness of invariant probability measure or any fiber disintegration.
-/

open scoped Matrix Matrix.Norms.Operator ENNReal Pointwise

noncomputable section

open MeasureTheory
open TopologicalSpace

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 100000

def identitySpecialOrthogonalOrthogonalMatrix
    (n : ℕ) (g : identitySpecialOrthogonalGroup n) :
    Matrix.orthogonalGroup (Fin (n + 1)) ℝ :=
  ⟨g.1.1.1, by
    rw [Matrix.mem_orthogonalGroup_iff']
    have hpres := g.1.2
    change g.1.1.1ᵀ * 1 * g.1.1.1 = 1 at hpres
    simpa using hpres⟩

def identitySpecialOrthogonalMatrixActionLinearEquiv
    (n : ℕ) (g : identitySpecialOrthogonalGroup n) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).trans
    ((Matrix.UnitaryGroup.toLinearEquiv
      (identitySpecialOrthogonalOrthogonalMatrix n g)).trans
        (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm)

@[simp] theorem identitySpecialOrthogonalMatrixActionLinearEquiv_apply
    (n : ℕ) (g : identitySpecialOrthogonalGroup n)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    identitySpecialOrthogonalMatrixActionLinearEquiv n g v =
      identitySpecialOrthogonalMatrixActionVector n g v :=
  rfl

theorem norm_identitySpecialOrthogonalMatrixActionVector
    (n : ℕ) (g : identitySpecialOrthogonalGroup n)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖identitySpecialOrthogonalMatrixActionVector n g v‖ = ‖v‖ := by
  apply sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  change
    (g.1.1.1 *ᵥ fun j => v j) ⬝ᵥ
        (g.1.1.1 *ᵥ fun j => v j) =
      (fun i => v i) ⬝ᵥ fun i => v i
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  have hpres := g.1.2
  change g.1.1.1ᵀ * 1 * g.1.1.1 = 1 at hpres
  rw [show g.1.1.1ᵀ * g.1.1.1 = 1 by simpa using hpres]
  simp

def identitySpecialOrthogonalMatrixActionLinearIsometryEquiv
    (n : ℕ) (g : identitySpecialOrthogonalGroup n) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  ⟨identitySpecialOrthogonalMatrixActionLinearEquiv n g,
    norm_identitySpecialOrthogonalMatrixActionVector n g⟩

@[simp] theorem identitySpecialOrthogonalMatrixActionLinearIsometryEquiv_apply
    (n : ℕ) (g : identitySpecialOrthogonalGroup n)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    identitySpecialOrthogonalMatrixActionLinearIsometryEquiv n g v =
      identitySpecialOrthogonalMatrixActionVector n g v :=
  rfl

theorem identitySpecialOrthogonalMatrixAction_preimage_radialSector
    (n : ℕ) (hn : 0 < n) (g : identitySpecialOrthogonalGroup n)
    (U : Set (identitySpecialOrthogonalLastColumnSphere n)) :
    (identitySpecialOrthogonalMatrixActionLinearIsometryEquiv n g) ⁻¹'
        (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' U :
            Set (EuclideanSpace ℝ (Fin (n + 1))))) =
      Set.Ioo (0 : ℝ) 1 •
        ((↑) ''
          ((identitySpecialOrthogonalLastColumnSphereActionHomeomorph
            n hn g) ⁻¹' U) :
          Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, hxy⟩
    let L :=
      identitySpecialOrthogonalMatrixActionLinearIsometryEquiv n g
    let a :=
      identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g
    let z : identitySpecialOrthogonalLastColumnSphere n :=
      ⟨L.symm y, by
        rw [Metric.mem_sphere, dist_zero_right, L.symm.norm_map]
        simpa [Metric.mem_sphere, dist_zero_right] using y.2⟩
    have haz : a z = y := by
      apply Subtype.ext
      rw [coe_identitySpecialOrthogonalLastColumnSphereActionHomeomorph]
      change L z = y
      exact L.apply_symm_apply y
    refine ⟨r, hr, z, ⟨z, ?_, rfl⟩, ?_⟩
    · change a z ∈ U
      rw [haz]
      exact hy
    · apply L.injective
      rw [map_smul, L.apply_symm_apply]
      exact hxy
  · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨r, hr, _, ⟨
      identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g z,
      hz, rfl⟩, ?_⟩
    rw [map_smul,
      identitySpecialOrthogonalMatrixActionLinearIsometryEquiv_apply,
      ← coe_identitySpecialOrthogonalLastColumnSphereActionHomeomorph]

theorem map_identitySpecialOrthogonalSphereMeasure_sphereAction
    (n : ℕ) (hn : 0 < n) (g : identitySpecialOrthogonalGroup n) :
    Measure.map
        (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g)
        ((volume :
          Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere) =
      (volume :
        Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere := by
  apply Measure.OuterRegular.ext_isOpen
  intro U hU
  rw [Measure.map_apply
    (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g).measurable
    hU.measurableSet]
  rw [Measure.toSphere_apply' _ hU.measurableSet,
    Measure.toSphere_apply' _
      (hU.preimage
        (identitySpecialOrthogonalLastColumnSphereActionHomeomorph
          n hn g).continuous).measurableSet]
  congr 1
  rw [← identitySpecialOrthogonalMatrixAction_preimage_radialSector
    n hn g U]
  let L :=
    identitySpecialOrthogonalMatrixActionLinearIsometryEquiv n g
  have hsector :
      IsOpen
        (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' U :
            Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isOpen_Ioo.smul_sphere one_ne_zero (by simp) hU
  calc
    volume
        (L ⁻¹'
          (Set.Ioo (0 : ℝ) 1 •
            ((↑) '' U :
              Set (EuclideanSpace ℝ (Fin (n + 1)))))) =
        Measure.map L volume
          (Set.Ioo (0 : ℝ) 1 •
            ((↑) '' U :
              Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
          rw [Measure.map_apply L.continuous.measurable hsector.measurableSet]
    _ = volume
          (Set.Ioo (0 : ℝ) 1 •
            ((↑) '' U :
              Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
      exact congrArg
        (fun μ : Measure (EuclideanSpace ℝ (Fin (n + 1))) =>
          μ (Set.Ioo (0 : ℝ) 1 •
            ((↑) '' U :
              Set (EuclideanSpace ℝ (Fin (n + 1))))))
        L.measurePreserving.map_eq

/-- The additive-Haar-induced Euclidean sphere measure normalized to total
mass one. -/
def identitySpecialOrthogonalNormalizedSphereMeasure (n : ℕ) :
    Measure (identitySpecialOrthogonalLastColumnSphere n) :=
  ((volume :
      Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere Set.univ)⁻¹ •
    (volume :
      Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere

theorem identitySpecialOrthogonalNormalizedSphereMeasure_univ
    (n : ℕ) :
    identitySpecialOrthogonalNormalizedSphereMeasure n Set.univ = 1 := by
  rw [identitySpecialOrthogonalNormalizedSphereMeasure,
    Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel
  · rw [
      euclideanVolumeToSphere_univ_eq_two_mul_identitySpecialOrthogonalSphereStep
        (n + 1) (Nat.succ_pos n)]
    exact mul_ne_zero (by norm_num)
      (identitySpecialOrthogonalSphereStep_ne_zero (n + 1) (Nat.succ_pos n))
  · exact
      (measure_lt_top
        ((volume :
          Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere)
        Set.univ).ne

instance identitySpecialOrthogonalNormalizedSphereMeasure_instProbability
    (n : ℕ) :
    IsProbabilityMeasure
      (identitySpecialOrthogonalNormalizedSphereMeasure n) :=
  ⟨identitySpecialOrthogonalNormalizedSphereMeasure_univ n⟩

theorem map_identitySpecialOrthogonalNormalizedSphereMeasure_sphereAction
    (n : ℕ) (hn : 0 < n) (g : identitySpecialOrthogonalGroup n) :
    Measure.map
        (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g)
        (identitySpecialOrthogonalNormalizedSphereMeasure n) =
      identitySpecialOrthogonalNormalizedSphereMeasure n := by
  rw [identitySpecialOrthogonalNormalizedSphereMeasure,
    Measure.map_smul,
    map_identitySpecialOrthogonalSphereMeasure_sphereAction]

end PositiveDefiniteIntegralLattice
