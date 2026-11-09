import SMSFormula.SpecialOrthogonalRealIdentitySphereMeasureInvariant
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Compact averaging on the identity-model sphere
-/

open scoped Matrix Matrix.Norms.Operator ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 100000

/-- The jointly defined matrix action on the identity-model unit sphere. -/
def identitySpecialOrthogonalLastColumnSphereJointAction
    (n : ℕ) :
    identitySpecialOrthogonalGroup n ×
        identitySpecialOrthogonalLastColumnSphere n →
      identitySpecialOrthogonalLastColumnSphere n :=
  fun p =>
    ⟨identitySpecialOrthogonalMatrixActionVector n p.1 p.2, by
      rw [Metric.mem_sphere, dist_zero_right,
        norm_identitySpecialOrthogonalMatrixActionVector]
      simpa [Metric.mem_sphere, dist_zero_right] using p.2.2⟩

@[simp] theorem coe_identitySpecialOrthogonalLastColumnSphereJointAction
    (n : ℕ)
    (p : identitySpecialOrthogonalGroup n ×
      identitySpecialOrthogonalLastColumnSphere n) :
    (identitySpecialOrthogonalLastColumnSphereJointAction n p :
      EuclideanSpace ℝ (Fin (n + 1))) =
      identitySpecialOrthogonalMatrixActionVector n p.1 p.2 :=
  rfl

theorem continuous_identitySpecialOrthogonalLastColumnSphereJointAction
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalLastColumnSphereJointAction n) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
  apply continuous_pi
  intro i
  have hmatrix :
      Continuous
        (fun p : identitySpecialOrthogonalGroup n ×
            identitySpecialOrthogonalLastColumnSphere n =>
          p.1.1.1.1) :=
    Units.continuous_val.comp
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_fst))
  have hvector :
      Continuous
        (fun p : identitySpecialOrthogonalGroup n ×
            identitySpecialOrthogonalLastColumnSphere n =>
          (p.2 : EuclideanSpace ℝ (Fin (n + 1))).ofLp) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
      (continuous_subtype_val.comp continuous_snd)
  change Continuous fun p : identitySpecialOrthogonalGroup n ×
      identitySpecialOrthogonalLastColumnSphere n =>
    ∑ j, p.1.1.1.1 i j *
      (p.2 : EuclideanSpace ℝ (Fin (n + 1))) j
  apply continuous_finset_sum
  intro j _
  exact
    ((continuous_apply j).comp ((continuous_apply i).comp hmatrix)).mul
      ((continuous_apply j).comp hvector)

@[simp] theorem identitySpecialOrthogonalLastColumnSphereJointAction_apply
    (n : ℕ) (hn : 0 < n) (g : identitySpecialOrthogonalGroup n)
    (x : identitySpecialOrthogonalLastColumnSphere n) :
    identitySpecialOrthogonalLastColumnSphereJointAction n (g, x) =
      identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g x := by
  apply Subtype.ext
  rw [coe_identitySpecialOrthogonalLastColumnSphereJointAction,
    coe_identitySpecialOrthogonalLastColumnSphereActionHomeomorph]

local instance identitySpecialOrthogonalGroupMeasurableSpace'
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identitySpecialOrthogonalGroupBorelSpace'
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

theorem map_prod_probabilityHaar_invariantMeasure_jointAction
    (n : ℕ) (hn : 0 < n)
    (ν : Measure (identitySpecialOrthogonalLastColumnSphere n))
    [IsProbabilityMeasure ν]
    (hν : ∀ g : identitySpecialOrthogonalGroup n,
      Measure.map
          (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g)
          ν = ν) :
    Measure.map
        (identitySpecialOrthogonalLastColumnSphereJointAction n)
        ((identitySpecialOrthogonalProbabilityHaarMeasure n).prod ν) =
      ν := by
  ext U hU
  rw [Measure.map_apply
    (continuous_identitySpecialOrthogonalLastColumnSphereJointAction n).measurable
    hU]
  rw [Measure.prod_apply
    ((continuous_identitySpecialOrthogonalLastColumnSphereJointAction n).measurable
      hU)]
  have hsection :
      ∀ g : identitySpecialOrthogonalGroup n,
        ν (Prod.mk g ⁻¹'
          (identitySpecialOrthogonalLastColumnSphereJointAction n ⁻¹' U)) =
          ν U := by
    intro g
    have hg := congrArg (fun μ : Measure
        (identitySpecialOrthogonalLastColumnSphere n) => μ U) (hν g)
    change
      (Measure.map
        (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g)
        ν) U = ν U at hg
    rw [Measure.map_apply
      (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g).measurable
      hU] at hg
    rw [← hg]
    congr 1
    ext x
    simp only [Set.mem_preimage]
    rw [identitySpecialOrthogonalLastColumnSphereJointAction_apply n hn]
  simp_rw [hsection]
  rw [lintegral_const,
    identitySpecialOrthogonalProbabilityHaarMeasure_univ, mul_one]

theorem map_identitySpecialOrthogonalProbabilityHaarMeasure_mul_right
    (n : ℕ) (h : identitySpecialOrthogonalGroup n) :
    Measure.map (fun g : identitySpecialOrthogonalGroup n => g * h)
        (identitySpecialOrthogonalProbabilityHaarMeasure n) =
      identitySpecialOrthogonalProbabilityHaarMeasure n := by
  letI : IsProbabilityMeasure
      (identitySpecialOrthogonalProbabilityHaarMeasure n) :=
    ⟨identitySpecialOrthogonalProbabilityHaarMeasure_univ n⟩
  letI : IsProbabilityMeasure
      (Measure.map (fun g : identitySpecialOrthogonalGroup n => g * h)
        (identitySpecialOrthogonalProbabilityHaarMeasure n)) :=
    Measure.isProbabilityMeasure_map
      (continuous_mul_right h).measurable.aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem exists_identitySpecialOrthogonalLastColumnSphereAction_eq
    (n : ℕ) (hn : 0 < n)
    (x y : identitySpecialOrthogonalLastColumnSphere n) :
    ∃ g : identitySpecialOrthogonalGroup n,
      identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g x = y := by
  obtain ⟨gx, rfl⟩ :=
    surjective_identitySpecialOrthogonalLastColumn n hn x
  obtain ⟨gy, rfl⟩ :=
    surjective_identitySpecialOrthogonalLastColumn n hn y
  refine ⟨gy * gx⁻¹, ?_⟩
  rw [identitySpecialOrthogonalLastColumnSphereActionHomeomorph_apply,
    mul_assoc, inv_mul_cancel, mul_one]

theorem identitySpecialOrthogonalLastColumnSphereAction_mul
    (n : ℕ) (hn : 0 < n)
    (g h : identitySpecialOrthogonalGroup n)
    (x : identitySpecialOrthogonalLastColumnSphere n) :
    identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g
        (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn h x) =
      identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn (g * h) x := by
  obtain ⟨k, rfl⟩ :=
    surjective_identitySpecialOrthogonalLastColumn n hn x
  rw [identitySpecialOrthogonalLastColumnSphereActionHomeomorph_apply,
    identitySpecialOrthogonalLastColumnSphereActionHomeomorph_apply,
    identitySpecialOrthogonalLastColumnSphereActionHomeomorph_apply,
    mul_assoc]

theorem map_identitySpecialOrthogonalSphereOrbit_probabilityHaar_eq
    (n : ℕ) (hn : 0 < n)
    (x y : identitySpecialOrthogonalLastColumnSphere n) :
    Measure.map
        (fun g : identitySpecialOrthogonalGroup n =>
          identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g x)
        (identitySpecialOrthogonalProbabilityHaarMeasure n) =
      Measure.map
        (fun g : identitySpecialOrthogonalGroup n =>
          identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g y)
        (identitySpecialOrthogonalProbabilityHaarMeasure n) := by
  obtain ⟨h, rfl⟩ :=
    exists_identitySpecialOrthogonalLastColumnSphereAction_eq n hn x y
  let f : identitySpecialOrthogonalGroup n →
      identitySpecialOrthogonalLastColumnSphere n :=
    fun g =>
      identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g x
  have hf : Continuous f := by
    rw [show f = fun g =>
        identitySpecialOrthogonalLastColumnSphereJointAction n (g, x) by
      funext g
      exact
        (identitySpecialOrthogonalLastColumnSphereJointAction_apply n hn g x).symm]
    exact
      (continuous_identitySpecialOrthogonalLastColumnSphereJointAction n).comp
        (continuous_id.prodMk continuous_const)
  calc
    Measure.map f (identitySpecialOrthogonalProbabilityHaarMeasure n) =
        Measure.map f
          (Measure.map (fun g : identitySpecialOrthogonalGroup n => g * h)
            (identitySpecialOrthogonalProbabilityHaarMeasure n)) := by
      rw [map_identitySpecialOrthogonalProbabilityHaarMeasure_mul_right]
    _ = Measure.map (f ∘ fun g : identitySpecialOrthogonalGroup n => g * h)
          (identitySpecialOrthogonalProbabilityHaarMeasure n) := by
      rw [Measure.map_map hf.measurable (continuous_mul_right h).measurable]
    _ = Measure.map
          (fun g : identitySpecialOrthogonalGroup n =>
            identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g
              (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn h x))
          (identitySpecialOrthogonalProbabilityHaarMeasure n) := by
      congr 1
      funext g
      exact
        (identitySpecialOrthogonalLastColumnSphereAction_mul n hn g h x).symm

theorem continuous_identitySpecialOrthogonalLastColumnSphereOrbit
    (n : ℕ) (hn : 0 < n)
    (x : identitySpecialOrthogonalLastColumnSphere n) :
    Continuous
      (fun g : identitySpecialOrthogonalGroup n =>
        identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g x) := by
  rw [show (fun g : identitySpecialOrthogonalGroup n =>
      identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g x) =
      fun g => identitySpecialOrthogonalLastColumnSphereJointAction n (g, x) by
    funext g
    exact
      (identitySpecialOrthogonalLastColumnSphereJointAction_apply n hn g x).symm]
  exact
    (continuous_identitySpecialOrthogonalLastColumnSphereJointAction n).comp
      (continuous_id.prodMk continuous_const)

theorem map_prod_probabilityHaar_jointAction_eq_sphereOrbit
    (n : ℕ) (hn : 0 < n)
    (ν : Measure (identitySpecialOrthogonalLastColumnSphere n))
    [IsProbabilityMeasure ν]
    (x₀ : identitySpecialOrthogonalLastColumnSphere n) :
    Measure.map (identitySpecialOrthogonalLastColumnSphereJointAction n)
        ((identitySpecialOrthogonalProbabilityHaarMeasure n).prod ν) =
      Measure.map
        (fun g : identitySpecialOrthogonalGroup n =>
          identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g x₀)
        (identitySpecialOrthogonalProbabilityHaarMeasure n) := by
  ext U hU
  rw [Measure.map_apply
    (continuous_identitySpecialOrthogonalLastColumnSphereJointAction n).measurable hU]
  rw [Measure.prod_apply_symm
    ((continuous_identitySpecialOrthogonalLastColumnSphereJointAction n).measurable hU)]
  rw [Measure.map_apply
    (continuous_identitySpecialOrthogonalLastColumnSphereOrbit n hn x₀).measurable hU]
  have hsection :
      ∀ x : identitySpecialOrthogonalLastColumnSphere n,
        identitySpecialOrthogonalProbabilityHaarMeasure n
            ((fun g : identitySpecialOrthogonalGroup n => (g, x)) ⁻¹'
              (identitySpecialOrthogonalLastColumnSphereJointAction n ⁻¹' U)) =
          identitySpecialOrthogonalProbabilityHaarMeasure n
            ((fun g : identitySpecialOrthogonalGroup n =>
              identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g x₀) ⁻¹'
              U) := by
    intro x
    have hx := congrArg
      (fun μ : Measure (identitySpecialOrthogonalLastColumnSphere n) => μ U)
      (map_identitySpecialOrthogonalSphereOrbit_probabilityHaar_eq n hn x x₀)
    change
      (Measure.map
        (fun g : identitySpecialOrthogonalGroup n =>
          identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g x)
        (identitySpecialOrthogonalProbabilityHaarMeasure n)) U =
      (Measure.map
        (fun g : identitySpecialOrthogonalGroup n =>
          identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g x₀)
        (identitySpecialOrthogonalProbabilityHaarMeasure n)) U at hx
    rw [Measure.map_apply
        (continuous_identitySpecialOrthogonalLastColumnSphereOrbit n hn x).measurable hU,
      Measure.map_apply
        (continuous_identitySpecialOrthogonalLastColumnSphereOrbit n hn x₀).measurable hU]
      at hx
    rw [← hx]
    congr 1
    ext g
    simp only [Set.mem_preimage]
    rw [identitySpecialOrthogonalLastColumnSphereJointAction_apply n hn]
  simp_rw [hsection]
  rw [lintegral_const, measure_univ, mul_one]

theorem invariant_probabilityMeasure_eq_identitySpecialOrthogonalLastColumnProbabilityMeasure
    (n : ℕ) (hn : 0 < n)
    (ν : Measure (identitySpecialOrthogonalLastColumnSphere n))
    [IsProbabilityMeasure ν]
    (hν : ∀ g : identitySpecialOrthogonalGroup n,
      Measure.map
          (identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g)
          ν = ν) :
    ν = identitySpecialOrthogonalLastColumnProbabilityMeasure n := by
  calc
    ν = Measure.map (identitySpecialOrthogonalLastColumnSphereJointAction n)
        ((identitySpecialOrthogonalProbabilityHaarMeasure n).prod ν) :=
      (map_prod_probabilityHaar_invariantMeasure_jointAction n hn ν hν).symm
    _ = Measure.map
        (fun g : identitySpecialOrthogonalGroup n =>
          identitySpecialOrthogonalLastColumnSphereActionHomeomorph n hn g
            (identitySpecialOrthogonalNorthPole n))
        (identitySpecialOrthogonalProbabilityHaarMeasure n) :=
      map_prod_probabilityHaar_jointAction_eq_sphereOrbit n hn ν
        (identitySpecialOrthogonalNorthPole n)
    _ = identitySpecialOrthogonalLastColumnProbabilityMeasure n := by
      rw [identitySpecialOrthogonalLastColumnProbabilityMeasure]
      congr 1
      funext g
      simpa [identitySpecialOrthogonalNorthPole] using
        identitySpecialOrthogonalLastColumnSphereActionHomeomorph_apply
          n hn g 1

theorem identitySpecialOrthogonalLastColumnProbabilityMeasure_eq_normalizedSphereMeasure
    (n : ℕ) (hn : 0 < n) :
    identitySpecialOrthogonalLastColumnProbabilityMeasure n =
      identitySpecialOrthogonalNormalizedSphereMeasure n := by
  exact
    (invariant_probabilityMeasure_eq_identitySpecialOrthogonalLastColumnProbabilityMeasure
      n hn (identitySpecialOrthogonalNormalizedSphereMeasure n)
      (map_identitySpecialOrthogonalNormalizedSphereMeasure_sphereAction n hn)).symm

end PositiveDefiniteIntegralLattice
