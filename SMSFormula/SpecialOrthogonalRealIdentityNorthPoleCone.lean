import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleSphereMeasure
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The identity north-pole radial cone

This module uses a square-dimensional cone parametrization in place of a
codimension-one sphere graph-area formula, which is not available.  It
establishes the geometry and the derivatives but does not apply nonlinear
change of variables or identify the sphere-coordinate density measure.
-/

open scoped ENNReal Matrix Matrix.Norms.Operator Pointwise ContDiff

noncomputable section

open Metric Set

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 100000

/-- The ambient domain of the north-pole radial cone. -/
def identitySpecialOrthogonalNorthPoleConeDomainSet (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ Set.Ioo 0 1

abbrev identitySpecialOrthogonalNorthPoleConeDomain (n : ℕ) :=
  identitySpecialOrthogonalNorthPoleConeDomainSet n

theorem isOpen_identitySpecialOrthogonalNorthPoleConeDomainSet (n : ℕ) :
    IsOpen (identitySpecialOrthogonalNorthPoleConeDomainSet n) :=
  Metric.isOpen_ball.prod isOpen_Ioo

theorem measurableSet_identitySpecialOrthogonalNorthPoleConeDomainSet
    (n : ℕ) :
    MeasurableSet (identitySpecialOrthogonalNorthPoleConeDomainSet n) :=
  (isOpen_identitySpecialOrthogonalNorthPoleConeDomainSet n).measurableSet

/-- The square-dimensional cone map over the positive hemisphere. -/
def identitySpecialOrthogonalNorthPoleCone
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  p.2 • identitySpecialOrthogonalNorthPoleInverseVector n p.1

@[simp]
theorem identitySpecialOrthogonalNorthPoleCone_apply_castSucc
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ) (i : Fin n) :
    identitySpecialOrthogonalNorthPoleCone n p i.castSucc =
      p.2 * p.1 i := by
  simp [identitySpecialOrthogonalNorthPoleCone]

@[simp]
theorem identitySpecialOrthogonalNorthPoleCone_apply_last
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    identitySpecialOrthogonalNorthPoleCone n p (Fin.last n) =
      p.2 * identitySpecialOrthogonalNorthPoleFinalCoordinate p.1 := by
  simp [identitySpecialOrthogonalNorthPoleCone]

theorem continuous_identitySpecialOrthogonalNorthPoleCone (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleCone n) :=
  continuous_snd.smul
    ((continuous_identitySpecialOrthogonalNorthPoleInverseVector n).comp
      continuous_fst)

theorem contDiffOn_identitySpecialOrthogonalNorthPoleCone (n : ℕ) :
    ContDiffOn ℝ ∞
      (identitySpecialOrthogonalNorthPoleCone n)
      (identitySpecialOrthogonalNorthPoleConeDomainSet n) := by
  have hlift : ContDiffOn ℝ ∞
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        identitySpecialOrthogonalNorthPoleInverseVector n p.1)
      (identitySpecialOrthogonalNorthPoleConeDomainSet n) :=
    (contDiffOn_identitySpecialOrthogonalNorthPoleInverseVector n).comp
      contDiff_fst.contDiffOn (by
        rintro ⟨v, r⟩ ⟨hv, hr⟩
        exact hv)
  exact contDiff_snd.contDiffOn.smul hlift

/-- The explicit derivative of the positive final coordinate on the open
ball. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleFinalCoordinateDerivative
    (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  -(identitySpecialOrthogonalNorthPoleFinalCoordinate v)⁻¹ •
    innerSL ℝ v

@[simp]
theorem identitySpecialOrthogonalNorthPoleFinalCoordinateDerivative_apply
    (v h : EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleFinalCoordinateDerivative v h =
      -(inner ℝ v h) /
        identitySpecialOrthogonalNorthPoleFinalCoordinate v := by
  simp [identitySpecialOrthogonalNorthPoleFinalCoordinateDerivative,
    div_eq_mul_inv, mul_comm]

theorem
    hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleFinalCoordinate
    {n : ℕ} {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    HasFDerivWithinAt
      (identitySpecialOrthogonalNorthPoleFinalCoordinate :
        EuclideanSpace ℝ (Fin n) → ℝ)
      (identitySpecialOrthogonalNorthPoleFinalCoordinateDerivative v)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) v := by
  have harg :
      HasFDerivAt
        (fun w : EuclideanSpace ℝ (Fin n) => 1 - ‖w‖ ^ 2)
        (-(2 : ℝ) • innerSL ℝ v) v := by
    convert
      (hasFDerivAt_const
        (x := v) (c := (1 : ℝ))).sub
        (hasFDerivAt_id (x := v)).norm_sq using 1
    ext h
    simp
  have harg_pos : 0 < 1 - ‖v‖ ^ 2 := by
    have ht :=
      identitySpecialOrthogonalNorthPoleFinalCoordinate_pos hv
    exact Real.sqrt_pos.mp (by
      simpa [identitySpecialOrthogonalNorthPoleFinalCoordinate] using ht)
  have hsqrt := harg.sqrt harg_pos.ne'
  have hderiv :
      ((1 / (2 * Real.sqrt (1 - ‖v‖ ^ 2))) •
          (-(2 : ℝ) • innerSL ℝ v)) =
        identitySpecialOrthogonalNorthPoleFinalCoordinateDerivative v := by
    ext h
    simp only [ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    rw [identitySpecialOrthogonalNorthPoleFinalCoordinateDerivative_apply]
    rw [identitySpecialOrthogonalNorthPoleFinalCoordinate]
    field_simp [
      (identitySpecialOrthogonalNorthPoleFinalCoordinate_pos hv).ne']
  have hsqrt' :
      HasFDerivAt
        (identitySpecialOrthogonalNorthPoleFinalCoordinate :
          EuclideanSpace ℝ (Fin n) → ℝ)
        (identitySpecialOrthogonalNorthPoleFinalCoordinateDerivative v) v := by
    rw [hderiv] at hsqrt
    simpa only [identitySpecialOrthogonalNorthPoleFinalCoordinate] using hsqrt
  exact hsqrt'.hasFDerivWithinAt

/-- The explicit differential of the square-root lift. -/
def identitySpecialOrthogonalNorthPoleInverseVectorDerivativeLinearMap
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) where
  toFun h :=
    WithLp.toLp 2
      (Fin.lastCases
        (identitySpecialOrthogonalNorthPoleFinalCoordinateDerivative v h)
        (fun i => h i))
  map_add' h k := by
    apply PiLp.ext
    intro i
    cases i using Fin.lastCases with
    | last =>
        simp [identitySpecialOrthogonalNorthPoleFinalCoordinateDerivative_apply,
          inner_add_right]
        ring
    | cast i => simp
  map_smul' c h := by
    apply PiLp.ext
    intro i
    cases i using Fin.lastCases with
    | last =>
        simp [identitySpecialOrthogonalNorthPoleFinalCoordinateDerivative_apply]
    | cast i => simp

noncomputable def
    identitySpecialOrthogonalNorthPoleInverseVectorDerivative
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  ⟨identitySpecialOrthogonalNorthPoleInverseVectorDerivativeLinearMap n v,
    LinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem identitySpecialOrthogonalNorthPoleInverseVectorDerivative_castSucc
    (n : ℕ) (v h : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    identitySpecialOrthogonalNorthPoleInverseVectorDerivative n v h i.castSucc =
      h i := by
  simp [identitySpecialOrthogonalNorthPoleInverseVectorDerivative,
    identitySpecialOrthogonalNorthPoleInverseVectorDerivativeLinearMap]

@[simp]
theorem identitySpecialOrthogonalNorthPoleInverseVectorDerivative_last
    (n : ℕ) (v h : EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleInverseVectorDerivative n v h
        (Fin.last n) =
      -(inner ℝ v h) /
        identitySpecialOrthogonalNorthPoleFinalCoordinate v := by
  simp [identitySpecialOrthogonalNorthPoleInverseVectorDerivative,
    identitySpecialOrthogonalNorthPoleInverseVectorDerivativeLinearMap]

theorem hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleInverseVector
    {n : ℕ} {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    HasFDerivWithinAt
      (identitySpecialOrthogonalNorthPoleInverseVector n)
      (identitySpecialOrthogonalNorthPoleInverseVectorDerivative n v)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) v := by
  rw [hasFDerivWithinAt_piLp]
  intro i
  cases i using Fin.lastCases with
  | last =>
      convert
        hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleFinalCoordinate hv
          using 1
      · funext x
        simp
      · apply ContinuousLinearMap.ext
        intro h
        simp [identitySpecialOrthogonalNorthPoleInverseVectorDerivative,
          identitySpecialOrthogonalNorthPoleInverseVectorDerivativeLinearMap]
  | cast i =>
      convert
        (PiLp.proj (𝕜 := ℝ) 2
          (fun _ : Fin n => ℝ) i).hasFDerivAt.hasFDerivWithinAt using 1
      · funext x
        simp
      · apply ContinuousLinearMap.ext
        intro h
        simp [identitySpecialOrthogonalNorthPoleInverseVectorDerivative,
          identitySpecialOrthogonalNorthPoleInverseVectorDerivativeLinearMap]

theorem fderivWithin_identitySpecialOrthogonalNorthPoleInverseVector
    {n : ℕ} {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    fderivWithin ℝ
        (identitySpecialOrthogonalNorthPoleInverseVector n)
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) v =
      identitySpecialOrthogonalNorthPoleInverseVectorDerivative n v :=
  (hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleInverseVector
    hv).fderivWithin (Metric.isOpen_ball.uniqueDiffWithinAt hv)

/-- The radial sector over the positive hemisphere. -/
def identitySpecialOrthogonalNorthPoleRadialSector (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Set.Ioo (0 : ℝ) 1 •
    ((↑) '' identitySpecialOrthogonalNorthPoleHemisphere n :
      Set (EuclideanSpace ℝ (Fin (n + 1))))

theorem identitySpecialOrthogonalNorthPoleCone_image_domain (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCone n ''
        identitySpecialOrthogonalNorthPoleConeDomainSet n =
      identitySpecialOrthogonalNorthPoleRadialSector n := by
  ext x
  constructor
  · rintro ⟨⟨v, r⟩, ⟨hv, hr⟩, rfl⟩
    refine ⟨r, hr, _, ⟨
      identitySpecialOrthogonalNorthPoleInverse n ⟨v, hv⟩,
      identitySpecialOrthogonalNorthPoleInverse_mem_hemisphere n ⟨v, hv⟩,
      rfl⟩, ?_⟩
    rfl
  · rintro ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    let v := identitySpecialOrthogonalNorthPoleCoordinate n x
    have hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      identitySpecialOrthogonalNorthPoleCoordinate_mem_ball n x hx
    refine ⟨(v, r), ⟨hv, hr⟩, ?_⟩
    rw [identitySpecialOrthogonalNorthPoleCone]
    congr 1
    exact identitySpecialOrthogonalNorthPoleInverse_coordinate n x hx

theorem norm_identitySpecialOrthogonalNorthPoleCone_of_mem
    (n : ℕ) {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n) :
    ‖identitySpecialOrthogonalNorthPoleCone n p‖ = p.2 := by
  rw [identitySpecialOrthogonalNorthPoleCone, norm_smul,
    norm_identitySpecialOrthogonalNorthPoleInverseVector n p.1 hp.1]
  simp [abs_of_pos hp.2.1]

theorem identitySpecialOrthogonalNorthPoleCone_injOn (n : ℕ) :
    Set.InjOn
      (identitySpecialOrthogonalNorthPoleCone n)
      (identitySpecialOrthogonalNorthPoleConeDomainSet n) := by
  intro p hp q hq hpq
  have hr : p.2 = q.2 := by
    rw [← norm_identitySpecialOrthogonalNorthPoleCone_of_mem n hp,
      hpq, norm_identitySpecialOrthogonalNorthPoleCone_of_mem n hq]
  apply Prod.ext
  · apply PiLp.ext
    intro i
    have hij := congrArg (fun z => z i.castSucc) hpq
    change
      identitySpecialOrthogonalNorthPoleCone n p i.castSucc =
        identitySpecialOrthogonalNorthPoleCone n q i.castSucc at hij
    rw [identitySpecialOrthogonalNorthPoleCone_apply_castSucc,
      identitySpecialOrthogonalNorthPoleCone_apply_castSucc, hr] at hij
    exact (mul_left_cancel₀ hq.2.1.ne' hij)
  · exact hr

/-- The derivative of the cone map, split into its ball and radial
directions. -/
noncomputable def identitySpecialOrthogonalNorthPoleConeDerivative
    (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  p.2 •
      ((fderivWithin ℝ
          (identitySpecialOrthogonalNorthPoleInverseVector n)
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) p.1).comp
        (ContinuousLinearMap.fst ℝ
          (EuclideanSpace ℝ (Fin n)) ℝ)) +
    (ContinuousLinearMap.snd ℝ
      (EuclideanSpace ℝ (Fin n)) ℝ).smulRight
        (identitySpecialOrthogonalNorthPoleInverseVector n p.1)

@[simp]
theorem identitySpecialOrthogonalNorthPoleConeDerivative_apply
    (n : ℕ) (p h : EuclideanSpace ℝ (Fin n) × ℝ) :
    identitySpecialOrthogonalNorthPoleConeDerivative n p h =
      p.2 •
          fderivWithin ℝ
            (identitySpecialOrthogonalNorthPoleInverseVector n)
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) p.1 h.1 +
        h.2 • identitySpecialOrthogonalNorthPoleInverseVector n p.1 := by
  rfl

theorem identitySpecialOrthogonalNorthPoleConeDerivative_apply_of_mem
    (n : ℕ) {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n)
    (h : EuclideanSpace ℝ (Fin n) × ℝ) :
    identitySpecialOrthogonalNorthPoleConeDerivative n p h =
      p.2 •
          identitySpecialOrthogonalNorthPoleInverseVectorDerivative
            n p.1 h.1 +
        h.2 • identitySpecialOrthogonalNorthPoleInverseVector n p.1 := by
  rw [identitySpecialOrthogonalNorthPoleConeDerivative_apply,
    fderivWithin_identitySpecialOrthogonalNorthPoleInverseVector hp.1]

theorem
    identitySpecialOrthogonalNorthPoleConeDerivative_apply_castSucc_of_mem
    (n : ℕ) {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n)
    (h : EuclideanSpace ℝ (Fin n) × ℝ) (i : Fin n) :
    identitySpecialOrthogonalNorthPoleConeDerivative n p h i.castSucc =
      p.2 * h.1 i + h.2 * p.1 i := by
  rw [identitySpecialOrthogonalNorthPoleConeDerivative_apply_of_mem n hp]
  simp

theorem identitySpecialOrthogonalNorthPoleConeDerivative_apply_last_of_mem
    (n : ℕ) {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n)
    (h : EuclideanSpace ℝ (Fin n) × ℝ) :
    identitySpecialOrthogonalNorthPoleConeDerivative n p h (Fin.last n) =
      p.2 *
          (-(inner ℝ p.1 h.1) /
            identitySpecialOrthogonalNorthPoleFinalCoordinate p.1) +
        h.2 * identitySpecialOrthogonalNorthPoleFinalCoordinate p.1 := by
  rw [identitySpecialOrthogonalNorthPoleConeDerivative_apply_of_mem n hp]
  simp

theorem hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleCone
    (n : ℕ) {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n) :
    HasFDerivWithinAt
      (identitySpecialOrthogonalNorthPoleCone n)
      (identitySpecialOrthogonalNorthPoleConeDerivative n p)
      (identitySpecialOrthogonalNorthPoleConeDomainSet n) p := by
  have hlift :
      HasFDerivWithinAt
        (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
          identitySpecialOrthogonalNorthPoleInverseVector n q.1)
        ((fderivWithin ℝ
            (identitySpecialOrthogonalNorthPoleInverseVector n)
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) p.1).comp
          (ContinuousLinearMap.fst ℝ
            (EuclideanSpace ℝ (Fin n)) ℝ))
        (identitySpecialOrthogonalNorthPoleConeDomainSet n) p := by
    have hbase :
        HasFDerivWithinAt
          (identitySpecialOrthogonalNorthPoleInverseVector n)
          (fderivWithin ℝ
            (identitySpecialOrthogonalNorthPoleInverseVector n)
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) p.1)
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) p.1 :=
      ((contDiffOn_identitySpecialOrthogonalNorthPoleInverseVector n)
        p.1 hp.1).differentiableWithinAt (by simp) |>.hasFDerivWithinAt
    exact hbase.comp p
      (ContinuousLinearMap.fst ℝ
        (EuclideanSpace ℝ (Fin n)) ℝ).hasFDerivAt.hasFDerivWithinAt
      (by
        rintro ⟨v, r⟩ ⟨hv, hr⟩
        exact hv)
  have hr :
      HasFDerivWithinAt
        (fun q : EuclideanSpace ℝ (Fin n) × ℝ => q.2)
        (ContinuousLinearMap.snd ℝ
          (EuclideanSpace ℝ (Fin n)) ℝ)
        (identitySpecialOrthogonalNorthPoleConeDomainSet n) p :=
    (ContinuousLinearMap.snd ℝ
      (EuclideanSpace ℝ (Fin n)) ℝ).hasFDerivAt.hasFDerivWithinAt
  simpa [identitySpecialOrthogonalNorthPoleCone,
    identitySpecialOrthogonalNorthPoleConeDerivative] using hr.smul hlift

theorem fderivWithin_identitySpecialOrthogonalNorthPoleCone
    (n : ℕ) {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hp : p ∈ identitySpecialOrthogonalNorthPoleConeDomainSet n) :
    fderivWithin ℝ
        (identitySpecialOrthogonalNorthPoleCone n)
        (identitySpecialOrthogonalNorthPoleConeDomainSet n) p =
      identitySpecialOrthogonalNorthPoleConeDerivative n p :=
  (hasFDerivWithinAt_identitySpecialOrthogonalNorthPoleCone n hp).fderivWithin
    ((isOpen_identitySpecialOrthogonalNorthPoleConeDomainSet n).uniqueDiffWithinAt
      hp)

end PositiveDefiniteIntegralLattice
