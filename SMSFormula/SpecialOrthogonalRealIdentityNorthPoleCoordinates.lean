import SMSFormula.SpecialOrthogonalRealIdentityFiberDifferential
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# North-pole coordinates on the identity last-column sphere
-/

open scoped Matrix Matrix.Norms.Operator ContDiff

noncomputable section

open Metric Set

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 100000

/-- Drop the final coordinate from the ambient Euclidean space. -/
def identitySpecialOrthogonalNorthPoleCoordinateLinearMap (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => x i.castSucc)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The continuous nonfinal-coordinate projection. -/
noncomputable def
    identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ⟨identitySpecialOrthogonalNorthPoleCoordinateLinearMap n,
    LinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap_apply
    (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n x i =
      x i.castSucc :=
  rfl

/-- The open hemisphere on which the final coordinate is positive. -/
def identitySpecialOrthogonalNorthPoleHemisphere (n : ℕ) :
    Set (identitySpecialOrthogonalLastColumnSphere n) :=
  {x | 0 < (x.1 : EuclideanSpace ℝ (Fin (n + 1))) (Fin.last n)}

theorem isOpen_identitySpecialOrthogonalNorthPoleHemisphere (n : ℕ) :
    IsOpen (identitySpecialOrthogonalNorthPoleHemisphere n) := by
  apply isOpen_lt continuous_const
  exact
    (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).comp
      continuous_subtype_val

theorem measurableSet_identitySpecialOrthogonalNorthPoleHemisphere (n : ℕ) :
    MeasurableSet (identitySpecialOrthogonalNorthPoleHemisphere n) :=
  (isOpen_identitySpecialOrthogonalNorthPoleHemisphere n).measurableSet

theorem isOpen_identitySpecialOrthogonalNorthPoleCoordinateBall (n : ℕ) :
    IsOpen (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  Metric.isOpen_ball

theorem measurableSet_identitySpecialOrthogonalNorthPoleCoordinateBall
    (n : ℕ) :
    MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (isOpen_identitySpecialOrthogonalNorthPoleCoordinateBall n).measurableSet

/-- The north-pole coordinate projection on the unit sphere. -/
def identitySpecialOrthogonalNorthPoleCoordinate
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere n) :
    EuclideanSpace ℝ (Fin n) :=
  identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n x.1

@[simp]
theorem identitySpecialOrthogonalNorthPoleCoordinate_apply
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere n) (i : Fin n) :
    identitySpecialOrthogonalNorthPoleCoordinate n x i = x.1 i.castSucc :=
  rfl

theorem continuous_identitySpecialOrthogonalNorthPoleCoordinate (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleCoordinate n) :=
  (identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n).continuous.comp
    continuous_subtype_val

theorem contDiff_identitySpecialOrthogonalNorthPoleCoordinateLinearMap
    (n : ℕ) :
    ContDiff ℝ ∞
      (identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n) :=
  (identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n).contDiff

theorem identitySpecialOrthogonalLastColumnSphere_norm_sq
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere n) :
    ‖(x.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 = 1 := by
  have hx := x.2
  rw [Metric.mem_sphere, dist_zero_right] at hx
  rw [hx]
  norm_num

theorem identitySpecialOrthogonalNorthPoleCoordinate_norm_sq_add_last_sq
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere n) :
    ‖identitySpecialOrthogonalNorthPoleCoordinate n x‖ ^ 2 +
        x.1 (Fin.last n) ^ 2 = 1 := by
  have hnorm :=
    identitySpecialOrthogonalLastColumnSphere_norm_sq n x
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_castSucc] at hnorm
  rw [PiLp.norm_sq_eq_of_L2]
  simpa [identitySpecialOrthogonalNorthPoleCoordinate, Real.norm_eq_abs,
    sq_abs] using hnorm

theorem identitySpecialOrthogonalNorthPoleCoordinate_mem_ball
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere n)
    (hx : x ∈ identitySpecialOrthogonalNorthPoleHemisphere n) :
    identitySpecialOrthogonalNorthPoleCoordinate n x ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [Metric.mem_ball, dist_zero_right]
  rw [← sq_lt_sq₀ (norm_nonneg _) zero_le_one]
  have hlast : 0 < x.1 (Fin.last n) := hx
  nlinarith [
    identitySpecialOrthogonalNorthPoleCoordinate_norm_sq_add_last_sq n x]

/-- The positive final coordinate over the open Euclidean unit ball. -/
def identitySpecialOrthogonalNorthPoleFinalCoordinate
    (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (1 - ‖v‖ ^ 2)

/-- Insert nonfinal coordinates and the positive square-root final
coordinate. -/
def identitySpecialOrthogonalNorthPoleInverseVector
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2
    (Fin.lastCases
      (identitySpecialOrthogonalNorthPoleFinalCoordinate v)
      (fun i => v i))

@[simp]
theorem identitySpecialOrthogonalNorthPoleInverseVector_castSucc
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    identitySpecialOrthogonalNorthPoleInverseVector n v i.castSucc = v i := by
  simp [identitySpecialOrthogonalNorthPoleInverseVector]

@[simp]
theorem identitySpecialOrthogonalNorthPoleInverseVector_last
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleInverseVector n v (Fin.last n) =
      identitySpecialOrthogonalNorthPoleFinalCoordinate v := by
  simp [identitySpecialOrthogonalNorthPoleInverseVector]

theorem identitySpecialOrthogonalNorthPoleFinalCoordinate_pos
    {n : ℕ} {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    0 < identitySpecialOrthogonalNorthPoleFinalCoordinate v := by
  rw [identitySpecialOrthogonalNorthPoleFinalCoordinate, Real.sqrt_pos]
  rw [Metric.mem_ball, dist_zero_right] at hv
  nlinarith [norm_nonneg v, (sq_lt_sq₀ (norm_nonneg v) zero_le_one).2 hv]

theorem norm_identitySpecialOrthogonalNorthPoleInverseVector
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ‖identitySpecialOrthogonalNorthPoleInverseVector n v‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_castSucc]
  have hpos :
      0 < 1 - ‖v‖ ^ 2 := by
    rw [Metric.mem_ball, dist_zero_right] at hv
    nlinarith [norm_nonneg v,
      (sq_lt_sq₀ (norm_nonneg v) zero_le_one).2 hv]
  calc
    (∑ i : Fin n,
          ‖identitySpecialOrthogonalNorthPoleInverseVector n v i.castSucc‖ ^ 2) +
        ‖identitySpecialOrthogonalNorthPoleInverseVector n v (Fin.last n)‖ ^ 2 =
        ‖v‖ ^ 2 + (1 - ‖v‖ ^ 2) := by
      simp only [
        identitySpecialOrthogonalNorthPoleInverseVector_castSucc,
        identitySpecialOrthogonalNorthPoleInverseVector_last]
      rw [← PiLp.norm_sq_eq_of_L2]
      simp [identitySpecialOrthogonalNorthPoleFinalCoordinate,
        Real.norm_eq_abs, sq_abs, Real.sq_sqrt hpos.le]
    _ = 1 := by ring
    _ = 1 ^ 2 := by norm_num

theorem continuous_identitySpecialOrthogonalNorthPoleInverseVector (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleInverseVector n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
  apply continuous_pi
  intro j
  cases j using Fin.lastCases with
  | last =>
      have h : Continuous (fun v : EuclideanSpace ℝ (Fin n) =>
          Real.sqrt (1 - ‖v‖ ^ 2)) :=
        Real.continuous_sqrt.comp
          ((continuous_const :
          Continuous (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))).sub
            (continuous_norm.pow 2))
      simpa [identitySpecialOrthogonalNorthPoleInverseVector,
        identitySpecialOrthogonalNorthPoleFinalCoordinate] using h
  | cast i =>
      have h : Continuous (fun v : EuclideanSpace ℝ (Fin n) => v i) :=
        PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i
      simpa [identitySpecialOrthogonalNorthPoleInverseVector] using h

theorem contDiffOn_identitySpecialOrthogonalNorthPoleInverseVector
    (n : ℕ) :
    ContDiffOn ℝ ∞ (identitySpecialOrthogonalNorthPoleInverseVector n)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [contDiffOn_piLp]
  intro j
  cases j using Fin.lastCases with
  | last =>
      have h : ContDiffOn ℝ ∞
          (fun v : EuclideanSpace ℝ (Fin n) =>
            Real.sqrt (1 - ‖v‖ ^ 2))
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
        apply
          (contDiffOn_const.sub
          (contDiff_norm_sq ℝ).contDiffOn).sqrt
        intro v hv
        have hpos :=
          identitySpecialOrthogonalNorthPoleFinalCoordinate_pos hv
        have harg : 0 < 1 - ‖v‖ ^ 2 :=
          Real.sqrt_pos.mp (by
            simpa [identitySpecialOrthogonalNorthPoleFinalCoordinate] using hpos)
        exact harg.ne'
      simpa [identitySpecialOrthogonalNorthPoleInverseVector,
        identitySpecialOrthogonalNorthPoleFinalCoordinate] using h
  | cast i =>
      have h : ContDiffOn ℝ ∞
          (fun v : EuclideanSpace ℝ (Fin n) => v i)
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
        contDiffOn_piLp_apply (𝕜 := ℝ) (p := 2)
      simpa [identitySpecialOrthogonalNorthPoleInverseVector] using h

/-- The square-root lift from the open coordinate ball to the unit sphere. -/
def identitySpecialOrthogonalNorthPoleInverse
    (n : ℕ) (v : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    identitySpecialOrthogonalLastColumnSphere n :=
  ⟨identitySpecialOrthogonalNorthPoleInverseVector n v.1, by
    rw [Metric.mem_sphere, dist_zero_right,
      norm_identitySpecialOrthogonalNorthPoleInverseVector n v.1 v.2]⟩

@[simp]
theorem coe_identitySpecialOrthogonalNorthPoleInverse
    (n : ℕ) (v : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (identitySpecialOrthogonalNorthPoleInverse n v :
      EuclideanSpace ℝ (Fin (n + 1))) =
        identitySpecialOrthogonalNorthPoleInverseVector n v.1 :=
  rfl

theorem identitySpecialOrthogonalNorthPoleInverse_mem_hemisphere
    (n : ℕ) (v : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    identitySpecialOrthogonalNorthPoleInverse n v ∈
      identitySpecialOrthogonalNorthPoleHemisphere n := by
  change 0 <
    identitySpecialOrthogonalNorthPoleInverseVector n v.1 (Fin.last n)
  rw [identitySpecialOrthogonalNorthPoleInverseVector_last]
  exact identitySpecialOrthogonalNorthPoleFinalCoordinate_pos v.2

theorem identitySpecialOrthogonalNorthPoleCoordinate_inverse
    (n : ℕ) (v : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    identitySpecialOrthogonalNorthPoleCoordinate n
        (identitySpecialOrthogonalNorthPoleInverse n v) = v.1 := by
  ext i
  simp [identitySpecialOrthogonalNorthPoleCoordinate]

theorem identitySpecialOrthogonalNorthPoleFinalCoordinate_coordinate
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere n)
    (hx : x ∈ identitySpecialOrthogonalNorthPoleHemisphere n) :
    identitySpecialOrthogonalNorthPoleFinalCoordinate
        (identitySpecialOrthogonalNorthPoleCoordinate n x) =
      x.1 (Fin.last n) := by
  rw [identitySpecialOrthogonalNorthPoleFinalCoordinate]
  have hsquare :
      1 - ‖identitySpecialOrthogonalNorthPoleCoordinate n x‖ ^ 2 =
        x.1 (Fin.last n) ^ 2 := by
    nlinarith [
      identitySpecialOrthogonalNorthPoleCoordinate_norm_sq_add_last_sq n x]
  rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_pos hx]

theorem identitySpecialOrthogonalNorthPoleInverse_coordinate
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere n)
    (hx : x ∈ identitySpecialOrthogonalNorthPoleHemisphere n) :
    identitySpecialOrthogonalNorthPoleInverseVector n
        (identitySpecialOrthogonalNorthPoleCoordinate n x) = x.1 := by
  ext j
  cases j using Fin.lastCases with
  | last =>
      rw [identitySpecialOrthogonalNorthPoleInverseVector_last,
        identitySpecialOrthogonalNorthPoleFinalCoordinate_coordinate n x hx]
  | cast i =>
      rw [identitySpecialOrthogonalNorthPoleInverseVector_castSucc,
        identitySpecialOrthogonalNorthPoleCoordinate_apply]

theorem continuous_identitySpecialOrthogonalNorthPoleInverse (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleInverse n) :=
  ((continuous_identitySpecialOrthogonalNorthPoleInverseVector n).comp
    continuous_subtype_val).subtype_mk _

theorem identitySpecialOrthogonalNorthPole_mem_hemisphere (n : ℕ) :
    identitySpecialOrthogonalNorthPole n ∈
      identitySpecialOrthogonalNorthPoleHemisphere n := by
  change 0 <
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      (Fin.last n) (Fin.last n)
  simp

@[simp]
theorem identitySpecialOrthogonalNorthPoleCoordinate_northPole (n : ℕ) :
    identitySpecialOrthogonalNorthPoleCoordinate n
        (identitySpecialOrthogonalNorthPole n) = 0 := by
  ext i
  simp [identitySpecialOrthogonalNorthPoleCoordinate,
    identitySpecialOrthogonalNorthPole,
    identitySpecialOrthogonalLastColumn,
    identitySpecialOrthogonalLastColumnVector, Matrix.one_apply,
    Fin.castSucc_ne_last]

/-- The ambient north-pole coordinate map has its defining continuous linear
map as derivative at every point. -/
theorem hasFDerivAt_identitySpecialOrthogonalNorthPoleCoordinateLinearMap
    (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    HasFDerivAt
      (identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n)
      (identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n) x :=
  (identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n).hasFDerivAt

/-- At the north pole, the coordinate derivative is the nonfinal-coordinate
projection. -/
theorem fderiv_identitySpecialOrthogonalNorthPoleCoordinateLinearMap_northPole
    (n : ℕ) :
    fderiv ℝ
        (identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n)
        (identitySpecialOrthogonalNorthPole n).1 =
      identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n :=
  (hasFDerivAt_identitySpecialOrthogonalNorthPoleCoordinateLinearMap n
    (identitySpecialOrthogonalNorthPole n).1).fderiv

/-- Forgetting the Euclidean `L2` structure after the north-pole coordinate
projection gives the standard plain `Fin n -> ℝ` coordinate map. -/
theorem identitySpecialOrthogonalNorthPoleCoordinate_plain
    (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
        (identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n x) =
      fun i => x i.castSucc :=
  rfl

/-- The plain-function version of the nonfinal-coordinate projection used by
the tangent decomposition. -/
noncomputable def
    identitySpecialOrthogonalNorthPolePlainCoordinateContinuousLinearMap
    (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] (Fin n → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin n => ℝ)).toContinuousLinearMap.comp
      (identitySpecialOrthogonalNorthPoleCoordinateContinuousLinearMap n)

@[simp]
theorem
    identitySpecialOrthogonalNorthPolePlainCoordinateContinuousLinearMap_apply
    (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    identitySpecialOrthogonalNorthPolePlainCoordinateContinuousLinearMap n x i =
      x i.castSucc :=
  rfl

/-- In the plain coordinates used by the tangent split, the derivative at the
north pole is exactly nonfinal-coordinate projection. -/
theorem
    fderiv_identitySpecialOrthogonalNorthPolePlainCoordinate_northPole
    (n : ℕ) :
    fderiv ℝ
        (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          fun i : Fin n => x i.castSucc)
        (identitySpecialOrthogonalNorthPole n).1 =
      identitySpecialOrthogonalNorthPolePlainCoordinateContinuousLinearMap n :=
  (identitySpecialOrthogonalNorthPolePlainCoordinateContinuousLinearMap n).hasFDerivAt.fderiv

/-- North-pole coordinates of the last-column map are exactly its
nonfinal matrix entries. -/
theorem identitySpecialOrthogonalNorthPoleCoordinate_lastColumn
    (n : ℕ) (g : identitySpecialOrthogonalGroup n) :
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
        (identitySpecialOrthogonalNorthPoleCoordinate n
          (identitySpecialOrthogonalLastColumn n g)) =
      fun i => g.1.1.1 i.castSucc (Fin.last n) :=
  rfl

/-- Positive-hemisphere coordinates as a homeomorphism with the open
Euclidean unit ball. -/
def identitySpecialOrthogonalNorthPoleCoordinateHomeomorph
    (n : ℕ) :
    (identitySpecialOrthogonalNorthPoleHemisphere n :
      Set (identitySpecialOrthogonalLastColumnSphere n)) ≃ₜ
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 where
  toFun x :=
    ⟨identitySpecialOrthogonalNorthPoleCoordinate n x.1,
      identitySpecialOrthogonalNorthPoleCoordinate_mem_ball n x.1 x.2⟩
  invFun v :=
    ⟨identitySpecialOrthogonalNorthPoleInverse n v,
      identitySpecialOrthogonalNorthPoleInverse_mem_hemisphere n v⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact identitySpecialOrthogonalNorthPoleInverse_coordinate n x.1 x.2
  right_inv v := by
    apply Subtype.ext
    exact identitySpecialOrthogonalNorthPoleCoordinate_inverse n v
  continuous_toFun :=
    ((continuous_identitySpecialOrthogonalNorthPoleCoordinate n).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_identitySpecialOrthogonalNorthPoleInverse n).subtype_mk _

end PositiveDefiniteIntegralLattice
