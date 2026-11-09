import SMSFormula.SpecialOrthogonalRealIdentityNorthPoleCoordinates

/-!
# A local special-orthogonal section over the north-pole coordinate ball
-/

open scoped Matrix Matrix.Norms.Operator ContDiff

noncomputable section

open Metric Set

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 200000

def identitySpecialOrthogonalNorthPoleSectionMatrix
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j =>
    Fin.lastCases
      (Fin.lastCases
        (identitySpecialOrthogonalNorthPoleFinalCoordinate v)
        (fun j => -v j) j)
      (fun i =>
        Fin.lastCases
          (v i)
          (fun j =>
            (1 : Matrix (Fin n) (Fin n) ℝ) i j -
              v i * v j /
                (1 + identitySpecialOrthogonalNorthPoleFinalCoordinate v))
          j)
      i

@[simp]
theorem identitySpecialOrthogonalNorthPoleSectionMatrix_castSucc_castSucc
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    identitySpecialOrthogonalNorthPoleSectionMatrix n v i.castSucc j.castSucc =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j -
        v i * v j /
          (1 + identitySpecialOrthogonalNorthPoleFinalCoordinate v) := by
  simp [identitySpecialOrthogonalNorthPoleSectionMatrix]

@[simp]
theorem identitySpecialOrthogonalNorthPoleSectionMatrix_castSucc_last
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    identitySpecialOrthogonalNorthPoleSectionMatrix n v i.castSucc (Fin.last n) =
      v i := by
  simp [identitySpecialOrthogonalNorthPoleSectionMatrix]

@[simp]
theorem identitySpecialOrthogonalNorthPoleSectionMatrix_last_castSucc
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    identitySpecialOrthogonalNorthPoleSectionMatrix n v (Fin.last n) j.castSucc =
      -v j := by
  simp [identitySpecialOrthogonalNorthPoleSectionMatrix]

@[simp]
theorem identitySpecialOrthogonalNorthPoleSectionMatrix_last_last
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    identitySpecialOrthogonalNorthPoleSectionMatrix n v (Fin.last n) (Fin.last n) =
      identitySpecialOrthogonalNorthPoleFinalCoordinate v := by
  simp [identitySpecialOrthogonalNorthPoleSectionMatrix]

theorem identitySpecialOrthogonalNorthPoleFinalCoordinate_sq_add_norm_sq
    {n : ℕ} {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    identitySpecialOrthogonalNorthPoleFinalCoordinate v ^ 2 + ‖v‖ ^ 2 = 1 := by
  have hpos : 0 < 1 - ‖v‖ ^ 2 := by
    rw [Metric.mem_ball, dist_zero_right] at hv
    nlinarith [norm_nonneg v,
      (sq_lt_sq₀ (norm_nonneg v) zero_le_one).2 hv]
  rw [identitySpecialOrthogonalNorthPoleFinalCoordinate,
    Real.sq_sqrt hpos.le]
  ring

theorem identitySpecialOrthogonalNorthPoleSectionDenominator_pos
    {n : ℕ} {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    0 < 1 + identitySpecialOrthogonalNorthPoleFinalCoordinate v := by
  have ht := identitySpecialOrthogonalNorthPoleFinalCoordinate_pos hv
  linarith

theorem identitySpecialOrthogonalNorthPoleSectionMatrix_transpose_mul_self
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (identitySpecialOrthogonalNorthPoleSectionMatrix n v)ᵀ *
        identitySpecialOrthogonalNorthPoleSectionMatrix n v = 1 := by
  classical
  let t := identitySpecialOrthogonalNorthPoleFinalCoordinate v
  have hd : 1 + t ≠ 0 := by
    exact (identitySpecialOrthogonalNorthPoleSectionDenominator_pos hv).ne'
  have ht : t ^ 2 + ‖v‖ ^ 2 = 1 :=
    identitySpecialOrthogonalNorthPoleFinalCoordinate_sq_add_norm_sq hv
  dsimp [t] at hd ht
  have hd2 :
      1 + identitySpecialOrthogonalNorthPoleFinalCoordinate v * 2 +
          identitySpecialOrthogonalNorthPoleFinalCoordinate v ^ 2 ≠ 0 := by
    have hpos :=
      identitySpecialOrthogonalNorthPoleSectionDenominator_pos hv
    nlinarith
  have hnorm_sq :
      ‖v‖ ^ 2 =
        1 - identitySpecialOrthogonalNorthPoleFinalCoordinate v ^ 2 := by
    nlinarith [ht]
  have hsum : (∑ k : Fin n, v k * v k) = ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro k _
    simp [Real.norm_eq_abs, pow_two]
  have hsum_sq : (∑ k : Fin n, v k ^ 2) = ‖v‖ ^ 2 := by
    simpa [pow_two] using hsum
  have hsum_sq_mul (a b : ℝ) :
      (∑ k : Fin n, a * v k ^ 2 * b) = a * ‖v‖ ^ 2 * b := by
    calc
      (∑ k : Fin n, a * v k ^ 2 * b) =
          a * (∑ k : Fin n, v k ^ 2 * b) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = a * ((∑ k : Fin n, v k ^ 2) * b) := by
            rw [Finset.sum_mul]
      _ = a * ‖v‖ ^ 2 * b := by rw [hsum_sq]; ring
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp only [Matrix.transpose_apply,
            identitySpecialOrthogonalNorthPoleSectionMatrix_castSucc_last,
            identitySpecialOrthogonalNorthPoleSectionMatrix_last_last]
          rw [hsum]
          simp only [Matrix.one_apply, if_pos]
          nlinarith
      | cast j =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp only [Matrix.transpose_apply,
            identitySpecialOrthogonalNorthPoleSectionMatrix_castSucc_last,
            identitySpecialOrthogonalNorthPoleSectionMatrix_castSucc_castSucc,
            identitySpecialOrthogonalNorthPoleSectionMatrix_last_last,
            identitySpecialOrthogonalNorthPoleSectionMatrix_last_castSucc]
          rw [Matrix.one_apply, if_neg (Fin.castSucc_ne_last j).symm]
          simp [Matrix.one_apply, div_eq_mul_inv]
          ring_nf
          simp only [Finset.sum_sub_distrib]
          simp
          ring_nf
          rw [hsum_sq_mul]
          field_simp [hd, hd2]
          rw [hnorm_sq]
          ring
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp only [Matrix.transpose_apply,
            identitySpecialOrthogonalNorthPoleSectionMatrix_castSucc_castSucc,
            identitySpecialOrthogonalNorthPoleSectionMatrix_castSucc_last,
            identitySpecialOrthogonalNorthPoleSectionMatrix_last_castSucc,
            identitySpecialOrthogonalNorthPoleSectionMatrix_last_last]
          rw [Matrix.one_apply, if_neg (Fin.castSucc_ne_last i)]
          simp [Matrix.one_apply, div_eq_mul_inv]
          ring_nf
          simp only [Finset.sum_sub_distrib]
          simp
          ring_nf
          rw [hsum_sq_mul]
          field_simp [hd, hd2]
          rw [hnorm_sq]
          ring
      | cast j =>
          rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp only [Matrix.transpose_apply,
            identitySpecialOrthogonalNorthPoleSectionMatrix_castSucc_castSucc,
            identitySpecialOrthogonalNorthPoleSectionMatrix_last_castSucc]
          rw [Matrix.one_apply]
          by_cases hij : i = j
          · subst j
            simp [Matrix.one_apply, div_eq_mul_inv]
            ring_nf
            simp only [Finset.sum_add_distrib]
            simp
            ring_nf
            rw [hsum_sq_mul]
            field_simp [hd, hd2]
            rw [hnorm_sq]
            ring
          · have hji : ¬j = i := fun h => hij h.symm
            simp [Matrix.one_apply, hij, div_eq_mul_inv]
            ring_nf
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp [hji]
            ring_nf
            rw [hsum_sq_mul]
            field_simp [hd, hd2]
            rw [hnorm_sq]
            ring

@[simp]
theorem identitySpecialOrthogonalNorthPoleSectionMatrix_zero (n : ℕ) :
    identitySpecialOrthogonalNorthPoleSectionMatrix n 0 = 1 := by
  classical
  ext i j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last =>
          simp [identitySpecialOrthogonalNorthPoleFinalCoordinate]
      | cast j =>
          rw [identitySpecialOrthogonalNorthPoleSectionMatrix_last_castSucc]
          rw [Matrix.one_apply, if_neg (Fin.castSucc_ne_last j).symm]
          simp
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          rw [identitySpecialOrthogonalNorthPoleSectionMatrix_castSucc_last]
          rw [Matrix.one_apply, if_neg (Fin.castSucc_ne_last i)]
          simp
      | cast j =>
          simp [identitySpecialOrthogonalNorthPoleFinalCoordinate,
            Matrix.one_apply]

theorem continuous_identitySpecialOrthogonalNorthPoleFinalCoordinate
    (n : ℕ) :
    Continuous
      (identitySpecialOrthogonalNorthPoleFinalCoordinate :
        EuclideanSpace ℝ (Fin n) → ℝ) :=
  Real.continuous_sqrt.comp
    ((continuous_const :
      Continuous (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))).sub
      (continuous_norm.pow 2))

theorem continuous_identitySpecialOrthogonalNorthPoleSectionMatrix
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalNorthPoleSectionMatrix n) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last =>
          simpa [identitySpecialOrthogonalNorthPoleSectionMatrix] using
            continuous_identitySpecialOrthogonalNorthPoleFinalCoordinate n
      | cast j =>
          simpa [identitySpecialOrthogonalNorthPoleSectionMatrix] using
            (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).neg
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          simpa [identitySpecialOrthogonalNorthPoleSectionMatrix] using
            PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i
      | cast j =>
          have hdiv : Continuous
              (fun v : EuclideanSpace ℝ (Fin n) =>
                v i * v j /
                  (1 + identitySpecialOrthogonalNorthPoleFinalCoordinate v)) := by
            apply Continuous.div
            · exact
                (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).mul
                  (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)
            · exact continuous_const.add
                (continuous_identitySpecialOrthogonalNorthPoleFinalCoordinate n)
            · intro v
              have hsqrt :
                  0 ≤ identitySpecialOrthogonalNorthPoleFinalCoordinate v :=
                Real.sqrt_nonneg _
              linarith
          simpa [identitySpecialOrthogonalNorthPoleSectionMatrix] using
            (continuous_const.sub hdiv)

theorem contDiffOn_identitySpecialOrthogonalNorthPoleFinalCoordinate
    (n : ℕ) :
    ContDiffOn ℝ ∞
      (identitySpecialOrthogonalNorthPoleFinalCoordinate :
        EuclideanSpace ℝ (Fin n) → ℝ)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  apply
    (contDiffOn_const.sub
      (contDiff_norm_sq ℝ).contDiffOn).sqrt
  intro v hv
  have hpos :=
    identitySpecialOrthogonalNorthPoleFinalCoordinate_pos hv
  exact (Real.sqrt_pos.mp (by
    simpa [identitySpecialOrthogonalNorthPoleFinalCoordinate] using hpos)).ne'

/-- Flatten a real matrix to a function on pairs of indices. -/
def identitySpecialOrthogonalMatrixFlattenLinearEquiv (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ≃ₗ[ℝ]
      (Fin (n + 1) × Fin (n + 1) → ℝ) where
  toFun A ij := A ij.1 ij.2
  invFun f i j := f (i, j)
  left_inv A := by ext i j; rfl
  right_inv f := by ext ij; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contDiffOn_identitySpecialOrthogonalNorthPoleSectionMatrix
    (n : ℕ) :
    ContDiffOn ℝ ∞ (identitySpecialOrthogonalNorthPoleSectionMatrix n)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  classical
  let e :=
    (identitySpecialOrthogonalMatrixFlattenLinearEquiv n).toContinuousLinearEquiv
  rw [← e.comp_contDiffOn_iff]
  rw [contDiffOn_pi]
  intro ij
  rcases ij with ⟨i, j⟩
  change ContDiffOn ℝ ∞
    (fun v => identitySpecialOrthogonalNorthPoleSectionMatrix n v i j)
    (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last =>
          simpa [identitySpecialOrthogonalNorthPoleSectionMatrix] using
            contDiffOn_identitySpecialOrthogonalNorthPoleFinalCoordinate n
      | cast j =>
          simpa [identitySpecialOrthogonalNorthPoleSectionMatrix] using
            (contDiffOn_piLp_apply (𝕜 := ℝ) (p := 2) :
              ContDiffOn ℝ ∞
                (fun v : EuclideanSpace ℝ (Fin n) => v j)
                (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).neg
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          simpa [identitySpecialOrthogonalNorthPoleSectionMatrix] using
            (contDiffOn_piLp_apply (𝕜 := ℝ) (p := 2) :
              ContDiffOn ℝ ∞
                (fun v : EuclideanSpace ℝ (Fin n) => v i)
                (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      | cast j =>
          have hi : ContDiffOn ℝ ∞
              (fun v : EuclideanSpace ℝ (Fin n) => v i)
              (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
            contDiffOn_piLp_apply (𝕜 := ℝ) (p := 2)
          have hj : ContDiffOn ℝ ∞
              (fun v : EuclideanSpace ℝ (Fin n) => v j)
              (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
            contDiffOn_piLp_apply (𝕜 := ℝ) (p := 2)
          have hdiv : ContDiffOn ℝ ∞
              (fun v : EuclideanSpace ℝ (Fin n) =>
                v i * v j /
                  (1 + identitySpecialOrthogonalNorthPoleFinalCoordinate v))
              (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
            apply (hi.mul hj).div
              (contDiffOn_const.add
                (contDiffOn_identitySpecialOrthogonalNorthPoleFinalCoordinate n))
            intro v hv
            exact
              (identitySpecialOrthogonalNorthPoleSectionDenominator_pos hv).ne'
          simpa [identitySpecialOrthogonalNorthPoleSectionMatrix] using
            (contDiffOn_const.sub hdiv)

theorem identitySpecialOrthogonalNorthPoleSectionMatrix_det_sq
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (identitySpecialOrthogonalNorthPoleSectionMatrix n v).det ^ 2 = 1 := by
  have hdet := congrArg Matrix.det
    (identitySpecialOrthogonalNorthPoleSectionMatrix_transpose_mul_self n v hv)
  simpa [Matrix.det_mul, Matrix.det_transpose, pow_two] using hdet

theorem identitySpecialOrthogonalNorthPoleSectionMatrix_det
    (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (identitySpecialOrthogonalNorthPoleSectionMatrix n v).det = 1 := by
  classical
  let f : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun w => (identitySpecialOrthogonalNorthPoleSectionMatrix n w).det
  have hf : Continuous f :=
    (continuous_identitySpecialOrthogonalNorthPoleSectionMatrix n).matrix_det
  have hsq : Set.EqOn (f ^ 2) 1
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    intro w hw
    exact identitySpecialOrthogonalNorthPoleSectionMatrix_det_sq n w hw
  rcases Metric.isPreconnected_ball.eq_one_or_eq_neg_one_of_sq_eq
      hf.continuousOn hsq with hpos | hneg
  · exact hpos hv
  · have hzero :
        (0 : EuclideanSpace ℝ (Fin n)) ∈
          Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by simp
    have := hneg hzero
    norm_num [f] at this

/-- The explicit orientation-preserving orthogonal section over the north-pole
coordinate ball. -/
def identitySpecialOrthogonalNorthPoleSection
    (n : ℕ) (v : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    identitySpecialOrthogonalGroup n := by
  let A := identitySpecialOrthogonalNorthPoleSectionMatrix n v.1
  let Aset : Matrix.specialOrthogonalMatrixSet
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
    ⟨A,
      (Matrix.formPreservingConstraint_eq_zero_iff _ _).mpr
        (by
          have h :=
            identitySpecialOrthogonalNorthPoleSectionMatrix_transpose_mul_self
              n v.1 v.2
          change Aᵀ * 1 * A = 1
          simpa [A] using h),
      identitySpecialOrthogonalNorthPoleSectionMatrix_det n v.1 v.2⟩
  exact specialOrthogonalMatrixSetToSpecialSubgroup _ Aset

@[simp]
theorem coe_identitySpecialOrthogonalNorthPoleSection
    (n : ℕ) (v : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (identitySpecialOrthogonalNorthPoleSection n v).1.1.1 =
      identitySpecialOrthogonalNorthPoleSectionMatrix n v.1 :=
  rfl

theorem identitySpecialOrthogonalLastColumn_northPoleSection
    (n : ℕ) (v : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    identitySpecialOrthogonalLastColumn n
        (identitySpecialOrthogonalNorthPoleSection n v) =
      identitySpecialOrthogonalNorthPoleInverse n v := by
  apply Subtype.ext
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp [identitySpecialOrthogonalLastColumn,
        identitySpecialOrthogonalLastColumnVector]
  | cast i =>
      simp [identitySpecialOrthogonalLastColumn,
        identitySpecialOrthogonalLastColumnVector]

@[simp]
theorem identitySpecialOrthogonalNorthPoleSection_zero (n : ℕ) :
    identitySpecialOrthogonalNorthPoleSection n
        ⟨0, by simp⟩ = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change
    (identitySpecialOrthogonalNorthPoleSection n ⟨0, by simp⟩).1.1.1 =
      (1 : identitySpecialOrthogonalGroup n).1.1.1
  rw [coe_identitySpecialOrthogonalNorthPoleSection]
  exact identitySpecialOrthogonalNorthPoleSectionMatrix_zero n

end PositiveDefiniteIntegralLattice
