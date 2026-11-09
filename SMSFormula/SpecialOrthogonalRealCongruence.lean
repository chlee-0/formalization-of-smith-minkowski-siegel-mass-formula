import SMSFormula.SkewAdjointCongruenceNormalization

/-!
# Congruence transport of real special-orthogonal groups

A rational matrix unit `W` sends the real special-orthogonal group of `F` to
that of `Wᵀ F W` by conjugation. This module packages that map as a continuous
multiplicative equivalence and isolates the global Haar scalar whose
identification with the explicit tangent determinant from
`SkewAdjointCongruenceNormalization` remains a cross-form chart theorem.

No gamma integral or reference-Haar normalization is used here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance realCongruenceSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance realCongruenceSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

/-- A rational matrix unit viewed over the real numbers. -/
def rationalMatrixUnitReal (W : GL (Fin n) ℚ) : GL (Fin n) ℝ :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) W

@[simp]
theorem coe_rationalMatrixUnitReal
    (W : GL (Fin n) ℚ) :
    (rationalMatrixUnitReal W : Matrix (Fin n) (Fin n) ℝ) =
      (W : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ ℝ) := by
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply (algebraMap ℚ ℝ) i j W

/-- Scalar extension commutes with rational congruence of the form matrix. -/
theorem map_skewAdjointCongruenceForm_real
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    (Matrix.skewAdjointCongruenceForm F W).map (algebraMap ℚ ℝ) =
      (rationalMatrixUnitReal W : Matrix (Fin n) (Fin n) ℝ)ᵀ *
        F.map (algebraMap ℚ ℝ) *
        (rationalMatrixUnitReal W : Matrix (Fin n) (Fin n) ℝ) := by
  simp [Matrix.skewAdjointCongruenceForm, Matrix.map_mul,
    Matrix.transpose_map]

/-- Congruence by a matrix unit preserves symmetry of a rational form. -/
theorem skewAdjointCongruenceForm_isSymm
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (W : GL (Fin n) ℚ) :
    (Matrix.skewAdjointCongruenceForm F W).IsSymm := by
  rw [Matrix.IsSymm]
  simp [Matrix.skewAdjointCongruenceForm, Matrix.transpose_mul,
    hF.eq, Matrix.mul_assoc]

/-- Congruence by a matrix unit preserves nonsingularity of a rational
form. -/
theorem skewAdjointCongruenceForm_det_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    (Matrix.skewAdjointCongruenceForm F W).det ≠ 0 := by
  have hW : (W : Matrix (Fin n) (Fin n) ℚ).det ≠ 0 := by
    exact Units.ne_zero (Matrix.GeneralLinearGroup.det W)
  simp only [Matrix.skewAdjointCongruenceForm, Matrix.det_mul,
    Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero hW hdet) hW

/-- Conjugation by a rational matrix unit, restricted to the two real
special-orthogonal carriers of congruent forms. -/
def specialFormPreservingRealCongruenceContinuousMulEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ)) ≃ₜ*
      specialFormPreservingMatrixSubgroup
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ)) where
  toFun g := by
    let U := rationalMatrixUnitReal W
    let UM : Matrix (Fin n) (Fin n) ℝ := U
    let UiM : Matrix (Fin n) (Fin n) ℝ := (U⁻¹ : GL (Fin n) ℝ)
    let A : GL (Fin n) ℝ := U⁻¹ * g.1.1 * U
    have hA :
        A ∈ formPreservingMatrixSubgroup
          ((Matrix.skewAdjointCongruenceForm F W).map
            (algebraMap ℚ ℝ)) := by
      rw [mem_formPreservingMatrixSubgroup_iff,
        map_skewAdjointCongruenceForm_real]
      have hg := g.1.2
      rw [mem_formPreservingMatrixSubgroup_iff] at hg
      have hUU : UM * UiM = 1 := by
        change (U * U⁻¹ : GL (Fin n) ℝ).1 = 1
        simp
      have hUiU : UiM * UM = 1 := by
        change (U⁻¹ * U : GL (Fin n) ℝ).1 = 1
        simp
      have hUUi : UM * UiM = 1 := by
        change (U * U⁻¹ : GL (Fin n) ℝ).1 = 1
        simp
      have hUiTUT :
          UiMᵀ * UMᵀ = 1 := by
        rw [← Matrix.transpose_mul, hUU, Matrix.transpose_one]
      change
        (UiM *
              (g.1.1 : Matrix (Fin n) (Fin n) ℝ) *
              UM)ᵀ *
            (UMᵀ *
              F.map (algebraMap ℚ ℝ) *
              UM) *
            (UiM *
              (g.1.1 : Matrix (Fin n) (Fin n) ℝ) *
              UM) =
          UMᵀ *
            F.map (algebraMap ℚ ℝ) *
            UM
      calc
        _ = UMᵀ *
            (g.1.1 : Matrix (Fin n) (Fin n) ℝ)ᵀ *
            (UiMᵀ * UMᵀ) *
            F.map (algebraMap ℚ ℝ) *
            (UM * UiM) *
            (g.1.1 : Matrix (Fin n) (Fin n) ℝ) *
            UM := by
              simp only [Matrix.transpose_mul]
              noncomm_ring
        _ = UMᵀ *
            ((g.1.1 : Matrix (Fin n) (Fin n) ℝ)ᵀ *
              F.map (algebraMap ℚ ℝ) *
              (g.1.1 : Matrix (Fin n) (Fin n) ℝ)) *
            UM := by
              rw [hUiTUT, hUU]
              simp [Matrix.mul_assoc]
        _ = _ := by rw [hg]
    let og :
        formPreservingMatrixSubgroup
          ((Matrix.skewAdjointCongruenceForm F W).map
            (algebraMap ℚ ℝ)) :=
      ⟨A, hA⟩
    refine ⟨og, (mem_specialFormPreservingMatrixSubgroup_iff _ og).mpr ?_⟩
    have hgdet :=
      (mem_specialFormPreservingMatrixSubgroup_iff
        (F.map (algebraMap ℚ ℝ)) g.1).mp g.2
    change
      (UiM *
        (g.1.1 : Matrix (Fin n) (Fin n) ℝ) *
        UM).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, hgdet, mul_one,
      ← Matrix.det_mul]
    rw [show UiM * UM = 1 by
      change (U⁻¹ * U : GL (Fin n) ℝ).1 = 1
      simp, Matrix.det_one]
  invFun h := by
    let U := rationalMatrixUnitReal W
    let UM : Matrix (Fin n) (Fin n) ℝ := U
    let UiM : Matrix (Fin n) (Fin n) ℝ := (U⁻¹ : GL (Fin n) ℝ)
    let A : GL (Fin n) ℝ := U * h.1.1 * U⁻¹
    have hA : A ∈
        formPreservingMatrixSubgroup
          (F.map (algebraMap ℚ ℝ)) := by
      rw [mem_formPreservingMatrixSubgroup_iff]
      have hh := h.1.2
      rw [mem_formPreservingMatrixSubgroup_iff] at hh
      have hUiU : UiM * UM = 1 := by
        change (U⁻¹ * U : GL (Fin n) ℝ).1 = 1
        simp
      have hUUi : UM * UiM = 1 := by
        change (U * U⁻¹ : GL (Fin n) ℝ).1 = 1
        simp
      have hUTUiT :
          UMᵀ * UiMᵀ = 1 := by
        rw [← Matrix.transpose_mul, hUiU, Matrix.transpose_one]
      have hUiTUT :
          UiMᵀ * UMᵀ = 1 := by
        rw [← Matrix.transpose_mul, hUUi, Matrix.transpose_one]
      change
        (UM *
              (h.1.1 : Matrix (Fin n) (Fin n) ℝ) *
              UiM)ᵀ *
            F.map (algebraMap ℚ ℝ) *
            (UM *
              (h.1.1 : Matrix (Fin n) (Fin n) ℝ) *
              UiM) =
          F.map (algebraMap ℚ ℝ)
      have hcore :
          (h.1.1 : Matrix (Fin n) (Fin n) ℝ)ᵀ *
              (UMᵀ *
                F.map (algebraMap ℚ ℝ) *
                UM) *
              (h.1.1 : Matrix (Fin n) (Fin n) ℝ) =
            UMᵀ *
              F.map (algebraMap ℚ ℝ) *
              UM := by
        rw [← map_skewAdjointCongruenceForm_real F W]
        exact hh
      calc
        _ = UiMᵀ *
            ((h.1.1 : Matrix (Fin n) (Fin n) ℝ)ᵀ *
              (UMᵀ *
                F.map (algebraMap ℚ ℝ) *
                UM) *
              (h.1.1 : Matrix (Fin n) (Fin n) ℝ)) *
            UiM := by
              simp only [Matrix.transpose_mul]
              noncomm_ring
        _ = UiMᵀ *
            (UMᵀ *
              F.map (algebraMap ℚ ℝ) *
              UM) *
            UiM := by rw [hcore]
        _ = (UiMᵀ * UMᵀ) *
            F.map (algebraMap ℚ ℝ) *
            (UM * UiM) := by noncomm_ring
        _ = _ := by rw [hUiTUT, hUUi]; simp
    let og : formPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℝ)) :=
      ⟨A, hA⟩
    refine ⟨og, (mem_specialFormPreservingMatrixSubgroup_iff _ og).mpr ?_⟩
    have hhdet :=
      (mem_specialFormPreservingMatrixSubgroup_iff
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ)) h.1).mp h.2
    change
      (UM *
        (h.1.1 : Matrix (Fin n) (Fin n) ℝ) *
        UiM).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, hhdet, mul_one,
      ← Matrix.det_mul]
    rw [show UM * UiM = 1 by
      change (U * U⁻¹ : GL (Fin n) ℝ).1 = 1
      simp, Matrix.det_one]
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    group
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    group
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    change
      (rationalMatrixUnitReal W)⁻¹ * (g.1.1 * h.1.1) *
          rationalMatrixUnitReal W =
        ((rationalMatrixUnitReal W)⁻¹ * g.1.1 *
          rationalMatrixUnitReal W) *
        ((rationalMatrixUnitReal W)⁻¹ * h.1.1 *
          rationalMatrixUnitReal W)
    group
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop

@[simp]
theorem coe_specialFormPreservingRealCongruenceContinuousMulEquiv_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ)
    (g : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℝ))) :
    ((specialFormPreservingRealCongruenceContinuousMulEquiv F W g).1.1.1 :
      Matrix (Fin n) (Fin n) ℝ) =
      (rationalMatrixUnitReal W⁻¹ : Matrix (Fin n) (Fin n) ℝ) *
        g.1.1.1 *
        (rationalMatrixUnitReal W : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

@[simp]
theorem coe_specialFormPreservingRealCongruenceContinuousMulEquiv_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ)
    (h : specialFormPreservingMatrixSubgroup
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))) :
    ((specialFormPreservingRealCongruenceContinuousMulEquiv F W).symm h).1.1.1 =
      (rationalMatrixUnitReal W : Matrix (Fin n) (Fin n) ℝ) *
        h.1.1.1 *
      (rationalMatrixUnitReal W⁻¹ : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

/-- Conjugation transports the source real differential Haar measure to a
Haar measure on the congruent target group. -/
theorem map_specialFormPreservingSmoothRealDifferentialMeasure_congruence_isHaarMeasure
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.IsHaarMeasure
      (Measure.map
        (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)) := by
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_locallyCompact F' hF' hdet'
  letI : SecondCountableTopology
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_secondCountable F'
  letI : Measure.IsHaarMeasure
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) :=
    specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
      F hF hdet
  exact
    (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toMulEquiv
      |>.isHaarMeasure_map
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)
        (specialFormPreservingRealCongruenceContinuousMulEquiv F W).continuous
        (specialFormPreservingRealCongruenceContinuousMulEquiv F W).symm.continuous

/-- The canonical Haar-uniqueness scalar comparing transported source
differential Haar with target differential Haar. Its identification with the
tangent comparison determinant is a separate chart-normalization theorem. -/
def specialFormPreservingRealCongruenceHaarScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) : ℝ≥0∞ :=
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  let e := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let μ := Measure.map e.toHomeomorph
    (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)
  let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_locallyCompact F' hF' hdet'
  letI : SecondCountableTopology
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_secondCountable F'
  letI : Measure.IsHaarMeasure μ :=
    map_specialFormPreservingSmoothRealDifferentialMeasure_congruence_isHaarMeasure
      F hF hdet W
  letI : Measure.IsHaarMeasure ν :=
    specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
      F' hF' hdet'
  Measure.haarScalarFactor μ ν

/-- Haar uniqueness compares the transported source differential measure with
the target differential measure by the canonical congruence scalar. -/
theorem map_specialFormPreservingSmoothRealDifferentialMeasure_congruence_eq_smul
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    Measure.map
        (specialFormPreservingRealCongruenceContinuousMulEquiv F W).toHomeomorph
        (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet) =
      specialFormPreservingRealCongruenceHaarScalar F hF hdet W •
        specialFormPreservingSmoothRealDifferentialMeasure
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) := by
  let F' := Matrix.skewAdjointCongruenceForm F W
  let hF' := skewAdjointCongruenceForm_isSymm F hF W
  let hdet' := skewAdjointCongruenceForm_det_ne_zero F hdet W
  let e := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let μ :=
    Measure.map e.toHomeomorph
      (specialFormPreservingSmoothRealDifferentialMeasure F hF hdet)
  let ν := specialFormPreservingSmoothRealDifferentialMeasure F' hF' hdet'
  letI : LocallyCompactSpace
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_locallyCompact F' hF' hdet'
  letI : SecondCountableTopology
      (specialFormPreservingMatrixSubgroup
        (F'.map (algebraMap ℚ ℝ))) :=
    specialFormPreservingRealGroup_secondCountable F'
  letI : Measure.IsHaarMeasure μ :=
    map_specialFormPreservingSmoothRealDifferentialMeasure_congruence_isHaarMeasure
      F hF hdet W
  letI : Measure.IsHaarMeasure ν :=
    specialFormPreservingSmoothRealDifferentialMeasure_isHaarMeasure
      F' hF' hdet'
  simpa [specialFormPreservingRealCongruenceHaarScalar, μ, ν, e, F',
    hF', hdet'] using Measure.isMulLeftInvariant_eq_smul μ ν

/-- The global comparison gives the exact total-mass relation. No
compact-group volume is used to define its scalar. -/
theorem specialFormPreservingSmoothRealDifferentialMeasure_congruence_univ
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealDifferentialMeasure F hF hdet Set.univ =
      specialFormPreservingRealCongruenceHaarScalar F hF hdet W *
        specialFormPreservingSmoothRealDifferentialMeasure
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W) Set.univ := by
  let e := specialFormPreservingRealCongruenceContinuousMulEquiv F W
  let μ := specialFormPreservingSmoothRealDifferentialMeasure F hF hdet
  have h := congrArg
    (fun μ : Measure
      (specialFormPreservingMatrixSubgroup
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))) => μ Set.univ)
    (map_specialFormPreservingSmoothRealDifferentialMeasure_congruence_eq_smul
      F hF hdet W)
  have hmap : Measure.map e.toHomeomorph μ Set.univ = μ Set.univ := by
    rw [Measure.map_apply e.measurable MeasurableSet.univ]
    simp
  change Measure.map e.toHomeomorph μ Set.univ =
    (specialFormPreservingRealCongruenceHaarScalar F hF hdet W •
      specialFormPreservingSmoothRealDifferentialMeasure
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)) Set.univ at h
  rw [hmap] at h
  simpa [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using h

end PositiveDefiniteIntegralLattice
