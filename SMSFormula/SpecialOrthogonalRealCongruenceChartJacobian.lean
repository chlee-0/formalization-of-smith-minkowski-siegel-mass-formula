import SMSFormula.SpecialOrthogonalRealCongruenceChartDifferential

/-!
# Jacobian of the real congruence-chart transition

For `F' = Wᵀ F W`, the cross-form transition has derivatives on two
equal-dimensional skew-adjoint tangent carriers.  Conjugating the target
derivative by the tangent congruence gives the fixed-source derivative.  This
module takes determinants only after those composites are endomorphisms; the
intermediate matrix-valued derivatives carry no determinants.

The explicit basis-comparison scalar of tangent congruence cancels from this
transition Jacobian by `LinearMap.det_conj`.  It remains present in the
separate coordinate-measure transport theorem.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ContDiff

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Determinant of the fixed-source derivative of the cross-form chart
transition. -/
def specialFormPreservingSmoothRealCongruenceChartSourceTransitionDeterminant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) : ℝ :=
  LinearMap.det
    (specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative
      F hF hdet W x).toLinearMap

/-- Determinant of the ambient target-carrier derivative.  This determinant
is well-typed because the full staged composite is an endomorphism of the
target skew-adjoint tangent carrier. -/
def specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDeterminant
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : (skewAdjointMatricesLieSubalgebra
      ((Matrix.skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule) : ℝ :=
  LinearMap.det
    (specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDerivative
      F hF hdet W y).toLinearMap

private theorem det_skewAdjointRealCongruence_conj
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ)
    (D : (skewAdjointMatricesLieSubalgebra
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        ((Matrix.skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule) :
    LinearMap.det
      ((Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
          F W).symm.toContinuousLinearMap.comp
        (D.comp (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
          F W).toContinuousLinearMap)).toLinearMap =
      LinearMap.det D.toLinearMap := by
  rw [← ContinuousLinearMap.comp_assoc]
  simpa only [ContinuousLinearMap.comp_assoc] using
    LinearMap.det_conj D.toLinearMap
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
        F W).symm.toLinearEquiv

/-- The fixed-source derivative is the target derivative conjugated by the
real tangent congruence equivalence. -/
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative_eq_conj
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative
        F hF hdet W x =
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
          F W).symm.toContinuousLinearMap.comp
        ((specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDerivative
          F hF hdet W
            (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W x)).comp
          (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
            F W).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative,
    specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDerivative,
    specialFormPreservingSmoothRealCongruenceChartAmbientMatrixStageDerivative,
    specialFormPreservingSmoothRealCongruenceChartAmbientInverseStageDerivative,
    specialFormPreservingSmoothRealCongruenceChartAmbientMatrixStage,
    specialFormPreservingSmoothRealCongruenceChartAmbientInverseStage,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [show
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
        F W).symm.toContinuousLinearMap
      ((Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
        F W).toContinuousLinearMap v) = v from
    (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
      F W).symm_apply_apply v]

/-- The source-model and target-model transition derivatives have the same
determinant.  In particular, the congruence basis-comparison scalar cancels
between the two conjugating maps. -/
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransitionDeterminant_eq_ambient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDeterminant
        F hF hdet W x =
      specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDeterminant
        F hF hdet W
          (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W x) := by
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransitionDeterminant,
    specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDeterminant,
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative_eq_conj,
    det_skewAdjointRealCongruence_conj]

/-- Absolute Jacobian of the fixed-source cross-form transition. -/
def specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) : ℝ :=
  |specialFormPreservingSmoothRealCongruenceChartSourceTransitionDeterminant
    F hF hdet W x|

theorem specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian_nonneg
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    0 ≤ specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian
      F hF hdet W x :=
  abs_nonneg _

/-- The absolute source Jacobian is the absolute determinant of the target
ambient transition derivative. -/
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian_eq_ambient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian
        F hF hdet W x =
      |specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDeterminant
        F hF hdet W
          (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W x)| := by
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian,
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDeterminant_eq_ambient]

/-- On the source chart target, the transition Jacobian is the absolute
determinant of the Frechet derivative. -/
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian_eq_fderiv
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealCongruenceChartSourceTransitionSmoothSet
        F hF hdet) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian
        F hF hdet W x =
      |LinearMap.det
        (fderiv ℝ
          (specialFormPreservingSmoothRealCongruenceChartSourceTransition
            F hF hdet W) x).toLinearMap| := by
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian,
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDeterminant,
    fderiv_specialFormPreservingSmoothRealCongruenceChartSourceTransition
      F hF hdet W x hx]

/-- The fixed-source transition determinant is normalized to one at the
central coordinate. -/
@[simp]
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransitionDeterminant_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDeterminant
      F hF hdet W 0 = 1 := by
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransitionDeterminant,
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDerivative_zero]
  exact LinearMap.det_id

/-- The absolute fixed-source Jacobian is normalized to one at the central
coordinate. -/
@[simp]
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian
      F hF hdet W 0 = 1 := by
  rw [specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian,
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionDeterminant_zero,
    abs_one]

private theorem fderiv_openPartialHomeomorph_symm_trans_self
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : OpenPartialHomeomorph X E) (y : E) (hy : y ∈ A.target) :
    fderiv ℝ (A.symm.trans A) y = ContinuousLinearMap.id ℝ E := by
  have hsource : y ∈ (A.symm.trans A).source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hy, A.symm.map_source hy⟩
  have heq : (A.symm.trans A : E → E) =ᶠ[nhds y] id := by
    filter_upwards [(A.symm.trans A).open_source.mem_nhds hsource] with z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    change A (A.symm z) = z
    exact A.right_inv hz.1
  rw [heq.fderiv_eq, fderiv_id]

/-- Zero belongs to the exact target of the real identity chart. -/
theorem zero_mem_specialFormPreservingSmoothRealIdentityChart_target
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    (0 : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) ∈
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target := by
  rw [specialFormPreservingSmoothTranslatedSkewAdjointOpenPartialHomeomorph_target]
  simpa only using
    Matrix.zero_mem_specialOrthogonalSmoothIdentitySkewAdjointNeighborhood
      (F.map (algebraMap ℚ ℝ)) (hF.map _)
      (by
        intro hz
        apply hdet
        exact (algebraMap ℚ ℝ).injective
          (by simpa only [map_zero] using
            (RingHom.map_det (algebraMap ℚ ℝ) F).trans hz))
      (by norm_num)

/-- The inverse real identity chart sends its central coordinate to the group
identity. -/
@[simp]
theorem specialFormPreservingSmoothRealIdentityChart_symm_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).symm
      (0 : (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule) = 1 := by
  ext i j
  have hcoe :=
    coe_specialFormPreservingSmoothRealIdentityChart_symm_eq_inverseCoordinateMatrix
      F hF hdet 0
        (zero_mem_specialFormPreservingSmoothRealIdentityChart_target
          F hF hdet)
  change
    ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm
      (0 : (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule)).1.1.1 i j =
        (1 : Matrix (Fin n) (Fin n) ℝ) i j
  simpa only [specialFormPreservingSmoothRealInverseCoordinateMatrix_zero] using
    congrFun (congrFun hcoe i) j

/-- The invariant differential density in the real identity chart is normalized
to one at its central coordinate. -/
@[simp]
theorem specialFormPreservingSmoothRealIdentityChartCoordinateDensityENNReal_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet 1
        ⟨0, zero_mem_specialFormPreservingSmoothRealIdentityChart_target
          F hF hdet⟩ =
      1 := by
  rw [specialFormPreservingSmoothRealChartCoordinateDensityENNReal,
    specialFormPreservingSmoothRealChartCoordinateDensity_eq,
    specialFormPreservingSmoothRealIdentityChart_symm_zero]
  let A := specialFormPreservingSmoothRealIdentityChart F hF hdet
  change ENNReal.ofReal |(fderiv ℝ (A.symm.trans A) 0).det| = 1
  have hderiv : fderiv ℝ (A.symm.trans A) 0 =
      ContinuousLinearMap.id ℝ
        ((skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) :=
    fderiv_openPartialHomeomorph_symm_trans_self A 0
      (zero_mem_specialFormPreservingSmoothRealIdentityChart_target
        F hF hdet)
  have hdetid :
      (ContinuousLinearMap.id ℝ
        ((skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule)).det = 1 :=
    LinearMap.det_id
  exact (congrArg
    (fun derivative :
      (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule =>
      ENNReal.ofReal |derivative.det|) hderiv).trans
        (by rw [hdetid, abs_one, ENNReal.ofReal_one])

/-- The central point of the transported congruence chart, constructed by
transporting the source identity-chart zero coordinate. -/
def specialFormPreservingSmoothRealCongruenceChartCentralTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartTarget F hF hdet W :=
  specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
    F hF hdet W
    ⟨0, zero_mem_specialFormPreservingSmoothRealIdentityChart_target
      F hF hdet⟩

/-- The underlying tangent coordinate of the transported central point is
zero. -/
@[simp]
theorem coe_specialFormPreservingSmoothRealCongruenceChartCentralTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    (specialFormPreservingSmoothRealCongruenceChartCentralTarget
      F hF hdet W).1 = 0 := by
  rw [specialFormPreservingSmoothRealCongruenceChartCentralTarget,
    coe_specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph_apply]
  exact map_zero _

/-- The transported central point lies in the exact same-point intersection
with the independently defined target-form identity chart. -/
theorem specialFormPreservingSmoothRealCongruenceChartCentralTarget_mem_overlap
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartCentralTarget F hF hdet W ∈
      specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W := by
  change
    ((specialFormPreservingSmoothRealCongruenceChartHomeomorph
      F hF hdet W).symm
        (specialFormPreservingSmoothRealCongruenceChartCentralTarget
          F hF hdet W)).1 ∈
      (specialFormPreservingSmoothRealIdentityChart
        (Matrix.skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceForm_isSymm F hF W)
        (skewAdjointCongruenceForm_det_ne_zero F hdet W)).source
  rw [
    coe_specialFormPreservingSmoothRealCongruenceChartHomeomorph_symm_apply,
    coe_specialFormPreservingSmoothRealCongruenceChartCentralTarget]
  simp only [ContinuousLinearEquiv.map_zero,
    specialFormPreservingSmoothRealIdentityChart_symm_zero, map_one]
  simpa only [specialFormPreservingSmoothRealIdentityChart_symm_zero] using
    (specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).symm.map_source
        (zero_mem_specialFormPreservingSmoothRealIdentityChart_target
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W))

/-- The ambient cross-form transition sends the transported central coordinate
to the independently defined target-form central coordinate. -/
@[simp]
theorem specialFormPreservingSmoothRealCongruenceChartAmbientTransition_central
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartAmbientTransition
        F hF hdet W
        (specialFormPreservingSmoothRealCongruenceChartCentralTarget
          F hF hdet W) =
      0 := by
  rw [specialFormPreservingSmoothRealCongruenceChartAmbientTransition,
    coe_specialFormPreservingSmoothRealCongruenceChartHomeomorph_symm_apply,
    coe_specialFormPreservingSmoothRealCongruenceChartCentralTarget]
  simp only [ContinuousLinearEquiv.map_zero,
    specialFormPreservingSmoothRealIdentityChart_symm_zero, map_one]
  let A :=
    specialFormPreservingSmoothRealIdentityChart
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  have hzero :=
    zero_mem_specialFormPreservingSmoothRealIdentityChart_target
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)
  rw [← specialFormPreservingSmoothRealIdentityChart_symm_zero
    (Matrix.skewAdjointCongruenceForm F W)
    (skewAdjointCongruenceForm_isSymm F hF W)
    (skewAdjointCongruenceForm_det_ne_zero F hdet W)]
  exact A.right_inv hzero

/-- The density on the transported target is exactly the source-form density
after inverse tangent congruence. -/
theorem specialFormPreservingSmoothRealCongruenceChartTargetDensityENNReal_eq_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget
      F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceChartTargetDensityENNReal
        F hF hdet W y =
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
        F hF hdet 1
          ((specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
            F hF hdet W).symm y) :=
  rfl

/-- At transported coordinates, the source-model Jacobian is the absolute
determinant of the ambient target transition derivative. -/
theorem specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian_symm_eq_ambient
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget
      F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian
        F hF hdet W
          ((Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
            F W).symm y.1) =
      |specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDeterminant
        F hF hdet W y.1| := by
  simpa using
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian_eq_ambient
      F hF hdet W
        ((Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm y.1)

/-- The remaining transported/standard density cocycle can be stated on the
fixed source carrier without changing its mathematical content.  This is a
pointwise reduction only; it does not assert the still-open density
compatibility. -/
theorem specialFormPreservingSmoothRealCongruenceChartDensityCocycle_iff_source
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ)
    (y : specialFormPreservingSmoothRealCongruenceChartTarget
      F hF hdet W)
    (hy :
      y ∈ specialFormPreservingSmoothRealCongruenceChartTransportedCoordinateOverlapSet
        F hF hdet W) :
    specialFormPreservingSmoothRealCongruenceChartTargetDensityENNReal
          F hF hdet W y =
        specialFormPreservingSmoothRealChartCoordinateDensityENNReal
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
            ⟨specialFormPreservingSmoothRealCongruenceChartAmbientTransition
                F hF hdet W y,
              specialFormPreservingSmoothRealCongruenceChartAmbientTransition_mem_target
                F hF hdet W y hy⟩ *
          ENNReal.ofReal
            |specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDeterminant
              F hF hdet W y.1| ↔
      specialFormPreservingSmoothRealChartCoordinateDensityENNReal
            F hF hdet 1
            ((specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
              F hF hdet W).symm y) =
        specialFormPreservingSmoothRealChartCoordinateDensityENNReal
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
            ⟨specialFormPreservingSmoothRealCongruenceChartAmbientTransition
                F hF hdet W y,
              specialFormPreservingSmoothRealCongruenceChartAmbientTransition_mem_target
                F hF hdet W y hy⟩ *
          ENNReal.ofReal
            (specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian
              F hF hdet W
                ((Matrix.skewAdjointRealCongruenceContinuousLinearEquiv
                  F W).symm y.1)) := by
  rw [specialFormPreservingSmoothRealCongruenceChartTargetDensityENNReal_eq_source,
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian_symm_eq_ambient]

/-- The transported and independently defined target-form chart densities
satisfy the exact Jacobian cocycle at their common central point. This is only
the central specialization, not compatibility on the full overlap. -/
theorem specialFormPreservingSmoothRealCongruenceChartDensityCocycle_central
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (W : GL (Fin n) ℚ) :
    specialFormPreservingSmoothRealCongruenceChartTargetDensityENNReal
          F hF hdet W
          (specialFormPreservingSmoothRealCongruenceChartCentralTarget
            F hF hdet W) =
        specialFormPreservingSmoothRealChartCoordinateDensityENNReal
            (Matrix.skewAdjointCongruenceForm F W)
            (skewAdjointCongruenceForm_isSymm F hF W)
            (skewAdjointCongruenceForm_det_ne_zero F hdet W) 1
            ⟨specialFormPreservingSmoothRealCongruenceChartAmbientTransition
                F hF hdet W
                (specialFormPreservingSmoothRealCongruenceChartCentralTarget
                  F hF hdet W),
              specialFormPreservingSmoothRealCongruenceChartAmbientTransition_mem_target
                F hF hdet W
                (specialFormPreservingSmoothRealCongruenceChartCentralTarget
                  F hF hdet W)
                (specialFormPreservingSmoothRealCongruenceChartCentralTarget_mem_overlap
                  F hF hdet W)⟩ *
          ENNReal.ofReal
            |specialFormPreservingSmoothRealCongruenceChartAmbientTransitionDeterminant
              F hF hdet W
                (specialFormPreservingSmoothRealCongruenceChartCentralTarget
                  F hF hdet W).1| := by
  apply
    (specialFormPreservingSmoothRealCongruenceChartDensityCocycle_iff_source
      F hF hdet W
      (specialFormPreservingSmoothRealCongruenceChartCentralTarget
        F hF hdet W)
      (specialFormPreservingSmoothRealCongruenceChartCentralTarget_mem_overlap
        F hF hdet W)).2
  have hsymm :
      (specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
        F hF hdet W).symm
          (specialFormPreservingSmoothRealCongruenceChartCentralTarget
            F hF hdet W) =
        ⟨0, zero_mem_specialFormPreservingSmoothRealIdentityChart_target
          F hF hdet⟩ := by
    exact
      (specialFormPreservingSmoothRealCongruenceChartTargetHomeomorph
        F hF hdet W).symm_apply_apply
          ⟨0, zero_mem_specialFormPreservingSmoothRealIdentityChart_target
            F hF hdet⟩
  have hstandard :
      (⟨specialFormPreservingSmoothRealCongruenceChartAmbientTransition
          F hF hdet W
            (specialFormPreservingSmoothRealCongruenceChartCentralTarget
              F hF hdet W),
        specialFormPreservingSmoothRealCongruenceChartAmbientTransition_mem_target
          F hF hdet W
            (specialFormPreservingSmoothRealCongruenceChartCentralTarget
              F hF hdet W)
            (specialFormPreservingSmoothRealCongruenceChartCentralTarget_mem_overlap
              F hF hdet W)⟩ :
        (specialFormPreservingSmoothRealIdentityChart
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)).target) =
        ⟨0, zero_mem_specialFormPreservingSmoothRealIdentityChart_target
          (Matrix.skewAdjointCongruenceForm F W)
          (skewAdjointCongruenceForm_isSymm F hF W)
          (skewAdjointCongruenceForm_det_ne_zero F hdet W)⟩ := by
    apply Subtype.ext
    exact
      specialFormPreservingSmoothRealCongruenceChartAmbientTransition_central
        F hF hdet W
  have hsourceCoordinate :
      (Matrix.skewAdjointRealCongruenceContinuousLinearEquiv F W).symm
          (specialFormPreservingSmoothRealCongruenceChartCentralTarget
            F hF hdet W).1 =
        0 := by
    rw [coe_specialFormPreservingSmoothRealCongruenceChartCentralTarget]
    exact map_zero _
  rw [hsymm,
    specialFormPreservingSmoothRealIdentityChartCoordinateDensityENNReal_zero,
    hstandard, hsourceCoordinate]
  simp only [
    specialFormPreservingSmoothRealCongruenceChartSourceTransitionJacobian_zero,
    ENNReal.ofReal_one, mul_one]
  exact
    (specialFormPreservingSmoothRealIdentityChartCoordinateDensityENNReal_zero
      (Matrix.skewAdjointCongruenceForm F W)
      (skewAdjointCongruenceForm_isSymm F hF W)
      (skewAdjointCongruenceForm_det_ne_zero F hdet W)).symm

end PositiveDefiniteIntegralLattice
