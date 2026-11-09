import SMSFormula.SpecialOrthogonalRealFormCongruenceChartOverlap

/-!
# Differential of an explicit real-congruence chart transition

This module differentiates the fixed-source transition attached to
`SpecialOrthogonalRealFormCongruenceData`.  The real matrix unit need not be
the scalar extension of a rational unit.  The transition is first represented
by a globally smooth four-stage matrix formula and then compared with the
partial-chart transition on its exact open source.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ContDiff

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Ambient matrix conjugation induced by an explicit real form congruence. -/
def specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ)
    ((c.unit⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
    (c.unit : Matrix (Fin n) (Fin n) ℝ)

@[simp]
theorem specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap_apply
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (A : Matrix (Fin n) (Fin n) ℝ) :
    specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap c A =
      ((c.unit⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * A *
        (c.unit : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

/-- The globally smooth matrix formula for the fixed-source transition. -/
def specialFormPreservingSmoothRealFormCongruenceTransitionFormula
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  c.tangentEquiv.symm
    (specialFormPreservingSmoothRealForwardCoordinate F' hF' hdet'
      (specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap c
        (specialFormPreservingSmoothRealInverseCoordinateMatrix
          F hF hdet x)))

/-- On the exact source overlap, the partial-chart transition is the
globally smooth explicit matrix formula. -/
theorem specialFormPreservingSmoothRealFormCongruenceAmbientTransition_eq_formula
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c x =
      specialFormPreservingSmoothRealFormCongruenceTransitionFormula
        F F' hF hdet hF' hdet' c x := by
  change x ∈
    (specialFormPreservingSmoothRealIdentityChart F hF hdet).target ∩
      (fun y => c.groupEquiv
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm y)) ⁻¹'
          (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').source
    at hx
  rw [specialFormPreservingSmoothRealFormCongruenceAmbientTransition_apply,
    specialFormPreservingSmoothRealIdentityChart_apply_eq_forwardCoordinate
      F' hF' hdet'
      (c.groupEquiv
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x))
      hx.2]
  congr 2
  rw [specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap_apply,
    SpecialOrthogonalRealFormCongruenceData.coe_groupEquiv_apply,
    coe_specialFormPreservingSmoothRealIdentityChart_symm_eq_inverseCoordinateMatrix
      F hF hdet x hx.1]

/-- The explicit four-stage transition formula is maximally smooth on the
source identity-chart target. -/
theorem contDiffOn_specialFormPreservingSmoothRealFormCongruenceTransitionFormula
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    ContDiffOn ℝ ∞
      (specialFormPreservingSmoothRealFormCongruenceTransitionFormula
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target := by
  have hinv :=
    contDiffOn_specialFormPreservingSmoothRealInverseCoordinateMatrix
      F hF hdet 1
  have hmatrix :=
    (specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap
      c).contDiff.comp_contDiffOn hinv
  have hforward :=
    (contDiff_specialFormPreservingSmoothRealForwardCoordinate
      F' hF' hdet').comp_contDiffOn hmatrix
  have houter :=
    c.tangentEquiv.symm.contDiff.comp_contDiffOn hforward
  simpa only [
    specialFormPreservingSmoothRealFormCongruenceTransitionFormula,
    Function.comp_apply] using houter

/-- The transition is maximally smooth on its exact open overlap. -/
theorem contDiffOn_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    ContDiffOn ℝ ∞
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) := by
  apply
    (contDiffOn_specialFormPreservingSmoothRealFormCongruenceTransitionFormula
      F F' hF hdet hF' hdet' c).mono (fun _ hx => hx.1) |>.congr
  intro x hx
  exact
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition_eq_formula
      F F' hF hdet hF' hdet' c x hx

/-- The explicit complete four-stage derivative on the fixed source tangent
carrier. -/
def specialFormPreservingSmoothRealFormCongruenceTransitionDerivative
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule →L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  c.tangentEquiv.symm.toContinuousLinearMap.comp
    ((fderiv ℝ
      (specialFormPreservingSmoothRealForwardCoordinate F' hF' hdet')
      (specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap c
        (specialFormPreservingSmoothRealInverseCoordinateMatrix
          F hF hdet x))).comp
      ((specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap c).comp
        (fderiv ℝ
          (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet)
          x)))

/-- The globally smooth transition formula has the four-stage
derivative at every source identity coordinate. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceTransitionFormula
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈ (specialFormPreservingSmoothRealIdentityChart
      F hF hdet).target) :
    HasFDerivAt
      (specialFormPreservingSmoothRealFormCongruenceTransitionFormula
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceTransitionDerivative
        F F' hF hdet hF' hdet' c x) x := by
  have hinv :=
    hasFDerivAt_specialFormPreservingSmoothRealInverseCoordinateMatrix
      F hF hdet 1 x hx
  have hmatrix :=
    (specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap
      c).hasFDerivAt.comp x hinv
  have hfwd : HasFDerivAt
      (specialFormPreservingSmoothRealForwardCoordinate F' hF' hdet')
      (fderiv ℝ
        (specialFormPreservingSmoothRealForwardCoordinate F' hF' hdet')
        (specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap c
          (specialFormPreservingSmoothRealInverseCoordinateMatrix
            F hF hdet x)))
      (specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap c
        (specialFormPreservingSmoothRealInverseCoordinateMatrix
          F hF hdet x)) := by
    apply DifferentiableAt.hasFDerivAt
    exact
      ((contDiff_specialFormPreservingSmoothRealForwardCoordinate
        F' hF' hdet').differentiable (by simp)).differentiableAt
  have hinner := hfwd.comp x hmatrix
  have houter := c.tangentEquiv.symm.hasFDerivAt.comp x hinner
  simpa only [
    specialFormPreservingSmoothRealFormCongruenceTransitionFormula,
    specialFormPreservingSmoothRealFormCongruenceTransitionDerivative,
    Function.comp_apply] using houter

/-- On the exact overlap, the partial-chart transition has the
explicit complete derivative. -/
theorem hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    HasFDerivAt
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceTransitionDerivative
        F F' hF hdet hF' hdet' c x) x := by
  have hx' : x ∈
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target :=
    hx.1
  have hformula :=
    hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceTransitionFormula
      F F' hF hdet hF' hdet' c x hx'
  have heq :
      specialFormPreservingSmoothRealFormCongruenceTransitionFormula
          F F' hF hdet hF' hdet' c =ᶠ[nhds x]
        specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c := by
    filter_upwards
      [(isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c).mem_nhds hx]
      with y hy
    exact
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition_eq_formula
        F F' hF hdet hF' hdet' c y hy).symm
  exact hformula.congr_of_eventuallyEq heq.symm

/-- The Frechet derivative of the transition on its exact
source is the explicit four-stage endomorphism. -/
theorem fderiv_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    fderiv ℝ
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c) x =
      specialFormPreservingSmoothRealFormCongruenceTransitionDerivative
        F F' hF hdet hF' hdet' c x :=
  (hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    F F' hF hdet hF' hdet' c x hx).fderiv

/-- Determinant of the complete fixed-source transition derivative. -/
def specialFormPreservingSmoothRealFormCongruenceTransitionDeterminant
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) : ℝ :=
  LinearMap.det
    (specialFormPreservingSmoothRealFormCongruenceTransitionDerivative
      F F' hF hdet hF' hdet' c x).toLinearMap

/-- The positive-diagonal transition derivative. -/
abbrev positiveDiagonalSmoothRealFormCongruenceTransitionDerivative
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :=
  specialFormPreservingSmoothRealFormCongruenceTransitionDerivative
    (Matrix.diagonal d) 1
    (positiveDiagonalForm_isSymm d)
    (positiveDiagonalForm_det_ne_zero d hd)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (positiveDiagonalRealFormCongruenceData d hd)

/-- The positive-diagonal transition has the specialized complete
derivative on its exact overlap. -/
theorem hasFDerivAt_positiveDiagonalSmoothRealFormCongruenceAmbientTransition
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i)
    (x : (skewAdjointMatricesLieSubalgebra
      ((Matrix.diagonal d).map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      positiveDiagonalSmoothRealFormCongruenceAmbientSourceOverlapSet d hd) :
    HasFDerivAt
      (positiveDiagonalSmoothRealFormCongruenceAmbientTransition d hd)
      (positiveDiagonalSmoothRealFormCongruenceTransitionDerivative d hd x) x :=
  hasFDerivAt_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (Matrix.diagonal d) 1
    (positiveDiagonalForm_isSymm d)
    (positiveDiagonalForm_det_ne_zero d hd)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (positiveDiagonalRealFormCongruenceData d hd) x hx

end PositiveDefiniteIntegralLattice
