import SMSFormula.SpecialOrthogonalRealFormCongruenceChartDifferential

/-!
# Central Jacobian normalization for explicit real congruences

This module normalizes the explicit real-congruence transition at the central
coordinate.  Matrix conjugation fixes the identity and restricts to the
tangent equivalence, so the inverse and forward chart derivatives
cancel without any rational scalar-extension argument.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ContDiff

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Explicit real matrix conjugation fixes the identity matrix. -/
@[simp]
theorem specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap_one
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap c
      (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  change
    ((c.unit⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * 1 *
      (c.unit : Matrix (Fin n) (Fin n) ℝ) = 1
  have hunit : c.unit⁻¹ * c.unit = (1 : GL (Fin n) ℝ) := by
    group
  have h := congrArg
    (fun U : GL (Fin n) ℝ => (U : Matrix (Fin n) (Fin n) ℝ)) hunit
  simpa only [Matrix.mul_one] using h

/-- On the source tangent carrier, explicit real matrix conjugation is the
tangent congruence. -/
theorem specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap_comp_subtypeL
    {F F' : Matrix (Fin n) (Fin n) ℚ}
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    (specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap c).comp
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL =
      (skewAdjointMatricesLieSubalgebra
        (F'.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL.comp
          c.tangentEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro X
  change
    ((c.unit⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *
          (X : Matrix (Fin n) (Fin n) ℝ) *
        (c.unit : Matrix (Fin n) (Fin n) ℝ) =
      (c.tangentEquiv X : Matrix (Fin n) (Fin n) ℝ)
  have h :=
    (SpecialOrthogonalRealFormCongruenceData.coe_tangentEquiv_apply
      c X).symm
  rw [← Matrix.GeneralLinearGroup.coe_inv] at h
  exact h

/-- The globally smooth explicit real-congruence formula fixes zero. -/
@[simp]
theorem specialFormPreservingSmoothRealFormCongruenceTransitionFormula_zero
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceTransitionFormula
      F F' hF hdet hF' hdet' c 0 = 0 := by
  rw [specialFormPreservingSmoothRealFormCongruenceTransitionFormula,
    specialFormPreservingSmoothRealInverseCoordinateMatrix_zero,
    specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap_one]
  have hzero :=
    specialFormPreservingSmoothRealForwardCoordinate_one_add
      F' hF' hdet'
      (0 : (skewAdjointMatricesLieSubalgebra
        (F'.map (algebraMap ℚ ℝ))).toSubmodule)
  simpa using congrArg c.tangentEquiv.symm hzero

/-- The complete fixed-source derivative of an explicit real-congruence
transition is the identity at zero. -/
@[simp]
theorem specialFormPreservingSmoothRealFormCongruenceTransitionDerivative_zero
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceTransitionDerivative
        F F' hF hdet hF' hdet' c 0 =
      ContinuousLinearMap.id ℝ
        ((skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) := by
  let e := c.tangentEquiv
  have hinv :
      fderiv ℝ
        (specialFormPreservingSmoothRealInverseCoordinateMatrix F hF hdet) 0 =
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL :=
    (hasFDerivAt_specialFormPreservingSmoothRealInverseCoordinateMatrix_zero
      F hF hdet).fderiv
  have hmatrix :
      (specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap c).comp
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL =
        (skewAdjointMatricesLieSubalgebra
          (F'.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL.comp
            e.toContinuousLinearMap :=
    specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap_comp_subtypeL
      c
  have hfwd :=
    fderiv_specialFormPreservingSmoothRealForwardCoordinate_one_comp_subtypeL
      F' hF' hdet'
  have hmiddle :
      (fderiv ℝ
        (specialFormPreservingSmoothRealForwardCoordinate
          F' hF' hdet') 1).comp
          ((skewAdjointMatricesLieSubalgebra
            (F'.map (algebraMap ℚ ℝ))).toSubmodule.subtypeL.comp
              e.toContinuousLinearMap) =
        e.toContinuousLinearMap := by
    rw [← ContinuousLinearMap.comp_assoc, hfwd]
    simp
  rw [specialFormPreservingSmoothRealFormCongruenceTransitionDerivative,
    hinv, specialFormPreservingSmoothRealInverseCoordinateMatrix_zero,
    specialFormPreservingRealFormCongruenceMatrixContinuousLinearMap_one,
    hmatrix, hmiddle]
  simp [e]

/-- Zero belongs to the exact overlap source for every explicit real
congruence. -/
theorem zero_mem_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    (0 : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c := by
  change
    (0 : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) ∈
        (specialFormPreservingSmoothRealIdentityChart F hF hdet).target ∧
      c.groupEquiv
          ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm 0) ∈
        (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').source
  constructor
  · exact zero_mem_specialFormPreservingSmoothRealIdentityChart_target
      F hF hdet
  · simp only [specialFormPreservingSmoothRealIdentityChart_symm_zero, map_one]
    simpa only [specialFormPreservingSmoothRealIdentityChart_symm_zero] using
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').symm.map_source
        (zero_mem_specialFormPreservingSmoothRealIdentityChart_target
          F' hF' hdet')

/-- The explicit real-congruence transition fixes zero. -/
@[simp]
theorem specialFormPreservingSmoothRealFormCongruenceAmbientTransition_zero
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c 0 = 0 := by
  rw [specialFormPreservingSmoothRealFormCongruenceAmbientTransition_eq_formula
    F F' hF hdet hF' hdet' c 0
      (zero_mem_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c)]
  exact specialFormPreservingSmoothRealFormCongruenceTransitionFormula_zero
    F F' hF hdet hF' hdet' c

/-- The Frechet derivative of the transition is the identity
at zero. -/
@[simp]
theorem fderiv_specialFormPreservingSmoothRealFormCongruenceAmbientTransition_zero
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    fderiv ℝ
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c) 0 =
      ContinuousLinearMap.id ℝ
        ((skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule) := by
  rw [fderiv_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
      F F' hF hdet hF' hdet' c 0
      (zero_mem_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c),
    specialFormPreservingSmoothRealFormCongruenceTransitionDerivative_zero]

/-- The complete explicit real-congruence transition determinant is one at
zero. -/
@[simp]
theorem specialFormPreservingSmoothRealFormCongruenceTransitionDeterminant_zero
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceTransitionDeterminant
      F F' hF hdet hF' hdet' c 0 = 1 := by
  rw [specialFormPreservingSmoothRealFormCongruenceTransitionDeterminant,
    specialFormPreservingSmoothRealFormCongruenceTransitionDerivative_zero]
  exact LinearMap.det_id

/-- Absolute Jacobian of the complete explicit real-congruence transition
derivative. -/
def specialFormPreservingSmoothRealFormCongruenceTransitionJacobian
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) : ℝ :=
  |specialFormPreservingSmoothRealFormCongruenceTransitionDeterminant
    F F' hF hdet hF' hdet' c x|

/-- The absolute Jacobian is one at zero. -/
@[simp]
theorem specialFormPreservingSmoothRealFormCongruenceTransitionJacobian_zero
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceTransitionJacobian
      F F' hF hdet hF' hdet' c 0 = 1 := by
  rw [specialFormPreservingSmoothRealFormCongruenceTransitionJacobian,
    specialFormPreservingSmoothRealFormCongruenceTransitionDeterminant_zero,
    abs_one]

/-- The positive-diagonal transition derivative is the identity at zero. -/
@[simp]
theorem positiveDiagonalSmoothRealFormCongruenceTransitionDerivative_zero
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    positiveDiagonalSmoothRealFormCongruenceTransitionDerivative d hd 0 =
      ContinuousLinearMap.id ℝ
        ((skewAdjointMatricesLieSubalgebra
          ((Matrix.diagonal d).map (algebraMap ℚ ℝ))).toSubmodule) :=
  specialFormPreservingSmoothRealFormCongruenceTransitionDerivative_zero
    (Matrix.diagonal d) 1
    (positiveDiagonalForm_isSymm d)
    (positiveDiagonalForm_det_ne_zero d hd)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (positiveDiagonalRealFormCongruenceData d hd)

end PositiveDefiniteIntegralLattice
