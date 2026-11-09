import SMSFormula.RealCrossChartAmbient
import SMSFormula.SpecialOrthogonalRealFormCongruenceChart

/-!
# Overlaps for explicit real form congruences

This module specializes the fixed-carrier ambient cross-chart construction to
an explicit real congruence between two rational forms.  It compares the
transported source identity chart with the independently selected target-form
identity chart without constructing a homeomorphism between nested dependent
coordinate subtypes.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Source coordinates where the source identity chart and the independently
selected target identity chart represent the same point. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set ((skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :=
  realCrossChartAmbientSource
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet')
    c.groupEquiv.toHomeomorph

/-- Target coordinates pulled back to the source tangent carrier. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set ((skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :=
  realCrossChartAmbientTarget
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet')
    c.groupEquiv.toHomeomorph c.tangentEquiv

/-- The exact same-point group overlap between the transported source chart
and the independently selected target-form identity chart. -/
def specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set (specialFormPreservingMatrixSubgroup
      (F'.map (algebraMap ℚ ℝ))) :=
  realCrossChartAmbientGroupOverlap
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet')
    c.groupEquiv.toHomeomorph

/-- The standard target-form coordinates of the exact common group overlap. -/
def specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set ((skewAdjointMatricesLieSubalgebra
      (F'.map (algebraMap ℚ ℝ))).toSubmodule) :=
  realCrossChartAmbientTargetRange
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet')
    c.groupEquiv.toHomeomorph

/-- The common group overlap is definitionally the intersection of the
transported chart source and the target identity-chart source. -/
theorem specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet_eq
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c =
      specialFormPreservingSmoothRealFormCongruenceChartSourceSet
          F F' hF hdet c ∩
        (specialFormPreservingSmoothRealIdentityChart
          F' hF' hdet').source :=
  rfl

theorem isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    IsOpen
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :=
  isOpen_realCrossChartAmbientSource _ _ _

theorem isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    IsOpen
      (specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
        F F' hF hdet hF' hdet' c) :=
  isOpen_realCrossChartAmbientTarget _ _ _ _

theorem isOpen_specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    IsOpen
      (specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c) :=
  isOpen_realCrossChartAmbientGroupOverlap _ _ _

theorem isOpen_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    IsOpen
      (specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c) :=
  isOpen_realCrossChartAmbientTargetRange _ _ _

/-- The fixed-source coordinate transition for an explicit real congruence. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule →
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  realCrossChartAmbientTransition
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet')
    c.groupEquiv.toHomeomorph c.tangentEquiv

/-- The pointwise inverse of the fixed-source coordinate transition. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientTransitionInv
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule →
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  realCrossChartAmbientTransitionInv
    (specialFormPreservingSmoothRealIdentityChart F hF hdet)
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet')
    c.groupEquiv.toHomeomorph c.tangentEquiv

/-- Pointwise formula for the explicit real-congruence transition. -/
theorem specialFormPreservingSmoothRealFormCongruenceAmbientTransition_apply
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c x =
      c.tangentEquiv.symm
        (specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
          (c.groupEquiv
            ((specialFormPreservingSmoothRealIdentityChart
              F hF hdet).symm x))) :=
  rfl

theorem mapsTo_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set.MapsTo
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
        F F' hF hdet hF' hdet' c) :=
  mapsTo_realCrossChartAmbientTransition _ _ _ _

theorem mapsTo_specialFormPreservingSmoothRealFormCongruenceAmbientTransitionInv
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set.MapsTo
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransitionInv
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :=
  mapsTo_realCrossChartAmbientTransitionInv _ _ _ _

theorem leftInverseOn_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set.LeftInvOn
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransitionInv
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :=
  leftInverseOn_realCrossChartAmbientTransition _ _ _ _

theorem rightInverseOn_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set.RightInvOn
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransitionInv
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
        F F' hF hdet hF' hdet' c) :=
  rightInverseOn_realCrossChartAmbientTransition _ _ _ _

theorem injOn_specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    Set.InjOn
      (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c)
      (specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :=
  injOn_realCrossChartAmbientTransition _ _ _ _

theorem image_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c ''
        specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
          F F' hF hdet hF' hdet' c =
      specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
        F F' hF hdet hF' hdet' c :=
  image_realCrossChartAmbientSource _ _ _ _

/-- Source coordinates are homeomorphic to the exact common group overlap. -/
def specialFormPreservingSmoothRealFormCongruenceAmbientSourceToGroup
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c ≃ₜ
      specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c :=
  realCrossChartAmbientSourceToGroup _ _ _

/-- Standard target coordinates are homeomorphic to the exact common group
overlap. -/
def specialFormPreservingSmoothRealFormCongruenceStandardTargetToGroup
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F') :
    specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
        F F' hF hdet hF' hdet' c ≃ₜ
      specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
        F F' hF hdet hF' hdet' c :=
  realCrossChartAmbientTargetRangeToGroup _ _ _

/-- The standard target coordinate produced from a source overlap coordinate. -/
theorem coe_specialFormPreservingSmoothRealFormCongruenceSourceToStandardTarget
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c) :
    (realCrossChartAmbientSourceToTargetRange
      (specialFormPreservingSmoothRealIdentityChart F hF hdet)
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet')
      c.groupEquiv.toHomeomorph x).1 =
      c.tangentEquiv
        (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c x.1) :=
  coe_realCrossChartAmbientSourceToTargetRange _ _ _ _ x

/-- Both explicit overlap coordinate systems represent the same target-group
point. -/
theorem specialFormPreservingSmoothRealFormCongruence_samePoint
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
      F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealFormCongruenceStandardTargetToGroup
        F F' hF hdet hF' hdet' c
        (realCrossChartAmbientSourceToTargetRange
          (specialFormPreservingSmoothRealIdentityChart F hF hdet)
          (specialFormPreservingSmoothRealIdentityChart F' hF' hdet')
          c.groupEquiv.toHomeomorph x) =
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceToGroup
        F F' hF hdet hF' hdet' c x :=
  realCrossChartAmbientTargetRangeToGroup_sourceToTargetRange _ _ _ x

/-- The rational identity form is symmetric. -/
theorem identityRationalForm_isSymm :
    (1 : Matrix (Fin n) (Fin n) ℚ).IsSymm := by
  simp [Matrix.IsSymm]

/-- The rational identity form is nonsingular. -/
theorem identityRationalForm_det_ne_zero :
    (1 : Matrix (Fin n) (Fin n) ℚ).det ≠ 0 := by
  simp

/-- The positive-diagonal source overlap for inverse-square-root scaling. -/
abbrev positiveDiagonalSmoothRealFormCongruenceAmbientSourceOverlapSet
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :=
  specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
    (Matrix.diagonal d) 1
    (positiveDiagonalForm_isSymm d)
    (positiveDiagonalForm_det_ne_zero d hd)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (positiveDiagonalRealFormCongruenceData d hd)

/-- The positive-diagonal pulled-back target overlap. -/
abbrev positiveDiagonalSmoothRealFormCongruenceAmbientTargetOverlapSet
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :=
  specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
    (Matrix.diagonal d) 1
    (positiveDiagonalForm_isSymm d)
    (positiveDiagonalForm_det_ne_zero d hd)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (positiveDiagonalRealFormCongruenceData d hd)

/-- The positive-diagonal exact common group overlap. -/
abbrev positiveDiagonalSmoothRealFormCongruenceGroupOverlapSet
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :=
  specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
    (Matrix.diagonal d) 1
    (positiveDiagonalForm_isSymm d)
    (positiveDiagonalForm_det_ne_zero d hd)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (positiveDiagonalRealFormCongruenceData d hd)

/-- The positive-diagonal standard identity-coordinate overlap. -/
abbrev positiveDiagonalSmoothRealFormCongruenceStandardTargetOverlapSet
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :=
  specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
    (Matrix.diagonal d) 1
    (positiveDiagonalForm_isSymm d)
    (positiveDiagonalForm_det_ne_zero d hd)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (positiveDiagonalRealFormCongruenceData d hd)

/-- The positive-diagonal fixed-source coordinate transition. -/
abbrev positiveDiagonalSmoothRealFormCongruenceAmbientTransition
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :=
  specialFormPreservingSmoothRealFormCongruenceAmbientTransition
    (Matrix.diagonal d) 1
    (positiveDiagonalForm_isSymm d)
    (positiveDiagonalForm_det_ne_zero d hd)
    identityRationalForm_isSymm identityRationalForm_det_ne_zero
    (positiveDiagonalRealFormCongruenceData d hd)

theorem isOpen_positiveDiagonalSmoothRealFormCongruenceAmbientSourceOverlapSet
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    IsOpen
      (positiveDiagonalSmoothRealFormCongruenceAmbientSourceOverlapSet d hd) :=
  isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
    _ _ _ _ _ _ _

theorem isOpen_positiveDiagonalSmoothRealFormCongruenceAmbientTargetOverlapSet
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    IsOpen
      (positiveDiagonalSmoothRealFormCongruenceAmbientTargetOverlapSet d hd) :=
  isOpen_specialFormPreservingSmoothRealFormCongruenceAmbientTargetOverlapSet
    _ _ _ _ _ _ _

theorem isOpen_positiveDiagonalSmoothRealFormCongruenceGroupOverlapSet
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    IsOpen
      (positiveDiagonalSmoothRealFormCongruenceGroupOverlapSet d hd) :=
  isOpen_specialFormPreservingSmoothRealFormCongruenceGroupOverlapSet
    _ _ _ _ _ _ _

theorem isOpen_positiveDiagonalSmoothRealFormCongruenceStandardTargetOverlapSet
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    IsOpen
      (positiveDiagonalSmoothRealFormCongruenceStandardTargetOverlapSet d hd) :=
  isOpen_specialFormPreservingSmoothRealFormCongruenceStandardTargetOverlapSet
    _ _ _ _ _ _ _

theorem image_positiveDiagonalSmoothRealFormCongruenceAmbientSourceOverlapSet
    (d : Fin n → ℚ) (hd : ∀ i, 0 < d i) :
    positiveDiagonalSmoothRealFormCongruenceAmbientTransition d hd ''
        positiveDiagonalSmoothRealFormCongruenceAmbientSourceOverlapSet d hd =
      positiveDiagonalSmoothRealFormCongruenceAmbientTargetOverlapSet d hd :=
  image_specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
    _ _ _ _ _ _ _

end PositiveDefiniteIntegralLattice
