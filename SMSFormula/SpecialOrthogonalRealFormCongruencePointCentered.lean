import SMSFormula.SpecialOrthogonalRealFormCongruenceChartJacobian

/-!
# Point-centered explicit real-congruence transitions

For a coordinate in the exact explicit-real overlap, this module defines the
represented source and target group points and the two identity-to-point
coordinate transitions on the fixed source tangent carrier.  It proves their
cross-form square on an explicit open neighborhood and retains the resulting
eventual equality.  Derivative composition is treated
separately.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The source group point represented by an exact overlap coordinate. -/
def specialFormPreservingSmoothRealFormCongruenceSourcePointAt
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℝ)) :=
  (specialFormPreservingSmoothRealIdentityChart F hF hdet).symm x

/-- The target group point represented by an exact overlap coordinate. -/
def specialFormPreservingSmoothRealFormCongruenceTargetPointAt
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    specialFormPreservingMatrixSubgroup (F'.map (algebraMap ℚ ℝ)) :=
  c.groupEquiv
    (specialFormPreservingSmoothRealFormCongruenceSourcePointAt
      F F' hF hdet hF' hdet' c x)

/-- The independently selected target identity coordinate represented by an
exact source overlap coordinate. -/
def specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').target :=
  ⟨specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
      (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
        F F' hF hdet hF' hdet' c x),
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').map_source
      hx.2⟩

/-- The source identity-to-represented-point transition. -/
def specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    OpenPartialHomeomorph
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  (specialFormPreservingSmoothRealIdentityChart F hF hdet).symm.trans
    (specialFormPreservingSmoothRealChart F hF hdet
      (specialFormPreservingSmoothRealFormCongruenceSourcePointAt
        F F' hF hdet hF' hdet' c x))

/-- Source of the target identity-to-represented-point transition, pulled
back to the fixed source tangent carrier. -/
def specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionSourceAt
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    Set ((skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :=
  c.tangentEquiv ⁻¹'
    ((specialFormPreservingSmoothRealSkewAdjointTransition
      F' hF' hdet' 1
      (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
        F F' hF hdet hF' hdet' c x)).source)

/-- The target identity-to-represented-point transition conjugated to the
fixed source tangent carrier. -/
def specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionAt
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  c.tangentEquiv.symm
    ((specialFormPreservingSmoothRealSkewAdjointTransition
      F' hF' hdet' 1
      (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
        F F' hF hdet hF' hdet' c x)) (c.tangentEquiv y))

/-- Pointwise inverse of the target point-centered transition. -/
def specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionInvAt
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  c.tangentEquiv.symm
    (((specialFormPreservingSmoothRealIdentityChart F' hF' hdet').symm.trans
      (specialFormPreservingSmoothRealChart F' hF' hdet'
        (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
          F F' hF hdet hF' hdet' c x))).symm (c.tangentEquiv y))

/-- The represented coordinate lies in its source point-centered transition. -/
theorem sourceCoordinate_mem_specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈ (specialFormPreservingSmoothRealIdentityChart
      F hF hdet).target) :
    x ∈ (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
      F F' hF hdet hF' hdet' c x).source := by
  rw [specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt,
    OpenPartialHomeomorph.trans_source]
  exact ⟨hx, self_mem_specialFormPreservingSmoothRealChart_source
    F hF hdet _⟩

/-- The source moving transition sends the represented coordinate to zero. -/
@[simp]
theorem specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt_self
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
      F F' hF hdet hF' hdet' c x x = 0 := by
  rw [specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt,
    OpenPartialHomeomorph.trans_apply]
  exact specialFormPreservingSmoothRealChart_center F hF hdet _

/-- The inverse source moving transition recovers the represented coordinate. -/
@[simp]
theorem specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt_symm_zero
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈ (specialFormPreservingSmoothRealIdentityChart
      F hF hdet).target) :
    (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
      F F' hF hdet hF' hdet' c x).symm 0 = x := by
  let S :=
    specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
      F F' hF hdet hF' hdet' c x
  calc
    S.symm 0 = S.symm (S x) := by
      rw [specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt_self]
    _ = x := S.left_inv
      (sourceCoordinate_mem_specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
        F F' hF hdet hF' hdet' c x hx)

/-- At the represented coordinate, the cross transition is the standard
target coordinate pulled back through tangent congruence. -/
theorem specialFormPreservingSmoothRealFormCongruenceAmbientTransition_at
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
      c.tangentEquiv.symm
        (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
          F F' hF hdet hF' hdet' c x hx).1 :=
  rfl

/-- The represented pulled-back standard coordinate lies in the target
point-centered transition source. -/
theorem ambientTransitionAt_mem_specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionSourceAt
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
        F F' hF hdet hF' hdet' c x ∈
      specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionSourceAt
        F F' hF hdet hF' hdet' c x := by
  rw [specialFormPreservingSmoothRealFormCongruenceAmbientTransition_at
      F F' hF hdet hF' hdet' c x hx,
    specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionSourceAt,
    Set.mem_preimage, c.tangentEquiv.apply_symm_apply]
  change
    (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
      F F' hF hdet hF' hdet' c x hx).1 ∈
      ((specialFormPreservingSmoothRealIdentityChart F' hF' hdet').symm.trans
        (specialFormPreservingSmoothRealChart F' hF' hdet'
          (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
            F F' hF hdet hF' hdet' c x))).source
  rw [OpenPartialHomeomorph.trans_source]
  constructor
  · exact
      (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
        F F' hF hdet hF' hdet' c x hx).2
  · change
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').symm
          (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
            F F' hF hdet hF' hdet' c x hx).1 ∈
        (specialFormPreservingSmoothRealChart F' hF' hdet'
          (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
            F F' hF hdet hF' hdet' c x)).source
    rw [show
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').symm
          (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
            F F' hF hdet hF' hdet' c x hx).1 =
        specialFormPreservingSmoothRealFormCongruenceTargetPointAt
          F F' hF hdet hF' hdet' c x by
        exact (specialFormPreservingSmoothRealIdentityChart
          F' hF' hdet').left_inv hx.2]
    exact self_mem_specialFormPreservingSmoothRealChart_source F' hF' hdet' _

/-- The target moving transition sends the represented coordinate to zero. -/
@[simp]
theorem specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionAt_ambientTransition
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionAt
        F F' hF hdet hF' hdet' c x
        (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c x) =
      0 := by
  rw [specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionAt,
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition_at
      F F' hF hdet hF' hdet' c x hx,
    c.tangentEquiv.apply_symm_apply]
  let q :
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').source :=
    ⟨specialFormPreservingSmoothRealFormCongruenceTargetPointAt
      F F' hF hdet hF' hdet' c x, hx.2⟩
  have hcenter :=
    specialFormPreservingSmoothRealChart_transition_to_self_apply_coordinate
      F' hF' hdet' 1 q
  have hmiddle :
      (specialFormPreservingSmoothRealSkewAdjointTransition
        F' hF' hdet' 1
        (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
          F F' hF hdet hF' hdet' c x))
        (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
          F F' hF hdet hF' hdet' c x hx).1 = 0 := by
    simpa only [specialFormPreservingSmoothRealSkewAdjointTransition,
      q, specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt,
      specialFormPreservingSmoothRealFormCongruenceTargetPointAt] using hcenter
  rw [hmiddle]
  exact map_zero _

/-- The inverse target moving transition recovers the represented coordinate. -/
@[simp]
theorem specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionInvAt_zero
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionInvAt
        F F' hF hdet hF' hdet' c x 0 =
      specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c x := by
  let M :=
    (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').symm.trans
      (specialFormPreservingSmoothRealChart F' hF' hdet'
        (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
          F F' hF hdet hF' hdet' c x))
  let z :=
    (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
      F F' hF hdet hF' hdet' c x hx).1
  have hz : z ∈ M.source := by
    change z ∈
      ((specialFormPreservingSmoothRealIdentityChart F' hF' hdet').symm.trans
        (specialFormPreservingSmoothRealChart F' hF' hdet'
          (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
            F F' hF hdet hF' hdet' c x))).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨(specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
      F F' hF hdet hF' hdet' c x hx).2, ?_⟩
    change
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').symm
          (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
            F F' hF hdet hF' hdet' c x hx).1 ∈
        (specialFormPreservingSmoothRealChart F' hF' hdet'
          (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
            F F' hF hdet hF' hdet' c x)).source
    rw [show
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').symm
          (specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt
            F F' hF hdet hF' hdet' c x hx).1 =
        specialFormPreservingSmoothRealFormCongruenceTargetPointAt
          F F' hF hdet hF' hdet' c x by
        exact (specialFormPreservingSmoothRealIdentityChart
          F' hF' hdet').left_inv hx.2]
    exact self_mem_specialFormPreservingSmoothRealChart_source F' hF' hdet' _
  have hMz : M z = 0 := by
    let q :
        (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').source :=
      ⟨specialFormPreservingSmoothRealFormCongruenceTargetPointAt
        F F' hF hdet hF' hdet' c x, hx.2⟩
    have hcenter :=
      specialFormPreservingSmoothRealChart_transition_to_self_apply_coordinate
        F' hF' hdet' 1 q
    simpa only [M, z, q,
      specialFormPreservingSmoothRealFormCongruenceStandardCoordinateAt,
      specialFormPreservingSmoothRealFormCongruenceTargetPointAt] using hcenter
  rw [specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionInvAt,
    map_zero]
  congr 1
  calc
    M.symm 0 = M.symm (M z) := congrArg M.symm hMz.symm
    _ = z := M.left_inv hz

/-- The cross transition is the target identity coordinate of group
congruence wherever both identity charts are defined. -/
theorem specialFormPreservingSmoothRealFormCongruenceAmbientTransition_eq_identityChart
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hcong :
      c.groupEquiv
          ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm y) ∈
        (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').source) :
    c.tangentEquiv
        (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c y) =
      specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
        (c.groupEquiv
          ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm y)) := by
  rw [specialFormPreservingSmoothRealFormCongruenceAmbientTransition_apply,
    c.tangentEquiv.apply_symm_apply]

/-- Exact ambient neighborhood on which both point-centered paths are
simultaneously chart-defined. -/
def specialFormPreservingSmoothRealFormCongruencePointCenteredCommutationSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    Set ((skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :=
  {y |
    y ∈
        (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
          F F' hF hdet hF' hdet' c x).source ∧
    c.groupEquiv
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm y) ∈
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').source ∧
    c.groupEquiv
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm y) ∈
      (specialFormPreservingSmoothRealChart F' hF' hdet'
        (specialFormPreservingSmoothRealFormCongruenceTargetPointAt
          F F' hF hdet hF' hdet' c x)).source ∧
    (specialFormPreservingSmoothRealFormCongruenceSourcePointAt
        F F' hF hdet hF' hdet' c x)⁻¹ *
        (specialFormPreservingSmoothRealIdentityChart F hF hdet).symm y ∈
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).source ∧
    specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
        F F' hF hdet hF' hdet' c x y ∈
      (specialFormPreservingSmoothRealIdentityChart F hF hdet).target ∧
    c.groupEquiv
        ((specialFormPreservingSmoothRealIdentityChart F hF hdet).symm
          (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
            F F' hF hdet hF' hdet' c x y)) ∈
      (specialFormPreservingSmoothRealIdentityChart F' hF' hdet').source}

/-- The explicit point-centered commutation domain is open. -/
theorem isOpen_specialFormPreservingSmoothRealFormCongruencePointCenteredCommutationSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    IsOpen
      (specialFormPreservingSmoothRealFormCongruencePointCenteredCommutationSet
        F F' hF hdet hF' hdet' c x) := by
  let C := c.groupEquiv
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  let p := specialFormPreservingSmoothRealFormCongruenceSourcePointAt
    F F' hF hdet hF' hdet' c x
  let q := specialFormPreservingSmoothRealFormCongruenceTargetPointAt
    F F' hF hdet hF' hdet' c x
  let S := specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
    F F' hF hdet hF' hdet' c x
  let K := specialFormPreservingSmoothRealChart F' hF' hdet' q
  let g := fun y => C (I.symm y)
  let shift := fun y => p⁻¹ * I.symm y
  let gS := fun y => C (I.symm (S y))
  have hSI : Set.MapsTo (fun y => y) S.source I.target := by
    intro y hy
    change y ∈
      (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
        F F' hF hdet hF' hdet' c x).source at hy
    rw [specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt,
      OpenPartialHomeomorph.trans_source] at hy
    exact hy.1
  have hIinv : ContinuousOn (fun y => I.symm y) S.source :=
    I.symm.continuousOn.mono hSI
  have hg : ContinuousOn g S.source :=
    C.continuous.comp_continuousOn hIinv
  let A1 := S.source ∩ g ⁻¹' J.source
  have hA1 : IsOpen A1 :=
    hg.isOpen_inter_preimage S.open_source J.open_source
  let A2 := A1 ∩ g ⁻¹' K.source
  have hA1S : A1 ⊆ S.source := fun _ hy => hy.1
  have hA2 : IsOpen A2 :=
    (hg.mono hA1S).isOpen_inter_preimage hA1 K.open_source
  let A3 := A2 ∩ shift ⁻¹' I.source
  have hA2S : A2 ⊆ S.source := fun _ hy => hy.1.1
  have hshift : ContinuousOn shift A2 :=
    continuousOn_const.mul (hIinv.mono hA2S)
  have hA3 : IsOpen A3 :=
    hshift.isOpen_inter_preimage hA2 I.open_source
  let A4 := A3 ∩ S ⁻¹' I.target
  have hA3S : A3 ⊆ S.source := fun _ hy => hy.1.1.1
  have hA4 : IsOpen A4 :=
    (S.continuousOn.mono hA3S).isOpen_inter_preimage hA3 I.open_target
  have hA4S : A4 ⊆ S.source := fun _ hy => hy.1.1.1.1
  have hA4map : Set.MapsTo S A4 I.target := fun _ hy => hy.2
  have hgS : ContinuousOn gS A4 :=
    C.continuous.comp_continuousOn
      (I.symm.continuousOn.comp (S.continuousOn.mono hA4S) hA4map)
  have hfinal : IsOpen (A4 ∩ gS ⁻¹' J.source) :=
    hgS.isOpen_inter_preimage hA4 J.open_source
  have hset :
      specialFormPreservingSmoothRealFormCongruencePointCenteredCommutationSet
          F F' hF hdet hF' hdet' c x =
        A4 ∩ gS ⁻¹' J.source := by
    ext y
    simp only [
      specialFormPreservingSmoothRealFormCongruencePointCenteredCommutationSet,
      C, I, J, p, q, S, K, g, shift, gS, A1, A2, A3, A4,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    tauto
  rw [hset]
  exact hfinal

/-- The point-centered square commutes throughout its exact common domain. -/
theorem specialFormPreservingSmoothRealFormCongruencePointCentered_square
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hy : y ∈
      specialFormPreservingSmoothRealFormCongruencePointCenteredCommutationSet
        F F' hF hdet hF' hdet' c x) :
    specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionAt
        F F' hF hdet hF' hdet' c x
        (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c y) =
      specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c
        (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
          F F' hF hdet hF' hdet' c x y) := by
  rcases hy with
    ⟨hyS, hycong, hycongPoint, hyshift, hyS_target, hyS_cong⟩
  have hCross :=
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition_eq_identityChart
      F F' hF hdet hF' hdet' c y hycong
  have hCrossS :=
    specialFormPreservingSmoothRealFormCongruenceAmbientTransition_eq_identityChart
      F F' hF hdet hF' hdet' c
        (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
          F F' hF hdet hF' hdet' c x y) hyS_cong
  let C := c.groupEquiv
  let e := c.tangentEquiv
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  let p := specialFormPreservingSmoothRealFormCongruenceSourcePointAt
    F F' hF hdet hF' hdet' c x
  let q := specialFormPreservingSmoothRealFormCongruenceTargetPointAt
    F F' hF hdet hF' hdet' c x
  let S := specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
    F F' hF hdet hF' hdet' c x
  let T := specialFormPreservingSmoothRealSkewAdjointTransition
    F' hF' hdet' 1 q
  have hTsource :
      e (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c y) ∈ T.source := by
    change
      e (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c y) ∈
        (J.symm.trans
          (specialFormPreservingSmoothRealChart F' hF' hdet' q)).source
    rw [OpenPartialHomeomorph.trans_source, hCross]
    constructor
    · exact J.map_source hycong
    · change
        J.symm (J (C (I.symm y))) ∈
          (specialFormPreservingSmoothRealChart F' hF' hdet' q).source
      rw [J.left_inv hycong]
      exact hycongPoint
  have hSformula : S y = I (p⁻¹ * I.symm y) := by
    simpa only [S, I, p,
      specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt]
      using
        specialFormPreservingSmoothRealSkewAdjointTransition_apply
          F hF hdet 1 p y hyS
  have hTformula :
      T (e (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c y)) =
        J (q⁻¹ * J.symm
          (e (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
            F F' hF hdet hF' hdet' c y))) := by
    simpa only [T, J, q] using
      specialFormPreservingSmoothRealSkewAdjointTransition_apply
        F' hF' hdet' 1 q
        (e (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c y)) hTsource
  rw [specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionAt]
  apply e.injective
  rw [e.apply_symm_apply, hTformula, hCrossS, hCross]
  congr 1
  rw [J.left_inv hycong]
  have hIshift : I.symm (S y) = p⁻¹ * I.symm y := by
    rw [hSformula, I.left_inv hyshift]
  rw [hIshift]
  change q⁻¹ * C (I.symm y) = C (p⁻¹ * I.symm y)
  change (C p)⁻¹ * C (I.symm y) = C (p⁻¹ * I.symm y)
  simp

/-- The represented coordinate belongs to the point-centered commutation
domain. -/
theorem self_mem_specialFormPreservingSmoothRealFormCongruencePointCenteredCommutationSet
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    x ∈
      specialFormPreservingSmoothRealFormCongruencePointCenteredCommutationSet
        F F' hF hdet hF' hdet' c x := by
  let p := specialFormPreservingSmoothRealFormCongruenceSourcePointAt
    F F' hF hdet hF' hdet' c x
  let q := specialFormPreservingSmoothRealFormCongruenceTargetPointAt
    F F' hF hdet hF' hdet' c x
  let C := c.groupEquiv
  let I := specialFormPreservingSmoothRealIdentityChart F hF hdet
  let J := specialFormPreservingSmoothRealIdentityChart F' hF' hdet'
  have hIx : I.symm x = p := rfl
  change
    x ∈
        (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
          F F' hF hdet hF' hdet' c x).source ∧
      C (I.symm x) ∈ J.source ∧
      C (I.symm x) ∈
        (specialFormPreservingSmoothRealChart F' hF' hdet' q).source ∧
      p⁻¹ * I.symm x ∈ I.source ∧
      specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
          F F' hF hdet hF' hdet' c x x ∈ I.target ∧
      C (I.symm
        (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
          F F' hF hdet hF' hdet' c x x)) ∈ J.source
  constructor
  · exact
      sourceCoordinate_mem_specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
        F F' hF hdet hF' hdet' c x hx.1
  constructor
  · exact hx.2
  constructor
  · change q ∈ (specialFormPreservingSmoothRealChart
      F' hF' hdet' q).source
    exact self_mem_specialFormPreservingSmoothRealChart_source F' hF' hdet' q
  constructor
  · rw [hIx]
    have hp : p⁻¹ * p = 1 := by simp
    rw [hp]
    exact self_mem_specialFormPreservingSmoothRealChart_source F hF hdet 1
  constructor
  · rw [specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt_self]
    exact zero_mem_specialFormPreservingSmoothRealIdentityChart_target F hF hdet
  · rw [specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt_self,
      specialFormPreservingSmoothRealIdentityChart_symm_zero, map_one]
    exact self_mem_specialFormPreservingSmoothRealChart_source F' hF' hdet' 1

/-- The neighborhood-level square as an eventual equality at the represented
coordinate. -/
theorem eventuallyEq_specialFormPreservingSmoothRealFormCongruencePointCentered
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hF' : F'.IsSymm) (hdet' : F'.det ≠ 0)
    (c : SpecialOrthogonalRealFormCongruenceData F F')
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule)
    (hx : x ∈
      specialFormPreservingSmoothRealFormCongruenceAmbientSourceOverlapSet
        F F' hF hdet hF' hdet' c) :
    (fun y =>
      specialFormPreservingSmoothRealFormCongruenceTargetPointTransitionAt
        F F' hF hdet hF' hdet' c x
        (specialFormPreservingSmoothRealFormCongruenceAmbientTransition
          F F' hF hdet hF' hdet' c y)) =ᶠ[nhds x]
    (fun y =>
      specialFormPreservingSmoothRealFormCongruenceAmbientTransition
        F F' hF hdet hF' hdet' c
        (specialFormPreservingSmoothRealFormCongruenceSourcePointTransitionAt
          F F' hF hdet hF' hdet' c x y)) := by
  filter_upwards [
    (isOpen_specialFormPreservingSmoothRealFormCongruencePointCenteredCommutationSet
      F F' hF hdet hF' hdet' c x).mem_nhds
        (self_mem_specialFormPreservingSmoothRealFormCongruencePointCenteredCommutationSet
          F F' hF hdet hF' hdet' c x hx)] with y hy
  exact
    specialFormPreservingSmoothRealFormCongruencePointCentered_square
      F F' hF hdet hF' hdet' c x y hy

end PositiveDefiniteIntegralLattice
