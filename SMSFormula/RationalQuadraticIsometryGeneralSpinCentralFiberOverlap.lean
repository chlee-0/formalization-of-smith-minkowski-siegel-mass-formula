import SMSFormula.RationalQuadraticIsometryGeneralSpinCentralFiberTopology

/-!
# Overlap of transported and ambient real central-fiber charts

The real central-fiber chart transported from a supplied anisotropic
presentation and the repository's independently chosen ambient chart have the
same global forward function, but their partial-homeomorphism domains need not
be equal.  This file keeps that distinction literal.  It defines their common
open group source and the two corresponding open target-coordinate overlaps,
then proves that the two cross-chart transitions are inverse (indeed, they are
the identity on their exact overlap domains).

No measure or Haar-normalization comparison is made here.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The actual common group domain of the transported and independently
chosen ambient real central-fiber charts. -/
def transportedAmbientRealCentralFiberSourceOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set (V.CliffordGeneralSpinIntrinsicPoint ℝ) :=
  (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source ∩
    V.realCliffordGeneralSpinCentralFiberIdentityChart.source

/-- Coordinates of the transported chart whose represented group point also
lies in the independently chosen ambient chart. -/
def transportedRealCentralFiberTargetOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set (ℝˣ × V.RealSpecialOrthogonalGroup) :=
  (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).target ∩
    (fun y ↦
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm y) ⁻¹'
      V.realCliffordGeneralSpinCentralFiberIdentityChart.source

/-- Coordinates of the ambient chart whose represented group point also lies
in the transported chart. -/
def ambientRealCentralFiberTargetOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set (ℝˣ × V.RealSpecialOrthogonalGroup) :=
  V.realCliffordGeneralSpinCentralFiberIdentityChart.target ∩
    (fun y ↦ V.realCliffordGeneralSpinCentralFiberIdentityChart.symm y) ⁻¹'
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source

/-- The transition from transported coordinates to ambient coordinates. -/
def transportedToAmbientRealCentralFiberTransition
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : ℝˣ × V.RealSpecialOrthogonalGroup) :
    ℝˣ × V.RealSpecialOrthogonalGroup :=
  V.realCliffordGeneralSpinCentralFiberIdentityChart
    ((P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm y)

/-- The reverse transition from ambient coordinates to transported
coordinates. -/
def ambientToTransportedRealCentralFiberTransition
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : ℝˣ × V.RealSpecialOrthogonalGroup) :
    ℝˣ × V.RealSpecialOrthogonalGroup :=
  P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
    (V.realCliffordGeneralSpinCentralFiberIdentityChart.symm y)

/-- The two charts have the same global forward function, without any claim
that their chosen domains agree. -/
theorem blockToAmbientTransportedRealCentralFiberIdentityChart_eq_ambient_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : V.CliffordGeneralSpinIntrinsicPoint ℝ) :
    P.blockToAmbientTransportedRealCentralFiberIdentityChart hx g =
      V.realCliffordGeneralSpinCentralFiberIdentityChart g := by
  rw [P.blockToAmbientTransportedRealCentralFiberIdentityChart_apply hx]
  rfl

/-- The common group overlap is open. -/
theorem isOpen_transportedAmbientRealCentralFiberSourceOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    IsOpen (P.transportedAmbientRealCentralFiberSourceOverlap hx) :=
  (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).open_source.inter
    V.realCliffordGeneralSpinCentralFiberIdentityChart.open_source

/-- The transported-coordinate overlap is open. -/
theorem isOpen_transportedRealCentralFiberTargetOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    IsOpen (P.transportedRealCentralFiberTargetOverlap hx) := by
  exact
    (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm.continuousOn
      |>.isOpen_inter_preimage
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).open_target
        V.realCliffordGeneralSpinCentralFiberIdentityChart.open_source

/-- The ambient-coordinate overlap is open. -/
theorem isOpen_ambientRealCentralFiberTargetOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    IsOpen (P.ambientRealCentralFiberTargetOverlap hx) := by
  exact
    V.realCliffordGeneralSpinCentralFiberIdentityChart.symm.continuousOn
      |>.isOpen_inter_preimage
        V.realCliffordGeneralSpinCentralFiberIdentityChart.open_target
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).open_source

/-- On the exact transported-coordinate overlap, the forward cross-chart
transition is literally the identity. -/
theorem transportedToAmbientRealCentralFiberTransition_eq_self
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {y : ℝˣ × V.RealSpecialOrthogonalGroup}
    (hy : y ∈ P.transportedRealCentralFiberTargetOverlap hx) :
    P.transportedToAmbientRealCentralFiberTransition hx y = y := by
  rw [transportedToAmbientRealCentralFiberTransition,
    ← P.blockToAmbientTransportedRealCentralFiberIdentityChart_eq_ambient_apply hx]
  exact
    (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).right_inv hy.1

/-- On the exact ambient-coordinate overlap, the reverse cross-chart
transition is literally the identity. -/
theorem ambientToTransportedRealCentralFiberTransition_eq_self
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {y : ℝˣ × V.RealSpecialOrthogonalGroup}
    (hy : y ∈ P.ambientRealCentralFiberTargetOverlap hx) :
    P.ambientToTransportedRealCentralFiberTransition hx y = y := by
  rw [ambientToTransportedRealCentralFiberTransition,
    P.blockToAmbientTransportedRealCentralFiberIdentityChart_eq_ambient_apply hx]
  exact V.realCliffordGeneralSpinCentralFiberIdentityChart.right_inv hy.1

/-- The forward transition maps its exact transported-coordinate overlap into
the exact ambient-coordinate overlap. -/
theorem mapsTo_transportedToAmbientRealCentralFiberTransition
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set.MapsTo
      (P.transportedToAmbientRealCentralFiberTransition hx)
      (P.transportedRealCentralFiberTargetOverlap hx)
      (P.ambientRealCentralFiberTargetOverlap hx) := by
  intro y hy
  change
    y ∈ (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).target ∩
      (fun y ↦
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm y) ⁻¹'
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source at hy
  change
    V.realCliffordGeneralSpinCentralFiberIdentityChart
          ((P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm y) ∈
        V.realCliffordGeneralSpinCentralFiberIdentityChart.target ∩
      (fun z ↦ V.realCliffordGeneralSpinCentralFiberIdentityChart.symm z) ⁻¹'
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source
  constructor
  · exact V.realCliffordGeneralSpinCentralFiberIdentityChart.map_source hy.2
  · change
      V.realCliffordGeneralSpinCentralFiberIdentityChart.symm
          (V.realCliffordGeneralSpinCentralFiberIdentityChart
            ((P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm y)) ∈
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source
    rw [V.realCliffordGeneralSpinCentralFiberIdentityChart.left_inv hy.2]
    exact
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm.map_source hy.1

/-- The reverse transition maps its exact ambient-coordinate overlap into the
exact transported-coordinate overlap. -/
theorem mapsTo_ambientToTransportedRealCentralFiberTransition
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set.MapsTo
      (P.ambientToTransportedRealCentralFiberTransition hx)
      (P.ambientRealCentralFiberTargetOverlap hx)
      (P.transportedRealCentralFiberTargetOverlap hx) := by
  intro y hy
  change
    y ∈ V.realCliffordGeneralSpinCentralFiberIdentityChart.target ∩
      (fun y ↦ V.realCliffordGeneralSpinCentralFiberIdentityChart.symm y) ⁻¹'
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source at hy
  change
    P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
          (V.realCliffordGeneralSpinCentralFiberIdentityChart.symm y) ∈
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).target ∩
      (fun z ↦
        (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm z) ⁻¹'
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source
  constructor
  · exact
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).map_source hy.2
  · change
      (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).symm
          (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx
            (V.realCliffordGeneralSpinCentralFiberIdentityChart.symm y)) ∈
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source
    rw [(P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).left_inv hy.2]
    exact V.realCliffordGeneralSpinCentralFiberIdentityChart.symm.map_source hy.1

/-- The two coordinate descriptions cut out the same exact open target
overlap. -/
theorem transportedRealCentralFiberTargetOverlap_eq_ambient
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedRealCentralFiberTargetOverlap hx =
      P.ambientRealCentralFiberTargetOverlap hx := by
  apply Set.Subset.antisymm
  · intro y hy
    have hmap := P.mapsTo_transportedToAmbientRealCentralFiberTransition hx hy
    rw [P.transportedToAmbientRealCentralFiberTransition_eq_self hx hy] at hmap
    exact hmap
  · intro y hy
    have hmap := P.mapsTo_ambientToTransportedRealCentralFiberTransition hx hy
    rw [P.ambientToTransportedRealCentralFiberTransition_eq_self hx hy] at hmap
    exact hmap

/-- The two explicit cross-chart transitions are left inverses on the
transported-coordinate overlap. -/
theorem leftInverseOn_transportedAmbientRealCentralFiberTransitions
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set.LeftInvOn
      (P.ambientToTransportedRealCentralFiberTransition hx)
      (P.transportedToAmbientRealCentralFiberTransition hx)
      (P.transportedRealCentralFiberTargetOverlap hx) := by
  intro y hy
  have hforward :=
    P.transportedToAmbientRealCentralFiberTransition_eq_self hx hy
  have hmap := P.mapsTo_transportedToAmbientRealCentralFiberTransition hx hy
  rw [hforward] at hmap ⊢
  exact P.ambientToTransportedRealCentralFiberTransition_eq_self hx hmap

/-- The two explicit cross-chart transitions are right inverses on the
ambient-coordinate overlap. -/
theorem rightInverseOn_transportedAmbientRealCentralFiberTransitions
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set.RightInvOn
      (P.ambientToTransportedRealCentralFiberTransition hx)
      (P.transportedToAmbientRealCentralFiberTransition hx)
      (P.ambientRealCentralFiberTargetOverlap hx) := by
  intro y hy
  have hreverse :=
    P.ambientToTransportedRealCentralFiberTransition_eq_self hx hy
  have hmap := P.mapsTo_ambientToTransportedRealCentralFiberTransition hx hy
  rw [hreverse] at hmap ⊢
  exact P.transportedToAmbientRealCentralFiberTransition_eq_self hx hmap

/-- The exact transported and ambient target overlaps are homeomorphic via
the actual cross-chart transition. -/
def transportedAmbientRealCentralFiberTargetOverlapHomeomorph
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedRealCentralFiberTargetOverlap hx ≃ₜ
      P.ambientRealCentralFiberTargetOverlap hx where
  toFun y := ⟨P.transportedToAmbientRealCentralFiberTransition hx y.1,
    P.mapsTo_transportedToAmbientRealCentralFiberTransition hx y.2⟩
  invFun y := ⟨P.ambientToTransportedRealCentralFiberTransition hx y.1,
    P.mapsTo_ambientToTransportedRealCentralFiberTransition hx y.2⟩
  left_inv y := Subtype.ext
    (P.leftInverseOn_transportedAmbientRealCentralFiberTransitions hx y.2)
  right_inv y := Subtype.ext
    (P.rightInverseOn_transportedAmbientRealCentralFiberTransitions hx y.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [show (fun y : P.transportedRealCentralFiberTargetOverlap hx ↦
        P.transportedToAmbientRealCentralFiberTransition hx y.1) =
      fun y ↦ y.1 by
        funext y
        exact P.transportedToAmbientRealCentralFiberTransition_eq_self hx y.2]
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    rw [show (fun y : P.ambientRealCentralFiberTargetOverlap hx ↦
        P.ambientToTransportedRealCentralFiberTransition hx y.1) =
      fun y ↦ y.1 by
        funext y
        exact P.ambientToTransportedRealCentralFiberTransition_eq_self hx y.2]
    exact continuous_subtype_val

@[simp]
theorem transportedAmbientRealCentralFiberTargetOverlapHomeomorph_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : P.transportedRealCentralFiberTargetOverlap hx) :
    (P.transportedAmbientRealCentralFiberTargetOverlapHomeomorph hx y).1 = y.1 :=
  P.transportedToAmbientRealCentralFiberTransition_eq_self hx y.2

@[simp]
theorem transportedAmbientRealCentralFiberTargetOverlapHomeomorph_symm_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : P.ambientRealCentralFiberTargetOverlap hx) :
    ((P.transportedAmbientRealCentralFiberTargetOverlapHomeomorph hx).symm y).1 = y.1 :=
  P.ambientToTransportedRealCentralFiberTransition_eq_self hx y.2

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
