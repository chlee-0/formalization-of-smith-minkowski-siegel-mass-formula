import SMSFormula.RationalQuadraticIsometryGeneralSpinCentralFiberTopology

/-!
# Overlap of transported and ambient p-adic central-fiber charts

The p-adic central-fiber chart transported from a supplied anisotropic
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
variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The actual common group domain of the transported and independently
chosen ambient p-adic central-fiber charts. -/
def transportedAmbientPadicCentralFiberSourceOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
  (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source ∩
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source

/-- Coordinates of the transported chart whose represented group point also
lies in the independently chosen ambient chart. -/
def transportedPadicCentralFiberTargetOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set (ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).target ∩
    (fun y ↦
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm y) ⁻¹'
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source

/-- Coordinates of the ambient chart whose represented group point also lies
in the transported chart. -/
def ambientPadicCentralFiberTargetOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set (ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).target ∩
    (fun y ↦ (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm y) ⁻¹'
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source

/-- The transition from transported coordinates to ambient coordinates. -/
def transportedToAmbientPadicCentralFiberTransition
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) :
    ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p] :=
  V.padicCliffordGeneralSpinCentralFiberIdentityChart p
    ((P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm y)

/-- The reverse transition from ambient coordinates to transported
coordinates. -/
def ambientToTransportedPadicCentralFiberTransition
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) :
    ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p] :=
  P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
    ((V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm y)

/-- The two charts have the same global forward function, without any claim
that their chosen domains agree. -/
theorem blockToAmbientTransportedPadicCentralFiberIdentityChart_eq_ambient_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :
    P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p g =
      V.padicCliffordGeneralSpinCentralFiberIdentityChart p g := by
  rw [P.blockToAmbientTransportedPadicCentralFiberIdentityChart_apply hx]
  rfl

/-- The common group overlap is open. -/
theorem isOpen_transportedAmbientPadicCentralFiberSourceOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    IsOpen (P.transportedAmbientPadicCentralFiberSourceOverlap p hx) :=
  (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).open_source.inter
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).open_source

/-- The transported-coordinate overlap is open. -/
theorem isOpen_transportedPadicCentralFiberTargetOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    IsOpen (P.transportedPadicCentralFiberTargetOverlap p hx) := by
  exact
    (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm.continuousOn
      |>.isOpen_inter_preimage
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).open_target
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).open_source

/-- The ambient-coordinate overlap is open. -/
theorem isOpen_ambientPadicCentralFiberTargetOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    IsOpen (P.ambientPadicCentralFiberTargetOverlap p hx) := by
  exact
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm.continuousOn
      |>.isOpen_inter_preimage
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).open_target
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).open_source

/-- On the exact transported-coordinate overlap, the forward cross-chart
transition is literally the identity. -/
theorem transportedToAmbientPadicCentralFiberTransition_eq_self
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {y : ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]}
    (hy : y ∈ P.transportedPadicCentralFiberTargetOverlap p hx) :
    P.transportedToAmbientPadicCentralFiberTransition p hx y = y := by
  rw [transportedToAmbientPadicCentralFiberTransition,
    ← P.blockToAmbientTransportedPadicCentralFiberIdentityChart_eq_ambient_apply p hx]
  exact
    (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).right_inv hy.1

/-- On the exact ambient-coordinate overlap, the reverse cross-chart
transition is literally the identity. -/
theorem ambientToTransportedPadicCentralFiberTransition_eq_self
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {y : ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]}
    (hy : y ∈ P.ambientPadicCentralFiberTargetOverlap p hx) :
    P.ambientToTransportedPadicCentralFiberTransition p hx y = y := by
  rw [ambientToTransportedPadicCentralFiberTransition,
    P.blockToAmbientTransportedPadicCentralFiberIdentityChart_eq_ambient_apply p hx]
  exact (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).right_inv hy.1

/-- The forward transition maps its exact transported-coordinate overlap into
the exact ambient-coordinate overlap. -/
theorem mapsTo_transportedToAmbientPadicCentralFiberTransition
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set.MapsTo
      (P.transportedToAmbientPadicCentralFiberTransition p hx)
      (P.transportedPadicCentralFiberTargetOverlap p hx)
      (P.ambientPadicCentralFiberTargetOverlap p hx) := by
  intro y hy
  change
    y ∈ (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).target ∩
      (fun y ↦
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm y) ⁻¹'
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source at hy
  change
    V.padicCliffordGeneralSpinCentralFiberIdentityChart p
          ((P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm y) ∈
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).target ∩
      (fun z ↦ (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm z) ⁻¹'
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source
  constructor
  · exact (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).map_source hy.2
  · change
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm
          (V.padicCliffordGeneralSpinCentralFiberIdentityChart p
            ((P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm y)) ∈
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source
    rw [(V.padicCliffordGeneralSpinCentralFiberIdentityChart p).left_inv hy.2]
    exact
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm.map_source hy.1

/-- The reverse transition maps its exact ambient-coordinate overlap into the
exact transported-coordinate overlap. -/
theorem mapsTo_ambientToTransportedPadicCentralFiberTransition
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set.MapsTo
      (P.ambientToTransportedPadicCentralFiberTransition p hx)
      (P.ambientPadicCentralFiberTargetOverlap p hx)
      (P.transportedPadicCentralFiberTargetOverlap p hx) := by
  intro y hy
  change
    y ∈ (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).target ∩
      (fun y ↦ (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm y) ⁻¹'
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source at hy
  change
    P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
          ((V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm y) ∈
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).target ∩
      (fun z ↦
        (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm z) ⁻¹'
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source
  constructor
  · exact
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).map_source hy.2
  · change
      (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).symm
          (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p
            ((V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm y)) ∈
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source
    rw [(P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).left_inv hy.2]
    exact (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).symm.map_source hy.1

/-- The two coordinate descriptions cut out the same exact open target
overlap. -/
theorem transportedPadicCentralFiberTargetOverlap_eq_ambient
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedPadicCentralFiberTargetOverlap p hx =
      P.ambientPadicCentralFiberTargetOverlap p hx := by
  apply Set.Subset.antisymm
  · intro y hy
    have hmap := P.mapsTo_transportedToAmbientPadicCentralFiberTransition p hx hy
    rw [P.transportedToAmbientPadicCentralFiberTransition_eq_self p hx hy] at hmap
    exact hmap
  · intro y hy
    have hmap := P.mapsTo_ambientToTransportedPadicCentralFiberTransition p hx hy
    rw [P.ambientToTransportedPadicCentralFiberTransition_eq_self p hx hy] at hmap
    exact hmap

/-- The two explicit cross-chart transitions are left inverses on the
transported-coordinate overlap. -/
theorem leftInverseOn_transportedAmbientPadicCentralFiberTransitions
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set.LeftInvOn
      (P.ambientToTransportedPadicCentralFiberTransition p hx)
      (P.transportedToAmbientPadicCentralFiberTransition p hx)
      (P.transportedPadicCentralFiberTargetOverlap p hx) := by
  intro y hy
  have hforward :=
    P.transportedToAmbientPadicCentralFiberTransition_eq_self p hx hy
  have hmap := P.mapsTo_transportedToAmbientPadicCentralFiberTransition p hx hy
  rw [hforward] at hmap ⊢
  exact P.ambientToTransportedPadicCentralFiberTransition_eq_self p hx hmap

/-- The two explicit cross-chart transitions are right inverses on the
ambient-coordinate overlap. -/
theorem rightInverseOn_transportedAmbientPadicCentralFiberTransitions
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Set.RightInvOn
      (P.ambientToTransportedPadicCentralFiberTransition p hx)
      (P.transportedToAmbientPadicCentralFiberTransition p hx)
      (P.ambientPadicCentralFiberTargetOverlap p hx) := by
  intro y hy
  have hreverse :=
    P.ambientToTransportedPadicCentralFiberTransition_eq_self p hx hy
  have hmap := P.mapsTo_ambientToTransportedPadicCentralFiberTransition p hx hy
  rw [hreverse] at hmap ⊢
  exact P.transportedToAmbientPadicCentralFiberTransition_eq_self p hx hmap

/-- The exact transported and ambient target overlaps are homeomorphic via
the actual cross-chart transition. -/
def transportedAmbientPadicCentralFiberTargetOverlapHomeomorph
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedPadicCentralFiberTargetOverlap p hx ≃ₜ
      P.ambientPadicCentralFiberTargetOverlap p hx where
  toFun y := ⟨P.transportedToAmbientPadicCentralFiberTransition p hx y.1,
    P.mapsTo_transportedToAmbientPadicCentralFiberTransition p hx y.2⟩
  invFun y := ⟨P.ambientToTransportedPadicCentralFiberTransition p hx y.1,
    P.mapsTo_ambientToTransportedPadicCentralFiberTransition p hx y.2⟩
  left_inv y := Subtype.ext
    (P.leftInverseOn_transportedAmbientPadicCentralFiberTransitions p hx y.2)
  right_inv y := Subtype.ext
    (P.rightInverseOn_transportedAmbientPadicCentralFiberTransitions p hx y.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [show (fun y : P.transportedPadicCentralFiberTargetOverlap p hx ↦
        P.transportedToAmbientPadicCentralFiberTransition p hx y.1) =
      fun y ↦ y.1 by
        funext y
        exact P.transportedToAmbientPadicCentralFiberTransition_eq_self p hx y.2]
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    rw [show (fun y : P.ambientPadicCentralFiberTargetOverlap p hx ↦
        P.ambientToTransportedPadicCentralFiberTransition p hx y.1) =
      fun y ↦ y.1 by
        funext y
        exact P.ambientToTransportedPadicCentralFiberTransition_eq_self p hx y.2]
    exact continuous_subtype_val

@[simp]
theorem transportedAmbientPadicCentralFiberTargetOverlapHomeomorph_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : P.transportedPadicCentralFiberTargetOverlap p hx) :
    (P.transportedAmbientPadicCentralFiberTargetOverlapHomeomorph p hx y).1 = y.1 :=
  P.transportedToAmbientPadicCentralFiberTransition_eq_self p hx y.2

@[simp]
theorem transportedAmbientPadicCentralFiberTargetOverlapHomeomorph_symm_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : P.ambientPadicCentralFiberTargetOverlap p hx) :
    ((P.transportedAmbientPadicCentralFiberTargetOverlapHomeomorph p hx).symm y).1 = y.1 :=
  P.ambientToTransportedPadicCentralFiberTransition_eq_self p hx y.2

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
