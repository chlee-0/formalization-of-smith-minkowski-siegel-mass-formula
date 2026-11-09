import SMSFormula.RationalQuadraticIsometryGeneralSpinCentralFiberTransport
import SMSFormula.RationalCliffordGeneralSpinPlacewiseTranslatedDifferentialChart

/-!
# Topological central-fiber transport across anisotropic presentations

The algebraic presentation equivalence on the special-orthogonal coordinate
is continuous for the repository's native finite-coordinate topologies.  Its
product with the identity on units therefore gives a continuous
multiplicative equivalence between the crossed central-fiber targets.

This file does not identify the independently chosen block and ambient
identity-chart domains and does not compare any Haar measures.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

private local instance specialOrthogonalMatrixPointTopologicalSpace
    {r : ℕ} {U : RationalQuadraticSpaceMatrix r}
    {A : Type*} [CommRing A] [Algebra ℚ A] [TopologicalSpace A] :
    TopologicalSpace (U.specialOrthogonalMatrixPoint A) :=
  TopologicalSpace.induced Subtype.val inferInstance

private theorem continuous_conjugatedMatrixCoordinate
    {r s : ℕ} {A X : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace X]
    (E : (Fin r → A) ≃ₗ[A] (Fin s → A))
    (hE : Continuous E)
    (M : X → Matrix (Fin r) (Fin r) A)
    (hM : ∀ i j, Continuous (fun z ↦ M z i j))
    (i j : Fin s) :
    Continuous (fun z ↦
      E (Matrix.mulVec (M z) (E.symm (Pi.single j 1))) i) := by
  apply (continuous_apply i).comp
  apply hE.comp
  apply continuous_pi
  intro k
  change Continuous (fun z ↦
    ∑ l, M z k l * E.symm (Pi.single j 1) l)
  apply continuous_finset_sum
  intro l _
  exact (hM k l).mul continuous_const

private theorem continuous_specialOrthogonalMatrixPointToGroup
    {r : ℕ} (U : RationalQuadraticSpaceMatrix r)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (U.specialOrthogonalMatrixPointToGroup A) := by
  let toSet : U.specialOrthogonalMatrixPoint A →
      Matrix.specialOrthogonalMatrixSet
        (U.specialOrthogonalMappedFormMatrix A) := fun g ↦
    ⟨g.1,
      (Matrix.formPreservingConstraint_eq_zero_iff
        (U.specialOrthogonalMappedFormMatrix A) g.1).mpr g.2.1,
      g.2.2⟩
  have htoSet : Continuous toSet := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  rw [show U.specialOrthogonalMatrixPointToGroup A =
      fun g ↦ specialOrthogonalMatrixSetToSpecialSubgroup
        (U.specialOrthogonalMappedFormMatrix A) (toSet g) by
    funext g
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl]
  exact
    (continuous_specialOrthogonalMatrixSetToSpecialSubgroup
      (U.specialOrthogonalMappedFormMatrix A)).comp htoSet

private theorem continuous_specialOrthogonalMatrixPointOfGroup
    {r : ℕ} (U : RationalQuadraticSpaceMatrix r)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (U.specialOrthogonalMatrixPointOfGroup A) := by
  apply continuous_induced_rng.mpr
  exact Units.continuous_val.comp
    (continuous_subtype_val.comp continuous_subtype_val)

/-- Forward presentation transport on special-orthogonal matrix points is
continuous over every topological commutative rational algebra. -/
theorem continuous_blockToAmbientSpecialOrthogonalMatrixPoint
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx) := by
  let E := P.blockToAmbientBaseChangeIsometryEquiv hx A
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  let b : Fin n → A := Pi.single j 1
  have hcont : Continuous (fun g :
      (P.blockSpace hx).specialOrthogonalMatrixPoint A ↦
      E (Matrix.mulVec g.1 (E.symm b)) i) := by
    simpa only [b] using
      (continuous_conjugatedMatrixCoordinate E
        (P.continuous_blockToAmbientBaseChangeIsometryEquiv hx A)
        (fun g : (P.blockSpace hx).specialOrthogonalMatrixPoint A ↦ g.1)
        (fun k l ↦ (continuous_apply l).comp
          ((continuous_apply k).comp continuous_subtype_val)) i j)
  change Continuous (fun g :
    (P.blockSpace hx).specialOrthogonalMatrixPoint A ↦
      (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx g).1 i j)
  rw [show (fun g : (P.blockSpace hx).specialOrthogonalMatrixPoint A ↦
      (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx g).1 i j) =
      fun g ↦ E (Matrix.mulVec g.1 (E.symm b)) i by
    funext g
    have hcol :
        (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx g).1 i j =
          Matrix.mulVec
            (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx g).1 b i := by
      simp [b, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcol, P.blockToAmbientSpecialOrthogonalMatrixPoint_mulVec A hx]
    rfl]
  exact hcont

/-- Reverse presentation transport on special-orthogonal matrix points is
continuous over the same native topologies. -/
theorem continuous_ambientToBlockSpecialOrthogonalMatrixPoint
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx) := by
  let E := P.blockToAmbientBaseChangeIsometryEquiv hx A
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  let b : Fin (m + 1) → A := Pi.single j 1
  have hcont : Continuous (fun g : V.specialOrthogonalMatrixPoint A ↦
      E.symm (Matrix.mulVec g.1 (E b)) i) := by
    simpa only [b] using
      (continuous_conjugatedMatrixCoordinate E.symm
        (P.continuous_blockToAmbientBaseChangeIsometryEquiv_symm hx A)
        (fun g : V.specialOrthogonalMatrixPoint A ↦ g.1)
        (fun k l ↦ (continuous_apply l).comp
          ((continuous_apply k).comp continuous_subtype_val)) i j)
  change Continuous (fun g : V.specialOrthogonalMatrixPoint A ↦
    (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx g).1 i j)
  rw [show (fun g : V.specialOrthogonalMatrixPoint A ↦
      (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx g).1 i j) =
      fun g ↦ E.symm (Matrix.mulVec g.1 (E b)) i by
    funext g
    have hcol :
        (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx g).1 i j =
          Matrix.mulVec
            (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx g).1 b i := by
      simp [b, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcol, P.ambientToBlockSpecialOrthogonalMatrixPoint_mulVec A hx]
    rfl]
  exact hcont

/-- The forward special-orthogonal presentation group map is continuous. -/
theorem continuous_blockToAmbientSpecialOrthogonalGroupEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (P.blockToAmbientSpecialOrthogonalGroupEquiv A hx) := by
  exact (continuous_specialOrthogonalMatrixPointToGroup V A).comp
    ((P.continuous_blockToAmbientSpecialOrthogonalMatrixPoint hx A).comp
      (continuous_specialOrthogonalMatrixPointOfGroup (P.blockSpace hx) A))

/-- The inverse special-orthogonal presentation group map is continuous. -/
theorem continuous_blockToAmbientSpecialOrthogonalGroupEquiv_symm
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (P.blockToAmbientSpecialOrthogonalGroupEquiv A hx).symm := by
  exact
    (continuous_specialOrthogonalMatrixPointToGroup (P.blockSpace hx) A).comp
      ((P.continuous_ambientToBlockSpecialOrthogonalMatrixPoint hx A).comp
        (continuous_specialOrthogonalMatrixPointOfGroup V A))

/-- The algebraic special-orthogonal presentation equivalence is a continuous
multiplicative equivalence. -/
def blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (P.blockSpace hx).specialOrthogonalMatrixGroup A ≃ₜ*
      V.specialOrthogonalMatrixGroup A :=
  ContinuousMulEquiv.mk'
    { toEquiv := P.blockToAmbientSpecialOrthogonalGroupEquiv A hx
      continuous_toFun :=
        P.continuous_blockToAmbientSpecialOrthogonalGroupEquiv hx A
      continuous_invFun :=
        P.continuous_blockToAmbientSpecialOrthogonalGroupEquiv_symm hx A }
    (P.blockToAmbientSpecialOrthogonalGroupMulEquiv A hx).map_mul

/-- The crossed central-fiber target presentation equivalence is continuous. -/
def blockToAmbientCentralFiberTargetContinuousMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (Aˣ × (P.blockSpace hx).specialOrthogonalMatrixGroup A) ≃ₜ*
      (Aˣ × V.specialOrthogonalMatrixGroup A) :=
  PositiveDefiniteIntegralLattice.prodContinuousMulEquiv
    (ContinuousMulEquiv.refl Aˣ)
    (P.blockToAmbientSpecialOrthogonalGroupContinuousMulEquiv hx A)

@[simp]
theorem blockToAmbientCentralFiberTargetContinuousMulEquiv_toMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (P.blockToAmbientCentralFiberTargetContinuousMulEquiv hx A).toMulEquiv =
      P.blockToAmbientCentralFiberTargetMulEquiv A hx := by
  rfl

/-! ## The transported real identity chart -/

/-- Transport the block real central-fiber identity chart through the native
presentation homeomorphisms.  This chart is deliberately distinct from the
ambient identity chart chosen independently by the repository. -/
noncomputable def blockToAmbientTransportedRealCentralFiberIdentityChart
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    OpenPartialHomeomorph
      (V.CliffordGeneralSpinIntrinsicPoint ℝ)
      (ℝˣ × V.RealSpecialOrthogonalGroup) :=
  (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℝ).symm.toHomeomorph
      |>.toOpenPartialHomeomorph |>.trans
    ((P.blockSpace hx).realCliffordGeneralSpinCentralFiberIdentityChart.trans
      ((P.blockToAmbientCentralFiberTargetContinuousMulEquiv hx ℝ).toHomeomorph
        |>.toOpenPartialHomeomorph))

/-- The transported chart has the same global forward function as the ambient
central-fiber homomorphism. -/
theorem blockToAmbientTransportedRealCentralFiberIdentityChart_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : V.CliffordGeneralSpinIntrinsicPoint ℝ) :
    P.blockToAmbientTransportedRealCentralFiberIdentityChart hx g =
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ g := by
  rw [blockToAmbientTransportedRealCentralFiberIdentityChart,
    OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply]
  change P.blockToAmbientCentralFiberTargetMulEquiv ℝ hx
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom
        (P.blockSpace hx) ℝ
        (P.ambientToBlockGeneralSpinIntrinsicPoint ℝ hx g)) = _
  rw [P.blockToAmbientGeneralSpin_centralFiber_commutes ℝ hx]
  rw [P.blockToAmbientGeneralSpinIntrinsicPoint_ambientToBlock ℝ hx]

set_option backward.isDefEq.respectTransparency false in
/-- Membership in the transported chart source is exactly membership of the
inverse presentation image in the block identity-chart source. -/
theorem mem_blockToAmbientTransportedRealCentralFiberIdentityChart_source_iff
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : V.CliffordGeneralSpinIntrinsicPoint ℝ) :
    g ∈ (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).source ↔
      P.ambientToBlockGeneralSpinIntrinsicPoint ℝ hx g ∈
        ((P.blockSpace hx).realCliffordGeneralSpinCentralFiberIdentityChart).source := by
  simp [blockToAmbientTransportedRealCentralFiberIdentityChart]
  change (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℝ).toMulEquiv.symm g ∈
    ((P.blockSpace hx).realCliffordGeneralSpinCentralFiberIdentityChart).source ↔ _
  rw [P.blockToAmbientGeneralSpinContinuousMulEquiv_toMulEquiv hx ℝ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Membership in the transported chart target is exactly membership of the
inverse crossed-target image in the block chart target. -/
theorem mem_blockToAmbientTransportedRealCentralFiberIdentityChart_target_iff
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : ℝˣ × V.RealSpecialOrthogonalGroup) :
    y ∈ (P.blockToAmbientTransportedRealCentralFiberIdentityChart hx).target ↔
      (P.blockToAmbientCentralFiberTargetMulEquiv ℝ hx).symm y ∈
        ((P.blockSpace hx).realCliffordGeneralSpinCentralFiberIdentityChart).target := by
  simp [blockToAmbientTransportedRealCentralFiberIdentityChart]
  change (P.blockToAmbientCentralFiberTargetContinuousMulEquiv hx ℝ).toMulEquiv.symm y ∈
    ((P.blockSpace hx).realCliffordGeneralSpinCentralFiberIdentityChart).target ↔ _
  rw [P.blockToAmbientCentralFiberTargetContinuousMulEquiv_toMulEquiv hx ℝ]

/-! ## The transported p-adic identity chart -/

/-- Transport the block p-adic central-fiber identity chart through the
presentation homeomorphisms.  As at the real place, this transported chart is
distinct from the independently chosen ambient p-adic identity chart. -/
noncomputable def blockToAmbientTransportedPadicCentralFiberIdentityChart
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    OpenPartialHomeomorph
      (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p])
      (ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  (P.blockToAmbientGeneralSpinContinuousMulEquiv hx ℚ_[p]).symm.toHomeomorph
      |>.toOpenPartialHomeomorph |>.trans
    ((P.blockSpace hx).padicCliffordGeneralSpinCentralFiberIdentityChart p |>.trans
      ((P.blockToAmbientCentralFiberTargetContinuousMulEquiv hx ℚ_[p]).toHomeomorph
        |>.toOpenPartialHomeomorph))

/-- The transported p-adic chart has the ambient central-fiber homomorphism as
its literal global forward function. -/
theorem blockToAmbientTransportedPadicCentralFiberIdentityChart_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :
    P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p g =
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] g := by
  rw [blockToAmbientTransportedPadicCentralFiberIdentityChart,
    OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply]
  change P.blockToAmbientCentralFiberTargetMulEquiv ℚ_[p] hx
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom
        (P.blockSpace hx) ℚ_[p]
        (P.ambientToBlockGeneralSpinIntrinsicPoint ℚ_[p] hx g)) = _
  rw [P.blockToAmbientGeneralSpin_centralFiber_commutes ℚ_[p] hx]
  rw [P.blockToAmbientGeneralSpinIntrinsicPoint_ambientToBlock ℚ_[p] hx]

/-- Membership in the transported p-adic chart source is exactly membership
of the inverse presentation image in the block identity-chart source. -/
theorem mem_blockToAmbientTransportedPadicCentralFiberIdentityChart_source_iff
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :
    g ∈ (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).source ↔
      P.ambientToBlockGeneralSpinIntrinsicPoint ℚ_[p] hx g ∈
        ((P.blockSpace hx).padicCliffordGeneralSpinCentralFiberIdentityChart p).source := by
  simp [blockToAmbientTransportedPadicCentralFiberIdentityChart]
  change P.ambientToBlockGeneralSpinIntrinsicPoint ℚ_[p] hx g ∈
      ((P.blockSpace hx).padicCliffordGeneralSpinCentralFiberIdentityChart p).source ↔ _
  rfl

/-- Membership in the transported p-adic chart target is exactly membership
of the inverse crossed-target image in the block chart target. -/
theorem mem_blockToAmbientTransportedPadicCentralFiberIdentityChart_target_iff
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (y : ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) :
    y ∈ (P.blockToAmbientTransportedPadicCentralFiberIdentityChart hx p).target ↔
      (P.blockToAmbientCentralFiberTargetMulEquiv ℚ_[p] hx).symm y ∈
        ((P.blockSpace hx).padicCliffordGeneralSpinCentralFiberIdentityChart p).target := by
  simp [blockToAmbientTransportedPadicCentralFiberIdentityChart]
  change (P.blockToAmbientCentralFiberTargetMulEquiv ℚ_[p] hx).symm y ∈
      ((P.blockSpace hx).padicCliffordGeneralSpinCentralFiberIdentityChart p).target ↔ _
  rfl

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
