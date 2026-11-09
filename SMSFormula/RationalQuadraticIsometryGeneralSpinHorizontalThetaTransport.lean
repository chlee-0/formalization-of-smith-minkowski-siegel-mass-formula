import SMSFormula.RationalQuadraticIsometryGeneralSpinHorizontalQuotientMeasureTransport
import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellRationalThetaOrbitEquiv
import SMSFormula.SpecialOrthogonalRealCongruenceOverlapWeightedMeasure

/-!
# Transport of a rational shell theta density to the ambient quotient

The intrinsic ambient density at a nonisotropic rational vector is the
ordinary nonnegative theta sum over its literal rational norm shell.  It is
rational-left invariant and therefore descends to the existing adelic
`GSpin` quotient.

A supplied complement presentation identifies the block theta-orbit density
with this ambient density.  The corresponding horizontal cutoff measure then
transports by exactly the already fixed horizontal Haar scalar.  No weight is
inserted into the ordinary theta summands, and no quotient representative,
shell representative, complement lattice, new measure, or chart is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Set
open scoped ENNReal Matrix NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The rational inverse special-orthogonal action of a `GSpin` point,
restricted to the literal rational shell through `x`. -/
def rationalGeneralSpinInvAmbientShellEquiv
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (d : V.RationalCliffordGeneralSpinGroup) :
    V.anisotropicRationalAmbientShell x ℚ ≃
      V.anisotropicRationalAmbientShell x ℚ := by
  let e := V.specialOrthogonalMatrixGroupIsometryEquiv ℚ (d.matrixGroup⁻¹)
  exact
    { toFun := fun y ↦ ⟨e y.1, by
          change V.commutativeScalarExtensionQuadraticForm ℚ (e y.1) = _
          rw [e.map_app, y.property]⟩
      invFun := fun y ↦ ⟨e.symm y.1, by
          change V.commutativeScalarExtensionQuadraticForm ℚ (e.symm y.1) = _
          rw [e.symm.map_app, y.property]⟩
      left_inv := fun y ↦ Subtype.ext (e.symm_apply_apply y.1)
      right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y.1) }

@[simp]
theorem rationalGeneralSpinInvAmbientShellEquiv_coe
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (d : V.RationalCliffordGeneralSpinGroup)
    (y : V.anisotropicRationalAmbientShell x ℚ) :
    (V.rationalGeneralSpinInvAmbientShellEquiv x d y).1 =
      V.specialOrthogonalMatrixGroupIsometryEquiv ℚ
        (d.matrixGroup⁻¹) y.1 :=
  rfl

/-- The intrinsic ordinary theta density on the literal rational norm shell
through `x`.  Every summand is the existing unweighted ambient theta
summand. -/
def fullAdelicCliffordGeneralSpinRationalShellTheta
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicCliffordGeneralSpinGroup) : ℝ≥0∞ :=
  ∑' y : V.anisotropicRationalAmbientShell x ℚ,
    V.fullAdelicCliffordGeneralSpinRationalVectorThetaSummand Phi g y.1

/-- A measurable nonnegative test function gives a measurable ambient shell
theta density. -/
theorem measurable_fullAdelicCliffordGeneralSpinRationalShellTheta
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    Measurable (V.fullAdelicCliffordGeneralSpinRationalShellTheta x Phi) := by
  unfold fullAdelicCliffordGeneralSpinRationalShellTheta
  exact Measurable.ennreal_tsum fun y ↦
    V.measurable_fullAdelicCliffordGeneralSpinRationalVectorThetaSummand
      Phi hPhi y.1

/-- The intrinsic rational-shell theta density is invariant under the full
rational adelic `GSpin` diagonal. -/
theorem fullAdelicCliffordGeneralSpinRationalShellTheta_rational_mul
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinRationalShellTheta x Phi
        ((delta : V.FullAdelicCliffordGeneralSpinGroup) * g) =
      V.fullAdelicCliffordGeneralSpinRationalShellTheta x Phi g := by
  rcases delta.2 with ⟨d, hd⟩
  have hdelta :
      (delta : V.FullAdelicCliffordGeneralSpinGroup) =
        V.rationalCliffordGeneralSpinFullAdelicDiagonalHom d := hd.symm
  rw [hdelta]
  unfold fullAdelicCliffordGeneralSpinRationalShellTheta
  simp_rw [fullAdelicCliffordGeneralSpinRationalVectorThetaSummand,
    fullAdelicCliffordGeneralSpinRationalVectorAction_rationalDiagonal_mul,
    ← V.rationalGeneralSpinInvAmbientShellEquiv_coe x d]
  exact (V.rationalGeneralSpinInvAmbientShellEquiv x d).tsum_eq
    (fun y ↦
      Phi (V.fullAdelicCliffordGeneralSpinRationalVectorAction g y.1))

/-- The intrinsic ambient rational-shell theta density on the existing left
quotient. -/
def fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient → ℝ≥0∞ :=
  Quot.lift (V.fullAdelicCliffordGeneralSpinRationalShellTheta x Phi) (by
    intro g h hrel
    rcases hrel with ⟨delta, rfl⟩
    exact (V.fullAdelicCliffordGeneralSpinRationalShellTheta_rational_mul
      x Phi delta g).symm)

@[simp]
theorem fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient_mk
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient x Phi
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap g) =
      V.fullAdelicCliffordGeneralSpinRationalShellTheta x Phi g :=
  rfl

/-- The descended ambient rational-shell theta density is measurable. -/
theorem measurable_fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    Measurable
      (V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
        x Phi) := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  intro s hs
  rcases hs with ⟨s', hs', rfl⟩
  rcases hs' with ⟨t, ht, rfl⟩
  simpa only [Set.preimage_preimage,
    fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient_mk] using
      (measurable_iff_comap_le.mp
        (V.measurable_fullAdelicCliffordGeneralSpinRationalShellTheta
          x Phi hPhi))
        ((V.fullAdelicCliffordGeneralSpinRationalShellTheta x Phi) ⁻¹' t)
        ⟨t, ht, rfl⟩

namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The represented inverse action commutes with the supplied rational
quadratic presentation on every rational vector. -/
theorem blockToAmbient_fullAdelicCliffordGeneralSpinRationalVectorAction
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup)
    (y : Fin (m + 1) → ℚ) :
    P.blockToAmbientBaseChangeIsometryEquiv hx RationalAdele
        ((P.blockSpace hx
          ).fullAdelicCliffordGeneralSpinRationalVectorAction g y) =
      V.fullAdelicCliffordGeneralSpinRationalVectorAction
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g)
        (P.blockToAmbientIsometryEquiv hx y) := by
  unfold fullAdelicCliffordGeneralSpinRationalVectorAction
  change
    P.blockToAmbientBaseChangeIsometryEquiv hx RationalAdele
        (Matrix.mulVec (g⁻¹).matrixPoint.1
          (fun i ↦ algebraMap ℚ RationalAdele (y i))) =
      Matrix.mulVec
        ((P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g)⁻¹
          ).matrixPoint.1
        (fun i ↦ algebraMap ℚ RationalAdele
          (P.blockToAmbientIsometryEquiv hx y i))
  rw [P.blockToAmbientBaseChangeIsometryEquiv_specialOrthogonal_mulVec
    hx RationalAdele]
  rw [P.blockToAmbientBaseChangeIsometryEquiv_rational hx RationalAdele]
  have hpoint :
      P.blockToAmbientSpecialOrthogonalMatrixPoint RationalAdele hx
          g⁻¹.matrixPoint =
        ((P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g)⁻¹
          ).matrixPoint := by
    change
      (P.blockToAmbientGeneralSpinIntrinsicPoint RationalAdele hx g⁻¹
        ).matrixPoint =
        ((P.blockToAmbientGeneralSpinIntrinsicPoint RationalAdele hx g)⁻¹
          ).matrixPoint
    exact congrArg
      (fun z : V.FullAdelicCliffordGeneralSpinGroup ↦ z.matrixPoint)
      ((P.blockToAmbientGeneralSpinMulEquiv RationalAdele hx).map_inv g)
  rw [hpoint]

/-- The block theta-orbit density, tested after the shell presentation map,
is exactly the intrinsic ambient rational-shell theta density. -/
theorem fullAdelicNonisotropicLastShellThetaOrbitSum_eq_ambientRationalShell
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    [NeZero m]
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup) :
    P.lowerSpace.fullAdelicNonisotropicLastShellThetaOrbitSum
        (V.nativeRationalQuadraticForm x) hx
        (fun y ↦ Phi (P.blockToAmbientShellHomeomorph
          hx RationalAdele y).1) g =
      V.fullAdelicCliffordGeneralSpinRationalShellTheta x Phi
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g) := by
  let Psi : (Fin (m + 1) → RationalAdele) → ℝ≥0∞ :=
    fun z ↦ Phi (P.blockToAmbientBaseChangeIsometryEquiv
      hx RationalAdele z)
  let e := P.blockToAmbientShellEquiv hx ℚ
  calc
    P.lowerSpace.fullAdelicNonisotropicLastShellThetaOrbitSum
        (V.nativeRationalQuadraticForm x) hx
        (fun y ↦ Phi (P.blockToAmbientShellHomeomorph
          hx RationalAdele y).1) g =
      ∑' y : P.lowerSpace.nonisotropicLastQuadraticShell
          (V.nativeRationalQuadraticForm x) hx ℚ,
        (P.blockSpace hx
          ).fullAdelicCliffordGeneralSpinRationalVectorThetaSummand
            Psi g y.1 := by
      change
        P.lowerSpace.fullAdelicNonisotropicLastShellThetaOrbitSum
            (V.nativeRationalQuadraticForm x) hx
            (fun y ↦ Psi y.1) g = _
      exact
        P.lowerSpace.fullAdelicNonisotropicLastShellThetaOrbitSum_eq_rationalShell
          (V.nativeRationalQuadraticForm x) hx Psi g
    _ = ∑' y : P.lowerSpace.nonisotropicLastQuadraticShell
          (V.nativeRationalQuadraticForm x) hx ℚ,
        Phi (P.blockToAmbientBaseChangeIsometryEquiv hx RationalAdele
          ((P.blockSpace hx
            ).fullAdelicCliffordGeneralSpinRationalVectorAction g y.1)) := rfl
    _ = ∑' y : P.lowerSpace.nonisotropicLastQuadraticShell
            (V.nativeRationalQuadraticForm x) hx ℚ,
          Phi
            (V.fullAdelicCliffordGeneralSpinRationalVectorAction
              (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g)
              (e y).1) := by
      apply tsum_congr
      intro y
      apply congrArg Phi
      have hey :
          (e y).1 = P.blockToAmbientIsometryEquiv hx y.1 := by
        change P.blockToAmbientBaseChangeIsometryEquiv hx ℚ y.1 = _
        simpa using
          P.blockToAmbientBaseChangeIsometryEquiv_rational hx ℚ y.1
      rw [hey]
      exact P.blockToAmbient_fullAdelicCliffordGeneralSpinRationalVectorAction
        hx g y.1
    _ = ∑' y : V.anisotropicRationalAmbientShell x ℚ,
          Phi
            (V.fullAdelicCliffordGeneralSpinRationalVectorAction
              (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g)
              y.1) := by
      exact e.tsum_eq
        (fun y ↦ Phi
          (V.fullAdelicCliffordGeneralSpinRationalVectorAction
            (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g)
            y.1))
    _ = V.fullAdelicCliffordGeneralSpinRationalShellTheta x Phi
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g) := rfl

/-- The exact density comparison descends through the existing quotient
homeomorphism. -/
theorem fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient_eq_ambient
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    [NeZero m]
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (C : (P.blockSpace hx).FullAdelicCliffordGeneralSpinLeftQuotient) :
    P.lowerSpace.fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient
        (V.nativeRationalQuadraticForm x) hx
        (fun y ↦ Phi (P.blockToAmbientShellHomeomorph
          hx RationalAdele y).1) C =
      V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient x Phi
        (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx C) := by
  refine Quot.inductionOn C ?_
  intro g
  change
    P.lowerSpace.fullAdelicNonisotropicLastShellThetaOrbitSum
        (V.nativeRationalQuadraticForm x) hx
        (fun y ↦ Phi (P.blockToAmbientShellHomeomorph
          hx RationalAdele y).1) g =
      V.fullAdelicCliffordGeneralSpinRationalShellTheta x Phi
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx g)
  exact P.fullAdelicNonisotropicLastShellThetaOrbitSum_eq_ambientRationalShell
    hx Phi g

/-- The block horizontal theta cutoff maps to the intrinsic ambient
rational-shell density on the existing horizontal quotient measure.  The
only scalar is the already fixed horizontal Haar comparison scalar. -/
theorem map_fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure_eq_ambient
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    [NeZero m]
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    Measure.map
        (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx)
        (P.lowerSpace.fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure
          (V.nativeRationalQuadraticForm x) hx
          (fun y ↦ Phi (P.blockToAmbientShellHomeomorph
            hx RationalAdele y).1)) =
      P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx •
        (V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
          |>.quotientMeasure).withDensity
            (V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
              x Phi) := by
  let eX := P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx
  let muB := (P.blockSpace hx
    ).fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure
  let muA := V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure
  let thetaA :=
    V.fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient x Phi
  have hthetaA : Measurable thetaA :=
    V.measurable_fullAdelicCliffordGeneralSpinRationalShellThetaOnLeftQuotient
      x Phi hPhi
  have hdensity :
      P.lowerSpace.fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient
          (V.nativeRationalQuadraticForm x) hx
          (fun y ↦ Phi (P.blockToAmbientShellHomeomorph
            hx RationalAdele y).1) =
        thetaA ∘ eX := by
    funext C
    exact
      P.fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient_eq_ambient
        hx Phi C
  change Measure.map eX (muB.withDensity _) = _
  rw [hdensity]
  calc
    Measure.map eX (muB.withDensity (thetaA ∘ eX)) =
        (Measure.map eX muB).withDensity thetaA :=
      PositiveDefiniteIntegralLattice.map_withDensity_comp_of_measurable
        eX muB thetaA eX.measurable hthetaA
    _ =
        (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx •
          muA).withDensity thetaA := by
      rw [P.map_blockToAmbientFullAdelicGeneralSpinHorizontalQuotientMeasure_eq_smul]
    _ = P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx •
          muA.withDensity thetaA := by
      ext s hs
      rw [withDensity_apply _ hs, Measure.coe_nnreal_smul_apply,
        withDensity_apply _ hs, Measure.restrict_smul,
        lintegral_smul_measure]
      rfl

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
