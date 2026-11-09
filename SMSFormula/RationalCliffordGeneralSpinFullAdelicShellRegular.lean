import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellMeasureInvariant
import SMSFormula.RationalAdeleRankOneQuadraticPhase
import SMSFormula.TransitiveOrbitHomeomorph
import Mathlib.Algebra.Group.Action.TransferInstance

/-!
# Regularity and nonvanishing of the existing native shell measure

Upgrade the continuous quotient bijection using the transitive matrix
action and the open-orbit theorem. Its pushforward is then regular. Nonvanishing
comes from the already proved kernel bind to nonzero horizontal Haar, not from
an evaluation of a density or any new normalization.
-/

noncomputable section
open PositiveDefiniteIntegralLattice MeasureTheory

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ}
local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

variable (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)

local instance : SecondCountableTopology
    (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinGroupSecondCountableTopology
local instance : LocallyCompactSpace
    (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace
local instance : MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) := borel _
local instance : BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) := ⟨rfl⟩
local instance : MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) := borel _
local instance : BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) := ⟨rfl⟩
local instance : LocallyCompactSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  (isClosed_eq (W.nonisotropicLastExtension a ha).continuous_fullAdelicQuadraticFormValue
    continuous_const).locallyCompactSpace

/-- This action is the translate, now bundled with its group laws. -/
def fullAdelicNonisotropicLastShellMulAction :
    MulAction (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup
      (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm.mulAction
    (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup

attribute [local instance] fullAdelicNonisotropicLastShellMulAction

@[simp] theorem fullAdelicNonisotropicLastShell_smul_eq
    (g : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (x : W.nonisotropicLastQuadraticShell a ha RationalAdele) :
    g • x = W.fullAdelicNonisotropicLastShellTranslate a ha g x := rfl

local instance : ContinuousSMul (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup
    (W.nonisotropicLastQuadraticShell a ha RationalAdele) where
  continuous_smul := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change Continuous (fun p : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup ×
      W.nonisotropicLastQuadraticShell a ha RationalAdele ↦ (p.1 • p.2).val i)
    simp only [fullAdelicNonisotropicLastShell_smul_eq,
      coe_fullAdelicNonisotropicLastShellTranslate, Matrix.mulVec, dotProduct]
    exact continuous_finset_sum _ (fun j _ ↦
      (((W.nonisotropicLastExtension a ha).continuous_cliffordGeneralSpinMatrixCoordinate
        RationalAdele i j).comp continuous_fst).mul
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)))

local instance : MulAction.IsPretransitive
    (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup
    (W.nonisotropicLastQuadraticShell a ha RationalAdele) where
  exists_smul_eq x y := by
    let e := W.fullAdelicNonisotropicLastShellQuotientEquiv a ha
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup (e.symm x) (e.symm y)
    refine ⟨g, ?_⟩
    change e (g • e.symm x) = y
    rw [hg, e.apply_symm_apply]

/-- The quotient bijection is a homeomorphism on the native topologies.
The value remains a nonzero rational value throughout. -/
def fullAdelicNonisotropicLastShellQuotientHomeomorph :
    W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha ≃ₜ
      W.nonisotropicLastQuadraticShell a ha RationalAdele := by
  let e := W.fullAdelicNonisotropicLastShellQuotientEquiv a ha
  apply SMSFormula.OrbitTopology.homeomorphOfFactorsOrbit
    (G := (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (e (QuotientGroup.mk 1)) continuous_quotient_mk' QuotientGroup.mk_surjective e
    (W.continuous_fullAdelicNonisotropicLastShellQuotientMap a ha)
  intro g
  change e (QuotientGroup.mk g) = e (g • e.symm (e (QuotientGroup.mk 1)))
  rw [e.symm_apply_apply]
  congr 1
  change QuotientGroup.mk g = QuotientGroup.mk (g * 1)
  rw [mul_one]

@[simp] theorem fullAdelicNonisotropicLastShellQuotientHomeomorph_apply
    (q : W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :
    W.fullAdelicNonisotropicLastShellQuotientHomeomorph a ha q =
      W.fullAdelicNonisotropicLastShellQuotientMap a ha q := rfl

/-- Regularity of the existing native shell measure, without a new measure. -/
theorem fullAdelicNonisotropicLastShellMeasure_regular :
    (W.fullAdelicNonisotropicLastShellMeasure a ha).Regular := by
  letI : LocallyCompactSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    W.fullAdelicShellMeasurableWeilQuotientLocallyCompact a ha
  letI : T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    W.fullAdelicShellMeasurableWeilQuotientT2Space a ha
  letI : (W.fullAdelicNonisotropicLastShellQuotientMeasure a ha).Regular :=
    RealRMK.regular_rieszMeasure (W.fullAdelicNonisotropicLastShellPositiveLinearMap a ha)
  exact Measure.Regular.map (μ := W.fullAdelicNonisotropicLastShellQuotientMeasure a ha)
    (W.fullAdelicNonisotropicLastShellQuotientHomeomorph a ha)

/-- The old kernel bind precludes zero shell measure, since horizontal Haar is nonzero. -/
theorem fullAdelicNonisotropicLastShellMeasure_ne_zero :
    W.fullAdelicNonisotropicLastShellMeasure a ha ≠ 0 := by
  letI := (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
  intro hz
  have he := W.fullAdelicNonisotropicLastShellMeasure_bind_orbitFiberKernel_eq_horizontal a ha
  rw [hz, Measure.bind_zero_left] at he
  exact (NeZero.ne (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) he.symm

end RationalQuadraticSpaceMatrix
