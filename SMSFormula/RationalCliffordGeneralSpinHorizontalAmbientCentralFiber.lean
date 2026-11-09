import SMSFormula.RationalCliffordGeneralSpinHorizontalCentralExtensionCylinder
import SMSFormula.RationalCliffordGeneralSpinHorizontalMeasurableDescent
import SMSFormula.RationalIdeleDifferentialHaar

/-!
# The ambient differential central fiber of adelic general Spin

The fixed differential Haar measure on rational ideles acts through the
literal central inclusion on full adelic intrinsic `GSpin`.  Mapping the
product of the identity kernel and this Haar measure through central
multiplication gives a measurable s-finite kernel on the ambient group.

Horizontal exactness shows that this kernel depends only on the image in
full adelic `SO`.  For lattice forms, adelic surjectivity and measurable
descent therefore produce a genuine `SO`-indexed central-fiber kernel.  This
is the ambient counterpart of the already completed normalized compact-tail
kernel.  No section, Cartesian product decomposition, quotient measure, or
comparison with the independently chosen idele-class Haar is asserted.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open MeasurableSpace
open scoped ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalAmbientCentralFiberFullGSpinMeasurableSpace :
    MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalAmbientCentralFiberFullGSpinBorelSpace :
    BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalAmbientCentralFiberFullSOMeasurableSpace :
    MeasurableSpace V.FullAdelicSpecialOrthogonalGroup :=
  borel _

local instance horizontalAmbientCentralFiberFullSOBorelSpace :
    BorelSpace V.FullAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1800000

/-! ## The source-indexed ambient fiber -/

/-- Joint central multiplication, with the ambient `GSpin` origin first and
the differential idele coordinate second. -/
def fullAdelicDifferentialCentralJointOrbit :
    V.FullAdelicCliffordGeneralSpinGroup × RationalAdeleˣ →
      V.FullAdelicCliffordGeneralSpinGroup :=
  fun p =>
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
      V RationalAdele p.2 * p.1

theorem continuous_fullAdelicDifferentialCentralJointOrbit :
    Continuous V.fullAdelicDifferentialCentralJointOrbit := by
  exact
    (V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom.comp
      continuous_snd).mul continuous_fst

/-- Differential idele Haar translated through every ambient `GSpin`
origin, packaged as a measurable s-finite kernel. -/
noncomputable def fullAdelicDifferentialCentralFiberKernel :
    ProbabilityTheory.Kernel
      V.FullAdelicCliffordGeneralSpinGroup
      V.FullAdelicCliffordGeneralSpinGroup :=
  ProbabilityTheory.Kernel.map
    (ProbabilityTheory.Kernel.id ×ₖ
      ProbabilityTheory.Kernel.const
        V.FullAdelicCliffordGeneralSpinGroup
        rationalIdeleDifferentialHaarMeasure)
    V.fullAdelicDifferentialCentralJointOrbit

instance fullAdelicDifferentialCentralFiberKernel_isSFinite :
    ProbabilityTheory.IsSFiniteKernel
      V.fullAdelicDifferentialCentralFiberKernel := by
  unfold fullAdelicDifferentialCentralFiberKernel
  infer_instance

/-- The kernel value is the literal central-orbit pushforward of differential
idele Haar. -/
theorem fullAdelicDifferentialCentralFiberKernel_apply
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicDifferentialCentralFiberKernel x =
      Measure.map
        (fun a : RationalAdeleˣ =>
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalAdele a * x)
        rationalIdeleDifferentialHaarMeasure := by
  ext A hA
  rw [fullAdelicDifferentialCentralFiberKernel,
    ProbabilityTheory.Kernel.map_apply'
      _ V.continuous_fullAdelicDifferentialCentralJointOrbit.measurable
      _ hA,
    ProbabilityTheory.Kernel.id_prod_apply' _ x
      (V.continuous_fullAdelicDifferentialCentralJointOrbit.measurable hA),
    ProbabilityTheory.Kernel.const_apply]
  change rationalIdeleDifferentialHaarMeasure
      ((fun a : RationalAdeleˣ =>
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele a * x) ⁻¹' A) =
    Measure.map
      (fun a : RationalAdeleˣ =>
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele a * x)
      rationalIdeleDifferentialHaarMeasure A
  have horbit : Measurable
      (fun a : RationalAdeleˣ =>
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele a * x) :=
    (V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom.comp
      continuous_id).mul continuous_const |>.measurable
  exact (Measure.map_apply horbit hA).symm

/-- Translating the origin by an adelic central scalar does not change its
differential central-fiber measure. -/
theorem fullAdelicDifferentialCentralFiberKernel_scalar_mul
    (a : RationalAdeleˣ)
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicDifferentialCentralFiberKernel
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele a * x) =
      V.fullAdelicDifferentialCentralFiberKernel x := by
  rw [V.fullAdelicDifferentialCentralFiberKernel_apply,
    V.fullAdelicDifferentialCentralFiberKernel_apply]
  let orbit := fun b : RationalAdeleˣ =>
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
      V RationalAdele b * x
  let rightMul := fun b : RationalAdeleˣ => b * a
  have horbit : Measurable orbit :=
    (V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom.comp
      continuous_id).mul continuous_const |>.measurable
  have hright : Measurable rightMul :=
    (continuous_id.mul continuous_const : Continuous rightMul).measurable
  have hfun :
      (fun b : RationalAdeleˣ =>
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalAdele b *
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalAdele a * x)) = orbit ∘ rightMul := by
    funext b
    simp only [Function.comp_apply, rightMul, orbit, map_mul, mul_assoc]
  rw [hfun, ← Measure.map_map horbit hright]
  exact congrArg (Measure.map orbit)
    (Measure.IsMulRightInvariant.map_mul_right_eq_self a)

/-- The differential central-fiber kernel is constant on the exact fibers of
the ambient map `GSpin(A) → SO(A)`. -/
theorem fullAdelicDifferentialCentralFiberKernel_eq_of_sameSO
    {x y : V.FullAdelicCliffordGeneralSpinGroup}
    (hxy : V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom y =
      V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x) :
    V.fullAdelicDifferentialCentralFiberKernel y =
      V.fullAdelicDifferentialCentralFiberKernel x := by
  let k := y * x⁻¹
  have hk : k ∈
      (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
        V RationalAdele).ker := by
    change V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom k = 1
    dsimp [k]
    rw [map_mul, map_inv, hxy]
    simp
  rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom
    V RationalAdele] at hk
  rcases hk with ⟨a, ha⟩
  have hy : y =
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V RationalAdele a * x := by
    calc
      y = (y * x⁻¹) * x := by simp [mul_assoc]
      _ = CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele a * x := by rw [ha]
  rw [hy, V.fullAdelicDifferentialCentralFiberKernel_scalar_mul]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalAmbientCentralFiberLatticeFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalAmbientCentralFiberLatticeFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalAmbientCentralFiberLatticeFullSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  borel _

local instance horizontalAmbientCentralFiberLatticeFullSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1800000

/-! ## Measurable descent to ambient `SO` -/

/-- A definition-only ambient `GSpin` lift of an adelic `SO` point. -/
noncomputable def fullAdelicDifferentialCentralFiberLift
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  Classical.choose
    (L.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom_surjective h)

@[simp]
theorem fullAdelicDifferentialCentralFiberLift_spec
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
        (L.fullAdelicDifferentialCentralFiberLift h) = h :=
  Classical.choose_spec
    (L.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom_surjective h)

/-- The representative-independent differential central-fiber measure above
an ambient adelic `SO` point. -/
noncomputable def fullAdelicDifferentialCentralFiberMeasureAtSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    Measure
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  L.rationalQuadraticSpaceMatrix.fullAdelicDifferentialCentralFiberKernel
    (L.fullAdelicDifferentialCentralFiberLift h)

/-- Pullback to any actual ambient `GSpin` origin recovers its literal
differential central-orbit kernel. -/
theorem fullAdelicDifferentialCentralFiberMeasureAtSO_projection
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    L.fullAdelicDifferentialCentralFiberMeasureAtSO
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
          x) =
      L.rationalQuadraticSpaceMatrix.fullAdelicDifferentialCentralFiberKernel x := by
  unfold fullAdelicDifferentialCentralFiberMeasureAtSO
  exact
    L.rationalQuadraticSpaceMatrix.fullAdelicDifferentialCentralFiberKernel_eq_of_sameSO
      (L.fullAdelicDifferentialCentralFiberLift_spec _)

/-- The pullback of the descended family is the already measurable
source-indexed ambient family. -/
theorem fullAdelicDifferentialCentralFiberMeasureAtSO_comp_projection
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    L.fullAdelicDifferentialCentralFiberMeasureAtSO ∘
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom =
      L.rationalQuadraticSpaceMatrix.fullAdelicDifferentialCentralFiberKernel := by
  funext x
  exact L.fullAdelicDifferentialCentralFiberMeasureAtSO_projection x

/-- The representative-independent ambient fiber family is measurable on
full adelic `SO`; measurable descent uses the existing Polish structure on
full adelic intrinsic `GSpin` and the literal surjective projection. -/
theorem measurable_fullAdelicDifferentialCentralFiberMeasureAtSO
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    Measurable L.fullAdelicDifferentialCentralFiberMeasureAtSO := by
  let V := L.rationalQuadraticSpaceMatrix
  let f := V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
  letI : StandardBorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupStandardBorelSpaceForMeasurableDescent
  letI : SecondCountableTopology
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv.isEmbedding.secondCountableTopology
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  letI : T2Space
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup := by
    infer_instance
  letI : T1Space V.FullAdelicSpecialOrthogonalGroup := T2Space.t1Space
  letI : CountablyGenerated V.FullAdelicSpecialOrthogonalGroup :=
    BorelSpace.countablyGenerated
  letI : SeparatesPoints V.FullAdelicSpecialOrthogonalGroup := by
    constructor
    intro x y hxy
    by_contra hne
    have hmeas : MeasurableSet ({y}ᶜ :
        Set V.FullAdelicSpecialOrthogonalGroup) :=
      (isClosed_singleton : IsClosed ({y} :
        Set V.FullAdelicSpecialOrthogonalGroup)).isOpen_compl.measurableSet
    have hx : x ∈ ({y}ᶜ : Set V.FullAdelicSpecialOrthogonalGroup) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne
    exact (hxy _ hmeas hx) (by simp)
  letI : CountablySeparated V.FullAdelicSpecialOrthogonalGroup :=
    countablySeparated_of_separatesPoints
  have hf : Measurable f :=
    V.continuous_fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom.measurable
  have hsurj : Function.Surjective f :=
    L.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom_surjective
  apply (hf.measurable_comp_iff_of_surjective hsurj).mp
  rw [L.fullAdelicDifferentialCentralFiberMeasureAtSO_comp_projection]
  exact V.fullAdelicDifferentialCentralFiberKernel.measurable

/-- The genuine ambient `SO`-indexed differential central-fiber kernel. -/
noncomputable def fullAdelicDifferentialCentralFiberKernelAtSO
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    ProbabilityTheory.Kernel
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨L.fullAdelicDifferentialCentralFiberMeasureAtSO,
    L.measurable_fullAdelicDifferentialCentralFiberMeasureAtSO⟩

@[simp]
theorem fullAdelicDifferentialCentralFiberKernelAtSO_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    L.fullAdelicDifferentialCentralFiberKernelAtSO h =
      L.fullAdelicDifferentialCentralFiberMeasureAtSO h :=
  rfl

/-- Pulling the genuine `SO`-indexed kernel back along the ambient projection
recovers the literal differential central-orbit kernel exactly. -/
theorem fullAdelicDifferentialCentralFiberKernelAtSO_comp_projection
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    L.fullAdelicDifferentialCentralFiberKernelAtSO
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
          x) =
      L.rationalQuadraticSpaceMatrix.fullAdelicDifferentialCentralFiberKernel x := by
  rw [L.fullAdelicDifferentialCentralFiberKernelAtSO_apply]
  exact L.fullAdelicDifferentialCentralFiberMeasureAtSO_projection x

end PositiveDefiniteIntegralLattice
