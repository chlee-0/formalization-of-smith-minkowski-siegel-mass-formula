import SMSFormula.RationalCliffordGeneralSpinHorizontalIntegralSOMarginal
import SMSFormula.RationalIdeleDifferentialLocalFactor
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# The normalized central-unit fiber of an integral horizontal GSpin factor

At a horizontal good finite place, integral scalar units map into the compact
integral `GSpin` subgroup.  Horizontal exactness and integrality of square
roots identify their image with the complete kernel of projection to integral
`SO`.  The already fixed probability Haar on integral units therefore gives
the literal normalized central fiber measure.

Translating that measure through an integral `GSpin` origin defines a
measurable source-indexed fiber kernel.  Averaging normalized integral
`GSpin` Haar against this kernel returns the same Haar measure.  This is the
compact central convolution identity needed before descent to the certified
`SO` marginal.  Representative independence and standard-Borel measurable
descent then give the genuine `SO`-indexed fiber kernel and its normalized
local Weil identity.  The chosen lift occurs only in the definition of that
descended kernel; no measurable group section or Cartesian-product
identification of the extension is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open Filter MeasurableSpace
open scoped ENNReal ProbabilityTheory
open scoped Uniformity

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalIntegralCentralFiberPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalIntegralCentralFiberDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalIntegralCentralFiberGroupMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance horizontalIntegralCentralFiberGroupBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

noncomputable local instance horizontalIntegralCentralFiberSOMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance horizontalIntegralCentralFiberSOBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance horizontalIntegralCentralFiberMeasurableMul₂
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    MeasurableMul₂
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  ⟨by
    apply Measurable.subtype_mk
    exact measurable_mul.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk
        (measurable_subtype_coe.comp measurable_snd))⟩

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

/-- Integral p-adic scalar units included in the compact horizontal `GSpin`
factor. -/
def padicCliffordGeneralSpinHorizontalIntegralScalarHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 →*
      V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v where
  toFun z := ⟨
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
      V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] z.1,
    V.padicCliffordGeneralSpin_ofScalar_isIntegral v.1
      (V.cliffordGeneralSpinIntegralStructureAt_of_not_mem_horizontalBadPlaces
        v.1 (fun hv => v.2 (Finset.mem_union_right S hv))) z.1 z.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' := by
    intro z w
    apply Subtype.ext
    exact map_mul _ _ _

theorem continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Continuous (V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v) := by
  apply Continuous.subtype_mk
  exact
    (V.continuous_cliffordGeneralSpinScalarGroupHom
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).comp continuous_subtype_val

theorem padicCliffordGeneralSpinHorizontalIntegralScalarHom_injective
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Function.Injective
      (V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v) := by
  intro z w hzw
  apply Subtype.ext
  apply Units.ext
  apply V.cliffordCoordinateBaseChange_algebraMap_injective
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
  have h := congrArg
    (fun x : V.HeightOnePadicCliffordGeneralSpinGroup v.1 =>
      (x.cliffordUnit :
        V.cliffordCoordinateBaseChangeAlgebra
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))
    (congrArg Subtype.val hzw)
  simpa only [CliffordGeneralSpinIntrinsicPoint.scalarGroupHom,
    CliffordGeneralSpinIntrinsicPoint.scalarMonoidHom,
    CliffordGeneralSpinIntrinsicPoint.ofScalar,
    CliffordGeneralSpinIntrinsicPoint.coe_scalarCliffordUnit] using h

/-- The integral scalar units are exactly the kernel of the compact
horizontal projection to integral `SO`. -/
theorem range_padicCliffordGeneralSpinHorizontalIntegralScalarHom_eq_ker_toSO
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    (V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v).range =
      (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v).ker := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    apply Subtype.ext
    exact CliffordGeneralSpinIntrinsicPoint.ofScalar_matrixGroup
      V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] z.1
  · intro hx
    have hmatrix : x.1.matrixGroup = 1 := by
      exact congrArg Subtype.val hx
    obtain ⟨z, hz⟩ :=
      CliffordGeneralSpinIntrinsicPoint.exists_scalar_eq_of_matrixGroup_eq_one
        V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] x.1 hmatrix
    have hzsq : z ^ 2 ∈ padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
      have hxnu := x.2.2.2.1
      rw [← hz] at hxnu
      simpa only [CliffordGeneralSpinIntrinsicPoint.ofScalar_similitude] using hxnu
    have hzIntegral : z ∈ padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 :=
      mem_padicIntegralUnitsSubgroup_of_sq_mem
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 z hzsq
    refine ⟨⟨z, hzIntegral⟩, ?_⟩
    apply Subtype.ext
    exact hz

/-- The literal probability measure on the compact central-unit fiber,
viewed inside the integral horizontal `GSpin` factor. -/
def padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Measure (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  Measure.map
    (V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v)
    (rationalPadicIdeleIntegralFactorMeasure v.1)

instance padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure_isProbability
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    IsProbabilityMeasure
      (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v) := by
  unfold padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure
  exact Measure.isProbabilityMeasure_map
    (V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom S v
      ).measurable.aemeasurable

/-- Projection to integral `SO` collapses the normalized central-unit fiber
to the identity atom. -/
theorem map_padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure_toSO
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Measure.map
        (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v)
        (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v) =
      Measure.dirac 1 := by
  rw [padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure,
    Measure.map_map
      (V.continuous_padicCliffordGeneralSpinHorizontalIntegralToSO S v).measurable
      (V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom S v).measurable]
  calc
    Measure.map
        ((V.padicCliffordGeneralSpinHorizontalIntegralToSO S v) ∘
          (V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v))
        (rationalPadicIdeleIntegralFactorMeasure v.1) =
        Measure.map (fun _ => 1)
          (rationalPadicIdeleIntegralFactorMeasure v.1) := by
      congr 1
      funext z
      apply Subtype.ext
      exact CliffordGeneralSpinIntrinsicPoint.ofScalar_matrixGroup
        V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] z.1
    _ = (rationalPadicIdeleIntegralFactorMeasure v.1 Set.univ) •
        Measure.dirac 1 := Measure.map_const _ _
    _ = Measure.dirac 1 := by simp

/-- Joint parametrization of the central fiber through an integral `GSpin`
origin. -/
def padicCliffordGeneralSpinHorizontalIntegralCentralJointOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v ×
        V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v →
      V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v :=
  fun p => p.2 * p.1

theorem continuous_padicCliffordGeneralSpinHorizontalIntegralCentralJointOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Continuous
      (V.padicCliffordGeneralSpinHorizontalIntegralCentralJointOrbit S v) := by
  exact continuous_snd.mul continuous_fst

theorem measurable_padicCliffordGeneralSpinHorizontalIntegralCentralJointOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Measurable
      (V.padicCliffordGeneralSpinHorizontalIntegralCentralJointOrbit S v) := by
  exact measurable_snd.mul measurable_fst

/-- The measurable kernel assigning to each integral origin its translated
normalized central-unit fiber measure. -/
def padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    ProbabilityTheory.Kernel
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  ProbabilityTheory.Kernel.map
    (ProbabilityTheory.Kernel.id ×ₖ
      ProbabilityTheory.Kernel.const
        (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
        (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v))
    (V.padicCliffordGeneralSpinHorizontalIntegralCentralJointOrbit S v)

@[simp]
theorem padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel_apply
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (g : V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v g =
      Measure.map (fun z => z * g)
        (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v) := by
  ext A hA
  rw [padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel,
    ProbabilityTheory.Kernel.map_apply'
      _
      (V.measurable_padicCliffordGeneralSpinHorizontalIntegralCentralJointOrbit
        S v) _ hA,
    ProbabilityTheory.Kernel.id_prod_apply' _ g
      (V.measurable_padicCliffordGeneralSpinHorizontalIntegralCentralJointOrbit
        S v hA),
    ProbabilityTheory.Kernel.const_apply]
  rw [Measure.map_apply (measurable_mul_const g) hA]
  rfl

/-- Averaging normalized integral horizontal `GSpin` Haar along its literal
central-unit fibers leaves that Haar measure unchanged. -/
theorem padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel_comp_normalizedHaar
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v ∘ₘ
        V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v =
      V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v := by
  let μG :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v
  let μZ :=
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind
    (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v).aemeasurable
    hf.aemeasurable]
  simp_rw [V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel_apply S v]
  simp_rw [lintegral_map hf (measurable_mul_const _)]
  calc
    ∫⁻ g, ∫⁻ z, f (z * g) ∂μZ ∂μG =
        ∫⁻ z, ∫⁻ g, f (z * g) ∂μG ∂μZ := by
      exact lintegral_lintegral_swap
        (hf.comp
          (V.measurable_padicCliffordGeneralSpinHorizontalIntegralCentralJointOrbit
            S v)).aemeasurable
    _ = ∫⁻ z, ∫⁻ g, f g ∂μG ∂μZ := by
      apply lintegral_congr
      intro z
      exact lintegral_mul_left_eq_self f z
    _ = ∫⁻ g, f g ∂μG := by
      simp [μZ]

/-! ## Descent to the integral SO quotient -/

theorem padicCliffordGeneralSpinHorizontalIntegralScalarHom_commutes
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (z : padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1)
    (g : V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :
    V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v z * g =
      g * V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v z := by
  apply Subtype.ext
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit
    V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
  apply Units.ext
  change algebraMap
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
      (V.cliffordCoordinateBaseChangeAlgebra
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]) (z.1 :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]) *
        (g.1.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]) =
      (g.1.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]) *
        algebraMap
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
          (V.cliffordCoordinateBaseChangeAlgebra
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]) z.1
  exact Algebra.commutes _ _

/-- The central-fiber probability is invariant under every literal integral
scalar translation. -/
theorem map_mul_left_padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (z : padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v.1).1) :
    Measure.map
        (fun g =>
          V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v z * g)
        (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v) =
      V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v := by
  let h := V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v
  let μ := rationalPadicIdeleIntegralFactorMeasure v.1
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_const_mul (h z))]
  change
    ∫⁻ a, f (h z * a) ∂Measure.map h μ =
      ∫⁻ a, f a ∂Measure.map h μ
  calc
    ∫⁻ a, f (h z * a) ∂Measure.map h μ =
        ∫⁻ u, f (h z * h u) ∂μ :=
      lintegral_map (μ := μ) (g := h)
        (hf.comp (measurable_const_mul (h z)))
        (V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom S v
          ).measurable
    _ = ∫⁻ u, f (h u) ∂μ := by
      simpa only [map_mul] using
        (lintegral_mul_left_eq_self (μ := μ) (fun u => f (h u)) z)
    _ = ∫⁻ a, f a ∂Measure.map h μ :=
      (lintegral_map (μ := μ) (g := h) hf
        (V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom S v
          ).measurable).symm

/-- The source-indexed central-fiber kernel depends only on the integral
`SO` image of its origin. -/
theorem padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel_eq_of_sameSO
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    {g w : V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v}
    (hgw : V.padicCliffordGeneralSpinHorizontalIntegralToSO S v w =
      V.padicCliffordGeneralSpinHorizontalIntegralToSO S v g) :
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v w =
      V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v g := by
  let π := V.padicCliffordGeneralSpinHorizontalIntegralToSO S v
  let h := V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v
  let μZ := V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure S v
  have hdker : w * g⁻¹ ∈ π.ker := by
    change π (w * g⁻¹) = 1
    rw [map_mul, map_inv, hgw, mul_inv_cancel]
  have hdrange : w * g⁻¹ ∈ h.range := by
    rw [V.range_padicCliffordGeneralSpinHorizontalIntegralScalarHom_eq_ker_toSO S v]
    exact hdker
  obtain ⟨z, hz⟩ := hdrange
  have hw : w = h z * g := by
    rw [hz]
    simp [mul_assoc]
  rw [V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel_apply S v,
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel_apply S v]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_mul_const w),
    lintegral_map hf (measurable_mul_const g), hw]
  calc
    ∫⁻ k, f (k * (h z * g)) ∂μZ =
        ∫⁻ k, f ((h z * k) * g) ∂μZ := by
      apply lintegral_congr
      intro k
      rw [← mul_assoc,
        V.padicCliffordGeneralSpinHorizontalIntegralScalarHom_commutes S v z k]
    _ = ∫⁻ k, f (k * g) ∂Measure.map (fun k => h z * k) μZ := by
      exact (lintegral_map
        (hf.comp (measurable_mul_const g)) (measurable_const_mul (h z))).symm
    _ = ∫⁻ k, f (k * g) ∂μZ := by
      rw [V.map_mul_left_padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasure
        S v z]

/-- A Polish structure on a local intrinsic `GSpin` group, obtained from its
existing second-countable locally compact group topology. -/
noncomputable def padicCliffordGeneralSpinHorizontalPolishSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    PolishSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) := by
  letI : UniformSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
    IsTopologicalGroup.rightUniformSpace _
  letI : IsRightUniformGroup (V.HeightOnePadicCliffordGeneralSpinGroup v) := ⟨rfl⟩
  letI : FirstCountableTopology (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  letI : CompleteSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
    IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : (𝓤 (V.HeightOnePadicCliffordGeneralSpinGroup v)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_one'
      (V.HeightOnePadicCliffordGeneralSpinGroup v)]
    exact Filter.comap.isCountablyGenerated _ _
  letI : T1Space (V.HeightOnePadicCliffordGeneralSpinGroup v) := T2Space.t1Space
  letI : T0Space (V.HeightOnePadicCliffordGeneralSpinGroup v) := T1Space.t0Space
  letI : TopologicalSpace.IsCompletelyMetrizableSpace
      (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
    TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
  exact {}

/-- A chosen compact integral `GSpin` origin above an integral `SO` point,
used only to define the representative-independent descended kernel. -/
def padicCliffordGeneralSpinHorizontalIntegralCentralFiberLift
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hsurj : Function.Surjective
      (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v))
    (q : V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :
    V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v :=
  Classical.choose (hsurj q)

@[simp]
theorem padicCliffordGeneralSpinHorizontalIntegralCentralFiberLift_spec
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hsurj : Function.Surjective
      (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v))
    (q : V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :
    V.padicCliffordGeneralSpinHorizontalIntegralToSO S v
        (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberLift
          S v hsurj q) = q :=
  Classical.choose_spec (hsurj q)

/-- The normalized central-unit fiber measure indexed by an integral `SO`
point. -/
def padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hsurj : Function.Surjective
      (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v))
    (q : V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :
    Measure (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v
    (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberLift S v hsurj q)

theorem padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO_image
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hsurj : Function.Surjective
      (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v))
    (g : V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO
        S v hsurj (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v g) =
      V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v g := by
  unfold padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO
  exact V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel_eq_of_sameSO
    S v
    ((V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberLift_spec
      S v hsurj _).trans rfl)

theorem measurable_padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hsurj : Function.Surjective
      (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v)) :
    Measurable
      (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO
        S v hsurj) := by
  letI : PolishSpace (V.HeightOnePadicCliffordGeneralSpinGroup v.1) :=
    V.padicCliffordGeneralSpinHorizontalPolishSpace v.1
  letI : PolishSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
    (V.isCompact_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v
      ).isClosed.polishSpace
  letI : StandardBorelSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) := by
    infer_instance
  letI : SecondCountableTopology
      (V.HeightOnePadicSpecialOrthogonalGroup v.1) :=
    V.padicSpecialOrthogonalGroupSecondCountable_spinorNorm
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  letI : CountablySeparated
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) := by
    infer_instance
  apply
    ((V.continuous_padicCliffordGeneralSpinHorizontalIntegralToSO S v).measurable
      |>.measurable_comp_iff_of_surjective hsurj).mp
  have hmeas : Measurable
      (fun g =>
        V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v g) :=
    (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v).measurable
  change Measurable (fun g =>
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO
      S v hsurj (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v g))
  rw [show
    (fun g =>
      V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO
        S v hsurj (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v g)) =
      (fun g =>
        V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v g) by
      funext g
      exact
        V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO_image
          S v hsurj g]
  exact hmeas

/-- The genuine integral-`SO`-indexed normalized central-unit fiber kernel. -/
def padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernelAtSO
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hsurj : Function.Surjective
      (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v)) :
    ProbabilityTheory.Kernel
      (V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1)
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  ⟨V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO
      S v hsurj,
    V.measurable_padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO
      S v hsurj⟩

@[simp]
theorem padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernelAtSO_comp_projection
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hsurj : Function.Surjective
      (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v))
    (g : V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :
    V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernelAtSO
        S v hsurj (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v g) =
      V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v g :=
  V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberMeasureAtSO_image
    S v hsurj g

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalIntegralCentralFiberLatticePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalIntegralCentralFiberLatticeDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance horizontalIntegralCentralFiberLatticeSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance horizontalIntegralCentralFiberLatticeSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

set_option maxHeartbeats 400000 in
/-- The compact central-extension Weil identity at every good place
of the lattice: normalized integral `GSpin` Haar is the bind of normalized
integral `SO` Haar against the normalized central-unit fibers. -/
theorem padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernelAtSO_comp_normalizedSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hvAdmissible : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    let hsurj :=
      L.padicCliffordGeneralSpinHorizontalIntegralToSO_surjective
        S v hvAdmissible hvOdd
    L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernelAtSO
        S v hsurj ∘ₘ
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure
        v.1 =
      L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
        S v := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let π := V.padicCliffordGeneralSpinHorizontalIntegralToSO S v
  let μG := V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v
  let μSO := V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v.1
  let hsurj :=
    L.padicCliffordGeneralSpinHorizontalIntegralToSO_surjective
      S v hvAdmissible hvOdd
  let κ := V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernelAtSO
    S v hsurj
  have hmarginal : Measure.map π μG = μSO :=
    L.map_padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_toSO
      S v hvAdmissible hvOdd
  change κ ∘ₘ μSO = μG
  rw [← hmarginal]
  calc
    κ ∘ₘ Measure.map π μG =
        V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v ∘ₘ μG := by
      ext t ht
      rw [Measure.bind_apply ht κ.aemeasurable,
        Measure.bind_apply ht
          (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel S v).aemeasurable,
        lintegral_map (κ.measurable_coe ht)
          (V.continuous_padicCliffordGeneralSpinHorizontalIntegralToSO S v).measurable]
      apply lintegral_congr
      intro g
      exact congrArg (fun μ : Measure _ => μ t)
        (V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernelAtSO_comp_projection
          S v hsurj g)
    _ = μG :=
      V.padicCliffordGeneralSpinHorizontalIntegralCentralFiberKernel_comp_normalizedHaar
        S v

end PositiveDefiniteIntegralLattice
