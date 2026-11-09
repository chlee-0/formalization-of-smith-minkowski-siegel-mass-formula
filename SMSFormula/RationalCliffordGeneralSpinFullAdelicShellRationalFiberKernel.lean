import SMSFormula.RationalCliffordGeneralSpinBlockStabilizerVerticalBoundMeasure
import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellMeasurableWeil
import SMSFormula.RationalCliffordGeneralSpinVerticalFiberKernel
import SMSFormula.RationalCliffordGeneralSpinVerticalFiberQuotientProper
import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Rational quotient fibers over the full-adelic GSpin shell

The crossed complement Spin-fiber measure on the block rational GSpin
quotient is translated by the inverse of an ambient block GSpin point.  The
established complement-right-invariance makes this family constant on the
native shell right-cosets.  It therefore descends first to the standard
homogeneous-space quotient and then to the existing quadratic shell, without
choosing a representative or a section.

This is the rational-quotient fiber kernel needed by the exact one-shell
cutoff.  No comparison with the horizontal raw orbit-fiber kernel or shell
bind is asserted here.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance fullAdelicShellRationalFiberInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellRationalFiberFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellRationalFiberT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellRationalFiberSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellRationalFiberSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellRationalFiberSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellRationalFiberSourcePolishSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    PolishSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupPolishSpaceForMeasurableDescent

noncomputable local instance fullAdelicShellRationalFiberBoundMeasureSFinite
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    SFinite (D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
      L hn a ha hsurj) := by
  rw [CliffordSpinCandidateRawOnoTamagawaData.nonisotropicLastComplementVerticalSpinFiberBoundMeasure]
  letI : SigmaFinite (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) :=
    D.verticalSpinFiberHaarBoundMeasure_sigmaFinite L hn hsurj
  infer_instance

noncomputable local instance fullAdelicShellRationalFiberStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellRationalFiberQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance fullAdelicShellRationalFiberQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellRationalFiberQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance fullAdelicShellRationalFiberQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellRationalFiberTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance fullAdelicShellRationalFiberTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

/-- The certified inverse quotient-to-shell equivalence is measurable for the
native Borel instances used by the rational-fiber kernel. -/
theorem measurable_fullAdelicNonisotropicLastShellQuotientEquiv_symm_forRationalFiber
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    Measurable (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm := by
  rw [measurable_iff_le_map]
  change borel (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) ≤
    MeasurableSpace.map
      (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm
      (borel (W.nonisotropicLastQuadraticShell a ha RationalAdele))
  rw [← W.map_borel_fullAdelicNonisotropicLastShellQuotientMap_eq a ha]
  rw [MeasurableSpace.map_comp]
  have hcomp :
      (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm ∘
          W.fullAdelicNonisotropicLastShellQuotientMap a ha = id := by
    funext x
    exact (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm_apply_apply x
  rw [hcomp]
  rfl

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- The measurable ambient family obtained by translating the crossed block
rational-quotient measure by the inverse ambient GSpin point. -/
noncomputable def fullAdelicNonisotropicLastShellAmbientRationalFiberKernel
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Kernel
      ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup)
      ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinLeftQuotient) := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  let G := V.FullAdelicCliffordGeneralSpinGroup
  let Z := V.FullAdelicCliffordGeneralSpinLeftQuotient
  let μ := D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
    L hn a ha hsurj
  exact Kernel.map
    (Kernel.compProd (Kernel.id : Kernel G G)
      (Kernel.const (G × G) μ))
    (fun p : G × Z ↦
      V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul p.1⁻¹ p.2)

/-- At an ambient point, the rational fiber is literally the inverse right
translate of the fixed crossed complement measure. -/
theorem fullAdelicNonisotropicLastShellAmbientRationalFiberKernel_apply
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (g : (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel
        L hn a ha hsurj g =
      Measure.map
        ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g⁻¹)
        (D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
          L hn a ha hsurj) := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  let G := V.FullAdelicCliffordGeneralSpinGroup
  let Z := V.FullAdelicCliffordGeneralSpinLeftQuotient
  let μ := D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
    L hn a ha hsurj
  have hmeas : Measurable (fun p : G × Z ↦
      V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul p.1⁻¹ p.2) :=
    (V.continuous_fullAdelicCliffordGeneralSpinVerticalJointRightOrbit.comp
      (continuous_fst.inv.prodMk continuous_snd)).measurable
  ext s hs
  rw [fullAdelicNonisotropicLastShellAmbientRationalFiberKernel]
  rw [Kernel.map_apply' _ hmeas g hs]
  rw [Kernel.compProd_apply (hs.preimage hmeas)]
  change ∫⁻ b : G,
      μ (Prod.mk b ⁻¹' ((fun p : G × Z ↦
        V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul p.1⁻¹ p.2) ⁻¹' s))
      ∂Measure.dirac g = _
  rw [lintegral_dirac]
  rw [Measure.map_apply
    (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul g⁻¹) hs]
  rfl

/-- Changing the ambient point within its native shell right coset does not
change the translated rational-quotient fiber.  The inverse is essential:
`(gk)⁻¹ = k⁻¹g⁻¹`, and the `k⁻¹` translate is absorbed by the fixed
complement-right-invariance theorem. -/
theorem fullAdelicNonisotropicLastShellAmbientRationalFiberKernel_mul
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (g : (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup)
    (k : L.rationalQuadraticSpaceMatrix
      |>.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha) :
    D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel
        L hn a ha hsurj (g * k.1) =
      D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel
        L hn a ha hsurj g := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  let μ := D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
    L hn a ha hsurj
  let e := W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
    a ha RationalAdele
  let x : W.FullAdelicCliffordGeneralSpinGroup := e.symm k⁻¹
  have hx : W.nonisotropicLastComplementGeneralSpinPoint
      a ha RationalAdele x = k.1⁻¹ := by
    change (e x).1 = k.1⁻¹
    have hex : e x = k⁻¹ := by simp [x]
    rw [hex]
    rfl
  rw [D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel_apply,
    D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel_apply]
  rw [mul_inv_rev]
  calc
    Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
          (k.1⁻¹ * g⁻¹)) μ =
      Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g⁻¹)
        (Measure.map
          (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
            (W.nonisotropicLastComplementGeneralSpinPoint
              a ha RationalAdele x)) μ) := by
        rw [Measure.map_map
          (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul g⁻¹)
          (V.measurable_fullAdelicCliffordGeneralSpinLeftQuotientRightMul
            (W.nonisotropicLastComplementGeneralSpinPoint
              a ha RationalAdele x))]
        congr 1
        funext z
        change
          V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
              (k.1⁻¹ * g⁻¹) z =
            V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g⁻¹
              (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
                (W.nonisotropicLastComplementGeneralSpinPoint
                  a ha RationalAdele x) z)
        rw [V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul_rightMul]
        rw [hx]
    _ = Measure.map
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g⁻¹) μ := by
      rw [D.map_nonisotropicLastComplementVerticalSpinFiberBoundMeasure_rightMul
        L hn a ha hsurj x]

/-- The section-free rational fiber measure on the standard native shell
quotient. -/
noncomputable def fullAdelicNonisotropicLastShellQuotientRationalFiberMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    L.rationalQuadraticSpaceMatrix.FullAdelicNonisotropicLastShellHomogeneousSpace
        a ha →
      Measure
        ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinLeftQuotient) :=
  Quotient.lift
    (D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel
      L hn a ha hsurj)
    (fun g h hrel ↦ by
      let W := L.rationalQuadraticSpaceMatrix
      change QuotientGroup.leftRel
        (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
          a ha RationalAdele) g h at hrel
      rw [QuotientGroup.leftRel_apply] at hrel
      let k : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha :=
        ⟨g⁻¹ * h, hrel⟩
      have hh : h = g * k.1 := by
        change h = g * (g⁻¹ * h)
        symm
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [hh, D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel_mul
        L hn a ha hsurj g k])

@[simp]
theorem fullAdelicNonisotropicLastShellQuotientRationalFiberMeasure_mk
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (g : (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    D.fullAdelicNonisotropicLastShellQuotientRationalFiberMeasure
        L hn a ha hsurj (QuotientGroup.mk g) =
      D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel
        L hn a ha hsurj g :=
  rfl

/-- The descended rational fiber varies measurably in the native quotient
Borel structure. -/
theorem measurable_fullAdelicNonisotropicLastShellQuotientRationalFiberMeasure
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Measurable
      (D.fullAdelicNonisotropicLastShellQuotientRationalFiberMeasure
        L hn a ha hsurj) := by
  let W := L.rationalQuadraticSpaceMatrix
  letI : T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    W.fullAdelicShellRationalFiberQuotientT2Space a ha
  letI : SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    W.fullAdelicShellRationalFiberQuotientSecondCountable a ha
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let X := W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha
  let q : G → X := QuotientGroup.mk
  rw [measurable_iff_le_map]
  change Measure.instMeasurableSpace ≤
    MeasurableSpace.map
      (D.fullAdelicNonisotropicLastShellQuotientRationalFiberMeasure
        L hn a ha hsurj) (borel X)
  have hq : MeasurableSpace.map q (borel G) = borel X :=
    continuous_quotient_mk'.map_borel_eq QuotientGroup.mk_surjective
  rw [← hq, MeasurableSpace.map_comp]
  exact
    (D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel
      L hn a ha hsurj).measurable.le_map

/-- The native-Borel rational-fiber kernel on the standard shell quotient. -/
noncomputable def fullAdelicNonisotropicLastShellQuotientRationalFiberKernel
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Kernel
      (L.rationalQuadraticSpaceMatrix
        |>.FullAdelicNonisotropicLastShellHomogeneousSpace a ha)
      ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinLeftQuotient) where
  toFun := D.fullAdelicNonisotropicLastShellQuotientRationalFiberMeasure
    L hn a ha hsurj
  measurable' :=
    D.measurable_fullAdelicNonisotropicLastShellQuotientRationalFiberMeasure
      L hn a ha hsurj

@[simp]
theorem fullAdelicNonisotropicLastShellQuotientRationalFiberKernel_mk
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (g : (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    D.fullAdelicNonisotropicLastShellQuotientRationalFiberKernel
        L hn a ha hsurj (QuotientGroup.mk g) =
      Measure.map
        ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g⁻¹)
        (D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
          L hn a ha hsurj) := by
  exact D.fullAdelicNonisotropicLastShellAmbientRationalFiberKernel_apply
    L hn a ha hsurj g

/-- The rational-quotient fiber kernel on the existing nonisotropic shell,
obtained by evaluating the quotient kernel through the already certified
measurable inverse. -/
noncomputable def fullAdelicNonisotropicLastShellRationalFiberKernel
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Kernel
      (L.rationalQuadraticSpaceMatrix
        |>.nonisotropicLastQuadraticShell a ha RationalAdele)
      ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinLeftQuotient) :=
  Kernel.comap
    (D.fullAdelicNonisotropicLastShellQuotientRationalFiberKernel
      L hn a ha hsurj)
    (L.rationalQuadraticSpaceMatrix
      |>.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm
    (L.rationalQuadraticSpaceMatrix
      |>.measurable_fullAdelicNonisotropicLastShellQuotientEquiv_symm_forRationalFiber
        a ha)

/-- At the actual shell orbit of `g`, the rational fiber is the literal
inverse right translate of the fixed crossed complement measure. -/
theorem fullAdelicNonisotropicLastShellRationalFiberKernel_orbit
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (g : (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    D.fullAdelicNonisotropicLastShellRationalFiberKernel
        L hn a ha hsurj
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          L.rationalQuadraticSpaceMatrix a ha RationalAdele g) =
      Measure.map
        ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g⁻¹)
        (D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
          L hn a ha hsurj) := by
  let W := L.rationalQuadraticSpaceMatrix
  rw [fullAdelicNonisotropicLastShellRationalFiberKernel, Kernel.comap_apply]
  have hclass :
      (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm
          (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele g) = QuotientGroup.mk g := by
    apply (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).injective
    simp
  rw [hclass]
  exact D.fullAdelicNonisotropicLastShellQuotientRationalFiberKernel_mk
    L hn a ha hsurj g

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
