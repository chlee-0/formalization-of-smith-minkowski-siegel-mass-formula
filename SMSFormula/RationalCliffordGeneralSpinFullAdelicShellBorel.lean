import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellHomogeneousSpace
import SMSFormula.RationalCliffordGeneralSpinHorizontalMeasurableDescent
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# The native Borel full-adelic block-shell quotient

The continuous bijection from the full-adelic complement-stabilizer quotient
to the existing nonisotropic shell is an equivalence of their native Borel
spaces.  The proof compares both Borel structures as exact pushforwards of
the Polish full-adelic intrinsic `GSpin` group; it does not transport an
arbitrary measurable structure through the underlying equivalence.

No quotient measure or Weil disintegration is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance fullAdelicShellBorelInfiniteT2Space : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellBorelFiniteT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellBorelT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellBorelSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellBorelSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellBorelSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellBorelSourcePolishSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    PolishSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupPolishSpaceForMeasurableDescent

noncomputable local instance fullAdelicShellBorelStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellBorelQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance fullAdelicShellBorelQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellBorelTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance fullAdelicShellBorelTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

/-- The native quotient Borel structure maps exactly to the native shell
Borel structure under the certified quotient-to-shell map. -/
theorem map_borel_fullAdelicNonisotropicLastShellQuotientMap_eq
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace.map
        (W.fullAdelicNonisotropicLastShellQuotientMap a ha)
        (borel (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha)) =
      borel (W.nonisotropicLastQuadraticShell a ha RationalAdele) := by
  letI : T2Space
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    W.fullAdelicShellBorelQuotientT2Space a ha
  letI : SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    W.fullAdelicShellBorelQuotientSecondCountable a ha
  let G := (W.nonisotropicLastExtension a ha)
    |>.FullAdelicCliffordGeneralSpinGroup
  let H := W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele
  let X := W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha
  let Y := W.nonisotropicLastQuadraticShell a ha RationalAdele
  let q : G → X := QuotientGroup.mk
  let p : G → Y :=
    CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele
  let f : X → Y := W.fullAdelicNonisotropicLastShellQuotientMap a ha
  have hq : MeasurableSpace.map q (borel G) = borel X := by
    exact continuous_quotient_mk'.map_borel_eq QuotientGroup.mk_surjective
  have hp : MeasurableSpace.map p (borel G) = borel Y := by
    exact (W.continuous_fullAdelic_nonisotropicLastShellOrbitMap a ha)
      |>.map_borel_eq
        (CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective
          W a ha)
  calc
    MeasurableSpace.map f (borel X) =
        MeasurableSpace.map f (MeasurableSpace.map q (borel G)) := by rw [hq]
    _ = MeasurableSpace.map (f ∘ q) (borel G) :=
      MeasurableSpace.map_comp
    _ = MeasurableSpace.map p (borel G) := by
      congr 1
    _ = borel Y := hp

/-- The certified quotient-to-shell equivalence is measurable in both
directions for the native quotient and shell Borel structures. -/
def fullAdelicNonisotropicLastShellQuotientMeasurableEquiv
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha ≃ᵐ
      W.nonisotropicLastQuadraticShell a ha RationalAdele := by
  letI : T2Space
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    W.fullAdelicShellBorelQuotientT2Space a ha
  letI : SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    W.fullAdelicShellBorelQuotientSecondCountable a ha
  refine
    { toEquiv := W.fullAdelicNonisotropicLastShellQuotientEquiv a ha
      measurable_toFun :=
        (W.continuous_fullAdelicNonisotropicLastShellQuotientMap a ha).measurable
      measurable_invFun := ?_ }
  rw [measurable_iff_le_map]
  have hQ :
      QuotientGroup.measurableSpace
          (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
            a ha RationalAdele) =
        borel (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
    BorelSpace.measurable_eq
  have hY :
      W.fullAdelicShellBorelTargetMeasurableSpace a ha =
        borel (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
    BorelSpace.measurable_eq
  rw [hQ, hY]
  change borel (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) ≤
    MeasurableSpace.map
      (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm
      (borel (W.nonisotropicLastQuadraticShell a ha RationalAdele))
  rw [← W.map_borel_fullAdelicNonisotropicLastShellQuotientMap_eq a ha]
  rw [MeasurableSpace.map_comp]
  have hcomp :
      (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm ∘
          W.fullAdelicNonisotropicLastShellQuotientMap a ha =
        id := by
    funext x
    exact (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm_apply_apply x
  rw [hcomp]
  rfl

@[simp]
theorem fullAdelicNonisotropicLastShellQuotientMeasurableEquiv_mk
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinGroup) :
    W.fullAdelicNonisotropicLastShellQuotientMeasurableEquiv a ha
        (QuotientGroup.mk g) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele g := by
  simp [fullAdelicNonisotropicLastShellQuotientMeasurableEquiv]

end RationalQuadraticSpaceMatrix
