import SMSFormula.RationalCliffordGeneralSpinLocalMultiplicationBridge
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Local differential measures on intrinsic general-Spin charts

The horizontal local parameter map for intrinsic `GSpin` is the product of
the scalar square map and the fixed Spin-to-`SO` chart.  This file equips its
target with the literal product of Mathlib's reference Haar measure on the
local unit group and the already fixed invariant-differential `SO` measure.
Inverse transport through the chosen product chart gives the source measure;
transport through scalar-times-Spin multiplication then gives a measure on
the intrinsic `GSpin` chart.

The combined map `(nu, pi)` sends this intrinsic chart measure exactly to the
restriction of the fixed product measure.  Thus the local horizontal scale is
recorded without an appeal to Haar uniqueness.  No ambient `GSpin` Haar
measure, adelic product, quotient disintegration or Tamagawa comparison is
constructed here.
-/

noncomputable section

open MeasureTheory
open Topology

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 200000

noncomputable local instance localDifferentialRealUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable local instance localDifferentialRealUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance localDifferentialPadicUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance localDifferentialPadicUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance localDifferentialRealSchemeSOGroupMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance localDifferentialRealSchemeSOGroupBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable local instance localDifferentialRealGeneralSpinMeasurableSpace :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℝ) := borel _

noncomputable local instance localDifferentialRealGeneralSpinBorelSpace :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℝ) := ⟨rfl⟩

noncomputable local instance localDifferentialPadicGeneralSpinMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := borel _

noncomputable local instance localDifferentialPadicGeneralSpinBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := ⟨rfl⟩

/-! ## Real place -/

/-- The fixed horizontal differential product measure at the real place. -/
noncomputable def realCliffordGeneralSpinHorizontalDifferentialProductMeasure :
    Measure (ℝˣ × V.RealSpecialOrthogonalGroup) :=
  (Measure.haar : Measure ℝˣ).prod
    V.realInvariantDifferentialGroupMeasure

/-- Restriction of the real horizontal differential product measure to the
target subtype of the chosen square/Spin chart. -/
noncomputable def
    realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure :
    Measure V.realCliffordGeneralSpinHorizontalProductIdentityChart.target :=
  Measure.comap Subtype.val
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure

/-- Exact inverse transport of the fixed real product measure through the
chosen square/Spin chart. -/
noncomputable def
    realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure :
    Measure V.realCliffordGeneralSpinHorizontalProductIdentityChart.source :=
  Measure.map
    V.realCliffordGeneralSpinHorizontalProductIdentityChart.toHomeomorphSourceTarget.symm
    V.realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure

/-- The real square/Spin chart sends its source measure exactly to the fixed
product target measure. -/
theorem
    map_realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure :
    Measure.map
        V.realCliffordGeneralSpinHorizontalProductIdentityChart.toHomeomorphSourceTarget
        V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure =
      V.realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure := by
  rw [realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure]
  exact MeasurableEquiv.map_map_symm
    V.realCliffordGeneralSpinHorizontalProductIdentityChart.toHomeomorphSourceTarget.toMeasurableEquiv

/-- The literal real square/Spin parameter map pushes the chosen source
measure to the restriction of the fixed horizontal product measure. -/
theorem
    map_realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_apply :
    Measure.map
        (fun x :
            V.realCliffordGeneralSpinHorizontalProductIdentityChart.source ↦
          V.realCliffordGeneralSpinHorizontalProductIdentityChart x)
        V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure =
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure.restrict
        V.realCliffordGeneralSpinHorizontalProductIdentityChart.target := by
  calc
    Measure.map
        (fun x :
            V.realCliffordGeneralSpinHorizontalProductIdentityChart.source ↦
          V.realCliffordGeneralSpinHorizontalProductIdentityChart x)
        V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure =
        Measure.map Subtype.val
          (Measure.map
            V.realCliffordGeneralSpinHorizontalProductIdentityChart.toHomeomorphSourceTarget
            V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure) := by
      rw [Measure.map_map continuous_subtype_val.measurable
        V.realCliffordGeneralSpinHorizontalProductIdentityChart.toHomeomorphSourceTarget.measurable]
      congr 1
    _ = Measure.map Subtype.val
        V.realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure := by
      rw [V.map_realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure]
    _ = V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure.restrict
        V.realCliffordGeneralSpinHorizontalProductIdentityChart.target := by
      rw [realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure]
      exact map_comap_subtype_coe
        V.realCliffordGeneralSpinHorizontalProductIdentityChart.open_target.measurableSet
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure

/-- The real intrinsic `GSpin` chart measure obtained from scalar-times-Spin
multiplication. -/
noncomputable def realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure :
    Measure V.realCliffordGeneralSpinCentralSpinIdentityChart.target :=
  Measure.map
    V.realCliffordGeneralSpinCentralSpinIdentityChart.toHomeomorphSourceTarget
    V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure

set_option backward.isDefEq.respectTransparency false in
/-- Scalar-times-Spin multiplication sends the fixed real parameter measure
exactly to the intrinsic chart measure. -/
theorem
    map_realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_centralSpin :
    Measure.map
        (fun x :
            V.realCliffordGeneralSpinHorizontalProductIdentityChart.source ↦
          V.cliffordGeneralSpinCentralSpinMultiplication ℝ x)
        V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure =
      Measure.map Subtype.val
        V.realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure := by
  rw [realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure,
    Measure.map_map (μ := V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure)
      continuous_subtype_val.measurable
      V.realCliffordGeneralSpinCentralSpinIdentityChart.toHomeomorphSourceTarget.measurable]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- On the intrinsic real chart, the combined map `(nu, pi)` has the exact
fixed horizontal differential product normalization. -/
theorem
    map_realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure_centralFiber :
    Measure.map
        (fun g : V.realCliffordGeneralSpinCentralSpinIdentityChart.target ↦
          CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ g)
        V.realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure =
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure.restrict
        V.realCliffordGeneralSpinHorizontalProductIdentityChart.target := by
  have hcentralFiber : Measurable
      (fun g : V.realCliffordGeneralSpinCentralSpinIdentityChart.target ↦
        CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ g) :=
    ((V.continuous_cliffordGeneralSpinSimilitudeGroupHom ℝ).measurable.comp
      continuous_subtype_val.measurable).prodMk
      ((V.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom ℝ).measurable.comp
        continuous_subtype_val.measurable)
  rw [realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure,
    Measure.map_map (μ := V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure)
      hcentralFiber
      V.realCliffordGeneralSpinCentralSpinIdentityChart.toHomeomorphSourceTarget.measurable]
  have hfun :
      (fun g : V.realCliffordGeneralSpinCentralSpinIdentityChart.target ↦
          CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ g) ∘
          V.realCliffordGeneralSpinCentralSpinIdentityChart.toHomeomorphSourceTarget =
        (fun x :
            V.realCliffordGeneralSpinHorizontalProductIdentityChart.source ↦
          V.realCliffordGeneralSpinHorizontalProductIdentityChart x) := by
    funext x
    exact V.centralFiberGroupHom_realCliffordGeneralSpinCentralSpinIdentityChart x
  rw [hfun]
  exact
    V.map_realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_apply

/-! ## P-adic places -/

/-- The fixed horizontal differential product measure at `p`. -/
noncomputable def padicCliffordGeneralSpinHorizontalDifferentialProductMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  (Measure.haar : Measure ℚ_[p]ˣ).prod
    (V.padicInvariantDifferentialGroupMeasure p)

/-- Restriction of the p-adic horizontal differential product measure to the
chosen product-chart target. -/
noncomputable def
    padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).target :=
  Measure.comap Subtype.val
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)

/-- Exact inverse transport through the p-adic square/Spin chart. -/
noncomputable def
    padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).source :=
  Measure.map
    (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).toHomeomorphSourceTarget.symm
    (V.padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure p)

/-- The p-adic square/Spin chart sends its source measure exactly to the fixed
product target measure. -/
theorem
    map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).toHomeomorphSourceTarget
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p) =
      V.padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure p := by
  rw [padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure]
  exact MeasurableEquiv.map_map_symm
    (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).toHomeomorphSourceTarget.toMeasurableEquiv

/-- The literal p-adic square/Spin parameter map pushes the chosen source
measure to the restriction of the fixed horizontal product measure. -/
theorem
    map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_apply
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (fun x :
            (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).source ↦
          V.padicCliffordGeneralSpinHorizontalProductIdentityChart p x)
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p) =
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p).restrict
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).target := by
  calc
    Measure.map
        (fun x :
            (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).source ↦
          V.padicCliffordGeneralSpinHorizontalProductIdentityChart p x)
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p) =
        Measure.map Subtype.val
          (Measure.map
            (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).toHomeomorphSourceTarget
            (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p)) := by
      rw [Measure.map_map continuous_subtype_val.measurable
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).toHomeomorphSourceTarget.measurable]
      congr 1
    _ = Measure.map Subtype.val
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure p) := by
      rw [V.map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p]
    _ = (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p).restrict
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).target := by
      rw [padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure]
      exact map_comap_subtype_coe
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).open_target.measurableSet
        (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)

/-- The p-adic intrinsic `GSpin` chart measure obtained from scalar-times-Spin
multiplication. -/
noncomputable def padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).target :=
  Measure.map
    (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).toHomeomorphSourceTarget
    (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p)

set_option backward.isDefEq.respectTransparency false in
/-- Scalar-times-Spin multiplication sends the fixed p-adic parameter measure
exactly to the intrinsic chart measure. -/
theorem
    map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_centralSpin
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (fun x :
            (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).source ↦
          V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] x)
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p) =
      Measure.map Subtype.val
        (V.padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure p) := by
  rw [padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure,
    Measure.map_map (μ := V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p)
      continuous_subtype_val.measurable
      (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).toHomeomorphSourceTarget.measurable]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- On the intrinsic p-adic chart, the combined map `(nu, pi)` has the exact
fixed horizontal differential product normalization. -/
theorem
    map_padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure_centralFiber
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (fun g : (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).target ↦
          CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] g)
        (V.padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure p) =
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p).restrict
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).target := by
  have hcentralFiber : Measurable
      (fun g : (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).target ↦
        CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] g) :=
    ((V.continuous_cliffordGeneralSpinSimilitudeGroupHom ℚ_[p]).measurable.comp
      continuous_subtype_val.measurable).prodMk
      ((V.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom ℚ_[p]).measurable.comp
        continuous_subtype_val.measurable)
  rw [padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure,
    Measure.map_map (μ := V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p)
      hcentralFiber
      (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).toHomeomorphSourceTarget.measurable]
  have hfun :
      (fun g : (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).target ↦
          CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] g) ∘
          (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).toHomeomorphSourceTarget =
        (fun x :
            (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).source ↦
          V.padicCliffordGeneralSpinHorizontalProductIdentityChart p x) := by
    funext x
    exact
      V.centralFiberGroupHom_padicCliffordGeneralSpinCentralSpinIdentityChart p x
  rw [hfun]
  exact
    V.map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_apply p

end RationalQuadraticSpaceMatrix
