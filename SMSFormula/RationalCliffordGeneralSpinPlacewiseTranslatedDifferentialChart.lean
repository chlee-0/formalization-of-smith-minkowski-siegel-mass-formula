import SMSFormula.RationalCliffordGeneralSpinLocalDifferentialChartMeasure
import SMSFormula.RationalCliffordSpinCandidatePlacewiseTranslatedChartMeasure

/-!
# Translated differential charts for local intrinsic general Spin

The normalized horizontal chart is oriented from scalar/Spin parameters into
intrinsic `GSpin`.  To use the common translated homomorphism-chart gluing
machinery, this file reverses that chart while keeping the global forward
function equal to the combined homomorphism

`(nu, pi) : GSpin(K) -> K^* x SO(K)`.

The resulting real and p-adic identity charts are translated by the local
`GSpin` group law.  Their source measures agree on every same-point overlap
and push forward exactly to restrictions of the fixed product of local-unit
Haar and the invariant-differential `SO` measure.  At the identity, the
generic inverse-transport measure is proved equal to the intrinsic chart
measure normalized by the scalar-square/Spin calculation.
-/

noncomputable section

open MeasureTheory
open Topology

namespace RationalQuadraticSpaceMatrix

open MeasureTheory.TranslatedHomChart

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 200000

/-! ## Borel structures -/

noncomputable instance realCliffordGeneralSpinHorizontalUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable instance realCliffordGeneralSpinHorizontalUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable instance realCliffordGeneralSpinHorizontalUnitSecondCountableTopology :
    SecondCountableTopology ℝˣ := by
  letI : SecondCountableTopology ℝᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

noncomputable instance padicCliffordGeneralSpinHorizontalUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable instance padicCliffordGeneralSpinHorizontalUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable instance padicCliffordGeneralSpinHorizontalUnitSecondCountableTopology
    (p : ℕ) [Fact (Nat.Prime p)] : SecondCountableTopology ℚ_[p]ˣ := by
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

noncomputable instance realCliffordGeneralSpinGroupMeasurableSpace_horizontal :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℝ) := borel _

noncomputable instance realCliffordGeneralSpinGroupBorelSpace_horizontal :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℝ) := ⟨rfl⟩

noncomputable instance padicCliffordGeneralSpinGroupMeasurableSpace_horizontal
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := borel _

noncomputable instance padicCliffordGeneralSpinGroupBorelSpace_horizontal
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := ⟨rfl⟩

noncomputable local instance translatedGeneralSpinRealSchemeSOMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance translatedGeneralSpinRealSchemeSOBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

local instance translatedGeneralSpinRealSchemeSOIsTopologicalGroup :
    IsTopologicalGroup (V.specialOrthogonalMatrixGroup ℝ) := by
  change IsTopologicalGroup
    (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℝ)))
  infer_instance

/-! ## A combined-homomorphism-oriented local chart -/

/-- Reverse a scalar-times-Spin chart while keeping its forward function
globally equal to the combined homomorphism `(nu, pi)`.  The explicit record
is important: composing partial homeomorphisms would only identify the two
functions on the chart source, whereas translated homomorphism charts require
literal global equality. -/
noncomputable def cliffordGeneralSpinCentralFiberLocalChart
    (K : Type*) [Field K] [Algebra ℚ K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (e : OpenPartialHomeomorph
      (Kˣ × V.CliffordSpinCandidateGroup K)
      (Kˣ × V.specialOrthogonalMatrixGroup K))
    (he : ∀ x,
      e x = CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
        (V.cliffordGeneralSpinCentralSpinMultiplication K x)) :
    OpenPartialHomeomorph
      (V.CliffordGeneralSpinIntrinsicPoint K)
      (Kˣ × V.specialOrthogonalMatrixGroup K) :=
  let c := V.cliffordGeneralSpinCentralSpinLocalChart K e he
  {
    toFun := CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
    invFun := fun y => c (e.symm y)
    source := c.target
    target := e.target
    map_source' := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← he x]
      exact e.map_source hx
    map_target' := by
      intro y hy
      exact c.map_source (e.map_target hy)
    left_inv' := by
      rintro _ ⟨x, hx, rfl⟩
      rw [V.cliffordGeneralSpinCentralSpinLocalChart_apply]
      rw [← he x, e.left_inv hx]
    right_inv' := by
      intro y hy
      rw [V.cliffordGeneralSpinCentralSpinLocalChart_apply]
      rw [← he (e.symm y), e.right_inv hy]
    open_source := c.open_target
    open_target := e.open_target
    continuousOn_toFun :=
      (V.continuous_cliffordGeneralSpinCentralFiberGroupHom K).continuousOn
    continuousOn_invFun := by
      apply c.continuousOn.comp e.symm.continuousOn
      intro y hy
      exact e.map_target hy
  }

@[simp]
theorem cliffordGeneralSpinCentralFiberLocalChart_apply
    (K : Type*) [Field K] [Algebra ℚ K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (e : OpenPartialHomeomorph
      (Kˣ × V.CliffordSpinCandidateGroup K)
      (Kˣ × V.specialOrthogonalMatrixGroup K))
    (he : ∀ x,
      e x = CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
        (V.cliffordGeneralSpinCentralSpinMultiplication K x))
    (g : V.CliffordGeneralSpinIntrinsicPoint K) :
    V.cliffordGeneralSpinCentralFiberLocalChart K e he g =
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K g :=
  rfl

/-! ## Real translated charts -/

set_option backward.isDefEq.respectTransparency false in
/-- The real identity chart for the combined homomorphism `(nu, pi)`. -/
noncomputable def realCliffordGeneralSpinCentralFiberIdentityChart :
    OpenPartialHomeomorph
      (V.CliffordGeneralSpinIntrinsicPoint ℝ)
      (ℝˣ × V.RealSpecialOrthogonalGroup) :=
  V.cliffordGeneralSpinCentralFiberLocalChart ℝ
    V.realCliffordGeneralSpinHorizontalProductIdentityChart (by
      intro x
      exact (V.realCliffordGeneralSpinHorizontalProductIdentityChart_apply x).trans
        (V.centralFiberGroupHom_cliffordGeneralSpinCentralSpinMultiplication ℝ x).symm)

theorem realCliffordGeneralSpinCentralFiberIdentityChart_coe :
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ :
      V.CliffordGeneralSpinIntrinsicPoint ℝ →
        ℝˣ × V.RealSpecialOrthogonalGroup) =
      V.realCliffordGeneralSpinCentralFiberIdentityChart :=
  rfl

@[simp]
theorem one_mem_realCliffordGeneralSpinCentralFiberIdentityChart_source :
    (1 : V.CliffordGeneralSpinIntrinsicPoint ℝ) ∈
      V.realCliffordGeneralSpinCentralFiberIdentityChart.source := by
  simpa [V.realCliffordGeneralSpinCentralSpinIdentityChart_apply,
    cliffordGeneralSpinCentralSpinMultiplication] using
      V.realCliffordGeneralSpinCentralSpinIdentityChart.map_source
        V.one_mem_realCliffordGeneralSpinHorizontalProductIdentityChart_source

set_option backward.isDefEq.respectTransparency false in
/-- The generic identity-source measure is exactly the normalized intrinsic
real chart measure. -/
theorem realCliffordGeneralSpinCentralFiberIdentitySourceMeasure_eq :
    identitySourceMeasure V.realCliffordGeneralSpinCentralFiberIdentityChart
        V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure =
      V.realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure := by
  rw [identitySourceMeasure, identityTargetMeasure,
    realCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure,
    realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure,
    realCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure]
  rw [Measure.map_map
    (μ := Measure.comap Subtype.val
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure)
    V.realCliffordGeneralSpinCentralSpinIdentityChart.toHomeomorphSourceTarget.measurable
    V.realCliffordGeneralSpinHorizontalProductIdentityChart.toHomeomorphSourceTarget.symm.measurable]
  congr 1

abbrev RealCliffordGeneralSpinTranslatedDifferentialChartSource
    (g : V.CliffordGeneralSpinIntrinsicPoint ℝ) :=
  source V.realCliffordGeneralSpinCentralFiberIdentityChart g

abbrev RealCliffordGeneralSpinTranslatedDifferentialChartTarget
    (g : V.CliffordGeneralSpinIntrinsicPoint ℝ) :=
  target (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart g

set_option backward.isDefEq.respectTransparency false in
noncomputable def realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure
    (g : V.CliffordGeneralSpinIntrinsicPoint ℝ) :
    Measure (V.RealCliffordGeneralSpinTranslatedDifferentialChartSource g) :=
  sourceMeasure
    (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart g
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure

set_option backward.isDefEq.respectTransparency false in
theorem map_realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure
    (g : V.CliffordGeneralSpinIntrinsicPoint ℝ) :
    Measure.map
        (fun x : V.RealCliffordGeneralSpinTranslatedDifferentialChartSource g ↦
          CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ x.1)
        (V.realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure g) =
      V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure.restrict
        (target (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
          V.realCliffordGeneralSpinCentralFiberIdentityChart g) :=
  map_sourceMeasure_pointMap
    (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart
    V.realCliffordGeneralSpinCentralFiberIdentityChart_coe g
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure

set_option backward.isDefEq.respectTransparency false in
theorem
    comap_realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure_overlap
    (g h : V.CliffordGeneralSpinIntrinsicPoint ℝ) :
    Measure.comap
        (sourceOverlapToLeft
          V.realCliffordGeneralSpinCentralFiberIdentityChart g h)
        (V.realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure g) =
      Measure.comap
        (sourceOverlapToRight
          V.realCliffordGeneralSpinCentralFiberIdentityChart g h)
        (V.realCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure h) :=
  comap_sourceMeasure_overlap
    (G := V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (H := ℝˣ × V.specialOrthogonalMatrixGroup ℝ)
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)
    V.realCliffordGeneralSpinCentralFiberIdentityChart
    V.realCliffordGeneralSpinCentralFiberIdentityChart_coe g h
    V.realCliffordGeneralSpinHorizontalDifferentialProductMeasure

/-! ## P-adic translated charts -/

/-- The p-adic identity chart for the combined homomorphism `(nu, pi)`. -/
noncomputable def padicCliffordGeneralSpinCentralFiberIdentityChart
    (p : ℕ) [Fact (Nat.Prime p)] :
    OpenPartialHomeomorph
      (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p])
      (ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.cliffordGeneralSpinCentralFiberLocalChart ℚ_[p]
    (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p) (by
      intro x
      rw [V.padicCliffordGeneralSpinHorizontalProductIdentityChart_apply]
      exact
        (V.centralFiberGroupHom_cliffordGeneralSpinCentralSpinMultiplication
          ℚ_[p] x).symm)

theorem padicCliffordGeneralSpinCentralFiberIdentityChart_coe
    (p : ℕ) [Fact (Nat.Prime p)] :
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] :
      V.CliffordGeneralSpinIntrinsicPoint ℚ_[p] →
        ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) =
      V.padicCliffordGeneralSpinCentralFiberIdentityChart p :=
  rfl

@[simp]
theorem one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source
    (p : ℕ) [Fact (Nat.Prime p)] :
    (1 : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) ∈
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source := by
  simpa [V.padicCliffordGeneralSpinCentralSpinIdentityChart_apply,
    cliffordGeneralSpinCentralSpinMultiplication] using
      (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).map_source
        (V.one_mem_padicCliffordGeneralSpinHorizontalProductIdentityChart_source p)

set_option backward.isDefEq.respectTransparency false in
/-- The generic identity-source measure is exactly the normalized intrinsic
p-adic chart measure. -/
theorem padicCliffordGeneralSpinCentralFiberIdentitySourceMeasure_eq
    (p : ℕ) [Fact (Nat.Prime p)] :
    identitySourceMeasure (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
        (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) =
      V.padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure p := by
  rw [identitySourceMeasure, identityTargetMeasure,
    padicCliffordGeneralSpinCentralSpinIdentityChartTargetMeasure,
    padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure,
    padicCliffordGeneralSpinHorizontalProductIdentityChartTargetMeasure]
  rw [Measure.map_map
    (μ := Measure.comap Subtype.val
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p))
    (V.padicCliffordGeneralSpinCentralSpinIdentityChart p).toHomeomorphSourceTarget.measurable
    (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).toHomeomorphSourceTarget.symm.measurable]
  congr 1

abbrev PadicCliffordGeneralSpinTranslatedDifferentialChartSource
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
  source (V.padicCliffordGeneralSpinCentralFiberIdentityChart p) g

abbrev PadicCliffordGeneralSpinTranslatedDifferentialChartTarget
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
  target (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p) g

noncomputable def padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :
    Measure (V.PadicCliffordGeneralSpinTranslatedDifferentialChartSource p g) :=
  sourceMeasure (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p) g
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)

theorem map_padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :
    Measure.map
        (fun x : V.PadicCliffordGeneralSpinTranslatedDifferentialChartSource p g ↦
          CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] x.1)
        (V.padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure p g) =
      (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p).restrict
        (target (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
          (V.padicCliffordGeneralSpinCentralFiberIdentityChart p) g) :=
  map_sourceMeasure_pointMap
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p) g
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)

theorem
    comap_padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure_overlap
    (p : ℕ) [Fact (Nat.Prime p)]
    (g h : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :
    Measure.comap
        (sourceOverlapToLeft
          (V.padicCliffordGeneralSpinCentralFiberIdentityChart p) g h)
        (V.padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure p g) =
      Measure.comap
        (sourceOverlapToRight
          (V.padicCliffordGeneralSpinCentralFiberIdentityChart p) g h)
        (V.padicCliffordGeneralSpinTranslatedDifferentialChartSourceMeasure p h) :=
  comap_sourceMeasure_overlap
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart p)
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p) g h
    (V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p)

end RationalQuadraticSpaceMatrix
