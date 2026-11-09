import SMSFormula.RationalCliffordGeneralSpinHorizontalAmbientCentralFiberCylinderBind

/-!
# Reassociating the bare SO-chart central-fiber bind

The restricted ambient central fiber is already known pointwise on the
literal full `SO` chart.  This file rearranges its measurable scalar, Spin,
and good-tail factors into the completed differential central-extension
cylinder.  The definition-only good-tail lift is never promoted to a
measurable section.
-/

noncomputable section

open MeasureTheory Measure
open scoped ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

local instance horizontalAmbientCylinderReassociationDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance horizontalAmbientCylinderReassociationPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

noncomputable local instance horizontalAmbientCylinderReassociationRealUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable local instance horizontalAmbientCylinderReassociationRealUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance horizontalAmbientCylinderReassociationPadicUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance horizontalAmbientCylinderReassociationPadicUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance horizontalAmbientCylinderReassociationRealSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℝ) :=
  L.rationalQuadraticSpaceMatrix.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance horizontalAmbientCylinderReassociationRealSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℝ) :=
  L.rationalQuadraticSpaceMatrix.realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable local instance horizontalAmbientCylinderReassociationPadicSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance horizontalAmbientCylinderReassociationPadicSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance horizontalAmbientCylinderReassociationHeightOneSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance horizontalAmbientCylinderReassociationHeightOneSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance horizontalAmbientCylinderReassociationHeightOneSOSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    L.rationalQuadraticSpaceMatrix.pairingMatrix
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance horizontalAmbientCylinderReassociationIntegralSOFactorBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  Subtype.borelSpace _

local instance horizontalAmbientCylinderReassociationIntegralSOFactorSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : {v // v ∉ S}) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance horizontalAmbientCylinderReassociationIntegralSOTailSecondCountable
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    SecondCountableTopology
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  TopologicalSpace.instSecondCountableTopologyForallOfCountable

local instance horizontalAmbientCylinderReassociationIntegralSOTailBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail S) :=
  Pi.borelSpace

/-! ## A dependent finite-product reassociation -/

private def dependentArrowProdEquivProdArrow
    {ι : Type*} {α β : ι → Type*}
    [(i : ι) → MeasurableSpace (α i)] [(i : ι) → MeasurableSpace (β i)] :
    ((i : ι) → α i × β i) ≃ᵐ (((i : ι) → α i) × ((i : ι) → β i)) where
  __ := Equiv.arrowProdEquivProdArrow ι α β
  measurable_toFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    exact (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst).prodMk
      (measurable_pi_lambda _ fun i => (measurable_pi_apply i).snd)
  measurable_invFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    exact measurable_pi_lambda _ fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)

private theorem measurePreserving_dependentArrowProdEquivProdArrow
    {ι : Type*} [Fintype ι] {α β : ι → Type*}
    [(i : ι) → MeasurableSpace (α i)] [(i : ι) → MeasurableSpace (β i)]
    (μ : (i : ι) → Measure (α i)) (ν : (i : ι) → Measure (β i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (dependentArrowProdEquivProdArrow (α := α) (β := β))
      (.pi fun i ↦ (μ i).prod (ν i))
      ((Measure.pi fun i ↦ μ i).prod (Measure.pi fun i ↦ ν i)) where
  measurable := (dependentArrowProdEquivProdArrow (α := α) (β := β)).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi (fun i ↦ (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply, dependentArrowProdEquivProdArrow,
        MeasurableEquiv.coe_mk]
      rw [show Equiv.arrowProdEquivProdArrow ι α β ⁻¹'
          (Set.univ.pi s ×ˢ Set.univ.pi t) =
          (Set.univ.pi fun i ↦ s i ×ˢ t i) by
          ext; simp [Set.mem_pi, forall_and]]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Finset.prod_mul_distrib]
      rw [Measure.pi_pi, Measure.pi_pi]

private theorem parallelComp_bind_prod
    {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (κ : ProbabilityTheory.Kernel A C) (η : ProbabilityTheory.Kernel B D)
    [ProbabilityTheory.IsSFiniteKernel κ] [ProbabilityTheory.IsSFiniteKernel η]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] :
    (κ ∥ₖ η) ∘ₘ (μ.prod ν) = (κ ∘ₘ μ).prod (η ∘ₘ ν) := by
  let kμ := ProbabilityTheory.Kernel.const Unit μ
  let kν := ProbabilityTheory.Kernel.const Unit ν
  have h := ProbabilityTheory.Kernel.parallelComp_comp_prod
    (κ := kμ) (κ' := kν) (η := κ) (η' := η)
  have h' := congrArg (fun k => k ()) h
  simpa only [ProbabilityTheory.Kernel.comp_apply,
    ProbabilityTheory.Kernel.prod_apply,
    ProbabilityTheory.Kernel.const_apply] using h'

/-! ## The measurable reassociation kernel -/

/-- At the real place, sample the differential scalar square branch while
preserving the supplied Spin chart point. -/
def cliffordGeneralSpinHorizontalRealDifferentialPairKernel
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    ProbabilityTheory.Kernel
      L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChart.source
      ((Rat.unitSquareIdentityChart ℝ).source ×
        L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChart.source) :=
  ((ProbabilityTheory.Kernel.id ×ₖ
      ProbabilityTheory.Kernel.const _
        RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure).map
    Prod.swap)

/-- At the finitely exceptional places, sample all differential scalar square
branches and pair them componentwise with the supplied Spin chart points. -/
def cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ProbabilityTheory.Kernel
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalExceptionalSOChartSource B)
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalExceptionalChartSplitSource B) :=
  let μ := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure B
  (ProbabilityTheory.Kernel.id ×ₖ ProbabilityTheory.Kernel.const _ μ).map
    (fun p v ↦ (p.2 v, p.1 v))

/-- The full bare-`SO`-source kernel: pair the real and exceptional scalar
branches with their Spin coordinates and use the already descended good-tail
central fiber on the unchanged infinite tail. -/
def cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ProbabilityTheory.Kernel
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)) :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  L.cliffordGeneralSpinHorizontalRealDifferentialPairKernel ∥ₖ
    (L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B ∥ₖ
      L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
        E
        (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
          (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
        (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
          (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)))

/-- Reassociate one bare full scalar chart with one retained `SO` chart
source point into the scalar/Spin split coordinates.  The good-tail lift is
used only at this fixed source point. -/
def cliffordGeneralSpinHorizontalFullSOChartScalarToSplit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) →
      L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
  fun a ↦
    ((a.1, x.1),
      (fun v ↦ (a.2.1 v, x.2.1 v),
        fun v ↦ V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a.2.2 v) * g v))

theorem measurable_cliffordGeneralSpinHorizontalFullSOChartScalarToSplit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    Measurable (L.cliffordGeneralSpinHorizontalFullSOChartScalarToSplit S x) := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
  unfold cliffordGeneralSpinHorizontalFullSOChartScalarToSplit
  exact (measurable_fst.prodMk measurable_const).prodMk
    ((measurable_pi_lambda _ fun v ↦
      ((measurable_pi_apply v).comp (measurable_fst.comp measurable_snd)).prodMk
        measurable_const).prodMk
      (measurable_pi_lambda _ fun v ↦
        measurable_mul_const (g v) |>.comp
          ((V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom E v).measurable.comp
            ((measurable_pi_apply v).comp (measurable_snd.comp measurable_snd)))))

/-- Reconstructing the reassociated scalar/Spin coordinates is the literal
ambient central orbit through the retained chart origin. -/
theorem cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic_fullSOChartScalarToSplit
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (a : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialFullSquareChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
      (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
    V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
        (L.cliffordGeneralSpinHorizontalFullSOChartScalarToSplit S x a) =
      V.cliffordGeneralSpinHorizontalFullCentralOrbit E x.1 x.2.1 g
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient B a) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)) x.2.2
  let z : V.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource E :=
    ((a.1, x.1),
      (fun v ↦ (a.2.1 v, x.2.1 v),
        fun v ↦ V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a.2.2 v) * g v))
  let y := (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph E).symm z
  have hy : V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph E y = z :=
    (V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph E).apply_symm_apply z
  rw [V.cliffordGeneralSpinHorizontalRealFiniteChartSplitHomeomorph_apply] at hy
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRealFiniteChartSplit
    RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalExceptionalChartSplit at hy
  change V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E z = _
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic
  simp only [Function.comp_apply]
  apply V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.injective
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_fullCentralOrbit]
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullAdelicChartParameterToAmbient
  change V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
      (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm _) = _
  rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply]
  unfold RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartToAmbient
  simp only [Function.comp_apply]
  rw [RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv.apply_symm_apply]
  unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRealFiniteChartParameterToAmbient
  apply Prod.ext
  · have hyR := congrArg (fun w ↦ w.1) hy
    change (Homeomorph.Set.prod
        (Rat.unitSquareIdentityChart ℝ).source
        V.realCliffordSpinCandidateIdentityChart.source y.1) =
      (a.1, x.1) at hyR
    have hyScalar : ((y.1 : ℝˣ × V.RealCliffordSpinCandidateGroup)).1 = a.1 := by
      simpa using congrArg (fun q ↦ (q.1 : ℝˣ)) hyR
    have hySpin : ((y.1 : ℝˣ × V.RealCliffordSpinCandidateGroup)).2 = x.1 := by
      simpa using congrArg (fun q ↦ (q.2 : V.RealCliffordSpinCandidateGroup)) hyR
    change V.cliffordGeneralSpinCentralSpinMultiplication ℝ
        (y.1 : ℝˣ × V.RealCliffordSpinCandidateGroup) =
      RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V ℝ (a.1 : ℝˣ) *
        V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ
          (x.1 : V.RealCliffordSpinCandidateGroup)
    unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinCentralSpinMultiplication
    rw [hyScalar, hySpin]
  · let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    have hyExceptional (v : {v // v ∈ B}) :
        (Homeomorph.Set.prod
            (Rat.unitSquareIdentityChart
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source
            (V.padicCliffordSpinCandidateIdentityChart
              (Rat.HeightOneSpectrum.primesEquiv v.1).1).source (y.2.1 v)) =
          (a.2.1 v, x.2.1 v) := by
      exact congrArg (fun w ↦ w.2.1 v) hy
    have hyTail := congrArg (fun w ↦ w.2.2) hy
    change y.2.2 =
      (fun v ↦ V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a.2.2 v) * g v)
      at hyTail
    change V.cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient E y.2 =
      V.cliffordGeneralSpinHorizontalFiniteCentralOrbit E x.2.1 g
        (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient
          B a.2)
    unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteChartParameterToAmbient
      RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteChartParameterToSource
    simp only [Function.comp_apply]
    apply V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom_injective
    funext v
    change
      V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
          (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient E
            (Prod.map (V.cliffordGeneralSpinHorizontalExceptionalChartToBlock E) id y.2)) =
        V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
          (V.cliffordGeneralSpinHorizontalFiniteCentralOrbit E x.2.1 g
            (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient
              B a.2))
    rw [V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient]
    unfold RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteCentralOrbit
      RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin
    rw [(V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v).map_mul,
      V.finiteAdelicCliffordGeneralSpinHeightOneComponent_scalarGroupHom]
    by_cases hv : v ∈ B
    · have hscalar :
          RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
              (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient
                B a.2) = a.2.1 ⟨v, hv⟩ := by
        rw [RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponent_squareChartToAmbient]
        simp [RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalTailLocalUnit,
          B, hv]
      have hvPair := hyExceptional ⟨v, hv⟩
      have hvScalar :
          (((y.2.1 ⟨v, hv⟩ :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ ×
              V.PadicCliffordSpinCandidateGroup
                (Rat.HeightOneSpectrum.primesEquiv v).1)).1) = a.2.1 ⟨v, hv⟩ := by
        simpa using congrArg
          (fun q ↦ (q.1 : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)) hvPair
      have hvSpin :
          (((y.2.1 ⟨v, hv⟩ :
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ ×
              V.PadicCliffordSpinCandidateGroup
                (Rat.HeightOneSpectrum.primesEquiv v).1)).2) = x.2.1 ⟨v, hv⟩ := by
        simpa using congrArg
          (fun q ↦ (q.2 : V.PadicCliffordSpinCandidateGroup
            (Rat.HeightOneSpectrum.primesEquiv v).1)) hvPair
      simp [RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalExceptionalChartToBlock,
        RationalQuadraticSpaceMatrix.cliffordGeneralSpinCentralSpinMultiplication,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
        B, hv, hscalar, hvScalar, hvSpin]
    · have hscalar :
          RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v
              (RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartToAmbient
                B a.2) = (a.2.2 ⟨v, hv⟩).1 := by
        rw [RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponent_squareChartToAmbient]
        simp [RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalTailLocalUnit,
          B, hv]
      have hvTail := congrFun hyTail ⟨v, hv⟩
      simpa [B, hv, hscalar,
        V.finiteAdelicCliffordGeneralSpinHeightOneComponent_identityChartSourceToAmbient,
        RationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralScalarHom]
        using congrArg Subtype.val hvTail

/-! ## Exact source-measure reassociation -/

theorem map_integralScalarTailMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (fun a v ↦
          L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralScalarHom
            S v (a v))
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure
          (S ∪
            L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure
        S := by
  let V := L.rationalQuadraticSpaceMatrix
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (RationalQuadraticSpaceMatrix.rationalPadicIdeleIntegralFactorMeasure v.1) :=
    RationalQuadraticSpaceMatrix.rationalPadicIdeleIntegralFactorMeasure_isProbability v.1
  unfold RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure
    RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure
  rw [Measure.infinitePi_map_pi
    (μ := fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
      RationalQuadraticSpaceMatrix.rationalPadicIdeleIntegralFactorMeasure v.1)
    (f := fun v a ↦ V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v a)
    (fun v ↦
      (V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom S v).measurable)]
  congr 1

theorem integralCentralFiberTailKernelAtSO_apply_eq_map_scalarTail
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hA : ∀ v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉ L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hO : ∀ v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉ L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (q : L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail
      (S ∪ L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift S hA hO q
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO S hA hO q =
      Measure.map
        (fun a v ↦ V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v (a v) * g v)
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift S hA hO q
  calc
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO S hA hO q =
        L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO S hA hO
          (L.cliffordGeneralSpinHorizontalIntegralTailToSO S g) := by
      congr 1
      exact (L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift_spec S hA hO q).symm
    _ = V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel S g :=
      L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_comp_projection
        S hA hO g
    _ = Measure.map (fun z ↦ z * g)
        (V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailMeasure S) :=
      V.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernel_apply S g
    _ = Measure.map
        (fun a v ↦ V.padicCliffordGeneralSpinHorizontalIntegralScalarHom S v (a v) * g v)
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
      rw [← L.map_integralScalarTailMeasure S, Measure.map_map]
      · congr 1
      · exact measurable_pi_lambda _ fun v ↦
          measurable_mul_const (g v) |>.comp (measurable_pi_apply v)
      · exact measurable_pi_lambda _ fun v ↦
          (V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom S v).measurable.comp
            (measurable_pi_apply v)

private theorem realDifferentialPairKernel_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (x : L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChart.source) :
    L.cliffordGeneralSpinHorizontalRealDifferentialPairKernel x =
      Measure.map (fun a ↦ (a, x))
        RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure := by
  let μ := RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) :=
    Measure.IsHaarMeasure.sigmaFinite _
  letI : SigmaFinite μ := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [show μ = RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure
        by rfl,
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure,
      map_comap_subtype_coe (Rat.unitSquareIdentityChart ℝ).open_source.measurableSet]
    infer_instance
  unfold cliffordGeneralSpinHorizontalRealDifferentialPairKernel
  rw [ProbabilityTheory.Kernel.map_apply _ measurable_swap,
    ProbabilityTheory.Kernel.prod_apply,
    ProbabilityTheory.Kernel.id_apply,
    ProbabilityTheory.Kernel.const_apply,
    Measure.dirac_prod,
    Measure.map_map]
  · congr 1
  · exact measurable_swap
  · exact measurable_prodMk_left

private theorem exceptionalDifferentialPairKernel_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalExceptionalSOChartSource B) :
    L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B x =
      Measure.map (fun a v ↦ (a v, x v))
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure
          B) := by
  let μ := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure
    B
  let pair := fun p :
      L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalExceptionalSOChartSource B ×
        RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource B =>
      fun v ↦ (p.2 v, p.1 v)
  have hpair : Measurable pair := measurable_pi_lambda _ fun v ↦
    ((measurable_pi_apply v).comp measurable_snd).prodMk
      ((measurable_pi_apply v).comp measurable_fst)
  unfold cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel
  change ((ProbabilityTheory.Kernel.id ×ₖ ProbabilityTheory.Kernel.const _ μ).map pair) x = _
  rw [ProbabilityTheory.Kernel.map_apply _ hpair,
    ProbabilityTheory.Kernel.prod_apply,
    ProbabilityTheory.Kernel.id_apply,
    ProbabilityTheory.Kernel.const_apply,
    Measure.dirac_prod,
    Measure.map_map]
  · congr 1
  · exact hpair
  · exact measurable_prodMk_left

/-- Pointwise, the measurable reassociation kernel is the pushforward of the
bare full differential square source by the fixed-origin scalar/Spin
reassociation map. -/
theorem cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    L.cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel S x =
      Measure.map
        (L.cliffordGeneralSpinHorizontalFullSOChartScalarToSplit S x)
        (RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure
          (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
            L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let hA := L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
    (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)
  let hO := L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
    (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)
  let g := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailLift E hA hO x.2.2
  let μR := RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure
  let μE := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialExceptionalSquareChartSourceMeasure
    B
  let μT := RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B
  let fR := fun a : (Rat.unitSquareIdentityChart ℝ).source ↦ (a, x.1)
  let fE := fun a : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialExceptionalSquareChartSource
      B ↦ fun v ↦ (a v, x.2.1 v)
  let fT := fun a : RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail B ↦
    fun v ↦ V.padicCliffordGeneralSpinHorizontalIntegralScalarHom E v (a v) * g v
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) :=
    Measure.IsHaarMeasure.sigmaFinite _
  letI : SigmaFinite μR := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [show μR = RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure
        by rfl,
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure,
      map_comap_subtype_coe (Rat.unitSquareIdentityChart ℝ).open_source.measurableSet]
    infer_instance
  letI : SigmaFinite μE := by infer_instance
  letI : SigmaFinite μT := IsFiniteMeasure.toSigmaFinite _
  letI : ProbabilityTheory.IsSFiniteKernel
      L.cliffordGeneralSpinHorizontalRealDifferentialPairKernel := by
    unfold cliffordGeneralSpinHorizontalRealDifferentialPairKernel
    infer_instance
  letI : ProbabilityTheory.IsSFiniteKernel
      (L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B) := by
    unfold cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel
    infer_instance
  have hfR : Measurable fR := measurable_id.prodMk measurable_const
  have hfE : Measurable fE := measurable_pi_lambda _ fun v ↦
    (measurable_pi_apply v).prodMk measurable_const
  have hfT : Measurable fT := measurable_pi_lambda _ fun v ↦
    measurable_mul_const (g v) |>.comp
      ((V.continuous_padicCliffordGeneralSpinHorizontalIntegralScalarHom E v).measurable.comp
        (measurable_pi_apply v))
  unfold cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel
  rw [ProbabilityTheory.Kernel.parallelComp_apply,
    ProbabilityTheory.Kernel.parallelComp_apply,
    L.realDifferentialPairKernel_apply,
    L.exceptionalDifferentialPairKernel_apply,
    L.integralCentralFiberTailKernelAtSO_apply_eq_map_scalarTail E hA hO x.2.2,
    Measure.map_prod_map μE μT hfE hfT,
    Measure.map_prod_map μR (μE.prod μT) hfR (hfE.prodMap hfT)]
  unfold RationalQuadraticSpaceMatrix.rationalIdeleDifferentialFullSquareChartSourceMeasure
    RationalQuadraticSpaceMatrix.rationalFiniteIdeleDifferentialSquareChartSourceMeasure
  congr 1

/-- Mapping the reassociation kernel to intrinsic full-adelic `GSpin` is
pointwise the pulled-back descended ambient differential fiber restricted to
the certified identity carrier. -/
theorem map_cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    Measure.map
        (V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E)
        (L.cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel S x) =
      (ProbabilityTheory.Kernel.comap
          (L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart E)
          (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient B)
          (V.measurable_cliffordGeneralSpinHorizontalFullSOChartToAmbient B)) x := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  rw [L.cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel_apply S x,
    Measure.map_map
      (V.measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E)
      (L.measurable_cliffordGeneralSpinHorizontalFullSOChartScalarToSplit S x),
    L.comap_fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_apply S x]
  congr 1
  funext a
  exact L.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic_fullSOChartScalarToSplit
    S x a

set_option backward.isDefEq.respectTransparency false in
private theorem realDifferentialPairKernel_comp_spinMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    L.cliffordGeneralSpinHorizontalRealDifferentialPairKernel ∘ₘ
        L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure =
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
        L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let μS := V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let μA := RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  let realSpinChart := V.realCliffordSpinCandidateIdentityChart
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe realSpinChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite μS := by
    rw [show μS = V.realCliffordSpinCandidateIdentityChartSourceMeasure by rfl,
      RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure]
    exact realSpinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) :=
    Measure.IsHaarMeasure.sigmaFinite _
  letI : SigmaFinite μA := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [show μA =
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure by rfl,
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure,
      map_comap_subtype_coe (Rat.unitSquareIdentityChart ℝ).open_source.measurableSet]
    infer_instance
  change
    ((ProbabilityTheory.Kernel.id ×ₖ ProbabilityTheory.Kernel.const _ μA).map Prod.swap) ∘ₘ μS =
      μA.prod μS
  rw [← Measure.map_comp _ _ measurable_swap]
  rw [← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  exact Measure.prod_swap

set_option backward.isDefEq.respectTransparency false in
private theorem exceptionalDifferentialPairKernel_comp_spinMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B ∘ₘ
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure B =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalExceptionalChartDifferentialAmbientSplitMeasure B := by
  let V := L.rationalQuadraticSpaceMatrix
  let μS := fun v : {v // v ∈ B} ↦
    V.padicCliffordSpinCandidateIdentityChartSourceMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  let μA := fun v : {v // v ∈ B} ↦
    RationalQuadraticSpaceMatrix.padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure v.1
  let Scalar : {v // v ∈ B} → Type := fun v ↦
    ↥(Rat.unitSquareIdentityChart
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source
  let Spin : {v // v ∈ B} → Type := fun v ↦
    ↥(V.padicCliffordSpinCandidateIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).source
  let pair : ((v : {v // v ∈ B}) → Spin v) ×
      ((v : {v // v ∈ B}) → Scalar v) →
      ((v : {v // v ∈ B}) → Scalar v × Spin v) :=
    fun p v ↦ (p.2 v, p.1 v)
  letI (v : {v // v ∈ B}) : SigmaFinite (μS v) := by
    let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
    let spinChart := V.padicCliffordSpinCandidateIdentityChart p
    letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
      PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
        p (r + 2) V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [RationalQuadraticSpaceMatrix.padicCliffordSpinCandidateIdentityChartTargetMeasure,
        map_comap_subtype_coe spinChart.open_target.measurableSet]
      infer_instance
    rw [show μS v = V.padicCliffordSpinCandidateIdentityChartSourceMeasure p by rfl,
      RationalQuadraticSpaceMatrix.padicCliffordSpinCandidateIdentityChartSourceMeasure]
    exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI (v : {v // v ∈ B}) : SigmaFinite (μA v) := by
    let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
    let squareChart := Rat.unitSquareIdentityChart ℚ_[p]
    letI : SigmaFinite
        (RationalQuadraticSpaceMatrix.rationalPadicIdeleDifferentialHaarMeasure v.1) :=
      Measure.IsHaarMeasure.sigmaFinite _
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [show μA v =
      RationalQuadraticSpaceMatrix.padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure
        v.1 by rfl,
      RationalQuadraticSpaceMatrix.padicUnitSquareIdentityChartDifferentialAmbientSourceMeasure,
      map_comap_subtype_coe squareChart.open_source.measurableSet]
    infer_instance
  let hpair : MeasurePreserving pair
      ((Measure.pi μS).prod (Measure.pi μA))
      (Measure.pi fun v ↦ (μA v).prod (μS v)) := by
    let e := dependentArrowProdEquivProdArrow (α := Scalar) (β := Spin)
    have hsplit := measurePreserving_dependentArrowProdEquivProdArrow μA μS
    have h := hsplit.symm.comp
      (Measure.measurePreserving_swap (μ := Measure.pi μS) (ν := Measure.pi μA))
    simpa only [pair, e, Function.comp_apply,
      dependentArrowProdEquivProdArrow, MeasurableEquiv.coe_mk,
      Equiv.arrowProdEquivProdArrow_apply] using h
  change
    ((ProbabilityTheory.Kernel.id ×ₖ ProbabilityTheory.Kernel.const _ (Measure.pi μA)).map pair) ∘ₘ
        Measure.pi μS =
      Measure.pi fun v ↦ (μA v).prod (μS v)
  rw [← Measure.map_comp _ _ hpair.measurable]
  rw [← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  exact hpair.map_eq

set_option backward.isDefEq.respectTransparency false in
/-- Binding the measurable bare-`SO` reassociation kernel over the literal
full `SO` chart source gives exactly the completed differential
central-extension cylinder source measure. -/
theorem cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel_comp_sourceMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel S ∘ₘ
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure
          (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
            L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) =
      L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S ∘ₘ
        L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderBaseMeasure S := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let μR := V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let μE := V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure B
  let μSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure B
  let κR := L.cliffordGeneralSpinHorizontalRealDifferentialPairKernel
  let κE := L.cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel B
  let κT := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
    E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
  let νR := RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod μR
  let νE := V.cliffordGeneralSpinHorizontalExceptionalChartDifferentialAmbientSplitMeasure B
  let νT := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
  letI : SigmaFinite V.realInvariantDifferentialGroupMeasure :=
    PositiveDefiniteIntegralLattice.specialFormPreservingSmoothRealDifferentialMeasure_sigmaFinite
      V.pairingMatrix V.form_symm V.form_det_ne_zero
  let realSpinChart := V.realCliffordSpinCandidateIdentityChart
  letI : SigmaFinite V.realCliffordSpinCandidateIdentityChartTargetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartTargetMeasure,
      map_comap_subtype_coe realSpinChart.open_target.measurableSet]
    infer_instance
  letI : SigmaFinite μR := by
    rw [show μR = V.realCliffordSpinCandidateIdentityChartSourceMeasure by rfl,
      RationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChartSourceMeasure]
    exact realSpinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite μE := by infer_instance
  letI : SigmaFinite μSO := IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite (μE.prod μSO) := by infer_instance
  let μA := RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) :=
    Measure.IsHaarMeasure.sigmaFinite _
  letI : SigmaFinite μA := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [show μA =
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure by rfl,
      RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure,
      map_comap_subtype_coe (Rat.unitSquareIdentityChart ℝ).open_source.measurableSet]
    infer_instance
  letI : SigmaFinite νR := by infer_instance
  letI : SigmaFinite νE := by infer_instance
  letI : ProbabilityTheory.IsSFiniteKernel κR := by
    unfold κR cliffordGeneralSpinHorizontalRealDifferentialPairKernel
    infer_instance
  letI : ProbabilityTheory.IsSFiniteKernel κE := by
    unfold κE cliffordGeneralSpinHorizontalExceptionalDifferentialPairKernel
    infer_instance
  have hR : κR ∘ₘ μR = νR := L.realDifferentialPairKernel_comp_spinMeasure
  have hE : κE ∘ₘ μE = νE := L.exceptionalDifferentialPairKernel_comp_spinMeasure B
  have hT : κT ∘ₘ μSO = νT :=
    L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_comp_normalizedSO_canonical
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)
  change (κR ∥ₖ (κE ∥ₖ κT)) ∘ₘ (μR.prod (μE.prod μSO)) =
    (ProbabilityTheory.Kernel.id ∥ₖ
      (ProbabilityTheory.Kernel.id ∥ₖ κT)) ∘ₘ (νR.prod (νE.prod μSO))
  calc
    _ = (κR ∘ₘ μR).prod ((κE ∥ₖ κT) ∘ₘ (μE.prod μSO)) :=
      parallelComp_bind_prod κR (κE ∥ₖ κT) μR (μE.prod μSO)
    _ = (κR ∘ₘ μR).prod ((κE ∘ₘ μE).prod (κT ∘ₘ μSO)) := by
      rw [parallelComp_bind_prod κE κT μE μSO]
    _ = νR.prod (νE.prod νT) := by rw [hR, hE, hT]
    _ = _ := by rw [← Measure.prod_comp_right, ← Measure.prod_comp_right, hT]

/-- Binding the pulled-back restricted descended ambient fiber over the bare
full `SO` chart source is exactly the calibrated differential full-adelic
`GSpin` cylinder. -/
theorem
    comap_fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart_comp_fullSOChartSourceMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    (ProbabilityTheory.Kernel.comap
        (L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart E)
        (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient B)
        (V.measurable_cliffordGeneralSpinHorizontalFullSOChartToAmbient B)) ∘ₘ
      V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure B =
        L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let κ := L.cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel S
  let η := ProbabilityTheory.Kernel.comap
    (L.fullAdelicDifferentialCentralFiberKernelAtSORestrictIdentityChart E)
    (V.cliffordGeneralSpinHorizontalFullSOChartToAmbient B)
    (V.measurable_cliffordGeneralSpinHorizontalFullSOChartToAmbient B)
  let μ := V.cliffordGeneralSpinHorizontalFullSOChartSourceMeasure B
  let f := V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
  have hpoint : ∀ x, η x = (κ.map f) x := by
    intro x
    rw [ProbabilityTheory.Kernel.map_apply _
      (V.measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E)]
    exact (L.map_cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel_apply
      S x).symm
  calc
    η ∘ₘ μ = (κ.map f) ∘ₘ μ :=
      Measure.comp_congr (Filter.Eventually.of_forall hpoint)
    _ = Measure.map f (κ ∘ₘ μ) := by
      rw [Measure.map_comp μ κ
        (V.measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E)]
    _ = Measure.map f
        (L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S ∘ₘ
          L.cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderBaseMeasure S) := by
      rw [L.cliffordGeneralSpinHorizontalDifferentialSOChartReassociationKernel_comp_sourceMeasure
        S]
    _ = L.cliffordGeneralSpinHorizontalDifferentialCentralExtensionFullAdelicCylinderMeasure S :=
      rfl

end PositiveDefiniteIntegralLattice
