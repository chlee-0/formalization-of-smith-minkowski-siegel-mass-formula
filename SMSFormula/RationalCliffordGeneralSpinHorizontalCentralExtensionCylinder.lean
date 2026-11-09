import SMSFormula.RationalCliffordGeneralSpinHorizontalFullAdelicCoordinateGraph
import SMSFormula.RationalCliffordGeneralSpinHorizontalIntegralCentralFiberTail

/-!
# The normalized horizontal central-extension cylinder

The real and exceptional scalar/Spin charts are combined here with
the normalized central-fiber kernel on the unchanged good tail.  The base
keeps the real and exceptional coordinates unchanged and replaces only the
good `GSpin` tail by its integral `SO` marginal.  The nested parallel
kernel

`id ∥ₖ (id ∥ₖ centralFiberTailKernelAtSO)`

then recovers the complete scalar/Spin split cylinder.  This is a
kernel disintegration over the compact central extension, not a Cartesian
product identification or a measurable group section.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalCentralExtensionCylinderPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalCentralExtensionCylinderDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance horizontalCentralExtensionCylinderRealUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable local instance horizontalCentralExtensionCylinderRealUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance horizontalCentralExtensionCylinderPadicUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance horizontalCentralExtensionCylinderPadicUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance horizontalCentralExtensionCylinderRealSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℝ) :=
  L.rationalQuadraticSpaceMatrix.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance horizontalCentralExtensionCylinderRealSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℝ) :=
  L.rationalQuadraticSpaceMatrix.realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable local instance horizontalCentralExtensionCylinderPadicSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance horizontalCentralExtensionCylinderPadicSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup ℚ_[p]) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance horizontalCentralExtensionCylinderHeightOneSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance horizontalCentralExtensionCylinderHeightOneSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

local instance horizontalCentralExtensionCylinderFullGSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalCentralExtensionCylinderFullGSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

/-! ## The canonical retained carrier -/

/-- Retain the dyadic place together with the two finite bad sets needed by
the constructive integral lift. -/
def cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces
    (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)

theorem cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces_dyadic
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace ∈
      L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S := by
  simp [cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces,
    cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces]

/-- The real scalar/Spin chart, the exceptional scalar/Spin chart, and the
normalized integral `SO` good tail. -/
abbrev CliffordGeneralSpinHorizontalCentralExtensionCylinderBase
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  ((Rat.unitSquareIdentityChart ℝ).source ×
      V.realCliffordSpinCandidateIdentityChart.source) ×
    (V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource
        (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) ×
      V.FiniteAdelicSpecialOrthogonalIntegralTail
        (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))

/-- The literal differential scalar/Spin chart measures times the normalized
integral `SO` good-tail marginal. -/
def cliffordGeneralSpinHorizontalCentralExtensionCylinderBaseMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (L.CliffordGeneralSpinHorizontalCentralExtensionCylinderBase S) :=
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  (RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
      V.realCliffordSpinCandidateIdentityChartSourceMeasure).prod
    ((V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure
        (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)).prod
      (V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
        (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)))

/-! ## The complete compact central-extension kernel -/

/-- Preserve every real and exceptional scalar/Spin coordinate and integrate
only the unchanged good tail against its genuine `SO`-indexed central fiber. -/
def cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ProbabilityTheory.Kernel
      (L.CliffordGeneralSpinHorizontalCentralExtensionCylinderBase S)
      (L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalRealFiniteChartSplitSource
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)) :=
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  ProbabilityTheory.Kernel.id ∥ₖ
    (ProbabilityTheory.Kernel.id ∥ₖ
      L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
        E
        (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
          (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
        (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
          (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)))

instance cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel_isMarkov
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ProbabilityTheory.IsMarkovKernel
      (L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S) := by
  unfold cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The normalized exceptional/real/good-tail central-extension cylinder
identity.  The two chart factors are preserved literally; only the certified
good-tail kernel is averaged. -/
theorem cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel_comp_baseMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S ∘ₘ
        L.cliffordGeneralSpinHorizontalCentralExtensionCylinderBaseMeasure S =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRealFiniteChartAmbientSplitMeasure
        (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let muA :=
    RationalQuadraticSpaceMatrix.realUnitSquareIdentityChartAmbientSourceMeasure.prod
    V.realCliffordSpinCandidateIdentityChartSourceMeasure
  let muB := V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure
    (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)
  let muSO := V.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
    (E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)
  let muG := V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E
  let kappa := L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO
    E
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
  letI : SigmaFinite muB := by
    let base := fun
        v : {v // v ∈ E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces} ↦
      (RationalQuadraticSpaceMatrix.padicUnitSquareIdentityChartAmbientSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).prod
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1)
    letI (v : {v // v ∈ E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
        SigmaFinite (base v) := by
      let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
      let squareChart := Rat.unitSquareIdentityChart ℚ_[p]
      let spinChart := V.padicCliffordSpinCandidateIdentityChart p
      letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) :=
        Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
      letI : SigmaFinite
          (RationalQuadraticSpaceMatrix.padicUnitSquareIdentityChartAmbientSourceMeasure p) := by
        apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
        rw [RationalQuadraticSpaceMatrix.padicUnitSquareIdentityChartAmbientSourceMeasure,
          map_comap_subtype_coe squareChart.open_source.measurableSet]
        infer_instance
      letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
        PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
          p (r + 2) V.pairingMatrix V.form_symm V.form_det_ne_zero
      letI : SigmaFinite
          (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
        apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
        rw [RationalQuadraticSpaceMatrix.padicCliffordSpinCandidateIdentityChartTargetMeasure,
          map_comap_subtype_coe spinChart.open_target.measurableSet]
        infer_instance
      letI : SigmaFinite
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
        rw [RationalQuadraticSpaceMatrix.padicCliffordSpinCandidateIdentityChartSourceMeasure]
        exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
      infer_instance
    unfold muB
      RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure
    infer_instance
  letI : SigmaFinite muSO := IsFiniteMeasure.toSigmaFinite _
  letI : SigmaFinite (muB.prod muSO) := by infer_instance
  have htail : kappa ∘ₘ muSO = muG := by
    exact
      L.cliffordGeneralSpinHorizontalIntegralCentralFiberTailKernelAtSO_comp_normalizedSO_canonical
        (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S)
  change
    (ProbabilityTheory.Kernel.id ∥ₖ
        (ProbabilityTheory.Kernel.id ∥ₖ kappa)) ∘ₘ
        (muA.prod (muB.prod muSO)) =
      muA.prod (muB.prod muG)
  rw [← Measure.prod_comp_right, ← Measure.prod_comp_right, htail]

/-- The block weight is external to the compact central extension and passes
through the kernel unchanged. -/
theorem cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel_comp_weightedBaseMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S ∘ₘ
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRestrictedBlockWeight
            (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) •
          L.cliffordGeneralSpinHorizontalCentralExtensionCylinderBaseMeasure S) =
      L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRestrictedBlockWeight
          (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) •
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRealFiniteChartAmbientSplitMeasure
          (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S) := by
  rw [Measure.comp_smul,
    L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel_comp_baseMeasure]

/-! ## Direct consumption by the global coordinate endpoint -/

/-- The actual global `(nu, pi)` image of the coherent full-adelic cylinder is
the reconstructed-coordinate pushforward of the completed compact
central-extension kernel.  This is the first ambient-facing cylinder
disintegration; it neither enlarges the compatible coordinate locus nor
compares an idele-class quotient normalization. -/
theorem map_cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure_coordinate_eq_centralExtensionCylinder
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    Measure.map
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullAdelicCoordinate
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure
          E) =
      (L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel S).map
          (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalFullAdelicCoordinate ∘
            L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic
              E) ∘ₘ
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalRestrictedBlockWeight E •
          L.cliffordGeneralSpinHorizontalCentralExtensionCylinderBaseMeasure S) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let reconstructedCoordinate :=
    V.cliffordGeneralSpinHorizontalFullAdelicCoordinate ∘
      V.cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E
  have hdyadic : RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace ∈
      E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces := by
    exact Finset.mem_union_left _
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces_dyadic S)
  have hreconstructed : Measurable reconstructedCoordinate :=
    V.measurable_cliffordGeneralSpinHorizontalFullAdelicCoordinate.comp
      (V.measurable_cliffordGeneralSpinHorizontalRealFiniteSplitToFullAdelic E)
  rw [V.map_cliffordGeneralSpinHorizontalCoherentIdentityChartFullAdelicMeasure_coordinate_of_dyadic
      E hdyadic]
  rw [← L.cliffordGeneralSpinHorizontalCentralExtensionCylinderKernel_comp_weightedBaseMeasure
    S]
  exact Measure.map_comp _ _ hreconstructed

end PositiveDefiniteIntegralLattice
