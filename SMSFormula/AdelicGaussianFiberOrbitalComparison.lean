import SMSFormula.AdelicGaussianFiberInvariance
import SMSFormula.FiniteAdelicClosedRange
import SMSFormula.CoareaRieszInvariance
import SMSFormula.CompactOpenSubgroupOrbit
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Operations

/-!
# The actual fiber measure in the existing orbital-comparison interface

The literal matrix action is continuous and its measure is invariant. All
space-level hypotheses of the compact-orbit comparison are supplied here.
Transitivity and the native invariant measure are still inputs: invariance at
an arbitrary adelic value never asserts transitivity there. Calibration stays
an independent equality of the two raw orbit masses.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix MeasureTheory
open SMSFormula.CompactOrbit

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}
local instance : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

/-- Second countability is inherited from the adelic coordinate space. -/
instance secondCountableTopology_adelicValueFiber (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) :
    SecondCountableTopology (adelicValueFiber L a) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- The already constructed fiber homeomorphisms form the literal matrix action. -/
instance adelicValueFiberMulAction (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) :
    MulAction L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L a) where
  smul h x := specialOrthogonalFiberHomeomorph L a h x
  one_smul x := by
    apply Subtype.ext
    exact Matrix.one_mulVec x.val
  mul_smul g h x := by
    apply Subtype.ext
    change (g.1.1.1 * h.1.1.1).mulVec x.val = g.1.1.1.mulVec (h.1.1.1.mulVec x.val)
    rw [Matrix.mulVec_mulVec]

@[simp] theorem adelicValueFiber_smul_val (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (x : adelicValueFiber L a) : (h • x).val = h.1.1.1.mulVec x.val := rfl

/-- Joint continuity is a finite sum of products of matrix and vector entries. -/
instance continuousSMul_adelicValueFiber (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) :
    ContinuousSMul L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L a) where
  continuous_smul := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change Continuous (fun p : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup ×
      adelicValueFiber L a ↦ ∑ j, p.1.1.1.1 i j * p.2.val j)
    have hM : Continuous (fun p : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup ×
        adelicValueFiber L a ↦ p.1.1.1.1) :=
      Units.continuous_val.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_fst))
    have hx : Continuous (fun p : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup ×
        adelicValueFiber L a ↦ p.2.val) := continuous_subtype_val.comp continuous_snd
    exact continuous_finset_sum _ (fun j _ ↦
      ((continuous_apply j).comp ((continuous_apply i).comp hM)).mul
        ((continuous_apply j).comp hx))

/-- Invariance in the instance form consumed by the compact-orbit theorem. -/
instance smulInvariantMeasure_gaussianFiberMeasure (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) :
    SMulInvariantMeasure L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L a) (gaussianFiberMeasure L hn hb a) := by
  constructor
  intro h s hs
  have hm := map_gaussianFiberMeasure_specialOrthogonal L hn hb a h
  have he := Measure.map_apply (μ := gaussianFiberMeasure L hn hb a) (specialOrthogonalFiberHomeomorph L a h).continuous.measurable hs
  exact he.symm.trans (congrArg (fun μ ↦ μ s) hm)

/-- Second countability holds on the concrete group; the topological
identification transports it to the rational-space group. -/
theorem secondCountableTopology_fiberActingGroup (L : PositiveDefiniteIntegralLattice n) :
    SecondCountableTopology L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv.isEmbedding.secondCountableTopology

/-- The compact open subgroup, transported through the identification.
No new subgroup construction or choice of canonical witness is made. -/
theorem exists_compactOpen_fiberActingGroup (L : PositiveDefiniteIntegralLattice n) :
    ∃ K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup,
      IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) ∧ IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) := by
  obtain ⟨K, hc, ho⟩ := L.exists_compactOpen_fullAdelicSpecialOrthogonal_unconditional
  exact ⟨_, SMSFormula.AdelicCompactOpen.isCompact_isOpen_comap
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv hc ho⟩

/-- Local compactness and second countability discharge sigma-compactness too. -/
theorem sigmaCompactSpace_fiberActingGroup (L : PositiveDefiniteIntegralLattice n) :
    SigmaCompactSpace L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup := by
  letI := secondCountableTopology_fiberActingGroup L
  obtain ⟨K, hc, ho⟩ := exists_compactOpen_fiberActingGroup L
  exact SMSFormula.CompactOpenCriterion.sigmaCompactSpace_of_compactOpen_subgroup hc ho

/-- The Gaussian fiber measure is proportional to any supplied nonzero regular invariant
measure once transitivity is supplied. The proportionality constant is the raw mass ratio.
Transitivity at arbitrary nonzero adeles is not proved here. -/
theorem gaussianFiberMeasure_eq_smul_of_transitive (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele)
    (M : Measure (adelicValueFiber L a)) [M.Regular]
    [SMulInvariantMeasure L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L a) M] (hM : M ≠ 0)
    (htrans : IsTransitiveAction L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L a)) (x₀ : adelicValueFiber L a)
    (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) :
    gaussianFiberMeasure L hn hb a =
      (gaussianFiberMeasure L hn hb a ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) /
        M ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))) • M := by
  letI := secondCountableTopology_fiberActingGroup L
  letI := sigmaCompactSpace_fiberActingGroup L
  exact eq_smul_of_compactOpen_subgroup _ M htrans x₀ K hc ho hM

/-- The actual raw orbit ratio is finite even if the Riesz measure is zero.
Regularity bounds its compact orbit mass; the native denominator is positive.
This leaves both zero and finite nonunit scalars possible. -/
theorem gaussianFiberMeasure_orbit_ratio_lt_top (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele)
    (M : Measure (adelicValueFiber L a)) [M.Regular]
    [SMulInvariantMeasure L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L a) M] (hM : M ≠ 0)
    (htrans : IsTransitiveAction L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L a)) (x₀ : adelicValueFiber L a)
    (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) :
    gaussianFiberMeasure L hn hb a ((fun g ↦ g • x₀) ''
        (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) /
      M ((fun g ↦ g • x₀) ''
        (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) < ⊤ := by
  letI := secondCountableTopology_fiberActingGroup L
  letI := sigmaCompactSpace_fiberActingGroup L
  have hU : IsCompact ((fun g ↦ g • x₀) ''
      (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) :=
    hc.image (continuous_id.smul continuous_const)
  have hnum := hU.measure_lt_top (μ := gaussianFiberMeasure L hn hb a)
  have hden := measure_pos_lt_top_of_compactOpen_subgroup M htrans x₀ K hc ho hM
  exact ENNReal.div_lt_top hnum.ne hden.1.ne'

/-- One independently calibrated raw orbit mass would identify the measures.
This is an implication: the calibration is neither supplied nor inferred. -/
theorem gaussianFiberMeasure_eq_of_orbit_mass_eq (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele)
    (M : Measure (adelicValueFiber L a)) [M.Regular]
    [SMulInvariantMeasure L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L a) M] (hM : M ≠ 0)
    (htrans : IsTransitiveAction L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L a)) (x₀ : adelicValueFiber L a)
    (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
    (hmass : gaussianFiberMeasure L hn hb a ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) =
      M ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))) :
    gaussianFiberMeasure L hn hb a = M := by
  letI := secondCountableTopology_fiberActingGroup L
  letI := sigmaCompactSpace_fiberActingGroup L
  exact eq_of_measure_orbit_eq _ M htrans x₀ K hc ho hM hmass

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
