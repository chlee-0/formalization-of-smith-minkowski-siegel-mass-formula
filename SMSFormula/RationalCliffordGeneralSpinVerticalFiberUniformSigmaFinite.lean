import SMSFormula.RationalCliffordGeneralSpinVerticalFiberQuotientPeriodized
import SMSFormula.RationalCliffordGeneralSpinVerticalEquivalence
import SMSFormula.RationalCliffordGeneralSpinAdelicQuotientMeasurePeriodizedSigmaFinite

/-!
# Uniform sigma-finiteness criterion for the vertical Spin bind

Pointwise sigma-finiteness of the translated Spin fibers is not by itself a
uniform kernel decomposition.  This module isolates the exact additional
geometric input needed by the vertical comparison: one countable measurable
cover of the rational adelic `GSpin` quotient on which every fiber has finite
mass.

Given such a cover, intersect its members with finite-mass spanning sets in
the idele-class base and with measurable fiber-mass level sets.  Exact fiber
support then bounds every resulting piece by a finite constant times a finite
base mass.  These pieces cover the whole quotient, proving sigma-finiteness of
the direct `Measure.bind`.  The existing exact fundamental-domain
periodization then gives sigma-finiteness of the ambient lift.

No measurable representative, Cartesian presentation, quotient comparison,
Spin-volume finiteness, or vertical normalization scalar is used here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Set
open scoped ENNReal ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The rational adelic `GSpin` left quotient is Hausdorff.  This local
witness is installed only when taking its fixed compact covering below. -/
noncomputable def
    fullAdelicCliffordGeneralSpinLeftQuotientT2SpaceForVerticalUniformSigmaFinite :
    T2Space V.FullAdelicCliffordGeneralSpinLeftQuotient := by
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  letI : T2Space V.FullAdelicCliffordGeneralSpinGroup :=
    V.cliffordGeneralSpinIntrinsicPointT2Space RationalAdele
  apply (t2Space_iff_of_isOpenQuotientMap
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isOpenQuotientMap).mpr
  rw [show
      {p : V.FullAdelicCliffordGeneralSpinGroup ×
          V.FullAdelicCliffordGeneralSpinGroup |
        V.fullAdelicCliffordGeneralSpinLeftQuotientMap p.1 =
          V.fullAdelicCliffordGeneralSpinLeftQuotientMap p.2} =
        (fun p : V.FullAdelicCliffordGeneralSpinGroup ×
            V.FullAdelicCliffordGeneralSpinGroup => p.2 * p.1⁻¹) ⁻¹'
          (V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :
            Set V.FullAdelicCliffordGeneralSpinGroup) by
    ext p
    exact V.fullAdelicCliffordGeneralSpinLeftQuotientMap_eq_iff p.1 p.2]
  exact V.isClosed_rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup.preimage
    (continuous_snd.mul continuous_fst.inv)

end RationalQuadraticSpaceMatrix

namespace MeasureTheory

variable {C X : Type*} [MeasurableSpace C] [MeasurableSpace X]

/-- The level-bounded pieces used to turn a common fiberwise-finite cover
into finite-mass spanning sets for a kernel bind. -/
def fiberwiseFiniteBindSpanningSet
    (mu : Measure C) [SigmaFinite mu]
    (kappa : ProbabilityTheory.Kernel C X)
    (p : X → C) (E : ℕ → Set X)
    (i j k : ℕ) : Set X :=
  E i ∩ p ⁻¹' (spanningSets mu j ∩
    {c | kappa c (E i) < (k : ℝ≥0∞)})

/-- A section-free sigma-finiteness criterion for a fiber-supported kernel
bind.  The only uniformity assumption is a countable measurable cover `E`
whose members have finite mass in every fiber. -/
theorem sigmaFinite_bind_of_uniform_fiberwiseFinite_cover
    (mu : Measure C) [SigmaFinite mu]
    (kappa : ProbabilityTheory.Kernel C X)
    (p : X → C) (hp : Measurable p)
    (E : ℕ → Set X)
    (hEmeas : ∀ i, MeasurableSet (E i))
    (hEcover : ⋃ i, E i = Set.univ)
    (hEfinite : ∀ c i, kappa c (E i) ≠ ∞)
    (hsupport : ∀ c (s : Set X), MeasurableSet s →
      Disjoint s {x | p x = c} → kappa c s = 0) :
    SigmaFinite (Measure.bind mu kappa) := by
  let S : Set (Set X) := Set.range fun q : (ℕ × ℕ) × ℕ =>
    fiberwiseFiniteBindSpanningSet mu kappa p E q.1.1 q.1.2 q.2
  have hScount : S.Countable := Set.countable_range _
  apply Measure.sigmaFinite_of_countable hScount
  · intro A hA
    rcases hA with ⟨⟨⟨i, j⟩, k⟩, rfl⟩
    let B : Set C := spanningSets mu j
    let T : Set C := {c | kappa c (E i) < (k : ℝ≥0∞)}
    have hB : MeasurableSet B := measurableSet_spanningSets mu j
    have hT : MeasurableSet T :=
      measurableSet_lt (kappa.measurable_coe (hEmeas i)) measurable_const
    have hAmeas : MeasurableSet
        (fiberwiseFiniteBindSpanningSet mu kappa p E i j k) :=
      (hEmeas i).inter ((hB.inter hT).preimage hp)
    rw [Measure.bind_apply hAmeas kappa.aemeasurable]
    refine lt_of_le_of_lt
      (show
        (∫⁻ c, kappa c
            (fiberwiseFiniteBindSpanningSet mu kappa p E i j k) ∂mu) ≤
          ∫⁻ c, B.indicator (fun _ => (k : ℝ≥0∞)) c ∂mu from
        lintegral_mono fun c => ?_)
      ?_
    · by_cases hcB : c ∈ B
      · by_cases hcT : c ∈ T
        · rw [Set.indicator_of_mem hcB]
          exact (measure_mono inter_subset_left).trans (le_of_lt hcT)
        · have hdisj : Disjoint
              (fiberwiseFiniteBindSpanningSet mu kappa p E i j k)
              {x | p x = c} := by
            apply Set.disjoint_left.2
            intro x hx hxc
            apply hcT
            change kappa c (E i) < (k : ℝ≥0∞)
            rw [← hxc]
            exact hx.2.2
          rw [hsupport c _ hAmeas hdisj]
          simp [hcB]
      · have hdisj : Disjoint
            (fiberwiseFiniteBindSpanningSet mu kappa p E i j k)
            {x | p x = c} := by
          apply Set.disjoint_left.2
          intro x hx hxc
          apply hcB
          rw [← hxc]
          exact hx.2.1
        rw [hsupport c _ hAmeas hdisj]
        simp [hcB]
    · rw [lintegral_indicator_const hB]
      exact ENNReal.mul_lt_top (by simp) (measure_spanningSets_lt_top mu j)
  · rw [Set.sUnion_range]
    apply Set.eq_univ_of_forall
    intro x
    have hxE : x ∈ ⋃ i, E i := by
      rw [hEcover]
      exact Set.mem_univ x
    rcases Set.mem_iUnion.mp hxE with ⟨i, hxi⟩
    have hxp : p x ∈ ⋃ j, spanningSets mu j := by
      rw [iUnion_spanningSets]
      exact Set.mem_univ (p x)
    rcases Set.mem_iUnion.mp hxp with ⟨j, hxj⟩
    rcases ENNReal.exists_nat_gt (hEfinite (p x) i) with ⟨k, hk⟩
    apply Set.mem_iUnion.mpr
    refine ⟨((i, j), k), ?_⟩
    exact ⟨hxi, hxj, hk⟩

/-- On a sigma-compact Hausdorff Borel space, pointwise finiteness of every
fiber measure on compact sets supplies the required common cover: use the
fixed topological compact covering.  No measurable choice in the base is
needed. -/
theorem exists_uniform_fiberwiseFinite_cover_of_finite_compacts
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    [SigmaCompactSpace X]
    (kappa : ProbabilityTheory.Kernel C X)
    (hfinite : ∀ c, IsFiniteMeasureOnCompacts (kappa c)) :
    ∃ E : ℕ → Set X,
      (∀ i, MeasurableSet (E i)) ∧
      (⋃ i, E i = Set.univ) ∧
      ∀ c i, kappa c (E i) ≠ ∞ := by
  refine ⟨compactCovering X, ?_, iUnion_compactCovering X, ?_⟩
  · intro i
    exact (isCompact_compactCovering X i).measurableSet
  · intro c i
    letI : IsFiniteMeasureOnCompacts (kappa c) := hfinite c
    exact ne_top_of_lt (isCompact_compactCovering X i).measure_lt_top

end MeasureTheory

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2000000

/-- The precise remaining geometric uniformity input for the vertical Spin
bind: a common measurable countable cover having finite mass in every
translated fiber. -/
def HasUniformFiniteVerticalFiberCover
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Prop :=
  ∃ E : ℕ → Set
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient,
    (∀ i, MeasurableSet (E i)) ∧
    (⋃ i, E i = Set.univ) ∧
    ∀ c i, D.verticalSpinFiberKernelAtIdeleClass L hn hsurj c (E i) ≠ ∞

/-- Finiteness of every translated vertical fiber on compact subsets is a
section-free sufficient input for the common uniform cover. -/
theorem hasUniformFiniteVerticalFiberCover_of_finite_compacts
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (hfinite : ∀ c, IsFiniteMeasureOnCompacts
      (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj c)) :
    D.HasUniformFiniteVerticalFiberCover L hn hsurj := by
  let V := L.rationalQuadraticSpaceMatrix
  letI : SecondCountableTopology
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientSecondCountableTopology
  letI : T2Space V.FullAdelicCliffordGeneralSpinLeftQuotient :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientT2SpaceForVerticalUniformSigmaFinite
  letI : SigmaCompactSpace
      V.FullAdelicCliffordGeneralSpinLeftQuotient := by
    infer_instance
  exact MeasureTheory.exists_uniform_fiberwiseFinite_cover_of_finite_compacts
    (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj) hfinite

/-- A common fiberwise-finite cover makes the class-Haar vertical bind
sigma-finite.  Exact idele-class fiber support supplies the zero contribution
outside each base mass-level piece. -/
theorem verticalSpinFiberHaarBoundMeasure_sigmaFinite_of_uniformFiniteCover
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (hcover : D.HasUniformFiniteVerticalFiberCover L hn hsurj) :
    SigmaFinite (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) := by
  rcases hcover with ⟨E, hEmeas, hEcover, hEfinite⟩
  let V := L.rationalQuadraticSpaceMatrix
  change SigmaFinite
    (Measure.bind rationalIdeleClassHaarMeasure
      (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj))
  apply MeasureTheory.sigmaFinite_bind_of_uniform_fiberwiseFinite_cover
    rationalIdeleClassHaarMeasure
    (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj)
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
    V.continuous_fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass.measurable
    E hEmeas hEcover hEfinite
  intro c s hs hdisj
  rw [D.verticalSpinFiberKernelAtIdeleClass_apply L hn hsurj c]
  exact verticalSpinFiberMeasure_apply_eq_zero_of_disjoint_fiber
    (V := V) D hsurj c hs hdisj

/-- Under the same isolated geometric input, exact rational-`GSpin`
periodization of the vertical quotient bind is sigma-finite. -/
theorem periodizedVerticalSpinFiberHaarBoundMeasure_sigmaFinite_of_uniformFiniteCover
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (hcover : D.HasUniformFiniteVerticalFiberCover L hn hsurj) :
    SigmaFinite
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (D.verticalSpinFiberHaarBoundMeasure L hn hsurj)) := by
  letI : SigmaFinite (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) :=
    D.verticalSpinFiberHaarBoundMeasure_sigmaFinite_of_uniformFiniteCover
      L hn hsurj hcover
  exact
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_sigmaFinite
      (D.verticalSpinFiberHaarBoundMeasure L hn hsurj)

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
