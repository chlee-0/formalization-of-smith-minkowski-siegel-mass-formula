import SMSFormula.RationalCliffordGeneralSpinAdelicQuotientMeasurePeriodizedRightInvariant
import SMSFormula.RationalCliffordGeneralSpinHorizontalBoundSigmaFinite

/-!
# Sigma-finiteness of periodized adelic GSpin quotient measures

For a sigma-finite measure on the rational adelic GSpin quotient, take its
standard measurable spanning sets, map them into the exact fundamental domain,
and translate them by every rational diagonal element.  These countably many
measurable sets cover the ambient group.  Exact recovery on the fundamental
domain and rational-diagonal left invariance show that every member has the
same finite mass as the corresponding quotient spanning set.

This proves sigma-finiteness without a local quotient-chart calculation or an
Euler-product normalization.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The explicit fundamental-domain section is a measurable embedding into
the ambient adelic GSpin group. -/
theorem measurableEmbedding_fullAdelicCliffordGeneralSpinFundamentalDomainSection :
    MeasurableEmbedding
      V.fullAdelicCliffordGeneralSpinFundamentalDomainSection := by
  have hcoe : MeasurableEmbedding
      ((↑) : V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain →
        V.FullAdelicCliffordGeneralSpinGroup) :=
    MeasurableEmbedding.subtype_coe
      V.measurableSet_fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain
  have hcomp := hcoe.comp
    V.fullAdelicCliffordGeneralSpinFundamentalDomainMeasurableEquiv.measurableEmbedding
  simpa only [Function.comp_apply,
    V.coe_fullAdelicCliffordGeneralSpinFundamentalDomainMeasurableEquiv_apply]
    using hcomp

/-- Left multiplication of the ambient integrand by a rational diagonal
element does not change its descended left periodization. -/
theorem fullAdelicCliffordGeneralSpinLeftPeriodize_rationalLeftMul
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (y : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        (fun z => f ((delta : V.FullAdelicCliffordGeneralSpinGroup) * z)) y =
      leftPeriodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f y := by
  induction y using Quot.inductionOn with
  | _ y =>
    change (∑' gamma :
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
          f ((delta : V.FullAdelicCliffordGeneralSpinGroup) *
            ((gamma : V.FullAdelicCliffordGeneralSpinGroup) * y))) =
      ∑' gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
        f ((gamma : V.FullAdelicCliffordGeneralSpinGroup) * y)
    calc
      (∑' gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
          f ((delta : V.FullAdelicCliffordGeneralSpinGroup) *
            ((gamma : V.FullAdelicCliffordGeneralSpinGroup) * y))) =
        ∑' gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
          f (((delta * gamma :
            V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
              V.FullAdelicCliffordGeneralSpinGroup) * y) := by
            apply tsum_congr
            intro gamma
            change f ((delta : V.FullAdelicCliffordGeneralSpinGroup) *
              ((gamma : V.FullAdelicCliffordGeneralSpinGroup) * y)) =
                f (((delta : V.FullAdelicCliffordGeneralSpinGroup) *
                  (gamma : V.FullAdelicCliffordGeneralSpinGroup)) * y)
            rw [mul_assoc]
      _ = ∑' gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
          f ((gamma : V.FullAdelicCliffordGeneralSpinGroup) * y) := by
            exact (Equiv.mulLeft delta).tsum_eq
              (fun gamma :
                V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup =>
                  f ((gamma : V.FullAdelicCliffordGeneralSpinGroup) * y))

/-- Every periodized quotient lift is invariant under left multiplication by
the rational adelic GSpin diagonal. -/
theorem map_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_rationalLeftMul
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    (delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
    Measure.map
        (Homeomorph.mulLeft
          (delta : V.FullAdelicCliffordGeneralSpinGroup))
        (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ) =
      V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf
    (Homeomorph.mulLeft
      (delta : V.FullAdelicCliffordGeneralSpinGroup)).measurable]
  calc
    ∫⁻ a, f ((delta : V.FullAdelicCliffordGeneralSpinGroup) * a) ∂
        V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ =
        ∫⁻ y, leftPeriodize
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
          (fun a => f ((delta : V.FullAdelicCliffordGeneralSpinGroup) * a)) y ∂μ :=
      V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
        μ _ (hf.comp
          (Homeomorph.mulLeft
            (delta : V.FullAdelicCliffordGeneralSpinGroup)).measurable)
    _ = ∫⁻ y, leftPeriodize
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f y ∂μ := by
      apply lintegral_congr
      exact V.fullAdelicCliffordGeneralSpinLeftPeriodize_rationalLeftMul f delta
    _ = ∫⁻ a, f a ∂
        V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ :=
      (V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
        μ f hf).symm

/-- The quotient spanning set transported into one rational translate of the
fundamental domain. -/
def fullAdelicCliffordGeneralSpinPeriodizedSpanningSet
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    [SigmaFinite μ]
    (delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (m : ℕ) : Set V.FullAdelicCliffordGeneralSpinGroup :=
  Homeomorph.mulLeft (delta : V.FullAdelicCliffordGeneralSpinGroup) ''
    (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection ''
      spanningSets μ m)

theorem measurableSet_fullAdelicCliffordGeneralSpinPeriodizedSpanningSet
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    [SigmaFinite μ]
    (delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (m : ℕ) :
    MeasurableSet
      (V.fullAdelicCliffordGeneralSpinPeriodizedSpanningSet μ delta m) := by
  apply (measurableEmbedding_mulLeft
    (delta : V.FullAdelicCliffordGeneralSpinGroup)).measurableSet_image.mpr
  apply
    V.measurableEmbedding_fullAdelicCliffordGeneralSpinFundamentalDomainSection
      |>.measurableSet_image.mpr
  exact measurableSet_spanningSets μ m

/-- The un-translated ambient spanning set has exactly the mass of its
quotient spanning set. -/
theorem fullAdelicCliffordGeneralSpinPeriodizedSpanningSet_one_measure
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    [SigmaFinite μ]
    (m : ℕ) :
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ
        (V.fullAdelicCliffordGeneralSpinPeriodizedSpanningSet μ 1 m) =
      μ (spanningSets μ m) := by
  let S := V.fullAdelicCliffordGeneralSpinFundamentalDomainSection ''
    spanningSets μ m
  have hS : MeasurableSet S :=
    V.measurableEmbedding_fullAdelicCliffordGeneralSpinFundamentalDomainSection
      |>.measurableSet_image.mpr (measurableSet_spanningSets μ m)
  have hsubset :
      S ⊆ V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain := by
    rintro _ ⟨y, _, rfl⟩
    exact V.fullAdelicCliffordGeneralSpinFundamentalDomainSection_mem y
  change V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ
      (Homeomorph.mulLeft
        (1 : V.FullAdelicCliffordGeneralSpinGroup) '' S) = _
  have hone :
      Homeomorph.mulLeft (1 : V.FullAdelicCliffordGeneralSpinGroup) '' S = S := by
    ext z
    simp
  rw [hone]
  calc
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ S =
        (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ).restrict
          V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain S := by
      rw [Measure.restrict_apply hS, Set.inter_eq_left.mpr hsubset]
    _ = V.fullAdelicCliffordGeneralSpinFundamentalSectionLift μ S := by
      rw [V.restrict_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ]
    _ = μ (spanningSets μ m) := by
      rw [fullAdelicCliffordGeneralSpinFundamentalSectionLift,
        Measure.map_apply
          V.measurable_fullAdelicCliffordGeneralSpinFundamentalDomainSection hS,
        Set.preimage_image_eq _
          V.injective_fullAdelicCliffordGeneralSpinFundamentalDomainSection]

/-- Every rational translate of an ambient spanning set has the same finite
mass as the original quotient spanning set. -/
theorem fullAdelicCliffordGeneralSpinPeriodizedSpanningSet_measure
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    [SigmaFinite μ]
    (delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
    (m : ℕ) :
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ
        (V.fullAdelicCliffordGeneralSpinPeriodizedSpanningSet μ delta m) =
      μ (spanningSets μ m) := by
  let T := V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ
  let S := V.fullAdelicCliffordGeneralSpinFundamentalDomainSection ''
    spanningSets μ m
  have hS : MeasurableSet S :=
    V.measurableEmbedding_fullAdelicCliffordGeneralSpinFundamentalDomainSection
      |>.measurableSet_image.mpr (measurableSet_spanningSets μ m)
  change T (Homeomorph.mulLeft
    (delta : V.FullAdelicCliffordGeneralSpinGroup) '' S) = _
  calc
    T (Homeomorph.mulLeft
        (delta : V.FullAdelicCliffordGeneralSpinGroup) '' S) =
        Measure.map
          (Homeomorph.mulLeft
            (delta : V.FullAdelicCliffordGeneralSpinGroup)) T
          (Homeomorph.mulLeft
            (delta : V.FullAdelicCliffordGeneralSpinGroup) '' S) := by
      rw [V.map_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_rationalLeftMul
        μ delta]
    _ = T S := by
      change (Measure.map
        (fun x : V.FullAdelicCliffordGeneralSpinGroup =>
          (delta : V.FullAdelicCliffordGeneralSpinGroup) * x) T)
          ((fun x : V.FullAdelicCliffordGeneralSpinGroup =>
            (delta : V.FullAdelicCliffordGeneralSpinGroup) * x) '' S) = T S
      rw [Measure.map_apply
        (show Measurable
            (fun x : V.FullAdelicCliffordGeneralSpinGroup =>
              (delta : V.FullAdelicCliffordGeneralSpinGroup) * x) from
          (Homeomorph.mulLeft
            (delta : V.FullAdelicCliffordGeneralSpinGroup)).measurable)
        ((measurableEmbedding_mulLeft
          (delta : V.FullAdelicCliffordGeneralSpinGroup)).measurableSet_image.mpr hS),
        Set.preimage_image_eq _
          (show Function.Injective
              (fun x : V.FullAdelicCliffordGeneralSpinGroup =>
                (delta : V.FullAdelicCliffordGeneralSpinGroup) * x) from
            (Homeomorph.mulLeft
              (delta : V.FullAdelicCliffordGeneralSpinGroup)).injective)]
    _ = μ (spanningSets μ m) := by
      simpa [T, S, fullAdelicCliffordGeneralSpinPeriodizedSpanningSet] using
        V.fullAdelicCliffordGeneralSpinPeriodizedSpanningSet_one_measure μ m

/-- The rational translates of the transported quotient spanning sets cover
the full ambient adelic GSpin group. -/
theorem iUnion_fullAdelicCliffordGeneralSpinPeriodizedSpanningSet
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    [SigmaFinite μ] :
    ⋃ p :
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup × ℕ,
      V.fullAdelicCliffordGeneralSpinPeriodizedSpanningSet μ p.1 p.2 =
        Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  let y := V.fullAdelicCliffordGeneralSpinLeftQuotientMap g
  have hyUnion : y ∈ ⋃ m, spanningSets μ m := by
    rw [iUnion_spanningSets]
    exact Set.mem_univ y
  rcases Set.mem_iUnion.mp hyUnion with ⟨m, hym⟩
  have hrelative :
      g * (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y)⁻¹ ∈
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup := by
    apply (V.fullAdelicCliffordGeneralSpinLeftQuotientMap_eq_iff
      (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y) g).mp
    exact
      (V.fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalDomainSection y).trans
        rfl
  let delta : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    ⟨g * (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y)⁻¹,
      hrelative⟩
  apply Set.mem_iUnion.mpr
  refine ⟨(delta, m), ?_⟩
  refine ⟨V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y,
    ⟨y, hym, rfl⟩, ?_⟩
  change
    (g * (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y)⁻¹) *
        V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y = g
  simp [mul_assoc]

/-- Periodizing any sigma-finite rational adelic GSpin quotient measure gives
a sigma-finite ambient measure. -/
theorem fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_sigmaFinite
    (μ : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient)
    [SigmaFinite μ] :
    SigmaFinite
      (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ) := by
  letI : Countable
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable
  let S : Set (Set V.FullAdelicCliffordGeneralSpinGroup) :=
    Set.range fun p :
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup × ℕ =>
      V.fullAdelicCliffordGeneralSpinPeriodizedSpanningSet μ p.1 p.2
  have hScount : S.Countable := Set.countable_range _
  apply Measure.sigmaFinite_of_countable hScount
  · intro A hA
    rcases hA with ⟨⟨delta, m⟩, rfl⟩
    rw [V.fullAdelicCliffordGeneralSpinPeriodizedSpanningSet_measure μ delta m]
    exact measure_spanningSets_lt_top μ m
  · rw [Set.sUnion_range]
    exact V.iUnion_fullAdelicCliffordGeneralSpinPeriodizedSpanningSet μ

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The periodized ambient lift of the literal lattice raw-`SO` horizontal
fiber-Haar bind is sigma-finite. -/
theorem periodizedHorizontalRawSOFiberHaarBoundMeasure_sigmaFinite
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    SigmaFinite
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (L.horizontalRawSOFiberHaarBoundMeasure inst
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
            L hn inst hP hconv))) := by
  letI : SigmaFinite
      (L.horizontalRawSOFiberHaarBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv)) :=
    L.horizontalRawSOFiberHaarBoundMeasure_sigmaFinite hn inst hP hconv
  exact
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_sigmaFinite
      (L.horizontalRawSOFiberHaarBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv))

end PositiveDefiniteIntegralLattice
