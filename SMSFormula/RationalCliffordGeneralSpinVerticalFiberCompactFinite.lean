import SMSFormula.RationalCliffordGeneralSpinVerticalFiberUniformSigmaFinite
import SMSFormula.RationalCliffordSpinCandidateAdelicLocalQuotientSlice

/-!
# Compact finiteness of the vertical Spin source

The exact Spin Weil identity already forces the raw rational Spin quotient
measure to be finite on compact sets.  An open surjection from a locally
compact source lifts every compact target set into the image of one compact
source set.  The rational periodization of that compact set is at least one
above the target compact, so the quotient mass is bounded by the finite
ambient Haar mass of the lift.

This argument uses neither finite total Spin volume nor a measurable global
representative.  The subsequent transport from the Spin quotient into each
vertical fiber is reduced exactly to properness of the induced map from the
rational Spin quotient to the rational `GSpin` quotient.  Under that isolated
topological input, every translated and descended fiber is compact-finite,
and the existing section-free uniformization theorem makes both the class-Haar
bind and its ambient periodization sigma-finite.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Set
open Topology
open scoped ENNReal

namespace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An open surjection from a weakly locally compact space is compact-covering
in the weak sense needed here: every compact target set is contained in the
image of a compact source set. -/
theorem exists_compact_image_superset_of_isOpenMap_surjective
    [WeaklyLocallyCompactSpace X]
    (f : X → Y) (hopen : IsOpenMap f) (hsurj : Function.Surjective f)
    {K : Set Y} (hK : IsCompact K) :
    ∃ C : Set X, IsCompact C ∧ K ⊆ f '' C := by
  choose C hCcompact hCnhds using fun x : X => exists_compact_mem_nhds x
  have hopenCover : ∀ x : X, IsOpen (f '' interior (C x)) :=
    fun x => hopen _ isOpen_interior
  have hcover : K ⊆ ⋃ x : X, f '' interior (C x) := by
    intro y _
    rcases hsurj y with ⟨x, rfl⟩
    exact mem_iUnion.mpr
      ⟨x, ⟨x, mem_interior_iff_mem_nhds.mpr (hCnhds x), rfl⟩⟩
  rcases hK.elim_finite_subcover (fun x : X => f '' interior (C x))
      hopenCover hcover with ⟨I, hKI⟩
  refine ⟨⋃ x ∈ I, C x, I.isCompact_biUnion fun x _ => hCcompact x, ?_⟩
  intro y hy
  have hyU := hKI hy
  rcases mem_iUnion.mp hyU with ⟨x, hyU⟩
  rcases mem_iUnion.mp hyU with ⟨hxI, hyU⟩
  rcases hyU with ⟨c, hc, rfl⟩
  refine ⟨c, ?_, rfl⟩
  exact mem_iUnion.mpr
    ⟨x, mem_iUnion.mpr ⟨hxI, interior_subset hc⟩⟩

end Topology

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The represented Spin inclusion is a topological embedding.  Projection
of the intrinsic `GSpin` coordinates to the Clifford and matrix coordinates
is exactly the coordinate embedding which defines the Spin topology. -/
theorem cliffordSpinCandidateToCliffordGeneralSpinHom_isEmbedding
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    IsEmbedding (V.cliffordSpinCandidateToCliffordGeneralSpinHom A) := by
  let p :
      (((Finset (Fin n) → A) × Aˣ) ×
          (Matrix (Fin n) (Fin n) A × Matrix (Fin n) (Fin n) A)) →
        ((Finset (Fin n) → A) × Matrix (Fin n) (Fin n) A) :=
    fun z => (z.1.1, z.2.1)
  have hp : Continuous p :=
    (continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd)
  have hcomp :
      (p ∘ V.cliffordGeneralSpinPointCoordinateMap A) ∘
          V.cliffordSpinCandidateToCliffordGeneralSpinHom A =
        V.cliffordSpinCandidatePointCoordinateMap A := by
    funext x
    apply Prod.ext
    · ext u
      simp [p, Function.comp_def,
        cliffordSpinCandidateToCliffordGeneralSpinHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpinGroupHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpin]
    · ext i j
      simp [p, Function.comp_def,
        cliffordSpinCandidateToCliffordGeneralSpinHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpinGroupHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpin]
  apply IsEmbedding.of_comp
    (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom A)
    (hp.comp (V.continuous_cliffordGeneralSpinPointCoordinateMap A))
  rw [hcomp]
  exact V.cliffordSpinCandidatePointCoordinateMap_isEmbedding A

/-- The represented Spin inclusion is a closed embedding: its literal range
is the kernel of the continuous similitude coordinate. -/
theorem cliffordSpinCandidateToCliffordGeneralSpinHom_isClosedEmbedding
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    IsClosedEmbedding (V.cliffordSpinCandidateToCliffordGeneralSpinHom A) := by
  refine ⟨V.cliffordSpinCandidateToCliffordGeneralSpinHom_isEmbedding A, ?_⟩
  change IsClosed
    ((V.cliffordSpinCandidateToCliffordGeneralSpinHom A).range :
      Set (V.CliffordGeneralSpinIntrinsicPoint A))
  rw [V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker A]
  change IsClosed {x : V.CliffordGeneralSpinIntrinsicPoint A |
    x.similitude = 1}
  exact isClosed_eq
    (V.continuous_cliffordGeneralSpinSimilitude A) continuous_const

end RationalQuadraticSpaceMatrix

namespace MeasureTheory

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [T2Space Y]

/-- A proper measurable pushforward of a compact-finite measure is
compact-finite.  This is the exact transport statement needed below; no
surjectivity or total finiteness is involved. -/
theorem isFiniteMeasureOnCompacts_map_of_isProperMap
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f : X → Y) (hf : Measurable f) (hproper : IsProperMap f) :
    IsFiniteMeasureOnCompacts (Measure.map f μ) where
  lt_top_of_isCompact := by
    intro K hK
    rw [Measure.map_apply hf hK.measurableSet]
    exact (hproper.isCompact_preimage hK).measure_lt_top

end MeasureTheory

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ} {V : RationalQuadraticSpaceMatrix n}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2000000

/-- The raw differential Spin quotient measure is finite on every compact
set.  Compact lifting and the exact measurable Weil identity replace any
assumption that its total mass is finite. -/
theorem spinData_quotientMeasure_measure_lt_top_of_isCompact
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    {K : Set V.FullAdelicCliffordSpinCandidateLeftQuotient}
    (hK : IsCompact K) :
    D.spinData.quotientMeasure K < ∞ := by
  let Gamma := V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
  let q := V.fullAdelicCliffordSpinCandidateLeftQuotientMap
  letI : Countable Gamma :=
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup_countable
  letI : Measure.IsHaarMeasure D.spinData.adelicMeasure := by
    rw [D.spinRaw.adelicMeasure_eq]
    exact
      V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_isHaarMeasure
        D.spinFiniteScale D.spinRaw.volumeProductCertificate
  letI : IsFiniteMeasureOnCompacts D.spinData.adelicMeasure := by
    infer_instance
  obtain ⟨C, hCcompact, hKC⟩ :=
    Topology.exists_compact_image_superset_of_isOpenMap_surjective q
      V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isOpenMap
      Quot.mk_surjective hK
  have hCmeas : MeasurableSet C := hCcompact.measurableSet
  have hKmeas : MeasurableSet K := hK.measurableSet
  let f : V.FullAdelicCliffordSpinCandidateGroup → ℝ≥0∞ :=
    C.indicator fun _ => 1
  have hf : Measurable f := measurable_const.indicator hCmeas
  have hpoint :
      K.indicator (fun _ => (1 : ℝ≥0∞)) ≤ leftPeriodize Gamma f := by
    intro z
    by_cases hzK : z ∈ K
    · rw [Set.indicator_of_mem hzK]
      induction z using Quot.inductionOn with
      | _ x =>
        change (1 : ℝ≥0∞) ≤ leftPeriodize Gamma f (leftCosetMap Gamma x)
        rw [leftPeriodize_leftCosetMap]
        rcases hKC hzK with ⟨c, hcC, hcx⟩
        have hrel :=
          (V.fullAdelicCliffordSpinCandidateLeftQuotientMap_eq_iff x c).mp
            hcx.symm
        let gamma : Gamma := ⟨c * x⁻¹, hrel⟩
        calc
          (1 : ℝ≥0∞) = f ((gamma :
              V.FullAdelicCliffordSpinCandidateGroup) * x) := by
                simp [f, gamma, mul_assoc, hcC]
          _ ≤ ∑' delta : Gamma,
              f ((delta : V.FullAdelicCliffordSpinCandidateGroup) * x) :=
            ENNReal.le_tsum gamma
    · simp [hzK]
  calc
    D.spinData.quotientMeasure K =
        ∫⁻ z, K.indicator (fun _ => (1 : ℝ≥0∞)) z
          ∂D.spinData.quotientMeasure := by
            rw [lintegral_indicator_const hKmeas]
            simp
    _ ≤ ∫⁻ z, leftPeriodize Gamma f z
          ∂D.spinData.quotientMeasure := lintegral_mono hpoint
    _ = ∫⁻ x, f x ∂D.spinData.adelicMeasure :=
      D.spinData.isMeasurableWeilQuotientMeasure.lintegral_leftPeriodize_eq f hf
    _ = D.spinData.adelicMeasure C := by
      rw [lintegral_indicator_const hCmeas]
      simp
    _ < ∞ := hCcompact.measure_lt_top

/-- The raw differential Spin quotient measure is locally finite. -/
theorem spinData_quotientMeasure_isFiniteMeasureOnCompacts
    (D : V.CliffordSpinCandidateRawOnoTamagawaData) :
    IsFiniteMeasureOnCompacts D.spinData.quotientMeasure where
  lt_top_of_isCompact := by
    intro K hK
    exact D.spinData_quotientMeasure_measure_lt_top_of_isCompact hK

/-- The precise topological input still needed to transport compact
finiteness from the rational Spin quotient into the common rational `GSpin`
quotient.  It is intentionally not replaced by continuous injectivity. -/
def HasProperSpinQuotientEmbedding
    (V : RationalQuadraticSpaceMatrix n) : Prop :=
  IsProperMap V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin

/-- Right multiplication on the rational `GSpin` quotient is a genuine
homeomorphism. -/
noncomputable def fullAdelicCliffordGeneralSpinLeftQuotientRightMulHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    V.FullAdelicCliffordGeneralSpinLeftQuotient ≃ₜ
      V.FullAdelicCliffordGeneralSpinLeftQuotient where
  toFun := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x
  invFun := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x⁻¹
  left_inv z := by
    simp [V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul_rightMul]
  right_inv z := by
    simp [V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul_rightMul]
  continuous_toFun :=
    V.continuous_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x
  continuous_invFun :=
    V.continuous_fullAdelicCliffordGeneralSpinLeftQuotientRightMul x⁻¹

/-- Properness of the induced Spin-to-`GSpin` quotient map makes the neutral
raw Spin pushforward finite on compact subsets of the common quotient. -/
theorem spinGeneralSpinQuotientPushforwardMeasure_isFiniteMeasureOnCompacts_of_proper
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hproper : HasProperSpinQuotientEmbedding V) :
    IsFiniteMeasureOnCompacts
      (spinGeneralSpinQuotientPushforwardMeasure V D) := by
  letI : T2Space V.FullAdelicCliffordGeneralSpinLeftQuotient :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientT2SpaceForVerticalUniformSigmaFinite
  letI : IsFiniteMeasureOnCompacts D.spinData.quotientMeasure :=
    D.spinData_quotientMeasure_isFiniteMeasureOnCompacts
  unfold spinGeneralSpinQuotientPushforwardMeasure
    fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpinPushforward
  exact MeasureTheory.isFiniteMeasureOnCompacts_map_of_isProperMap
    D.spinData.quotientMeasure
    V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
    V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_measurable
    hproper

/-- Under the same single properness input, every literal translated vertical
Spin fiber is finite on compact sets. -/
theorem verticalSpinFiberMeasure_isFiniteMeasureOnCompacts_of_proper
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hproper : HasProperSpinQuotientEmbedding V)
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    IsFiniteMeasureOnCompacts (D.verticalSpinFiberMeasure V hsurj c) := by
  letI : T2Space V.FullAdelicCliffordGeneralSpinLeftQuotient :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientT2SpaceForVerticalUniformSigmaFinite
  letI : IsFiniteMeasureOnCompacts
      (spinGeneralSpinQuotientPushforwardMeasure V D) :=
    D.spinGeneralSpinQuotientPushforwardMeasure_isFiniteMeasureOnCompacts_of_proper
      hproper
  unfold verticalSpinFiberMeasure
  simpa [fullAdelicCliffordGeneralSpinLeftQuotientRightMulHomeomorph] using
    (Measure.IsFiniteMeasureOnCompacts.map
      (spinGeneralSpinQuotientPushforwardMeasure V D)
      (fullAdelicCliffordGeneralSpinLeftQuotientRightMulHomeomorph V
        (V.verticalGeneralSpinRepresentative hsurj c)))

/-- Properness gives compact-finiteness of every value of the descended
idele-class-indexed vertical kernel. -/
theorem verticalSpinFiberKernelAtIdeleClass_apply_isFiniteMeasureOnCompacts_of_proper
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hproper : HasProperSpinQuotientEmbedding L.rationalQuadraticSpaceMatrix)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    IsFiniteMeasureOnCompacts
      (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj c) := by
  rw [D.verticalSpinFiberKernelAtIdeleClass_apply L hn hsurj c]
  exact D.verticalSpinFiberMeasure_isFiniteMeasureOnCompacts_of_proper
    hproper hsurj c

/-- The isolated properness input supplies the common fiberwise-finite cover
without choosing a measurable representative. -/
theorem hasUniformFiniteVerticalFiberCover_of_proper
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hproper : HasProperSpinQuotientEmbedding L.rationalQuadraticSpaceMatrix)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    D.HasUniformFiniteVerticalFiberCover L hn hsurj := by
  apply D.hasUniformFiniteVerticalFiberCover_of_finite_compacts L hn hsurj
  intro c
  exact
    D.verticalSpinFiberKernelAtIdeleClass_apply_isFiniteMeasureOnCompacts_of_proper
      L hn hproper hsurj c

/-- Consequently the class-Haar vertical bind is sigma-finite. -/
theorem verticalSpinFiberHaarBoundMeasure_sigmaFinite_of_proper
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hproper : HasProperSpinQuotientEmbedding L.rationalQuadraticSpaceMatrix)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    SigmaFinite (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) :=
  D.verticalSpinFiberHaarBoundMeasure_sigmaFinite_of_uniformFiniteCover
    L hn hsurj (D.hasUniformFiniteVerticalFiberCover_of_proper L hn hproper hsurj)

/-- The exact ambient periodization is sigma-finite under precisely the same
properness input. -/
theorem periodizedVerticalSpinFiberHaarBoundMeasure_sigmaFinite_of_proper
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hproper : HasProperSpinQuotientEmbedding L.rationalQuadraticSpaceMatrix)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    SigmaFinite
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (D.verticalSpinFiberHaarBoundMeasure L hn hsurj)) :=
  D.periodizedVerticalSpinFiberHaarBoundMeasure_sigmaFinite_of_uniformFiniteCover
    L hn hsurj (D.hasUniformFiniteVerticalFiberCover_of_proper L hn hproper hsurj)

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
