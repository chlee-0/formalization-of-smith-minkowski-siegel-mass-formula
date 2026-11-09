import SMSFormula.RationalCliffordSpinCandidateIntegralFiniteSheetHaar
import SMSFormula.RationalCliffordSpinCandidatePlacewiseUnimodular

/-!
# The placewise two-sheet Haar scalar of the Spin map

The real and p-adic glued Clifford--Spin measures were defined from the same
identity charts as the invariant-differential special-orthogonal measures.
This file evaluates the Haar scalar of the point-map pushforward on the
actual open image.  A compact positive part of the identity target chart has
a preimage consisting of exactly two disjoint sheets, related by the scalar
Clifford point `-1`, and one sheet has exactly the differential mass of the
target patch.  Consequently the pushforward is literally twice the
differential measure on the image.
-/

open MeasureTheory
open Topology
open TopologicalSpace
open scoped ENNReal

noncomputable section

namespace MeasureTheory.TranslatedHomChart

set_option linter.unusedSectionVars false

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

/-- A two-point local chart whose source restriction maps to the target
restriction has pushforward exactly twice the target measure restricted to
the actual open image. -/
theorem map_rangeRestrict_eq_two_smul_comap_of_two_sheet_local_chart
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hf : Continuous f) (hfe : (f : G → H) = e)
    (hone : (1 : G) ∈ e.source) (hrange : IsOpen (f.range : Set H))
    (k : G) (hk : f k = 1) (hkone : k ≠ 1)
    (hker : ∀ x : G, f x = 1 → x = 1 ∨ x = k)
    (μ : Measure G) (ν : Measure H)
    [Measure.IsHaarMeasure μ] [Measure.IsHaarMeasure ν]
    (hlocal : Measure.map f (μ.restrict e.source) = ν.restrict e.target) :
    Measure.map f.rangeRestrict μ =
      (2 : NNReal) • Measure.comap f.range.subtype ν := by
  let R := f.range
  let fR : G →* R := f.rangeRestrict
  let j : e.target → R := identityTargetToRange f e hfe
  have hj : IsOpenEmbedding j :=
    identityTargetToRange_isOpenEmbedding f e hfe hrange
  letI : LocallyCompactSpace e.target := e.open_target.locallyCompactSpace
  let y0 : e.target := ⟨e 1, e.map_source hone⟩
  letI : Nonempty e.target := ⟨y0⟩
  let K0 : PositiveCompacts e.target := Classical.arbitrary _
  let K : PositiveCompacts R := K0.map j hj.continuous hj.isOpenMap
  have hKcoe : (K : Set R) = j '' (K0 : Set e.target) :=
    PositiveCompacts.coe_map hj.continuous hj.isOpenMap K0
  let b : e.target → G := fun y => (e.toHomeomorphSourceTarget.symm y).1
  let B : Set G := b '' (K0 : Set e.target)
  have hbcont : Continuous b :=
    continuous_subtype_val.comp e.toHomeomorphSourceTarget.symm.continuous
  have hBcompact : IsCompact B := K0.isCompact.image hbcont
  have hBsource : B ⊆ e.source := by
    rintro _ ⟨y, -, rfl⟩
    exact (e.toHomeomorphSourceTarget.symm y).2
  have hpre : fR ⁻¹' (K : Set R) =
      B ∪ (fun x => k⁻¹ * x) ⁻¹' B := by
    ext x
    constructor
    · intro hx
      rw [hKcoe] at hx
      rcases hx with ⟨y, hyK, hfy⟩
      let u : G := b y
      have huB : u ∈ B := ⟨y, hyK, rfl⟩
      have hfu : f u = y.1 := by
        change f (e.toHomeomorphSourceTarget.symm y).1 = y.1
        rw [congrFun hfe]
        exact congrArg Subtype.val
          (e.toHomeomorphSourceTarget.apply_symm_apply y)
      have hfx : f x = y.1 := by
        simpa [j, identityTargetToRange, fR] using
          (congrArg Subtype.val hfy).symm
      have hfxu : f (x * u⁻¹) = 1 := by
        rw [map_mul, map_inv, hfx, hfu]
        simp
      rcases hker (x * u⁻¹) hfxu with hxone | hxk
      · left
        have : x = u := by
          calc
            x = (x * u⁻¹) * u := by simp
            _ = u := by rw [hxone, one_mul]
        rwa [this]
      · right
        change k⁻¹ * x ∈ B
        have hxku : x = k * u := by
          calc
            x = (x * u⁻¹) * u := by simp
            _ = k * u := by rw [hxk]
        rw [hxku]
        simpa using huB
    · rintro (hx | hx)
      · rcases hx with ⟨y, hyK, rfl⟩
        rw [hKcoe]
        refine ⟨y, hyK, Subtype.ext ?_⟩
        change y.1 = f (e.toHomeomorphSourceTarget.symm y).1
        rw [congrFun hfe]
        exact (congrArg Subtype.val
          (e.toHomeomorphSourceTarget.apply_symm_apply y)).symm
      · change k⁻¹ * x ∈ B at hx
        rcases hx with ⟨y, hyK, hyx⟩
        rw [hKcoe]
        refine ⟨y, hyK, Subtype.ext ?_⟩
        have hfx : f x = f (k⁻¹ * x) := by simp [hk]
        calc
          y.1 = f (b y) := by
            change y.1 = f (e.toHomeomorphSourceTarget.symm y).1
            rw [congrFun hfe]
            exact (congrArg Subtype.val
              (e.toHomeomorphSourceTarget.apply_symm_apply y)).symm
          _ = f (k⁻¹ * x) := congrArg f hyx
          _ = f x := hfx.symm
          _ = (fR x).1 := rfl
  have hdisj : Disjoint B ((fun x => k⁻¹ * x) ⁻¹' B) := by
    have hwhole := disjoint_source_translate_of_kernel_point f e hfe k hk hkone
    apply hwhole.mono hBsource
    intro x hx
    exact hBsource hx
  let T : Set H := Subtype.val '' (K0 : Set e.target)
  have hTcompact : IsCompact T := K0.isCompact.image continuous_subtype_val
  have hTtarget : T ⊆ e.target := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hpreLocal : f ⁻¹' T ∩ e.source = B := by
    ext x
    constructor
    · rintro ⟨⟨y, hyK, hfy⟩, hxsource⟩
      refine ⟨y, hyK, ?_⟩
      symm
      apply e.injOn hxsource (e.toHomeomorphSourceTarget.symm y).2
      calc
        e x = f x := (congrFun hfe x).symm
        _ = y.1 := hfy.symm
        _ = e (e.toHomeomorphSourceTarget.symm y).1 :=
          (congrArg Subtype.val
            (e.toHomeomorphSourceTarget.apply_symm_apply y)).symm
    · rintro ⟨y, hyK, rfl⟩
      constructor
      · refine ⟨y, hyK, ?_⟩
        rw [congrFun hfe]
        exact (congrArg Subtype.val
          (e.toHomeomorphSourceTarget.apply_symm_apply y)).symm
      · exact (e.toHomeomorphSourceTarget.symm y).2
  have hlocalMass : μ B = ν T := by
    have h := congrArg (fun m : Measure H => m T) hlocal
    change (Measure.map f (μ.restrict e.source)) T =
      (ν.restrict e.target) T at h
    rw [Measure.map_apply hf.measurable hTcompact.measurableSet,
      Measure.restrict_apply
        (hTcompact.measurableSet.preimage hf.measurable),
      hpreLocal, Measure.restrict_apply hTcompact.measurableSet,
      Set.inter_eq_left.mpr hTtarget] at h
    exact h
  have hsubtypeImage : R.subtype '' (K : Set R) = T := by
    rw [hKcoe]
    ext y
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨j w, ⟨w, hw, rfl⟩, rfl⟩
  let νR : Measure R := Measure.comap R.subtype ν
  letI : LocallyCompactSpace R := hrange.locallyCompactSpace
  letI : SecondCountableTopology R :=
    TopologicalSpace.Subtype.secondCountableTopology _
  letI : Measure.IsHaarMeasure νR := by
    dsimp [νR]
    exact Measure.IsHaarMeasure.comap
      (μ := ν) (f := R.subtype) (mH := ContinuousMul.measurableMul)
      hrange.isOpenEmbedding_subtypeVal
  have hmass : μ B = νR (K : Set R) := by
    calc
      μ B = ν T := hlocalMass
      _ = ν (R.subtype '' (K : Set R)) := congrArg ν hsubtypeImage.symm
      _ = νR (K : Set R) := by
        dsimp [νR]
        exact (comap_subtype_coe_apply hrange.measurableSet ν _).symm
  have hmapHaar : Measure.IsHaarMeasure (Measure.map fR μ) :=
    isHaarMeasure_map_rangeRestrict_of_two_point_local_chart
      f e hf hfe hone hrange k hk hker μ
  letI : Measure.IsHaarMeasure (Measure.map fR μ) := hmapHaar
  have hfR : Continuous fR := continuous_induced_rng.mpr hf
  let c : NNReal := Measure.haarScalarFactor (Measure.map fR μ) νR
  have hglobal : Measure.map fR μ = c • νR :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hc : c = 2 :=
    haarScalar_eq_two_of_two_sheet_patch fR μ νR c k
      (K : Set R) B
      hfR.measurable.aemeasurable
      K.isCompact.measurableSet
      (hBcompact.measurableSet.preimage
        (continuous_const.inv.mul continuous_id).measurable)
      hpre hdisj hmass
      (ne_of_gt (Measure.measure_pos_of_nonempty_interior νR K.interior_nonempty))
      (ne_of_lt K.isCompact.measure_lt_top) hglobal
  rw [hglobal, hc]

end MeasureTheory.TranslatedHomChart

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 3000000

noncomputable local instance placewiseFiniteSheetRealSOMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) := borel _

noncomputable local instance placewiseFiniteSheetRealSOBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) := ⟨rfl⟩

noncomputable local instance placewiseFiniteSheetRealInvariantMeasurableSpace :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := borel _

noncomputable local instance placewiseFiniteSheetRealInvariantBorelSpace :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := ⟨rfl⟩

noncomputable local instance placewiseFiniteSheetPadicSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := borel _

noncomputable local instance placewiseFiniteSheetPadicSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := ⟨rfl⟩

/-- The scalar Clifford point `-1` is nontrivial over every
characteristic-zero field. -/
theorem cliffordSpinCandidateNegOnePoint_ne_one
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] :
    V.cliffordSpinCandidateNegOnePoint K ≠ 1 := by
  intro hk
  let E :=
    V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint K
  have hE : E (negOneRootOfUnity K) = E 1 := by
    apply Subtype.ext
    simpa [cliffordSpinCandidateNegOnePoint, E] using hk
  have hz : negOneRootOfUnity K = 1 := E.injective hE
  have hval := congrArg (fun z : rootsOfUnity 2 K => ((z : Kˣ) : K)) hz
  have hneg : (-1 : K) = 1 := by simpa [negOneRootOfUnity] using hval
  norm_num at hneg

theorem restrict_realCliffordSpinCandidateChartGluedMeasure_identitySource :
    V.realCliffordSpinCandidateChartGluedMeasure.restrict
        V.realCliffordSpinCandidateIdentityChart.source =
      Measure.map Subtype.val
        V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
  let e := V.realCliffordSpinCandidateIdentityChart
  have hrestrict := V.restrict_realCliffordSpinCandidateChartGluedMeasure_source 1
  have hleft := V.map_realCliffordSpinCandidateIdentityChartSourceMeasure_left 1
  calc
    V.realCliffordSpinCandidateChartGluedMeasure.restrict e.source =
        V.realCliffordSpinCandidateChartGluedMeasure.restrict
          (MeasureTheory.TranslatedHomChart.source e 1) := by
      rw [source_one e]
    _ = Measure.map Subtype.val
        (V.realCliffordSpinCandidateTranslatedChartSourceMeasure 1) := hrestrict
    _ = Measure.map Subtype.val
        (Measure.map
          (MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph e 1)
          V.realCliffordSpinCandidateIdentityChartSourceMeasure) := by
      rw [hleft]
    _ = Measure.map Subtype.val
        V.realCliffordSpinCandidateIdentityChartSourceMeasure := by
      rw [Measure.map_map]
      · congr 1
        funext x
        simp [MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph]
      · exact continuous_subtype_val.measurable
      · exact
          (MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph e 1).measurable

theorem map_realCliffordSpinCandidateChartGluedMeasure_restrict_identitySource :
    Measure.map V.realCliffordSpinCandidateToSpecialOrthogonalHom
        (V.realCliffordSpinCandidateChartGluedMeasure.restrict
          V.realCliffordSpinCandidateIdentityChart.source) =
      V.realInvariantDifferentialGroupMeasure.restrict
        V.realCliffordSpinCandidateIdentityChart.target := by
  rw [V.restrict_realCliffordSpinCandidateChartGluedMeasure_identitySource,
    Measure.map_map]
  · exact V.map_realCliffordSpinCandidateIdentityChartSourceMeasure_pointMap
  · exact
      (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℝ).measurable
  · exact continuous_subtype_val.measurable

theorem restrict_padicCliffordSpinCandidateChartGluedMeasure_identitySource_atPrime
    (p : ℕ) [Fact (Nat.Prime p)] :
    (V.padicCliffordSpinCandidateChartGluedMeasure p).restrict
        (V.padicCliffordSpinCandidateIdentityChart p).source =
      Measure.map Subtype.val
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
  let e := V.padicCliffordSpinCandidateIdentityChart p
  have hrestrict :=
    V.restrict_padicCliffordSpinCandidateChartGluedMeasure_source p 1
  have hleft :=
    V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure_left p 1
  calc
    (V.padicCliffordSpinCandidateChartGluedMeasure p).restrict e.source =
        (V.padicCliffordSpinCandidateChartGluedMeasure p).restrict
          (MeasureTheory.TranslatedHomChart.source e 1) := by
      rw [source_one e]
    _ = Measure.map Subtype.val
        (V.padicCliffordSpinCandidateTranslatedChartSourceMeasure p 1) := hrestrict
    _ = Measure.map Subtype.val
        (Measure.map
          (MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph e 1)
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p)) := by
      rw [hleft]
    _ = Measure.map Subtype.val
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
      rw [Measure.map_map]
      · congr 1
        funext x
        simp [MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph]
      · exact continuous_subtype_val.measurable
      · exact
          (MeasureTheory.TranslatedHomChart.sourceLeftHomeomorph e 1).measurable

theorem map_padicCliffordSpinCandidateChartGluedMeasure_restrict_identitySource_atPrime
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
        ((V.padicCliffordSpinCandidateChartGluedMeasure p).restrict
          (V.padicCliffordSpinCandidateIdentityChart p).source) =
      (V.padicInvariantDifferentialGroupMeasure p).restrict
        (V.padicCliffordSpinCandidateIdentityChart p).target := by
  rw [V.restrict_padicCliffordSpinCandidateChartGluedMeasure_identitySource_atPrime p,
    Measure.map_map]
  · exact V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure_pointMap p
  · exact
      (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).measurable
  · exact continuous_subtype_val.measurable

local instance placewiseFiniteSheetRealCarrierBorelSpace :
    BorelSpace V.RealSpecialOrthogonalGroup := ⟨rfl⟩

local instance placewiseFiniteSheetPadicCarrierBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- At the real place, the glued Spin measure pushes to twice the fixed
differential measure on the actual image. -/
theorem map_realCliffordSpinCandidateChartGluedMeasure_eq_two_smul_imageMeasure :
    Measure.map
        V.realCliffordSpinCandidateToSpecialOrthogonalHom.rangeRestrict
        V.realCliffordSpinCandidateChartGluedMeasure =
      (2 : NNReal) • V.realCliffordSpinCandidateImageDifferentialMeasure := by
  letI : Measure.IsHaarMeasure V.realCliffordSpinCandidateChartGluedMeasure :=
    V.realCliffordSpinCandidateChartGluedMeasure_isHaarMeasure
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  exact
    MeasureTheory.TranslatedHomChart.map_rangeRestrict_eq_two_smul_comap_of_two_sheet_local_chart
      (G := V.RealCliffordSpinCandidateGroup) (H := V.RealSpecialOrthogonalGroup)
      V.realCliffordSpinCandidateToSpecialOrthogonalHom
      V.realCliffordSpinCandidateIdentityChart
      (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℝ)
      V.realCliffordSpinCandidateIdentityChart_coe
      V.one_mem_realCliffordSpinCandidateIdentityChart_source
      V.isOpen_realCliffordSpinCandidateImage
      (V.cliffordSpinCandidateNegOnePoint ℝ)
      (V.cliffordSpinCandidateNegOnePoint_mem_ker ℝ)
      (V.cliffordSpinCandidateNegOnePoint_ne_one ℝ)
      (V.eq_one_or_cliffordSpinCandidateNegOnePoint_of_pointMap_eq_one ℝ)
      V.realCliffordSpinCandidateChartGluedMeasure
      V.realInvariantDifferentialGroupMeasure
      V.map_realCliffordSpinCandidateChartGluedMeasure_restrict_identitySource

set_option backward.isDefEq.respectTransparency false in
/-- At every p-adic place, the glued Spin measure pushes to twice the fixed
differential measure on the actual image. -/
theorem map_padicCliffordSpinCandidateChartGluedMeasure_eq_two_smul_imageMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).rangeRestrict
        (V.padicCliffordSpinCandidateChartGluedMeasure p) =
      (2 : NNReal) • V.padicCliffordSpinCandidateImageDifferentialMeasure p := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordSpinCandidateChartGluedMeasure p) :=
    V.padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure p
  letI : Measure.IsHaarMeasure (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  exact
    MeasureTheory.TranslatedHomChart.map_rangeRestrict_eq_two_smul_comap_of_two_sheet_local_chart
      (G := V.PadicCliffordSpinCandidateGroup p)
      (H := V.specialOrthogonalMatrixGroup ℚ_[p])
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
      (V.padicCliffordSpinCandidateIdentityChart p)
      (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
      (V.padicCliffordSpinCandidateIdentityChart_coe p)
      (V.one_mem_padicCliffordSpinCandidateIdentityChart_source p)
      (V.isOpen_padicCliffordSpinCandidateImage p)
      (V.cliffordSpinCandidateNegOnePoint ℚ_[p])
      (V.cliffordSpinCandidateNegOnePoint_mem_ker ℚ_[p])
      (V.cliffordSpinCandidateNegOnePoint_ne_one ℚ_[p])
      (V.eq_one_or_cliffordSpinCandidateNegOnePoint_of_pointMap_eq_one ℚ_[p])
      (V.padicCliffordSpinCandidateChartGluedMeasure p)
      (V.padicInvariantDifferentialGroupMeasure p)
      (V.map_padicCliffordSpinCandidateChartGluedMeasure_restrict_identitySource_atPrime p)

end RationalQuadraticSpaceMatrix
