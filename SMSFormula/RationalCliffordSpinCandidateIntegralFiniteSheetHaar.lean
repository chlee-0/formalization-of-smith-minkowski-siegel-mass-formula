import SMSFormula.RationalCliffordSpinCandidateIntegralKernelFiniteSheet

/-!
# The integral two-sheet Haar scalar of the local Spin map

The integral scalar point `-1` completes the restricted local kernel to two
points. This file restricts the established p-adic identity chart to the
compact-open integral Spin subgroup and proves that the preimage of its image
patch is the disjoint union of the identity sheet and its `-1` translate.

Evaluating the Haar comparison on that one positive finite patch gives
`pointMapHaarScalar = 2`. Thus the finite kernel, local chart normalization,
and integral image index remain logically separate: the factor two comes from
the exact two-sheet measure calculation, not kernel cardinality alone.
-/

open MeasureTheory
open Topology
open TopologicalSpace
open scoped ENNReal

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 3000000

local instance integralFiniteSheetPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance integralFiniteSheetSOMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) := borel _

local instance integralFiniteSheetSOBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) := ⟨rfl⟩

def cliffordSpinCandidateAdmissibleIntegralOpen
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Opens (V.HeightOnePadicCliffordSpinCandidateGroup v.1) :=
  ⟨V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
      S v.1,
    V.isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
      S v.1 v.2⟩

noncomputable def padicCliffordSpinCandidateIntegralIdentityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    OpenPartialHomeomorph
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v)
      (V.HeightOnePadicSpecialOrthogonalGroup v.1) :=
  (V.padicCliffordSpinCandidateIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).subtypeRestr
    (show Nonempty (V.cliffordSpinCandidateAdmissibleIntegralOpen S v) from
      ⟨⟨1, Subgroup.one_mem _⟩⟩)

def heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Set (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
      S v).range :=
  {y | (y.1.1 : V.HeightOnePadicSpecialOrthogonalGroup v.1) ∈
    (V.padicCliffordSpinCandidateIntegralIdentityChart S v).target}

theorem measurableSet_heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    MeasurableSet (V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v) := by
  exact (V.padicCliffordSpinCandidateIntegralIdentityChart S v).open_target.measurableSet.preimage
    (continuous_subtype_val.comp continuous_subtype_val).measurable

theorem source_one
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (e : OpenPartialHomeomorph G H) :
    MeasureTheory.TranslatedHomChart.source e 1 = e.source := by
  ext x
  simp [MeasureTheory.TranslatedHomChart.source]

theorem restrict_padicCliffordSpinCandidateChartGluedMeasure_identitySource
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.padicCliffordSpinCandidateChartGluedMeasure
        (Rat.HeightOneSpectrum.primesEquiv v).1).restrict
        (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v).1).source =
      Measure.map Subtype.val
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v).1) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  let e := V.padicCliffordSpinCandidateIdentityChart
    (Rat.HeightOneSpectrum.primesEquiv v).1
  have hrestrict :=
    V.restrict_padicCliffordSpinCandidateChartGluedMeasure_source
      (Rat.HeightOneSpectrum.primesEquiv v).1 1
  have hleft :=
    V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure_left
      (Rat.HeightOneSpectrum.primesEquiv v).1 1
  calc
    (V.padicCliffordSpinCandidateChartGluedMeasure p).restrict e.source =
        (V.padicCliffordSpinCandidateChartGluedMeasure p).restrict
          (MeasureTheory.TranslatedHomChart.source e 1) := by
      rw [source_one e]
    _ = Measure.map Subtype.val
        (V.padicCliffordSpinCandidateTranslatedChartSourceMeasure p 1) :=
      hrestrict
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

theorem map_padicCliffordSpinCandidateChartGluedMeasure_restrict_identitySource
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.map
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
        ((V.padicCliffordSpinCandidateChartGluedMeasure
          (Rat.HeightOneSpectrum.primesEquiv v).1).restrict
          (V.padicCliffordSpinCandidateIdentityChart
            (Rat.HeightOneSpectrum.primesEquiv v).1).source) =
      (V.padicInvariantDifferentialGroupMeasure
        (Rat.HeightOneSpectrum.primesEquiv v).1).restrict
        (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v).1).target := by
  rw [V.restrict_padicCliffordSpinCandidateChartGluedMeasure_identitySource v, Measure.map_map]
  · exact
      V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure_pointMap
        (Rat.HeightOneSpectrum.primesEquiv v).1
  · exact
      (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).measurable
  · exact continuous_subtype_val.measurable

set_option backward.isDefEq.respectTransparency false in
theorem preimage_padicCliffordSpinCandidateIntegralIdentityChart_target_inter_source
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]) ⁻¹'
          (V.padicCliffordSpinCandidateIntegralIdentityChart S v).target ∩
        (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).source =
      (fun x : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor
          S v ↦ x.1) ''
        (V.padicCliffordSpinCandidateIntegralIdentityChart S v).source := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
  let e := V.padicCliffordSpinCandidateIdentityChart p
  let eK := V.padicCliffordSpinCandidateIntegralIdentityChart S v
  let f := V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]
  ext x
  constructor
  · rintro ⟨hxTarget, hxSource⟩
    rw [← eK.image_source_eq_target] at hxTarget
    rcases hxTarget with ⟨k, hkSource, hkx⟩
    have hkAmbient : k.1 ∈ e.source := by
      simpa [eK, padicCliffordSpinCandidateIntegralIdentityChart] using hkSource
    have hfx : e k.1 = e x := by
      have hchart : e k.1 = eK k := rfl
      exact hchart.trans (hkx.trans
        (congrFun (V.padicCliffordSpinCandidateIdentityChart_coe p) x))
    have hkx' : k.1 = x := e.injOn hkAmbient hxSource hfx
    exact ⟨k, hkSource, hkx'⟩
  · rintro ⟨k, hkSource, rfl⟩
    have hkAmbient : k.1 ∈ e.source := by
      simpa [eK, padicCliffordSpinCandidateIntegralIdentityChart] using hkSource
    constructor
    · change f k.1 ∈ eK.target
      have hmap := eK.map_source hkSource
      rw [V.padicCliffordSpinCandidateIdentityChart_coe p]
      exact hmap
    · exact hkAmbient

theorem padicCliffordSpinCandidateIntegralIdentityChart_source_mass_eq_ambient_target_mass
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
        S v (V.padicCliffordSpinCandidateIntegralIdentityChart S v).source =
      V.padicInvariantDifferentialGroupMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1
        (V.padicCliffordSpinCandidateIntegralIdentityChart S v).target := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
  let G := V.HeightOnePadicCliffordSpinCandidateGroup v.1
  let K := V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v
  let H := V.HeightOnePadicSpecialOrthogonalGroup v.1
  let e := V.padicCliffordSpinCandidateIdentityChart p
  let eK := V.padicCliffordSpinCandidateIntegralIdentityChart S v
  let f := V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]
  let μG := V.padicCliffordSpinCandidateChartGluedMeasure p
  let μH := V.padicInvariantDifferentialGroupMeasure p
  have hK : MeasurableSet
      (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
        S v.1 : Set G) :=
    (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
      S v.1 v.2).measurableSet
  have hf : Measurable f :=
    (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).measurable
  have ht : MeasurableSet eK.target := eK.open_target.measurableSet
  have hpre : f ⁻¹' eK.target ∩ e.source =
      (fun x : K ↦ x.1) '' eK.source :=
    V.preimage_padicCliffordSpinCandidateIntegralIdentityChart_target_inter_source S v
  have hmap := congrArg (fun m : Measure H ↦ m eK.target)
    (V.map_padicCliffordSpinCandidateChartGluedMeasure_restrict_identitySource v)
  calc
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
        S v eK.source = μG ((fun x : K ↦ x.1) '' eK.source) := by
      exact comap_subtype_coe_apply hK μG eK.source
    _ = μG (f ⁻¹' eK.target ∩ e.source) := by rw [hpre]
    _ = (Measure.map f (μG.restrict e.source)) eK.target := by
      rw [Measure.map_apply hf ht]
      exact (Measure.restrict_apply (ht.preimage hf)).symm
    _ = (μH.restrict e.target) eK.target := hmap
    _ = μH eK.target := by
      rw [Measure.restrict_apply ht]
      congr 1
      exact Set.inter_eq_left.mpr
        (e.subtypeRestr_target_subset
          (show Nonempty (V.cliffordSpinCandidateAdmissibleIntegralOpen S v) from
            ⟨⟨1, Subgroup.one_mem _⟩⟩))

theorem heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch_ambient_image
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (fun y : V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1 ↦
        (y.1 : V.HeightOnePadicSpecialOrthogonalGroup v.1)) ''
        ((V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
          S v).range.subtype '' V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v) =
      (V.padicCliffordSpinCandidateIntegralIdentityChart S v).target := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
  let eK := V.padicCliffordSpinCandidateIntegralIdentityChart S v
  let f := V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]
  ext y
  constructor
  · rintro ⟨j, ⟨r, hr, rfl⟩, rfl⟩
    exact hr
  · intro hy
    rw [← eK.image_source_eq_target] at hy
    rcases hy with ⟨k, hk, rfl⟩
    let j :=
      V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v k
    let r :
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
          S v).range := ⟨j, ⟨k, rfl⟩⟩
    refine ⟨j, ⟨r, ?_, rfl⟩, ?_⟩
    · change f k.1 ∈ eK.target
      rw [V.padicCliffordSpinCandidateIdentityChart_coe p]
      exact eK.map_source hk
    · change f k.1 = eK k
      rw [V.padicCliffordSpinCandidateIdentityChart_coe p]
      rfl

theorem heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch_mass_eq_ambient_target_mass
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v
        (V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v) =
      V.padicInvariantDifferentialGroupMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1
        (V.padicCliffordSpinCandidateIntegralIdentityChart S v).target := by
  let J := V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1
  let H := V.HeightOnePadicSpecialOrthogonalGroup v.1
  let R :=
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).range
  let μH := V.padicInvariantDifferentialGroupMeasure
    (Rat.HeightOneSpectrum.primesEquiv v.1).1
  have hR : MeasurableSet (R : Set J) :=
    (V.isOpen_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap_range
      S v).measurableSet
  have hJ : MeasurableSet
      (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v.1 : Set H) :=
    (V.isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup v.1).measurableSet
  calc
    V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v
        (V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v) =
      V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1
        (R.subtype '' V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v) := by
      exact comap_subtype_coe_apply hR
        (V.heightOnePadicSpecialOrthogonalIntegralMeasure v.1)
        (V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v)
    _ = μH
        ((fun y : J ↦ (y.1 : H)) ''
          (R.subtype '' V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v)) := by
      exact comap_subtype_coe_apply hJ μH _
    _ = μH (V.padicCliffordSpinCandidateIntegralIdentityChart S v).target := by
      rw [V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch_ambient_image S v]

theorem padicCliffordSpinCandidateIntegralIdentityChart_source_mass_eq_imageTargetPatch_mass
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
        S v (V.padicCliffordSpinCandidateIntegralIdentityChart S v).source =
      V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v
        (V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v) := by
  rw [V.padicCliffordSpinCandidateIntegralIdentityChart_source_mass_eq_ambient_target_mass S v,
    V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch_mass_eq_ambient_target_mass S v]

theorem isOpen_heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    IsOpen (V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v) :=
  (V.padicCliffordSpinCandidateIntegralIdentityChart S v).open_target.preimage
    (continuous_subtype_val.comp continuous_subtype_val)

theorem heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch_nonempty
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v).Nonempty := by
  let eK := V.padicCliffordSpinCandidateIntegralIdentityChart S v
  let fK := V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v
  have hone :
      (1 : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor
        S v) ∈ eK.source := by
    change (1 : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor
      S v) ∈ (V.padicCliffordSpinCandidateIntegralIdentityChart S v).source
    simpa only [padicCliffordSpinCandidateIntegralIdentityChart,
      OpenPartialHomeomorph.subtypeRestr_source] using
      V.one_mem_padicCliffordSpinCandidateIdentityChart_source
        (Rat.HeightOneSpectrum.primesEquiv v.1).1
  let y : fK.range := ⟨fK 1, ⟨1, rfl⟩⟩
  refine ⟨y, ?_⟩
  change
    ((fK 1 : V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :
      V.HeightOnePadicSpecialOrthogonalGroup v.1) ∈ eK.target
  have hmap := eK.map_source hone
  have hcoe :
      ((fK 1 : V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :
          V.HeightOnePadicSpecialOrthogonalGroup v.1) = eK 1 := by
    change
      V.cliffordSpinCandidateGroupToSpecialOrthogonal
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
          (1 : V.HeightOnePadicCliffordSpinCandidateGroup v.1) =
        V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 1
    exact congrFun
      (V.padicCliffordSpinCandidateIdentityChart_coe
        (Rat.HeightOneSpectrum.primesEquiv v.1).1) 1
  rwa [hcoe]

theorem heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch_mass_ne_zero
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v
        (V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v) ≠ 0 := by
  exact ne_of_gt
    ((V.isOpen_heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v).measure_pos
      (V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v)
      (V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch_nonempty S v))

theorem heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch_mass_ne_top
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v
        (V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v) ≠ ∞ := by
  rw [← V.padicCliffordSpinCandidateIntegralIdentityChart_source_mass_eq_imageTargetPatch_mass S v]
  exact ne_of_lt
    (lt_of_le_of_lt (measure_mono (Set.subset_univ _))
      IsFiniteMeasure.measure_univ_lt_top)

end RationalQuadraticSpaceMatrix

namespace MeasureTheory.TranslatedHomChart

set_option linter.unusedSectionVars false

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]

theorem preimage_target_eq_source_union_of_two_point_kernel
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (k : G) (hk : f k = 1)
    (hker : ∀ x : G, f x = 1 → x = 1 ∨ x = k) :
    f ⁻¹' e.target = e.source ∪ source e k := by
  ext x
  constructor
  · intro hx
    rw [← e.image_source_eq_target] at hx
    rcases hx with ⟨u, hu, hux⟩
    have hfu : f u = f x := by
      calc
        f u = e u := congrFun hfe u
        _ = f x := hux
    have hxker : f (x * u⁻¹) = 1 := by
      rw [map_mul, map_inv, hfu]
      simp
    rcases hker (x * u⁻¹) hxker with hone | hneg
    · left
      have hxu : x = u := by
        calc
          x = (x * u⁻¹) * u := by simp
          _ = u := by rw [hone, one_mul]
      rwa [hxu]
    · right
      change k⁻¹ * x ∈ e.source
      have hxu : x = k * u := by
        calc
          x = (x * u⁻¹) * u := by simp
          _ = k * u := by rw [hneg]
      rw [hxu]
      simpa using hu
  · rintro (hx | hx)
    · change f x ∈ e.target
      rw [hfe]
      exact e.map_source hx
    · change k⁻¹ * x ∈ e.source at hx
      have ht : f (k⁻¹ * x) ∈ e.target := by
        rw [hfe]
        exact e.map_source hx
      convert ht using 1
      simp [hk]

theorem disjoint_source_translate_of_kernel_point
    (f : G →* H) (e : OpenPartialHomeomorph G H)
    (hfe : (f : G → H) = e) (k : G) (hk : f k = 1)
    (hkone : k ≠ 1) :
    Disjoint e.source (source e k) := by
  rw [Set.disjoint_left]
  intro x hx hxk
  change k⁻¹ * x ∈ e.source at hxk
  have heq : e (k⁻¹ * x) = e x := by
    rw [← hfe]
    simp [hk]
  have harg : k⁻¹ * x = x := e.injOn hxk hx heq
  have hkinv : k⁻¹ = 1 := by
    have h := congrArg (fun y : G ↦ y * x⁻¹) harg
    simpa [mul_assoc] using h
  exact hkone (inv_eq_one.mp hkinv)

theorem haarScalar_eq_two_of_two_sheet_patch
    [MeasurableMul G]
    (f : G → H) (μ : Measure G) (ν : Measure H) (c : NNReal)
    [Measure.IsMulLeftInvariant μ]
    (k : G) (A : Set H) (B : Set G)
    (hf : AEMeasurable f μ) (hA : MeasurableSet A)
    (htranslate : MeasurableSet ((fun x ↦ k⁻¹ * x) ⁻¹' B))
    (hpre : f ⁻¹' A = B ∪ (fun x ↦ k⁻¹ * x) ⁻¹' B)
    (hdisj : Disjoint B ((fun x ↦ k⁻¹ * x) ⁻¹' B))
    (hmass : μ B = ν A)
    (hpos : ν A ≠ 0) (hfinite : ν A ≠ ∞)
    (hglobal : Measure.map f μ = c • ν) :
    c = 2 := by
  have heval := congrArg (fun m : Measure H ↦ m A) hglobal
  change (Measure.map f μ) A = (c • ν) A at heval
  rw [Measure.map_apply_of_aemeasurable hf hA, hpre,
    measure_union hdisj htranslate,
    measure_preimage_mul μ k⁻¹ B, Measure.smul_apply, hmass] at heval
  have hcancel : ν A * (c : ℝ≥0∞) = ν A * 2 := by
    calc
      ν A * (c : ℝ≥0∞) = (c : ℝ≥0∞) * ν A := mul_comm _ _
      _ = ν A + ν A := heval.symm
      _ = ν A * 2 := by ring
  have hc : (c : ℝ≥0∞) = 2 :=
    (ENNReal.mul_right_inj hpos hfinite).mp hcancel
  exact_mod_cast hc

end MeasureTheory.TranslatedHomChart

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 3000000

local instance integralFiniteSheetPrimeFact'
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance integralFiniteSheetSOMeasurableSpace'
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) := borel _

local instance integralFiniteSheetSOBorelSpace'
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) := ⟨rfl⟩

def finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapToPadic
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v →*
      V.HeightOnePadicSpecialOrthogonalGroup v.1 :=
  (V.cliffordSpinCandidateGroupToSpecialOrthogonal
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).comp
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorInclusion
      S v)

theorem padicCliffordSpinCandidateIntegralIdentityChart_coe
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapToPadic S v :
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v →
          V.HeightOnePadicSpecialOrthogonalGroup v.1) =
      V.padicCliffordSpinCandidateIntegralIdentityChart S v := by
  funext x
  rw [padicCliffordSpinCandidateIntegralIdentityChart]
  change
    V.cliffordSpinCandidateGroupToSpecialOrthogonal
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] x.1 =
      V.padicCliffordSpinCandidateIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 x.1
  exact congrFun
    (V.padicCliffordSpinCandidateIdentityChart_coe
      (Rat.HeightOneSpectrum.primesEquiv v.1).1) x.1

theorem finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapToPadic_negOne
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapToPadic S v
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOnePoint
          S v) = 1 :=
  V.heightOnePadicCliffordSpinCandidateNegOnePoint_mem_ker v.1

theorem eq_one_or_negOne_of_integralPointMapToPadic_eq_one
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (x : V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v)
    (hx : V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapToPadic S v x = 1) :
    x = 1 ∨
      x = V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOnePoint
        S v := by
  rcases
      V.eq_one_or_heightOnePadicCliffordSpinCandidateNegOnePoint_of_pointMap_eq_one
        v.1 x.1 hx with hxone | hxneg
  · exact Or.inl (Subtype.ext hxone)
  · exact Or.inr (Subtype.ext hxneg)

theorem rangePointMap_preimage_integralImageIdentityTargetPatch
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v).rangeRestrict ⁻¹' V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v =
      (V.padicCliffordSpinCandidateIntegralIdentityChart S v).source ∪
        MeasureTheory.TranslatedHomChart.source
          (V.padicCliffordSpinCandidateIntegralIdentityChart S v)
          (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOnePoint
            S v) := by
  have h :=
    MeasureTheory.TranslatedHomChart.preimage_target_eq_source_union_of_two_point_kernel
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapToPadic S v)
      (V.padicCliffordSpinCandidateIntegralIdentityChart S v)
      (V.padicCliffordSpinCandidateIntegralIdentityChart_coe S v)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOnePoint S v)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapToPadic_negOne S v)
      (V.eq_one_or_negOne_of_integralPointMapToPadic_eq_one S v)
  simpa [heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch, finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapToPadic] using h

theorem padicCliffordSpinCandidateIntegralIdentityChart_source_disjoint_negOne_translate
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Disjoint (V.padicCliffordSpinCandidateIntegralIdentityChart S v).source
      (MeasureTheory.TranslatedHomChart.source
        (V.padicCliffordSpinCandidateIntegralIdentityChart S v)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOnePoint
          S v)) := by
  exact MeasureTheory.TranslatedHomChart.disjoint_source_translate_of_kernel_point
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapToPadic S v)
    (V.padicCliffordSpinCandidateIntegralIdentityChart S v)
    (V.padicCliffordSpinCandidateIntegralIdentityChart_coe S v)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOnePoint S v)
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMapToPadic_negOne S v)
    (by
      intro h
      apply V.heightOnePadicCliffordSpinCandidateNegOnePoint_ne_one v.1
      exact congrArg Subtype.val h)

theorem heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar_eq_two
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar S v = 2 := by
  let K :=
    V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactor S v
  let R :=
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap S v).range
  let f :=
    (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
      S v).rangeRestrict
  let μ :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure S v
  let ν := V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v
  let k :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralNegOnePoint S v
  let A := V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v
  let B := (V.padicCliffordSpinCandidateIntegralIdentityChart S v).source
  letI : MeasurableMul K := ContinuousMul.measurableMul
  apply MeasureTheory.TranslatedHomChart.haarScalar_eq_two_of_two_sheet_patch
    f μ ν
    (V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar S v)
    k A B
  · exact (Measurable.subtype_mk
      (V.continuous_finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
        S v).measurable).aemeasurable
  · exact V.measurableSet_heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch S v
  · exact
      (MeasureTheory.TranslatedHomChart.isOpen_source
        (V.padicCliffordSpinCandidateIntegralIdentityChart S v) k).measurableSet
  · exact V.rangePointMap_preimage_integralImageIdentityTargetPatch S v
  · exact V.padicCliffordSpinCandidateIntegralIdentityChart_source_disjoint_negOne_translate S v
  · exact V.padicCliffordSpinCandidateIntegralIdentityChart_source_mass_eq_imageTargetPatch_mass S v
  · exact V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch_mass_ne_zero S v
  · exact V.heightOnePadicCliffordSpinCandidateIntegralImageIdentityTargetPatch_mass_ne_top S v
  · exact
      V.map_finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_eq_haarScalar_smul_imageMeasure
        S v

theorem map_finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_eq_two_smul_imageMeasure
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    Measure.map
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralPointMap
          S v).rangeRestrict
        (V.finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure
          S v) =
      (2 : NNReal) •
        V.heightOnePadicCliffordSpinCandidateIntegralImageMeasure S v := by
  rw [V.map_finiteAdelicCliffordSpinCandidateAdmissibleIntegralLocalFactorMeasure_eq_haarScalar_smul_imageMeasure
    S v, V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar_eq_two S v]

/-- Combining the genuine two-sheet Haar scalar with the finite-index image
comparison gives the exact division-free local volume identity. Computing
the remaining image index is a separate integral spinor-norm problem. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralVolume_index_mul_eq_two_mul_soIntegralVolume
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordSpinCandidateAdmissibleIntegralPlace S) :
    (V.heightOnePadicCliffordSpinCandidateIntegralImageIndex S v : ℝ≥0∞) *
        V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v.1 =
      (2 : ℝ≥0∞) *
        V.heightOnePadicSpecialOrthogonalIntegralVolume v.1 := by
  simpa [V.heightOnePadicCliffordSpinCandidateIntegralPointMapHaarScalar_eq_two
    S v] using
    V.heightOnePadicCliffordSpinCandidateIntegralVolume_index_mul_eq_haarScalar_mul_soIntegralVolume
      S v


end RationalQuadraticSpaceMatrix
