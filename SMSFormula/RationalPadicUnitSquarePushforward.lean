import SMSFormula.RationalCliffordSpinCandidatePlacewiseFiniteSheetHaar
import SMSFormula.RationalCliffordGeneralSpinUnitSquareLocalChart
import SMSFormula.RationalPadicIntegralUnitSquareIndex

/-!
# The global p-adic unit-square pushforward

The square map on `ℚ_[p]ˣ` is two-to-one onto its open square subgroup.  Its
pushforward, however, is not always twice ambient Haar restricted to that
subgroup: the scalar is detected by the compact integral units.  Their square
subgroup has index two at odd places and index four at the dyadic place.

This file turns those finite-index mass calculations into the exact global
pushforward coefficients `2` and `4`.  It does not restrict the equality
to one chosen local square sheet.
-/

noncomputable section

open MeasureTheory Topology
open RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace Rat

set_option maxHeartbeats 1600000

noncomputable local instance padicUnitSquarePushforwardMeasurableSpace
    (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance padicUnitSquarePushforwardBorelSpace
    (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance padicUnitSquarePushforwardSecondCountable
    (p : ℕ) [Fact p.Prime] : SecondCountableTopology ℚ_[p]ˣ := by
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[p] × ℚ_[p]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem unitSquareMonoidHom_range_eq_square
    (p : ℕ) [Fact p.Prime] :
    (unitSquareMonoidHom ℚ_[p]).range = Subgroup.square ℚ_[p]ˣ := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    rw [Subgroup.mem_square]
    exact ⟨x, by simpa [unitSquareMonoidHom, pow_two] using hx.symm⟩
  · rw [Subgroup.mem_square]
    rintro ⟨x, hx⟩
    exact ⟨x, by simpa [unitSquareMonoidHom, pow_two] using hx.symm⟩

@[simp]
theorem unitSquareMonoidHom_neg_one
    (p : ℕ) [Fact p.Prime] :
    unitSquareMonoidHom ℚ_[p] (-1) = 1 := by
  rfl

theorem neg_one_ne_one_padicUnit
    (p : ℕ) [Fact p.Prime] : (-1 : ℚ_[p]ˣ) ≠ 1 := by
  intro h
  have hv := congrArg Units.val h
  norm_num at hv

theorem eq_one_or_neg_one_of_unitSquareMonoidHom_eq_one
    (p : ℕ) [Fact p.Prime] (z : ℚ_[p]ˣ)
    (hz : unitSquareMonoidHom ℚ_[p] z = 1) :
    z = 1 ∨ z = -1 := by
  have hzval : (z : ℚ_[p]) ^ 2 = 1 := congrArg Units.val hz
  rcases sq_eq_one_iff.mp hzval with h | h
  · left
    apply Units.ext
    exact h
  · right
    apply Units.ext
    exact h

/-- The compact integral subgroup inside the actual square-map range. -/
def padicUnitSquareRangeIntegralSubgroup
    (p : ℕ) [Fact p.Prime] :
    Subgroup (unitSquareMonoidHom ℚ_[p]).range :=
  (padicIntegralUnitsSubgroup p).comap
    (unitSquareMonoidHom ℚ_[p]).range.subtype

theorem preimage_padicUnitSquareRangeIntegralSubgroup
    (p : ℕ) [Fact p.Prime] :
    (unitSquareMonoidHom ℚ_[p]).rangeRestrict ⁻¹'
        (padicUnitSquareRangeIntegralSubgroup p :
          Set (unitSquareMonoidHom ℚ_[p]).range) =
      (padicIntegralUnitsSubgroup p : Set ℚ_[p]ˣ) := by
  ext z
  change z ^ 2 ∈ padicIntegralUnitsSubgroup p ↔
    z ∈ padicIntegralUnitsSubgroup p
  constructor
  · exact mem_padicIntegralUnitsSubgroup_of_sq_mem p z
  · intro hz
    exact (padicIntegralUnitsSubgroup p).pow_mem hz 2

theorem image_padicUnitSquareRangeIntegralSubgroup_eq_image_square_integralUnits
    (p : ℕ) [Fact p.Prime] :
    (unitSquareMonoidHom ℚ_[p]).range.subtype ''
        (padicUnitSquareRangeIntegralSubgroup p :
          Set (unitSquareMonoidHom ℚ_[p]).range) =
      (padicIntegralUnitsSubgroup p).subtype ''
        (Subgroup.square (padicIntegralUnitsSubgroup p) :
          Set (padicIntegralUnitsSubgroup p)) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y.1 ∈ padicIntegralUnitsSubgroup p at hy
    rcases y.2 with ⟨x, hx⟩
    change x ^ 2 = y.1 at hx
    have hxmem : x ∈ padicIntegralUnitsSubgroup p :=
      mem_padicIntegralUnitsSubgroup_of_sq_mem p x (by
        rw [hx]
        exact hy)
    refine ⟨⟨x ^ 2, (padicIntegralUnitsSubgroup p).pow_mem hxmem 2⟩, ?_, ?_⟩
    · change (⟨x ^ 2, _⟩ : padicIntegralUnitsSubgroup p) ∈
        Subgroup.square (padicIntegralUnitsSubgroup p)
      rw [Subgroup.mem_square]
      refine ⟨⟨x, hxmem⟩, ?_⟩
      apply Subtype.ext
      simp [pow_two]
    · exact hx
  · rintro ⟨u, hu, rfl⟩
    change u ∈ Subgroup.square (padicIntegralUnitsSubgroup p) at hu
    rw [Subgroup.mem_square] at hu
    rcases hu with ⟨x, hx⟩
    let y : (unitSquareMonoidHom ℚ_[p]).range :=
      ⟨u.1, ⟨x.1, by
        change x.1 ^ 2 = u.1
        have h := congrArg Subtype.val hx
        simpa [pow_two] using h.symm⟩⟩
    refine ⟨y, ?_, rfl⟩
    exact u.2

/-- A compact-unit mass equation determines the full square-map pushforward
scalar on its actual open range. -/
theorem map_unitSquareMonoidHom_rangeRestrict_eq_smul_comap_of_integral_mass
    (p : ℕ) [Fact p.Prime] (q : NNReal)
    (hmass :
      (q : ENNReal) *
          (Measure.comap (padicIntegralUnitsSubgroup p).subtype
            (Measure.haar : Measure ℚ_[p]ˣ))
            (Subgroup.square (padicIntegralUnitsSubgroup p) :
              Set (padicIntegralUnitsSubgroup p)) =
        (Measure.comap (padicIntegralUnitsSubgroup p).subtype
          (Measure.haar : Measure ℚ_[p]ˣ)) Set.univ) :
    Measure.map (unitSquareMonoidHom ℚ_[p]).rangeRestrict
        (Measure.haar : Measure ℚ_[p]ˣ) =
      q • Measure.comap (unitSquareMonoidHom ℚ_[p]).range.subtype
        (Measure.haar : Measure ℚ_[p]ˣ) := by
  let f := unitSquareMonoidHom ℚ_[p]
  let e := unitSquareIdentityChart ℚ_[p]
  let U := padicIntegralUnitsSubgroup p
  let R := f.range
  let K := padicUnitSquareRangeIntegralSubgroup p
  let μ : Measure ℚ_[p]ˣ := Measure.haar
  let μU : Measure U := Measure.comap U.subtype μ
  let μR : Measure R := Measure.comap R.subtype μ
  have hUopen : IsOpen (U : Set ℚ_[p]ˣ) :=
    isOpen_padicIntegralUnitsSubgroup p
  have hRopen : IsOpen (R : Set ℚ_[p]ˣ) := by
    simpa [R, f, unitSquareMonoidHom_range_eq_square p] using
      isOpen_square_padicUnitsSubgroup p
  letI : LocallyCompactSpace U := hUopen.locallyCompactSpace
  letI : LocallyCompactSpace R := hRopen.locallyCompactSpace
  letI : SecondCountableTopology U :=
    TopologicalSpace.Subtype.secondCountableTopology _
  letI : SecondCountableTopology R :=
    TopologicalSpace.Subtype.secondCountableTopology _
  letI : Measure.IsHaarMeasure μU := by
    dsimp [μU, μ]
    exact Measure.IsHaarMeasure.comap
      (μ := (Measure.haar : Measure ℚ_[p]ˣ))
      (f := U.subtype) (mH := ContinuousMul.measurableMul)
      hUopen.isOpenEmbedding_subtypeVal
  letI : Measure.IsHaarMeasure μR := by
    dsimp [μR, μ]
    exact Measure.IsHaarMeasure.comap
      (μ := (Measure.haar : Measure ℚ_[p]ˣ))
      (f := R.subtype) (mH := ContinuousMul.measurableMul)
      hRopen.isOpenEmbedding_subtypeVal
  have hf : Continuous f := by
    exact continuous_pow 2
  have hmapHaar : Measure.IsHaarMeasure (Measure.map f.rangeRestrict μ) := by
    exact
      MeasureTheory.TranslatedHomChart.isHaarMeasure_map_rangeRestrict_of_two_point_local_chart
        f e hf (unitSquareIdentityChart_coe ℚ_[p])
        (one_mem_unitSquareIdentityChart_source ℚ_[p]) hRopen
        (-1 : ℚ_[p]ˣ) (unitSquareMonoidHom_neg_one p)
        (eq_one_or_neg_one_of_unitSquareMonoidHom_eq_one p) μ
  letI : Measure.IsHaarMeasure (Measure.map f.rangeRestrict μ) := hmapHaar
  let c : NNReal := Measure.haarScalarFactor (Measure.map f.rangeRestrict μ) μR
  have hglobal : Measure.map f.rangeRestrict μ = c • μR :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hKopen : IsOpen (K : Set R) := by
    exact hUopen.preimage continuous_subtype_val
  have hUuniv : μU Set.univ = μ (U : Set ℚ_[p]ˣ) := by
    dsimp [μU]
    calc
      (Measure.comap U.subtype μ) Set.univ =
          μ (U.subtype '' (Set.univ : Set U)) :=
        comap_subtype_coe_apply hUopen.measurableSet μ _
      _ = μ (U : Set ℚ_[p]ˣ) := by congr 1; ext x; simp
  have hKsquare :
      μR (K : Set R) =
        μU (Subgroup.square U : Set U) := by
    calc
      μR (K : Set R) = μ (R.subtype '' (K : Set R)) := by
        dsimp [μR]
        exact comap_subtype_coe_apply hRopen.measurableSet μ _
      _ = μ (U.subtype '' (Subgroup.square U : Set U)) := by
        congr 1
        simpa [R, U, K, f] using
          image_padicUnitSquareRangeIntegralSubgroup_eq_image_square_integralUnits p
      _ = μU (Subgroup.square U : Set U) := by
        dsimp [μU]
        exact (comap_subtype_coe_apply hUopen.measurableSet μ _).symm
  have hsquarePos : μU (Subgroup.square U : Set U) ≠ 0 := by
    apply ne_of_gt
    apply Measure.measure_pos_of_nonempty_interior μU
    rw [(isOpen_square_padicIntegralUnitsSubgroup p).interior_eq]
    exact ⟨1, Subgroup.one_mem _⟩
  have hsquareFinite : μU (Subgroup.square U : Set U) ≠ ∞ := by
    apply ne_of_lt
    calc
      μU (Subgroup.square U : Set U) ≤ μU Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = μ (U : Set ℚ_[p]ˣ) := hUuniv
      _ < ∞ := (isCompact_padicIntegralUnitsSubgroup p).measure_lt_top
  have heval := congrArg (fun m : Measure R => m (K : Set R)) hglobal
  have hpre : f.rangeRestrict ⁻¹' (K : Set R) = (U : Set ℚ_[p]ˣ) := by
    simpa [f, U, K] using preimage_padicUnitSquareRangeIntegralSubgroup p
  change (Measure.map f.rangeRestrict μ) (K : Set R) =
    (c • μR) (K : Set R) at heval
  have hmapEval :
      (Measure.map f.rangeRestrict μ) (K : Set R) =
        μ (f.rangeRestrict ⁻¹' (K : Set R)) :=
    Measure.map_apply (Measurable.subtype_mk hf.measurable)
      hKopen.measurableSet
  rw [hmapEval, hpre, Measure.smul_apply, hKsquare] at heval
  have hmass' :
      (q : ENNReal) * μU (Subgroup.square U : Set U) =
        μ (U : Set ℚ_[p]ˣ) := by
    calc
      (q : ENNReal) * μU (Subgroup.square U : Set U) = μU Set.univ := by
        simpa [μU, U, μ] using hmass
      _ = μ (U : Set ℚ_[p]ˣ) := hUuniv
  have hcENN : (c : ENNReal) = q := by
    apply (ENNReal.mul_right_inj hsquarePos hsquareFinite).mp
    calc
      μU (Subgroup.square U : Set U) * (c : ENNReal) =
          (c : ENNReal) * μU (Subgroup.square U : Set U) := mul_comm _ _
      _ =
          μ (U : Set ℚ_[p]ˣ) := heval.symm
      _ = (q : ENNReal) * μU (Subgroup.square U : Set U) := hmass'.symm
      _ = μU (Subgroup.square U : Set U) * (q : ENNReal) := mul_comm _ _
  have hc : c = q := by exact_mod_cast hcENN
  simpa [f, μR, μ, hc] using hglobal

/-- At every odd p-adic place, the full square-map pushforward has scalar
two against ambient Haar restricted by comap to the square subgroup. -/
theorem map_unitSquareMonoidHom_rangeRestrict_eq_two_smul_comap_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Measure.map (unitSquareMonoidHom ℚ_[p]).rangeRestrict
        (Measure.haar : Measure ℚ_[p]ˣ) =
      (2 : NNReal) •
        Measure.comap (unitSquareMonoidHom ℚ_[p]).range.subtype
          (Measure.haar : Measure ℚ_[p]ˣ) := by
  let U := padicIntegralUnitsSubgroup p
  letI : LocallyCompactSpace U :=
    (isOpen_padicIntegralUnitsSubgroup p).locallyCompactSpace
  letI : Measure.IsHaarMeasure
      (Measure.comap U.subtype (Measure.haar : Measure ℚ_[p]ˣ)) := by
    exact Measure.IsHaarMeasure.comap
      (μ := (Measure.haar : Measure ℚ_[p]ˣ))
      (f := U.subtype) (mH := ContinuousMul.measurableMul)
      (isOpen_padicIntegralUnitsSubgroup p).isOpenEmbedding_subtypeVal
  apply map_unitSquareMonoidHom_rangeRestrict_eq_smul_comap_of_integral_mass
  simpa [U] using
    two_mul_measure_square_padicIntegralUnitsSubgroup_eq_univ p hp
      (Measure.comap U.subtype (Measure.haar : Measure ℚ_[p]ˣ))

/-- At the dyadic place, the full square-map pushforward has scalar four
against ambient Haar restricted by comap to the square subgroup. -/
theorem map_unitSquareMonoidHom_rangeRestrict_two_eq_four_smul_comap :
    Measure.map (unitSquareMonoidHom ℚ_[2]).rangeRestrict
        (Measure.haar : Measure ℚ_[2]ˣ) =
      (4 : NNReal) •
        Measure.comap (unitSquareMonoidHom ℚ_[2]).range.subtype
          (Measure.haar : Measure ℚ_[2]ˣ) := by
  let U := padicIntegralUnitsSubgroup 2
  letI : LocallyCompactSpace U :=
    (isOpen_padicIntegralUnitsSubgroup 2).locallyCompactSpace
  letI : Measure.IsHaarMeasure
      (Measure.comap U.subtype (Measure.haar : Measure ℚ_[2]ˣ)) := by
    exact Measure.IsHaarMeasure.comap
      (μ := (Measure.haar : Measure ℚ_[2]ˣ))
      (f := U.subtype) (mH := ContinuousMul.measurableMul)
      (isOpen_padicIntegralUnitsSubgroup 2).isOpenEmbedding_subtypeVal
  apply map_unitSquareMonoidHom_rangeRestrict_eq_smul_comap_of_integral_mass
  simpa [U] using
    four_mul_measure_square_padicIntegralUnitsSubgroup_two_eq_univ
      (Measure.comap U.subtype (Measure.haar : Measure ℚ_[2]ˣ))

end Rat
