import SMSFormula.RationalCliffordGeneralSpinHorizontalIntegralTwoSheetMass
import SMSFormula.RationalPadicIntegralUnitSquareIndex
import SMSFormula.QuadraticPadicCayleyStabilizerGlobal
import SMSFormula.RationalSpecialOrthogonalIntegralLocalFactorNormalization
import SMSFormula.RationalCliffordGeneralSpinPlacewiseHorizontalUnimodular
import SMSFormula.RationalCliffordGeneralSpinLatticeFiniteAdelicSOSurjectivity

/-! The GSpin central factor at an odd horizontal good place. For
the horizontal p-adic `GSpin` Haar, with integral lifts of integral `SO`
points (the integral Cartan–Dieudonné lift at odd unimodular places),

`v^G_{V,p} = Haar(ℤ_p^×) · vol_SO(SO_int)`,

where `Haar` is the multiplicative Haar of the product measure and `vol_SO`
the invariant differential `SO` measure, i.e. `v^G_{V,p}` is the
height-one integral `SO` volume times the common central mass `Haar(ℤ_p^×)`.
The two sheets (factor 2) and the index-two unit square class (factor 1/2)
cancel: over each integral `g` the slice of the central-fiber image is the
translate `ν(y)·(ℤ_p^× ∩ squares)` for an integral lift `y` of `g`. The common
factor `Haar(ℤ_p^×)` is independent of `V`, so it cancels in `v^G_V / v^G_W`.
No section, sheet or square-class representative enters the statement. -/
noncomputable section
open MeasureTheory Set PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance centralFactorPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance centralFactorDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

noncomputable local instance centralFactorPadicUnitMeasurableSpace (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance centralFactorPadicUnitBorelSpace (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance centralFactorPadicSOMeasurableSpace (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance centralFactorPadicSOBorelSpace (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

/-- The integral units meeting the squares form the square subgroup of the
integral units. -/
theorem padicIntegralUnits_inf_square_subgroupOf (p : ℕ) [Fact p.Prime] :
    (padicIntegralUnitsSubgroup p ⊓ Subgroup.square ℚ_[p]ˣ).subgroupOf (padicIntegralUnitsSubgroup p) =
      Subgroup.square (padicIntegralUnitsSubgroup p) := by
  ext u
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_square, Subgroup.mem_square]
  constructor
  · rintro ⟨-, z, hz⟩
    have hzmem : z ∈ padicIntegralUnitsSubgroup p :=
      Rat.mem_padicIntegralUnitsSubgroup_of_sq_mem p z (by rw [pow_two, ← hz]; exact u.2)
    exact ⟨⟨z, hzmem⟩, Subtype.ext hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨u.2, z.1, congrArg Subtype.val hz⟩

/-- Half square class: at an odd prime the multiplicative Haar of
the integral units is twice that of the integral unit squares. -/
theorem haar_padicIntegralUnits_eq_two_mul (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (Measure.haar : Measure ℚ_[p]ˣ) (padicIntegralUnitsSubgroup p : Set ℚ_[p]ˣ) =
      2 * (Measure.haar : Measure ℚ_[p]ˣ)
        ((padicIntegralUnitsSubgroup p ⊓ Subgroup.square ℚ_[p]ˣ : Subgroup ℚ_[p]ˣ) : Set ℚ_[p]ˣ) := by
  have hrel : (padicIntegralUnitsSubgroup p ⊓ Subgroup.square ℚ_[p]ˣ).relIndex
      (padicIntegralUnitsSubgroup p) = 2 := by
    rw [Subgroup.relIndex, padicIntegralUnits_inf_square_subgroupOf,
      Rat.index_square_padicIntegralUnitsSubgroup_eq_two_of_ne_two p hp]
  have hmeas : MeasurableSet ((padicIntegralUnitsSubgroup p ⊓ Subgroup.square ℚ_[p]ˣ :
      Subgroup ℚ_[p]ˣ) : Set ℚ_[p]ˣ) :=
    ((isOpen_padicIntegralUnitsSubgroup p).inter (Rat.isOpen_square_padicUnitsSubgroup p)).measurableSet
  have h := MeasureTheory.measure_subgroup_eq_relIndex_mul (Measure.haar : Measure ℚ_[p]ˣ)
    (K := padicIntegralUnitsSubgroup p) inf_le_left (by rw [hrel]; norm_num) hmeas
  rw [hrel] at h
  exact_mod_cast h

/-- The common central mass `Haar(ℤ_p^×)` of the multiplicative Haar. -/
def padicIntegralUnitsHaarMass (p : ℕ) [Fact p.Prime] : ℝ≥0∞ :=
  (Measure.haar : Measure ℚ_[p]ˣ) (padicIntegralUnitsSubgroup p : Set ℚ_[p]ˣ)

set_option backward.isDefEq.respectTransparency false in
/-- Central factor: at an odd horizontal good place with integral lifts,
`v^G_{V,p} = Haar(ℤ_p^×) · vol_SO(SO_int)`. -/
theorem padicCliffordGeneralSpinHorizontalIntegralVolume_eq_haar_mul
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hp2 : (Rat.HeightOneSpectrum.primesEquiv v.1).1 ≠ 2)
    (hlift : ∀ g : V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      g ∈ V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 →
      ∃ y : V.CliffordGeneralSpinIntrinsicPoint ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
        V.PadicCliffordGeneralSpinIsIntegral (Rat.HeightOneSpectrum.primesEquiv v.1).1 y ∧
          CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _ y = g) :
    V.padicCliffordGeneralSpinHorizontalIntegralVolume v.1 =
      padicIntegralUnitsHaarMass (Rat.HeightOneSpectrum.primesEquiv v.1).1 *
        V.padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v.1).1
          (V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 :
            Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])) := by
  rw [padicIntegralUnitsHaarMass]
  haveI := padicCayleySpecialOrthogonalDifferentialMeasure_isHaarMeasure
    (Rat.HeightOneSpectrum.primesEquiv v.1).1 n V.pairingMatrix V.form_symm V.form_det_ne_zero
  haveI : SigmaFinite (padicCayleySpecialOrthogonalDifferentialMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 n V.pairingMatrix V.form_det_ne_zero) :=
    padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 n V.pairingMatrix V.form_symm V.form_det_ne_zero
  have hUo := isOpen_padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1
  have hGo := V.isOpen_padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1
  have hRo := V.isOpen_padicCliffordGeneralSpinCentralFiberImage (Rat.HeightOneSpectrum.primesEquiv v.1).1
  rw [MonoidHom.coe_range] at hRo
  have hA : MeasurableSet
      (((padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 : Set _) ×ˢ
          (V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 :
            Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) ∩
        Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])) :=
    ((hUo.prod hGo).inter hRo).measurableSet
  set Q : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ :=
    ((padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 ⊓
      Subgroup.square ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ :
        Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ) :
      Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ) with hQ
  -- the slices
  have hslice : ∀ g : V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      (Measure.haar : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
        ((fun t ↦ (t, g)) ⁻¹'
          (((padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 : Set _) ×ˢ
            (V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 :
              Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) ∩
          Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) =
      (V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 :
          Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])).indicator
        (fun _ ↦ (Measure.haar : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ) Q) g := by
    intro g
    by_cases hg : g ∈ V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1
    · rw [Set.indicator_of_mem hg]
      obtain ⟨y, hy, hyg⟩ := hlift g hg
      have hy0 : y.similitude ∈ padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 :=
        hy.2.2.1
      have hsl : (fun t ↦ (t, g)) ⁻¹'
          (((padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 : Set _) ×ˢ
            (V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v.1).1 :
              Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) ∩
          Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])) =
          (fun t ↦ y.similitude⁻¹ * t) ⁻¹' Q := by
        ext t
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, SetLike.mem_coe, Set.mem_range,
          hQ, Subgroup.mem_inf, Subgroup.mem_square]
        constructor
        · rintro ⟨⟨ht, -⟩, x, hx⟩
          have hxν : x.similitude = t := congrArg Prod.fst hx
          have hxπ : CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _ x = g :=
            congrArg Prod.snd hx
          have hker : x * y⁻¹ ∈
              (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _).ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hxπ, hyg, mul_inv_cancel]
          rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom]
            at hker
          obtain ⟨a, ha⟩ := hker
          have hxa : x = CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ a * y := by
            rw [ha, inv_mul_cancel_right]
          have htt : t = a ^ 2 * y.similitude := by
            rw [← hxν, hxa, CliffordGeneralSpinIntrinsicPoint.mul_similitude]; rfl
          refine ⟨(padicIntegralUnitsSubgroup _).mul_mem
            ((padicIntegralUnitsSubgroup _).inv_mem hy0) ht, a, ?_⟩
          rw [htt, pow_two, mul_comm, mul_inv_cancel_right]
        · rintro ⟨hmem, b, hb⟩
          have ht : t = y.similitude * (b * b) := by
            rw [← hb, mul_inv_cancel_left]
          refine ⟨⟨?_, hg⟩, CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b * y, ?_⟩
          · have := (padicIntegralUnitsSubgroup _).mul_mem hy0 hmem
            rwa [mul_inv_cancel_left] at this
          · refine Prod.ext ?_ ?_
            · change (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b * y).similitude = t
              rw [CliffordGeneralSpinIntrinsicPoint.mul_similitude, ht]
              change b ^ 2 * y.similitude = _
              rw [pow_two, mul_comm]
            · change CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _
                (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b * y) = g
              rw [map_mul, hyg]
              have : CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b ∈
                  (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _).ker := by
                rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom]
                exact ⟨b, rfl⟩
              rw [MonoidHom.mem_ker.mp this, one_mul]
      rw [hsl, measure_preimage_mul]
    · rw [Set.indicator_of_notMem hg]
      exact measure_mono_null (fun t ht ↦ (hg ht.1.2).elim) measure_empty
  rw [V.padicCliffordGeneralSpinHorizontalIntegralVolume_eq_two_mul S v hlift,
    padicCliffordGeneralSpinHorizontalDifferentialProductMeasure, padicInvariantDifferentialGroupMeasure,
    Measure.prod_apply_symm hA]
  simp_rw [hslice]
  rw [lintegral_indicator_const hGo.measurableSet, haar_padicIntegralUnits_eq_two_mul _ hp2, ← hQ,
    ← mul_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The integral `SO` subgroup at `p` is the height-one integral local
factor. -/
theorem padicSpecialOrthogonalIntegralSubgroup_eq_heightOne (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.padicSpecialOrthogonalIntegralSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1 :
      Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) =
      (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v : Set (V.HeightOnePadicSpecialOrthogonalGroup v)) := by
  ext g
  change g ∈ V.padicSpecialOrthogonalIntegralSubgroup _ ↔ g ∈ V.heightOnePadicSpecialOrthogonalIntegralSubgroup v
  rw [V.mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic,
    V.mem_padicSpecialOrthogonalIntegralSubgroup_iff]

/-- Central factor in the height-one volumes, for integral lattices at odd
unimodular admissible horizontal good places:
`v^G_{V,p} = Haar(ℤ_p^×) · heightOnePadicSpecialOrthogonalIntegralVolume V v`. -/
theorem padicCliffordGeneralSpinHorizontalIntegralVolume_eq_haar_mul_heightOne {r : ℕ}
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hvAdmissible : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hp2 : (Rat.HeightOneSpectrum.primesEquiv v.1).1 ≠ 2) :
    L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralVolume v.1 =
      padicIntegralUnitsHaarMass (Rat.HeightOneSpectrum.primesEquiv v.1).1 *
        L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume v.1 := by
  have hlift : ∀ g : L.rationalQuadraticSpaceMatrix.specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      g ∈ L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalIntegralSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 →
      ∃ y : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
        L.rationalQuadraticSpaceMatrix.PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 y ∧
          CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
            L.rationalQuadraticSpaceMatrix _ y = g := by
    intro g hg
    have hg' : g ∈ L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSubgroup v.1 := by
      have := congrArg (fun T ↦ g ∈ T)
        (L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalIntegralSubgroup_eq_heightOne v.1)
      simp only at this
      exact this.mp hg
    obtain ⟨x, hx, hxg⟩ := L.exists_integral_padicCliffordGeneralSpin_toSpecialOrthogonal_eq
      ⟨v.1, hvAdmissible⟩ hvOdd
      (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinIntegralStructureAt_of_not_mem_horizontalBadPlaces
        v.1 (fun hv ↦ v.2 (Finset.mem_union_right S hv))) ⟨g, hg'⟩
    exact ⟨x, hx, hxg⟩
  rw [L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralVolume_eq_haar_mul S v hp2
    hlift, heightOnePadicSpecialOrthogonalIntegralVolume,
    L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalIntegralSubgroup_eq_heightOne v.1]

end RationalQuadraticSpaceMatrix
