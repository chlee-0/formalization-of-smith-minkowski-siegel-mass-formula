import SMSFormula.RationalQuadraticIsometryGeneralSpinIntegralSupport

/-!
# Normalized integral-tail transport for rational GSpin presentations

Outside a certified finite presentation support, the block and ambient fixed
integral local subgroups are equivalent place by place.  This file packages
those local maps and their dependent product without selecting a new chart.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

local instance presentationIntegralTailTransportDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance presentationIntegralTailTransportPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

namespace AnisotropicComplementPresentation

set_option maxHeartbeats 1000000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Once a finite set contains both fixed bad sets, the block and ambient
good-place index types are canonically the same. -/
def blockToAmbientHorizontalIntegralPlaceEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralPlace S ≃
      V.CliffordGeneralSpinHorizontalIntegralPlace S where
  toFun v := ⟨v.1, by
    intro hv
    rcases Finset.mem_union.mp hv with hvS | hvbad
    · exact v.2 (Finset.mem_union_left _ hvS)
    · exact v.2 (Finset.mem_union_left _ (hS.2.1 hvbad))⟩
  invFun v := ⟨v.1, by
    intro hv
    rcases Finset.mem_union.mp hv with hvS | hvbad
    · exact v.2 (Finset.mem_union_left _ hvS)
    · exact v.2 (Finset.mem_union_left _ (hS.1 hvbad))⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem blockToAmbientHorizontalIntegralPlaceEquiv_apply_val
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (v : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralPlace S) :
    (P.blockToAmbientHorizontalIntegralPlaceEquiv hx hS v).1 = v.1 :=
  rfl

/-- The local presentation equivalence restricted to the two fixed integral
subgroups at a place outside the certified support. -/
def blockToAmbientPadicHorizontalIntegralSubgroupContinuousMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (v : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralPlace S) :
    (P.blockSpace hx).padicCliffordGeneralSpinHorizontalIntegralSubgroup S v ≃ₜ*
      V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S
        (P.blockToAmbientHorizontalIntegralPlaceEquiv hx hS v) := by
  let v0 : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralPlace ∅ :=
    ⟨v.1, fun hv ↦ v.2 (by
      apply Finset.mem_union.mpr
      exact Or.inr ((Finset.mem_union.mp hv).resolve_left (by simp)))⟩
  let w := P.blockToAmbientHorizontalIntegralPlaceEquiv hx hS v
  let w0 : V.CliffordGeneralSpinHorizontalIntegralPlace ∅ :=
    ⟨w.1, fun hw ↦ w.2 (by
      apply Finset.mem_union.mpr
      exact Or.inr ((Finset.mem_union.mp hw).resolve_left (by simp)))⟩
  let E := P.blockToAmbientGeneralSpinContinuousMulEquiv hx
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
  let e :
      (P.blockSpace hx).padicCliffordGeneralSpinHorizontalIntegralSubgroup S v ≃
        V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S w := {
    toFun g := ⟨E g.1,
      IsHorizontalIntegralTailPresentationSupport.forward_integral
        (P := P) hx hS v0
      (fun hv ↦ v.2 (Finset.mem_union_left _ hv)) g.1 g.2⟩
    invFun g := ⟨E.symm g.1,
      IsHorizontalIntegralTailPresentationSupport.reverse_integral
        (P := P) hx hS w0
      (fun hw ↦ w.2 (Finset.mem_union_left _ hw)) g.1 g.2⟩
    left_inv g := Subtype.ext (E.symm_apply_apply g.1)
    right_inv g := Subtype.ext (E.apply_symm_apply g.1) }
  exact ContinuousMulEquiv.mk'
    { toEquiv := e
      continuous_toFun := Continuous.subtype_mk
        (E.continuous.comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk
        (E.symm.continuous.comp continuous_subtype_val) _ }
    (fun g h ↦ Subtype.ext (E.map_mul g.1 h.1))

/-- The restricted local presentation equivalence preserves the independently
normalized compact Haar probabilities. -/
theorem blockToAmbientPadicHorizontalIntegralSubgroup_measurePreserving
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (v : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralPlace S) :
    MeasurePreserving
      (P.blockToAmbientPadicHorizontalIntegralSubgroupContinuousMulEquiv
        hx hS v)
      ((P.blockSpace hx)
        |>.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v)
      (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S
        (P.blockToAmbientHorizontalIntegralPlaceEquiv hx hS v)) := by
  let w := P.blockToAmbientHorizontalIntegralPlaceEquiv hx hS v
  let e := P.blockToAmbientPadicHorizontalIntegralSubgroupContinuousMulEquiv
    hx hS v
  let μ := (P.blockSpace hx)
    |>.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v
  let ν := V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S w
  letI : CompactSpace
      ((P.blockSpace hx).padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
    isCompact_iff_compactSpace.mp
      ((P.blockSpace hx)
        |>.isCompact_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
  letI : CompactSpace
      (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S w) :=
    isCompact_iff_compactSpace.mp
      (V.isCompact_padicCliffordGeneralSpinHorizontalIntegralSubgroup S w)
  letI : Measure.IsHaarMeasure μ := by
    apply Measure.isHaarMeasure_of_isCompact_nonempty_interior μ Set.univ
    · exact isCompact_univ
    · simp
    · simp
    · simp
  letI : Measure.IsHaarMeasure ν := by
    apply Measure.isHaarMeasure_of_isCompact_nonempty_interior ν Set.univ
    · exact isCompact_univ
    · simp
    · simp
    · simp
  have hmapHaar : Measure.IsHaarMeasure (Measure.map e μ) :=
    e.toMulEquiv.isHaarMeasure_map μ e.continuous e.symm.continuous
  letI : Measure.IsHaarMeasure (Measure.map e μ) := hmapHaar
  letI : IsProbabilityMeasure (Measure.map e μ) :=
    Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  refine ⟨e.measurable, ?_⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure (Measure.map e μ) ν

/-- Reindex the block tail by the canonical equality of good places and then
apply the restricted presentation equivalence in every local fiber. -/
def blockToAmbientHorizontalIntegralTailMeasurableEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralTail S ≃ᵐ
      V.CliffordGeneralSpinHorizontalIntegralTail S :=
  let e := P.blockToAmbientHorizontalIntegralPlaceEquiv hx hS
  let reindex :=
    (MeasurableEquiv.piCongrLeft
      (fun v : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralPlace S ↦
        (P.blockSpace hx)
          |>.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
      e.symm).symm
  let fiber := MeasurableEquiv.piCongrRight fun
      w : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
    (P.blockToAmbientPadicHorizontalIntegralSubgroupContinuousMulEquiv
      hx hS (e.symm w)).toMeasurableEquiv
  reindex.trans fiber

theorem blockToAmbientHorizontalIntegralTailMeasurableEquiv_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (g : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralTail S)
    (w : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    P.blockToAmbientHorizontalIntegralTailMeasurableEquiv hx hS g w =
      P.blockToAmbientPadicHorizontalIntegralSubgroupContinuousMulEquiv
        hx hS ((P.blockToAmbientHorizontalIntegralPlaceEquiv hx hS).symm w)
        (g ((P.blockToAmbientHorizontalIntegralPlaceEquiv hx hS).symm w)) :=
  rfl

/-- The complete cofinite presentation map preserves the normalized
infinite-product integral-tail probability measure. -/
theorem blockToAmbientHorizontalIntegralTail_measurePreserving
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    MeasurePreserving
      (P.blockToAmbientHorizontalIntegralTailMeasurableEquiv hx hS)
      ((P.blockSpace hx)
        |>.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)
      (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S) := by
  let e := P.blockToAmbientHorizontalIntegralPlaceEquiv hx hS
  let μ := fun
      v : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralPlace S ↦
    (P.blockSpace hx)
      |>.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v
  let ν := fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v
  let reindex :=
    (MeasurableEquiv.piCongrLeft
      (fun v : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralPlace S ↦
        (P.blockSpace hx)
          |>.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)
      e.symm).symm
  let fiber := MeasurableEquiv.piCongrRight fun
      w : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
    (P.blockToAmbientPadicHorizontalIntegralSubgroupContinuousMulEquiv
      hx hS (e.symm w)).toMeasurableEquiv
  letI (v : (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure (μ v) :=
    (P.blockSpace hx)
      |>.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability
        S v
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure (ν v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability S v
  have hReindexBack : MeasurePreserving reindex.symm
      (Measure.infinitePi fun w : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
        μ (e.symm w))
      (Measure.infinitePi μ) := by
    refine ⟨reindex.symm.measurable, ?_⟩
    exact Measure.infinitePi_map_piCongrLeft (μ := μ) e.symm
  have hReindex : MeasurePreserving reindex
      (Measure.infinitePi μ)
      (Measure.infinitePi fun w : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
        μ (e.symm w)) :=
    MeasurePreserving.symm reindex.symm hReindexBack
  have hFiber : MeasurePreserving fiber
      (Measure.infinitePi fun w : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
        μ (e.symm w))
      (Measure.infinitePi ν) := by
    refine ⟨fiber.measurable, ?_⟩
    change Measure.map
        (fun g w ↦
          P.blockToAmbientPadicHorizontalIntegralSubgroupContinuousMulEquiv
            hx hS (e.symm w) (g w))
        (Measure.infinitePi fun w : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
          μ (e.symm w)) = Measure.infinitePi ν
    rw [Measure.infinitePi_map_pi
      (μ := fun w : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
        μ (e.symm w))
      (f := fun w g ↦
        P.blockToAmbientPadicHorizontalIntegralSubgroupContinuousMulEquiv
          hx hS (e.symm w) g)
      (fun w ↦
        (P.blockToAmbientPadicHorizontalIntegralSubgroupContinuousMulEquiv
          hx hS (e.symm w)).measurable)]
    congr 1
    funext w
    exact (P.blockToAmbientPadicHorizontalIntegralSubgroup_measurePreserving
      hx hS (e.symm w)).map_eq
  simpa only [blockToAmbientHorizontalIntegralTailMeasurableEquiv,
    cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure,
    e, μ, ν, reindex, fiber] using hFiber.comp hReindex

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
