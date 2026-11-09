import SMSFormula.RationalCliffordGeneralSpinHorizontalIntegralSOMarginal
import SMSFormula.RationalCliffordGeneralSpinHorizontalCentralExtensionCylinder
import SMSFormula.RationalIdeleDifferentialExceptionalTailMeasure

/-!
# The normalized good horizontal GSpin factor projects to normalized ideles

At every lattice place where the constructive integral similitude lift is
available, the similitude character sends the normalized compact horizontal
`GSpin` Haar measure to the normalized integral-unit Haar measure.  Taking the
infinite product gives the corresponding exact marginal on the good idelic
tail.

This is only a measure marginal.  It chooses no lift and asserts no product
decomposition of `GSpin`.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalIntegralSimilitudeMarginalPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalIntegralSimilitudeMarginalDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

/-- Similitude on the displayed integral horizontal `GSpin` subgroup, with
codomain the literal p-adic integral-unit subgroup. -/
def padicCliffordGeneralSpinHorizontalIntegralSimilitude
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v →*
      padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 where
  toFun g := ⟨g.1.similitude, g.2.2.2.1⟩
  map_one' := by
    apply Subtype.ext
    change
      RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
        V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] 1 = 1
    exact map_one _
  map_mul' := by
    intro g h
    apply Subtype.ext
    change
      RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
          V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (g.1 * h.1) =
        RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
            V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] g.1 *
          RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
            V ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] h.1
    exact map_mul _ _ _

theorem continuous_padicCliffordGeneralSpinHorizontalIntegralSimilitude
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Continuous (V.padicCliffordGeneralSpinHorizontalIntegralSimilitude S v) := by
  apply Continuous.subtype_mk
  exact
    (V.continuous_cliffordGeneralSpinSimilitudeGroupHom
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).comp
        continuous_subtype_val

private noncomputable instance
    horizontalIntegralSimilitudeMarginalSourceCompactSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    CompactSpace (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  isCompact_iff_compactSpace.mp
    (V.isCompact_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)

private noncomputable instance
    horizontalIntegralSimilitudeMarginalTargetCompactSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    CompactSpace
      (padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  isCompact_iff_compactSpace.mp
    (isCompact_padicIntegralUnitsSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1)

private noncomputable instance
    horizontalIntegralSimilitudeMarginalSourceIsHaar
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p) :=
    V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure p
  letI : MeasurableMul (V.HeightOnePadicCliffordGeneralSpinGroup v.1) :=
    ContinuousMul.measurableMul
  letI : Measure.IsHaarMeasure
      (V.padicCliffordGeneralSpinHorizontalIntegralFactorMeasure S v) := by
    unfold padicCliffordGeneralSpinHorizontalIntegralFactorMeasure
    exact Measure.IsHaarMeasure.comap
      (μ := V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)
      (f := (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v).subtype)
      (mH := ContinuousMul.measurableMul)
      (V.isOpen_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v
        ).isOpenEmbedding_subtypeVal
  unfold padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
  apply Measure.IsHaarMeasure.smul
  · exact ENNReal.inv_ne_zero.mpr
      (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_top v.1)
  · exact ENNReal.inv_ne_top.mpr
      (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_zero S v)

private noncomputable instance
    horizontalIntegralSimilitudeMarginalTargetIsHaar
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsHaarMeasure (rationalPadicIdeleIntegralFactorMeasure v) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  letI : Measure.IsHaarMeasure
      (rationalPadicIdeleDifferentialHaarMeasure v) :=
    rationalPadicIdeleDifferentialHaarMeasure_isHaarMeasure v
  letI : MeasurableMul ℚ_[p]ˣ := ContinuousMul.measurableMul
  unfold rationalPadicIdeleIntegralFactorMeasure
  exact Measure.IsHaarMeasure.comap
    (μ := rationalPadicIdeleDifferentialHaarMeasure v)
    (f := (padicIntegralUnitsSubgroup p).subtype)
    (mH := ContinuousMul.measurableMul)
    (isOpen_padicIntegralUnitsSubgroup p).isOpenEmbedding_subtypeVal

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalIntegralSimilitudeMarginalLatticePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalIntegralSimilitudeMarginalLatticeDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-- At every odd-unimodular admissible horizontal good place, integral
similitude is onto the complete p-adic integral-unit subgroup. -/
theorem padicCliffordGeneralSpinHorizontalIntegralSimilitude_surjective
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hvAdmissible : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    Function.Surjective
      (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralSimilitude
        S v) := by
  intro a
  let w :
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace ∅ :=
    ⟨v.1, hvAdmissible⟩
  obtain ⟨x, hxIntegral, hx⟩ :=
    exists_integral_padicCliffordGeneralSpin_similitude_eq
      L w hvOdd
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinIntegralStructureAt_of_not_mem_horizontalBadPlaces
          v.1 (fun hv ↦ v.2 (Finset.mem_union_right S hv))) a.1 a.2
  refine ⟨⟨x, hxIntegral⟩, ?_⟩
  apply Subtype.ext
  exact hx

/-- The normalized horizontal good `GSpin` factor has exactly the normalized
integral idelic measure as its similitude marginal. -/
theorem map_padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_similitude
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hvAdmissible : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    Measure.map
        (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralSimilitude
          S v)
        (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
          S v) =
      RationalQuadraticSpaceMatrix.rationalPadicIdeleIntegralFactorMeasure v.1 := by
  have h : MeasurePreserving
      (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralSimilitude
        S v)
      (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
        S v)
      (RationalQuadraticSpaceMatrix.rationalPadicIdeleIntegralFactorMeasure v.1) :=
    (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralSimilitude
      S v).measurePreserving
      (μ := L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
        S v)
      (ν := RationalQuadraticSpaceMatrix.rationalPadicIdeleIntegralFactorMeasure v.1)
      (L.rationalQuadraticSpaceMatrix.continuous_padicCliffordGeneralSpinHorizontalIntegralSimilitude
        S v)
      (L.padicCliffordGeneralSpinHorizontalIntegralSimilitude_surjective
        S v hvAdmissible hvOdd)
      (by
        rw [L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_univ,
          RationalQuadraticSpaceMatrix.rationalPadicIdeleIntegralFactorMeasure_univ])
  exact h.map_eq

/-- Componentwise similitude from the normalized horizontal `GSpin` good tail
to the corresponding integral idelic tail. -/
def cliffordGeneralSpinHorizontalIntegralTailSimilitude
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S →
      RationalQuadraticSpaceMatrix.RationalIdeleDifferentialIntegralTail
        (S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) :=
  fun g v ↦
    L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralSimilitude
      S v (g v)

theorem measurable_cliffordGeneralSpinHorizontalIntegralTailSimilitude
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (L.cliffordGeneralSpinHorizontalIntegralTailSimilitude S) := by
  exact measurable_pi_lambda _ fun v ↦
    (L.rationalQuadraticSpaceMatrix.continuous_padicCliffordGeneralSpinHorizontalIntegralSimilitude
      S v).measurable.comp (measurable_pi_apply v)

/-- The normalized horizontal good `GSpin` tail pushes by similitude to the
existing normalized integral idelic tail. -/
theorem map_cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_similitude
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hvAdmissible : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : ∀
      v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S,
      v.1 ∉
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    Measure.map
        (L.cliffordGeneralSpinHorizontalIntegralTailSimilitude S)
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
          S) =
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure
        (S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
  let V := L.rationalQuadraticSpaceMatrix
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability S v
  unfold cliffordGeneralSpinHorizontalIntegralTailSimilitude
    RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
    RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure
  rw [Measure.infinitePi_map_pi
    (μ := fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
      V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v)
    (f := fun v x ↦
      V.padicCliffordGeneralSpinHorizontalIntegralSimilitude S v x)
    (fun v ↦
      (V.continuous_padicCliffordGeneralSpinHorizontalIntegralSimilitude S v).measurable)]
  congr 1
  funext v
  exact L.map_padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_similitude
    S v (hvAdmissible v) (hvOdd v)

/-- For the retained central-extension exceptional set, the required lifting
hypotheses are already built into that set.  Hence its normalized horizontal
`GSpin` tail has the normalized integral idelic tail as its literal similitude
marginal. -/
theorem
    map_cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_similitude_retained
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    Measure.map
        (L.cliffordGeneralSpinHorizontalIntegralTailSimilitude E)
        (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure E) =
      RationalQuadraticSpaceMatrix.rationalIdeleDifferentialNormalizedIntegralTailMeasure B := by
  dsimp only
  exact L.map_cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_similitude
    (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S)
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_admissible
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))
    (L.cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces_good_odd
      (insert RationalQuadraticSpaceMatrix.rationalIdeleDyadicPlace S))

end PositiveDefiniteIntegralLattice
