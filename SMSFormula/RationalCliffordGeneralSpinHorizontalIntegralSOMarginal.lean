import SMSFormula.RationalCliffordGeneralSpinHorizontalExceptionalTailMeasure
import SMSFormula.RationalCliffordGeneralSpinLatticeFiniteAdelicSOSurjectivity
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicDifferentialMeasureRegularity
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The normalized good horizontal GSpin factor projects to normalized SO

The full-adelic horizontal coordinate calculation leaves the normalized good
compact `GSpin` tail unchanged.  This file proves the first global
statement needed by that calculation: at a lattice place where the
integral Cartan--Dieudonne lift is available, projection to `SO` sends the
normalized compact `GSpin` Haar measure to the already fixed normalized
integral differential `SO` measure.

The proof uses the constructive integral lift and uniqueness of probability
Haar on the compact target.  It does not assert a product decomposition of the
central extension, choose a section, or construct an adelic Weil
disintegration.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalIntegralSOMarginalPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalIntegralSOMarginalDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance horizontalIntegralSOMarginalPadicSOMeasurableSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance horizontalIntegralSOMarginalPadicSOBorelSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicSpecialOrthogonalGroup v) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance horizontalIntegralSOMarginalLiteralPadicSOMeasurableSpace
    (p : ℕ) [Fact p.Prime] :
    MeasurableSpace (specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance horizontalIntegralSOMarginalLiteralPadicSOBorelSpace
    (p : ℕ) [Fact p.Prime] :
    BorelSpace (specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 3000000

/-- Projection from the displayed integral horizontal `GSpin` subgroup to the
literal integral `SO` subgroup at the same height-one place. -/
def padicCliffordGeneralSpinHorizontalIntegralToSO
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v →*
      V.HeightOnePadicSpecialOrthogonalIntegralGroup v.1 where
  toFun g := ⟨
    V.padicCliffordGeneralSpinToSpecialOrthogonalHom
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 g.1,
    by
      rw [V.mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic]
      exact g.2.2.2.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' := by
    intro g h
    apply Subtype.ext
    exact map_mul _ _ _

theorem continuous_padicCliffordGeneralSpinHorizontalIntegralToSO
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    Continuous (V.padicCliffordGeneralSpinHorizontalIntegralToSO S v) := by
  apply Continuous.subtype_mk
  exact
    (V.continuous_padicCliffordGeneralSpinToSpecialOrthogonalHom
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).comp continuous_subtype_val

private noncomputable instance
    padicCliffordGeneralSpinHorizontalIntegralSubgroupCompactSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    CompactSpace (V.padicCliffordGeneralSpinHorizontalIntegralSubgroup S v) :=
  isCompact_iff_compactSpace.mp
    (V.isCompact_padicCliffordGeneralSpinHorizontalIntegralSubgroup S v)

private noncomputable instance
    padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isHaar
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
  · exact
    (ENNReal.inv_ne_zero.mpr
      (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_top v.1))
  · exact
    (ENNReal.inv_ne_top.mpr
      (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_zero S v))

set_option backward.isDefEq.respectTransparency false in
private noncomputable instance
    heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isHaar
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Measure.IsHaarMeasure
      (V.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure v) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  letI : BorelSpace (specialFormPreservingMatrixSubgroup
      (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
    V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p
  letI : Measure.IsHaarMeasure (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  letI : MeasurableMul (V.HeightOnePadicSpecialOrthogonalGroup v) :=
    ContinuousMul.measurableMul
  letI : Measure.IsHaarMeasure
      (V.heightOnePadicSpecialOrthogonalIntegralMeasure v) := by
    unfold heightOnePadicSpecialOrthogonalIntegralMeasure
    exact Measure.IsHaarMeasure.comap
      (μ := V.padicInvariantDifferentialGroupMeasure p)
      (f := (V.heightOnePadicSpecialOrthogonalIntegralSubgroup v).subtype)
      (mH := ContinuousMul.measurableMul)
      (V.isOpen_heightOnePadicSpecialOrthogonalIntegralSubgroup v
        ).isOpenEmbedding_subtypeVal
  unfold heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure
  apply Measure.IsHaarMeasure.smul
  · exact
    (ENNReal.inv_ne_zero.mpr
      (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top v))
  · exact
    (ENNReal.inv_ne_top.mpr
      (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero v))

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance horizontalIntegralSOMarginalLatticePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalIntegralSOMarginalLatticeDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance
    horizontalIntegralSOMarginalLatticePadicSOMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

noncomputable local instance
    horizontalIntegralSOMarginalLatticePadicSOBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  L.rationalQuadraticSpaceMatrix.padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (Rat.HeightOneSpectrum.primesEquiv v).1

/-- At every odd-unimodular admissible horizontal good place, integral
`GSpin -> SO` is onto the complete integral `SO` subgroup. -/
theorem padicCliffordGeneralSpinHorizontalIntegralToSO_surjective
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hvAdmissible : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    Function.Surjective
      (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralToSO S v) := by
  intro g
  let w :
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace ∅ :=
    ⟨v.1, hvAdmissible⟩
  obtain ⟨x, hxIntegral, hx⟩ :=
    exists_integral_padicCliffordGeneralSpin_toSpecialOrthogonal_eq
      L w hvOdd
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinIntegralStructureAt_of_not_mem_horizontalBadPlaces
          v.1 (fun hv ↦ v.2 (Finset.mem_union_right S hv))) g
  refine ⟨⟨x, hxIntegral⟩, ?_⟩
  apply Subtype.ext
  exact hx

set_option backward.isDefEq.respectTransparency false in
/-- The normalized horizontal good `GSpin` factor has exactly the fixed
normalized integral differential `SO` measure as its `SO` marginal. -/
theorem map_padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_toSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralPlace S)
    (hvAdmissible : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅)
    (hvOdd : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    Measure.map
        (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralToSO S v)
        (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
          S v) =
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure
        v.1 := by
  letI : CompactSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
    L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralGroupCompactSpace v.1
  letI : BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v.1) :=
    Subtype.borelSpace _
  letI : Measure.IsHaarMeasure
      (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
        S v) :=
    L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isHaar
      S v
  letI : Measure.IsHaarMeasure
      (L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure
        v.1) :=
    L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_isHaar
      v.1
  have h : MeasurePreserving
      (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralToSO S v)
      (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
        S v)
      (L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure
        v.1) :=
    (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralToSO S v
      ).measurePreserving
      (μ := L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure
        S v)
      (ν := L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure
        v.1)
      (L.rationalQuadraticSpaceMatrix.continuous_padicCliffordGeneralSpinHorizontalIntegralToSO
        S v)
      (L.padicCliffordGeneralSpinHorizontalIntegralToSO_surjective
        S v hvAdmissible hvOdd)
      (by
        rw [L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_univ,
          L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalNormalizedIntegralMeasure_univ])
  exact h.map_eq

/-- Componentwise projection of the unchanged normalized horizontal `GSpin`
good tail to the corresponding integral `SO` tail. -/
def cliffordGeneralSpinHorizontalIntegralTailToSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalIntegralTail S →
      L.rationalQuadraticSpaceMatrix.FiniteAdelicSpecialOrthogonalIntegralTail
        (S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) :=
  fun g v ↦
    L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinHorizontalIntegralToSO
      S v (g v)

theorem measurable_cliffordGeneralSpinHorizontalIntegralTailToSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (L.cliffordGeneralSpinHorizontalIntegralTailToSO S) := by
  exact measurable_pi_lambda _ fun v ↦
    (L.rationalQuadraticSpaceMatrix.continuous_padicCliffordGeneralSpinHorizontalIntegralToSO
      S v).measurable.comp (measurable_pi_apply v)

/-- The complete normalized horizontal good tail has the normalized
integral differential `SO` tail as its `SO` marginal.  The hypotheses
state that every good coordinate lies outside the two explicit
lattice lifting bad sets. -/
theorem map_cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure_toSO
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
        (L.cliffordGeneralSpinHorizontalIntegralTailToSO S)
        (L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
          S) =
      L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
        (S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
  let V := L.rationalQuadraticSpaceMatrix
  letI (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
      IsProbabilityMeasure
        (V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v) :=
    V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_isProbability S v
  unfold cliffordGeneralSpinHorizontalIntegralTailToSO
    RationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure
    RationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalNormalizedIntegralTailMeasure
  rw [Measure.infinitePi_map_pi
    (μ := fun v : V.CliffordGeneralSpinHorizontalIntegralPlace S ↦
      V.padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure S v)
    (f := fun v x ↦
      V.padicCliffordGeneralSpinHorizontalIntegralToSO S v x)
    (fun v ↦
      (V.continuous_padicCliffordGeneralSpinHorizontalIntegralToSO S v).measurable)]
  congr 1
  funext v
  exact L.map_padicCliffordGeneralSpinHorizontalNormalizedIntegralFactorMeasure_toSO
    S v (hvAdmissible v) (hvOdd v)

end PositiveDefiniteIntegralLattice
