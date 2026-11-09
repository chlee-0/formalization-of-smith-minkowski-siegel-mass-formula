import SMSFormula.RationalIdeleDifferentialPositiveWeil
import SMSFormula.AdelicPeriodization

/-!
# Ambient periodization on positive rational idèles

The coefficient-one sign fold already identifies the differential measure on
the positive fundamental domain and its pushforward to ordinary idèle
classes.  This file proves the complementary ambient Weil formula: the folded
domain meets every orbit of the positive rational diagonal exactly once, so
integrating its nonnegative periodization recovers integration over all
positive idèles.

No new domain, section, or normalization coefficient is introduced.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

local instance positivePeriodizationAmbientAction :
    MulAction positiveRationalAdeleUnitsSubgroup
      positiveRationalAdeleUnitsSubgroup :=
  Monoid.toMulAction positiveRationalAdeleUnitsSubgroup

local instance positivePeriodizationDiagonalAction :
    MulAction positiveRationalIdeleDiagonalSubgroup
      positiveRationalAdeleUnitsSubgroup :=
  Subgroup.instMulAction

/-- The positive-idèle class map is injective on the folded positive
fundamental domain. -/
theorem positiveRationalIdeleToIdeleClassHom_injOn_fundamentalDomain :
    Set.InjOn positiveRationalIdeleToIdeleClassHom
      positiveRationalIdeleMeasurableFundamentalDomainSubtype := by
  intro x hx y hy hxy
  change rationalIdeleClassQuotientMap (x : RationalAdeleˣ) =
    rationalIdeleClassQuotientMap (y : RationalAdeleˣ) at hxy
  change (x : RationalAdeleˣ) ∈
    positiveRationalIdeleMeasurableFundamentalDomain at hx
  change (y : RationalAdeleˣ) ∈
    positiveRationalIdeleMeasurableFundamentalDomain at hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · apply Subtype.ext
    exact rationalIdeleClassQuotientMap_injOn_fundamentalDomain
      hx.1 hy.1 hxy
  · rcases hy with ⟨b, hb, hby⟩
    have hyb : rationalIdeleClassQuotientMap (y : RationalAdeleˣ) =
        rationalIdeleClassQuotientMap b := by
      calc
        rationalIdeleClassQuotientMap (y : RationalAdeleˣ) =
            rationalIdeleClassQuotientMap (rationalIdeleNegativeOne * b) :=
          congrArg rationalIdeleClassQuotientMap hby.symm
        _ = rationalIdeleClassQuotientMap b := by
          have hnormalize : rationalIdelePositiveNormalize b =
              rationalIdeleNegativeOne * b := if_neg hb.2
          rw [← hnormalize]
          exact rationalIdeleClassQuotientMap_positiveNormalize b
    have hxb : (x : RationalAdeleˣ) = b :=
      rationalIdeleClassQuotientMap_injOn_fundamentalDomain
        hx.1 hb.1 (hxy.trans hyb)
    exact (hb.2 (by simpa [hxb] using x.2)).elim
  · rcases hx with ⟨a, ha, hax⟩
    have hxa : rationalIdeleClassQuotientMap (x : RationalAdeleˣ) =
        rationalIdeleClassQuotientMap a := by
      calc
        rationalIdeleClassQuotientMap (x : RationalAdeleˣ) =
            rationalIdeleClassQuotientMap (rationalIdeleNegativeOne * a) :=
          congrArg rationalIdeleClassQuotientMap hax.symm
        _ = rationalIdeleClassQuotientMap a := by
          have hnormalize : rationalIdelePositiveNormalize a =
              rationalIdeleNegativeOne * a := if_neg ha.2
          rw [← hnormalize]
          exact rationalIdeleClassQuotientMap_positiveNormalize a
    have hay : a = (y : RationalAdeleˣ) :=
      rationalIdeleClassQuotientMap_injOn_fundamentalDomain
        ha.1 hy.1 (hxa.symm.trans hxy)
    apply (ha.2 ?_).elim
    rw [hay]
    exact y.2
  · rcases hx with ⟨a, ha, hax⟩
    rcases hy with ⟨b, hb, hby⟩
    have hxa : rationalIdeleClassQuotientMap (x : RationalAdeleˣ) =
        rationalIdeleClassQuotientMap a := by
      calc
        rationalIdeleClassQuotientMap (x : RationalAdeleˣ) =
            rationalIdeleClassQuotientMap (rationalIdeleNegativeOne * a) :=
          congrArg rationalIdeleClassQuotientMap hax.symm
        _ = rationalIdeleClassQuotientMap a := by
          have hnormalize : rationalIdelePositiveNormalize a =
              rationalIdeleNegativeOne * a := if_neg ha.2
          rw [← hnormalize]
          exact rationalIdeleClassQuotientMap_positiveNormalize a
    have hyb : rationalIdeleClassQuotientMap (y : RationalAdeleˣ) =
        rationalIdeleClassQuotientMap b := by
      calc
        rationalIdeleClassQuotientMap (y : RationalAdeleˣ) =
            rationalIdeleClassQuotientMap (rationalIdeleNegativeOne * b) :=
          congrArg rationalIdeleClassQuotientMap hby.symm
        _ = rationalIdeleClassQuotientMap b := by
          have hnormalize : rationalIdelePositiveNormalize b =
              rationalIdeleNegativeOne * b := if_neg hb.2
          rw [← hnormalize]
          exact rationalIdeleClassQuotientMap_positiveNormalize b
    have hab : a = b :=
      rationalIdeleClassQuotientMap_injOn_fundamentalDomain
        ha.1 hb.1 (hxa.symm.trans (hxy.trans hyb))
    apply Subtype.ext
    calc
      (x : RationalAdeleˣ) = rationalIdeleNegativeOne * a := hax.symm
      _ = rationalIdeleNegativeOne * b := by rw [hab]
      _ = (y : RationalAdeleˣ) := hby

/-- Every ordinary idèle class has exactly one representative in the folded
positive fundamental domain. -/
theorem existsUnique_mem_positiveRationalIdeleMeasurableFundamentalDomain
    (c : RationalIdeleClassGroup) :
    ∃! a : positiveRationalAdeleUnitsSubgroup,
      a ∈ positiveRationalIdeleMeasurableFundamentalDomainSubtype ∧
        positiveRationalIdeleToIdeleClassHom a = c := by
  obtain ⟨x, ⟨hx, hxc⟩, _hxunique⟩ :=
    existsUnique_mem_rationalIdeleMeasurableFundamentalDomain c
  let a : positiveRationalAdeleUnitsSubgroup :=
    ⟨rationalIdelePositiveNormalize x, rationalIdelePositiveNormalize_mem x⟩
  have ha : a ∈ positiveRationalIdeleMeasurableFundamentalDomainSubtype := by
    change rationalIdelePositiveNormalize x ∈
      positiveRationalIdeleMeasurableFundamentalDomain
    by_cases hpos : x ∈ positiveRationalAdeleUnitsSubgroup
    · left
      simpa [rationalIdelePositiveNormalize, hpos] using
        (show x ∈ rationalIdeleMeasurableFundamentalDomain ∩
          (positiveRationalAdeleUnitsSubgroup : Set RationalAdeleˣ) from
          ⟨hx, hpos⟩)
    · right
      refine ⟨x, ⟨hx, hpos⟩, ?_⟩
      simp [rationalIdelePositiveNormalize, hpos]
  have hac : positiveRationalIdeleToIdeleClassHom a = c := by
    change rationalIdeleClassQuotientMap (rationalIdelePositiveNormalize x) = c
    rw [rationalIdeleClassQuotientMap_positiveNormalize, hxc]
  refine ⟨a, ⟨ha, hac⟩, ?_⟩
  intro b hb
  exact positiveRationalIdeleToIdeleClassHom_injOn_fundamentalDomain
    hb.1 ha (hb.2.trans hac.symm)

/-- Every positive idèle has exactly one positive-rational-diagonal translate
in the folded domain. -/
theorem existsUnique_positiveRationalIdeleDiagonal_mul_mem_fundamentalDomain
    (x : positiveRationalAdeleUnitsSubgroup) :
    ∃! gamma : positiveRationalIdeleDiagonalSubgroup,
      (gamma : positiveRationalAdeleUnitsSubgroup) * x ∈
        positiveRationalIdeleMeasurableFundamentalDomainSubtype := by
  obtain ⟨a, ⟨ha, hclass⟩, _haunique⟩ :=
    existsUnique_mem_positiveRationalIdeleMeasurableFundamentalDomain
      (positiveRationalIdeleToIdeleClassHom x)
  let delta : positiveRationalAdeleUnitsSubgroup := a * x⁻¹
  have hdeltaKer : delta ∈ positiveRationalIdeleToIdeleClassHom.ker := by
    change positiveRationalIdeleToIdeleClassHom (a * x⁻¹) = 1
    rw [map_mul, map_inv, hclass, mul_inv_cancel]
  have hdelta : delta ∈ positiveRationalIdeleDiagonalSubgroup := by
    rw [range_positiveRationalUnitFullAdelicDiagonalHom_eq_ker]
    exact hdeltaKer
  let gamma : positiveRationalIdeleDiagonalSubgroup := ⟨delta, hdelta⟩
  have hgamma : (gamma : positiveRationalAdeleUnitsSubgroup) * x ∈
      positiveRationalIdeleMeasurableFundamentalDomainSubtype := by
    simpa [gamma, delta, mul_assoc] using ha
  refine ⟨gamma, hgamma, ?_⟩
  intro epsilon hepsilon
  have hepsilonKer : (epsilon : positiveRationalAdeleUnitsSubgroup) ∈
      positiveRationalIdeleToIdeleClassHom.ker := by
    rw [← range_positiveRationalUnitFullAdelicDiagonalHom_eq_ker]
    exact epsilon.2
  have hgammaKer : (gamma : positiveRationalAdeleUnitsSubgroup) ∈
      positiveRationalIdeleToIdeleClassHom.ker := by
    rw [← range_positiveRationalUnitFullAdelicDiagonalHom_eq_ker]
    exact gamma.2
  have hproducts :
      (epsilon : positiveRationalAdeleUnitsSubgroup) * x =
        (gamma : positiveRationalAdeleUnitsSubgroup) * x := by
    apply positiveRationalIdeleToIdeleClassHom_injOn_fundamentalDomain
      hepsilon hgamma
    rw [map_mul, map_mul]
    change positiveRationalIdeleToIdeleClassHom
        (epsilon : positiveRationalAdeleUnitsSubgroup) = 1 at hepsilonKer
    change positiveRationalIdeleToIdeleClassHom
        (gamma : positiveRationalAdeleUnitsSubgroup) = 1 at hgammaKer
    rw [hepsilonKer, hgammaKer]
  exact Subtype.ext (mul_right_cancel hproducts)

/-- Differential Haar on the positive open subgroup is left invariant. -/
noncomputable instance
    positiveRationalIdeleDifferentialHaarMeasure_isMulLeftInvariant :
    Measure.IsMulLeftInvariant positiveRationalIdeleDifferentialHaarMeasure := by
  letI : Measure.IsMulLeftInvariant rationalIdeleDifferentialHaarMeasure :=
    rationalIdeleDifferentialHaarMeasure_isHaarMeasure.toIsMulLeftInvariant
  exact subgroup_comap_measure_isMulLeftInvariant_of_subtype_mspace
    positiveRationalAdeleUnitsSubgroup rfl
    measurableSet_positiveRationalAdeleUnitsSubgroup

local instance positiveRationalIdeleDiagonalCountable :
    Countable positiveRationalIdeleDiagonalSubgroup := by
  letI : Countable positiveRationalUnitsSubgroup :=
    Function.Injective.countable
      (f := fun q : positiveRationalUnitsSubgroup => ((q : ℚˣ) : ℚ)) (by
        intro q r hqr
        apply Subtype.ext
        apply Units.ext
        exact hqr)
  exact Countable.of_equiv positiveRationalUnitsSubgroup
    positiveRationalUnitsEquivPositiveRationalIdeleDiagonal

/-- The folded positive domain is a genuine fundamental domain for the
positive rational diagonal at the differential Haar normalization. -/
theorem positiveRationalIdeleDifferentialHaar_isFundamentalDomain :
    IsFundamentalDomain positiveRationalIdeleDiagonalSubgroup
      positiveRationalIdeleMeasurableFundamentalDomainSubtype
      positiveRationalIdeleDifferentialHaarMeasure :=
  IsFundamentalDomain.mk'
    measurableSet_positiveRationalIdeleMeasurableFundamentalDomainSubtype.nullMeasurableSet
    (by
      intro x
      change ∃! gamma : positiveRationalIdeleDiagonalSubgroup,
        (gamma : positiveRationalAdeleUnitsSubgroup) * x ∈
          positiveRationalIdeleMeasurableFundamentalDomainSubtype
      exact existsUnique_positiveRationalIdeleDiagonal_mul_mem_fundamentalDomain x)

/-- Ambient positive-idèle differential Weil identity for every measurable
nonnegative integrand.  In particular, the sign fold contributes no factor
two. -/
theorem lintegral_positiveRationalIdele_tsum_diagonal_eq
    (f : positiveRationalAdeleUnitsSubgroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ a : positiveRationalAdeleUnitsSubgroup,
        ∑' gamma : positiveRationalIdeleDiagonalSubgroup,
          f ((gamma : positiveRationalAdeleUnitsSubgroup) * a)
      ∂(positiveRationalIdeleDifferentialHaarMeasure.restrict
        positiveRationalIdeleMeasurableFundamentalDomainSubtype) =
      ∫⁻ a : positiveRationalAdeleUnitsSubgroup, f a
        ∂positiveRationalIdeleDifferentialHaarMeasure := by
  simpa only [leftPeriodize, leftPreperiodize] using
    (lintegral_restrict_leftPeriodize_eq_lintegral_of_isFundamentalDomain
      positiveRationalIdeleDiagonalSubgroup hf
      positiveRationalIdeleDifferentialHaar_isFundamentalDomain)

end RationalQuadraticSpaceMatrix

end
