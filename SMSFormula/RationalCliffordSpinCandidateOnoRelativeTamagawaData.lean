import SMSFormula.RationalCliffordSpinCandidateOnoRelativeTamagawaPrecursor
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductConvergence

/-!
# Raw data for Ono's relative Spin--SO comparison

This module states the scalar input for Ono's orthogonal relative formula on
raw invariant-differential data on both sides.  The Spin scalar is the
quotient volume of the completed raw Spin measurable-Weil datum, rather than
an arbitrary `ENNReal`.

The data-level comparison is a proposition: proving it is precisely the
analytic content expected from Ono's theorem after its hypotheses, including
condition (K), are verified.  The candidate and target are proved to be
geometrically connected.  This library has no nonabelian `H¹(Spin)` carrier
or localization maps, does not prove target semisimplicity, and does not
contain a separately named classical Spin carrier.  Simply connectedness is a
separate route toward condition (K) and `tau(Spin) = 1`, not an implicit
hypothesis supplied here.  No substitute for condition (K) and no
`tau(Spin) = 1` statement is assumed here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Raw invariant-differential measurable-Weil data on both sides of the
Spin-to-`SO` cover.  The certificates are fields of the structure, so the
relative proposition cannot compare arbitrarily rescaled ambient and quotient
measures. -/
structure CliffordSpinCandidateRawOnoTamagawaData where
  specialOrthogonalData : SpecialOrthogonalAdelicMeasurableWeilMeasureData V
  specialOrthogonalFiniteScale : ℝ≥0∞
  spinFiniteScale : ℝ≥0
  spinData : V.CliffordSpinCandidateMeasurableWeilMeasureData
  specialOrthogonalRaw :
    V.IsRawInvariantDifferentialMeasurableWeilMeasureDataWithScale
      specialOrthogonalFiniteScale specialOrthogonalData
  spinRaw :
    V.IsRawCliffordSpinCandidateDifferentialMeasurableWeilDataWithScale
      spinFiniteScale spinData

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- The prospective Spin Tamagawa number is the literal total quotient
mass of the certified raw Spin measurable-Weil datum.  This definition names
the intended scalar but does not evaluate it. -/
def spinTamagawaNumberENNReal
    (D : V.CliffordSpinCandidateRawOnoTamagawaData) : ℝ≥0∞ :=
  D.spinData.quotientVolumeENNReal

/-- Ono's specialized relative formula for the actual raw `SO` and Spin
data.  Condition (K) and the classical-group applicability hypotheses are the
still-external prerequisites for proving this proposition. -/
def IsOnoRelativeTamagawaComparison
    (D : V.CliffordSpinCandidateRawOnoTamagawaData) : Prop :=
  V.IsCliffordSpinCandidateOnoRelativeTamagawaComparison
    D.specialOrthogonalData D.spinTamagawaNumberENNReal

/-- For the completed central coefficient, the actual-data comparison is
literally `tau(SO) / tau(Spin) = 2`. -/
theorem isOnoRelativeTamagawaComparison_iff
    (D : V.CliffordSpinCandidateRawOnoTamagawaData) :
    D.IsOnoRelativeTamagawaComparison ↔
      D.specialOrthogonalData.tamagawaNumberENNReal /
          D.spinTamagawaNumberENNReal = 2 := by
  exact V.isCliffordSpinCandidateOnoRelativeTamagawaComparison_iff
    D.specialOrthogonalData D.spinTamagawaNumberENNReal

/-- For actual raw data, positivity and finiteness of the Spin quotient volume
turn Ono's relative formula into `tau(SO) = 2 * tau(Spin)`.  Raw
normalization alone does not assert these two endpoint properties, so they
remain explicit. -/
theorem specialOrthogonalTamagawaNumberENNReal_eq_two_mul_spin
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hspin0 : D.spinTamagawaNumberENNReal ≠ 0)
    (hspinTop : D.spinTamagawaNumberENNReal ≠ ⊤)
    (hrelative : D.IsOnoRelativeTamagawaComparison) :
    D.specialOrthogonalData.tamagawaNumberENNReal =
      2 * D.spinTamagawaNumberENNReal := by
  exact V.tamagawaNumberENNReal_eq_two_mul_of_onoRelativeComparison
    D.specialOrthogonalData D.spinTamagawaNumberENNReal
    hspin0 hspinTop hrelative

/-- The exact final orthogonal specialization: Ono's comparison for the
actual raw data and the independent evaluation of the raw Spin quotient as
one imply that the raw `SO` datum has Tamagawa number two. -/
theorem specialOrthogonalTamagawaNumberENNReal_eq_two_of_spin_eq_one
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hrelative : D.IsOnoRelativeTamagawaComparison)
    (hspin : D.spinTamagawaNumberENNReal = 1) :
    D.specialOrthogonalData.tamagawaNumberENNReal = 2 := by
  exact V.specialOrthogonalTamagawaNumberENNReal_eq_two_of_onoRelativeComparison
    D.specialOrthogonalData
      D.specialOrthogonalRaw.toIsRawInvariantDifferentialMeasurableWeilMeasureData
      D.spinTamagawaNumberENNReal hrelative hspin

end CliffordSpinCandidateRawOnoTamagawaData

/-- In rank at least three, the completed Euler products construct
actual raw invariant-differential `SO` and Spin measurable-Weil data to which
Ono's relative proposition applies.  No relative comparison is claimed by
this existence theorem. -/
theorem nonempty_cliffordSpinCandidateRawOnoTamagawaData
    (L : PositiveDefiniteIntegralLattice (r + 3))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    Nonempty
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData := by
  obtain ⟨P, hPpos, hP⟩ :=
    L.exists_pos_massLocalInverseProductTendsTo
      (by omega)
  obtain ⟨finiteScale, CSpin⟩ :=
    exists_cliffordSpinCandidateRawDifferentialVolumeProductCertificate_of_massLocalInverseProductTendsTo
      (r := r + 1) L hPpos hP
  let DSO :=
    L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData
      inst hPpos
  let DSpin :=
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
      finiteScale
  exact ⟨
    { specialOrthogonalData := DSO
      specialOrthogonalFiniteScale :=
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P
      spinFiniteScale := finiteScale
      spinData := DSpin
      specialOrthogonalRaw :=
        L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasurableWeilMeasureData_isRawInvariantDifferentialWithScale
          inst hPpos hP
      spinRaw :=
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_isRawWithScale
          finiteScale CSpin }⟩

end RationalQuadraticSpaceMatrix
