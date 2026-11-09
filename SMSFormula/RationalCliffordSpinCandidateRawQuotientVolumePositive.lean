import SMSFormula.RationalCliffordSpinCandidateCanonicalRightQuotient

/-!
# Positivity of the raw Spin quotient volume

A countable exact fundamental domain for a nonzero left-invariant measure
cannot have measure zero: its countably many translates cover the group.  The
raw Spin ambient measure is Haar, and its quotient mass is the mass of the
completed exact fundamental domain.  Hence the actual raw Spin quotient
volume is nonzero before any application of Ono's theorem or Kottwitz's
volume-one theorem.
-/

noncomputable section

open MeasureTheory
open Set
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

universe u

/-- A measurable exact fundamental domain for a countable subgroup has
nonzero mass for every Haar measure. -/
theorem haarMeasure_fundamentalDomain_ne_zero
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (Gamma : Subgroup G) [Countable Gamma]
    (mu : Measure G) [Measure.IsHaarMeasure mu]
    {F : Set G}
    (hunique : ∀ x : G, ∃! gamma : Gamma, (gamma : G) * x ∈ F) :
    mu F ≠ 0 := by
  intro hF
  have htranslate : ∀ gamma : Gamma,
      mu ((fun x : G => (gamma : G) * x) ⁻¹' F) = 0 := by
    intro gamma
    rw [measure_preimage_mul]
    exact hF
  have hcover :
      (⋃ gamma : Gamma, (fun x : G => (gamma : G) * x) ⁻¹' F) =
        Set.univ := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      obtain ⟨gamma, hgamma, _⟩ := hunique x
      refine Set.mem_iUnion.mpr ⟨gamma, ?_⟩
      exact hgamma
  have hunivzero : mu (Set.univ : Set G) = 0 := by
    rw [← hcover]
    exact measure_iUnion_null htranslate
  have hunivpos : 0 < mu (Set.univ : Set G) :=
    isOpen_univ.measure_pos mu Set.univ_nonempty
  exact hunivpos.ne' hunivzero

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} {V : RationalQuadraticSpaceMatrix n}

local instance rawSpinQuotientPositiveDiagonalCountable
    (V : RationalQuadraticSpaceMatrix n) :
    Countable V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :=
  V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup_countable

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- The exact Spin fundamental domain has nonzero mass in the actual raw
ambient measure. -/
theorem spin_fundamentalDomain_mass_ne_zero
    (D : V.CliffordSpinCandidateRawOnoTamagawaData) :
    D.spinData.adelicMeasure
        V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain ≠ 0 := by
  letI : Measure.IsHaarMeasure D.spinData.adelicMeasure := by
    rw [D.spinRaw.adelicMeasure_eq]
    exact
      V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_isHaarMeasure
        D.spinFiniteScale D.spinRaw.volumeProductCertificate
  exact
    PositiveDefiniteIntegralLattice.haarMeasure_fundamentalDomain_ne_zero
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
      D.spinData.adelicMeasure
      V.existsUnique_rationalDiagonal_smul_mem_measurableFundamentalDomain

set_option backward.isDefEq.respectTransparency false in
/-- The actual raw Spin quotient volume is nonzero. -/
theorem spinTamagawaNumberENNReal_ne_zero
    (D : V.CliffordSpinCandidateRawOnoTamagawaData) :
    D.spinTamagawaNumberENNReal ≠ 0 := by
  rw [spinTamagawaNumberENNReal,
    CliffordSpinCandidateMeasurableWeilMeasureData.quotientVolumeENNReal_eq,
    D.spinData.quotientMeasure_eq_fundamentalDomain]
  rw [PositiveDefiniteIntegralLattice.leftQuotientFundamentalDomainMeasure_univ_map_mspace
    (Gamma := V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup)
    (μG := D.spinData.adelicMeasure)
    (F := V.fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain) rfl]
  exact D.spin_fundamentalDomain_mass_ne_zero

/-- Ono's actual-data relative equation itself rules out infinite Spin
quotient volume: division by `⊤` in `ENNReal` is zero, whereas the completed
central coefficient is two. -/
theorem spinTamagawaNumberENNReal_ne_top_of_onoRelativeComparison
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hrelative : D.IsOnoRelativeTamagawaComparison) :
    D.spinTamagawaNumberENNReal ≠ ⊤ := by
  intro htop
  have hratio :
      D.specialOrthogonalData.tamagawaNumberENNReal /
          D.spinTamagawaNumberENNReal = 2 :=
    D.isOnoRelativeTamagawaComparison_iff.mp hrelative
  rw [htop] at hratio
  simp at hratio

/-- Ono's actual-data comparison therefore needs only finiteness of the Spin
quotient volume for ENNReal division cancellation; nonzeroness is automatic. -/
theorem specialOrthogonalTamagawaNumberENNReal_eq_two_mul_spin_of_ne_top
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hspinTop : D.spinTamagawaNumberENNReal ≠ ⊤)
    (hrelative : D.IsOnoRelativeTamagawaComparison) :
    D.specialOrthogonalData.tamagawaNumberENNReal =
      2 * D.spinTamagawaNumberENNReal :=
  RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData.specialOrthogonalTamagawaNumberENNReal_eq_two_mul_spin
    V D D.spinTamagawaNumberENNReal_ne_zero hspinTop hrelative

/-- For the actual raw data, Ono's relative equation alone gives the
multiplication formula.  The exact fundamental domain supplies nonzeroness,
and the relative equation supplies finiteness, so no separate `ENNReal`
endpoint assumptions remain. -/
theorem specialOrthogonalTamagawaNumberENNReal_eq_two_mul_spin_of_onoRelativeComparison
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (hrelative : D.IsOnoRelativeTamagawaComparison) :
    D.specialOrthogonalData.tamagawaNumberENNReal =
      2 * D.spinTamagawaNumberENNReal :=
  D.specialOrthogonalTamagawaNumberENNReal_eq_two_mul_spin_of_ne_top
    (D.spinTamagawaNumberENNReal_ne_top_of_onoRelativeComparison hrelative)
    hrelative

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
