import SMSFormula.Applications.Unimodular.GenusMass
import SMSFormula.Applications.Unimodular.DyadicTypeI
import SMSFormula.Applications.Unimodular.LowRankMass
import SMSFormula.Applications.Unimodular.GenusClosure.TypeIModEight
import SMSFormula.Applications.Unimodular.ModEightTransport.NativeTransport

/-!
# Type I identity-lattice ordinary mass endpoints

This file connects the Type I dyadic finite counts in `DyadicTypeI` to
`ordinaryGenusMass` through the existing `GenusMass` assembly layer.  It gives
the concrete rank-three through rank-sixteen sample endpoints and closed
all-rank identity-lattice endpoints for ranks at least three.  These are
ordinary genus masses of the identity lattices; no geometric mass is
defined by the Bernoulli formula.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice
open scoped BigOperators
open UnimodularMass

/-- Rank-three Type I identity-lattice ordinary genus mass, routed through the
native dyadic local-factor computation. -/
theorem identityLattice_three_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 3).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 3 : ℝ) := by
  refine ordinaryGenusMass_oddRank_eq_typeIConstant_of_localFactor
    (r := 1) (by norm_num) (identityLattice 3) (identityLattice_isUnimodular 3) ?_
  rw [identityLattice_three_massLocalFactor_two_eq]
  norm_num [typeIOddRankSign]

/-- Rank-three Type I identity-lattice ordinary genus mass in the rational
mass type. -/
theorem identityLattice_three_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 3).ordinaryGenusMass = typeIConstant 3 := by
  exact Rat.cast_injective identityLattice_three_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-four Type I identity-lattice ordinary genus mass, routed through the
native dyadic local-factor computation. -/
theorem identityLattice_four_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 4).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 4 : ℝ) := by
  refine ordinaryGenusMass_evenRank_evenHalf_eq_typeIConstant_of_localFactor
    (m := 2) (by norm_num) (by decide) (identityLattice 4) (identityLattice_isUnimodular 4) ?_
  rw [identityLattice_four_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (2 - 1 : ℕ) = {1} := by decide
  norm_num [hIcc, typeIEvenRankSign]

/-- Rank-four Type I identity-lattice ordinary genus mass in the rational mass
type. -/
theorem identityLattice_four_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 4).ordinaryGenusMass = typeIConstant 4 := by
  exact Rat.cast_injective identityLattice_four_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-five Type I identity-lattice ordinary genus mass, routed through the
native dyadic local-factor computation. -/
theorem identityLattice_five_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 5).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 5 : ℝ) := by
  refine ordinaryGenusMass_oddRank_eq_typeIConstant_of_localFactor
    (r := 2) (by norm_num) (identityLattice 5) (identityLattice_isUnimodular 5) ?_
  rw [identityLattice_five_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (2 : ℕ) = {1, 2} := by decide
  norm_num [hIcc, typeIOddRankSign]

/-- Rank-five Type I identity-lattice ordinary genus mass in the rational mass
type. -/
theorem identityLattice_five_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 5).ordinaryGenusMass = typeIConstant 5 := by
  exact Rat.cast_injective identityLattice_five_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-six Type I identity-lattice ordinary genus mass, routed through the
native dyadic local-factor computation. -/
theorem identityLattice_six_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 6).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 6 : ℝ) := by
  refine ordinaryGenusMass_evenRank_oddHalf_eq_typeIConstant_of_localFactor
    (k := 1) (by norm_num) (identityLattice 6) (identityLattice_isUnimodular 6) ?_
  rw [identityLattice_six_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (2 * 1 + 1 - 1 : ℕ) = {1, 2} := by decide
  norm_num [hIcc]

/-- Rank-six Type I identity-lattice ordinary genus mass in the rational mass
type. -/
theorem identityLattice_six_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 6).ordinaryGenusMass = typeIConstant 6 := by
  exact Rat.cast_injective identityLattice_six_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-seven Type I identity-lattice ordinary genus mass, routed through the
native dyadic local-factor computation. -/
theorem identityLattice_seven_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 7).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 7 : ℝ) := by
  refine ordinaryGenusMass_oddRank_eq_typeIConstant_of_localFactor
    (r := 3) (by norm_num) (identityLattice 7) (identityLattice_isUnimodular 7) ?_
  rw [identityLattice_seven_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (3 : ℕ) = {1, 2, 3} := by decide
  norm_num [hIcc, typeIOddRankSign]

/-- Rank-seven Type I identity-lattice ordinary genus mass in the rational mass
type. -/
theorem identityLattice_seven_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 7).ordinaryGenusMass = typeIConstant 7 := by
  exact Rat.cast_injective identityLattice_seven_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-eight Type I identity-lattice ordinary genus mass, routed through the
native dyadic local-factor computation. -/
theorem identityLattice_eight_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 8).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 8 : ℝ) := by
  refine ordinaryGenusMass_evenRank_evenHalf_eq_typeIConstant_of_localFactor
    (m := 4) (by norm_num) (by decide) (identityLattice 8) (identityLattice_isUnimodular 8) ?_
  rw [identityLattice_eight_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (4 - 1 : ℕ) = {1, 2, 3} := by decide
  norm_num [hIcc, typeIEvenRankSign]

/-- Rank-eight Type I identity-lattice ordinary genus mass in the rational mass
type. -/
theorem identityLattice_eight_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 8).ordinaryGenusMass = typeIConstant 8 := by
  exact Rat.cast_injective identityLattice_eight_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-nine Type I identity-lattice ordinary genus mass, routed through the
native dyadic local-factor computation. -/
theorem identityLattice_nine_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 9).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 9 : ℝ) := by
  refine ordinaryGenusMass_oddRank_eq_typeIConstant_of_localFactor
    (r := 4) (by norm_num) (identityLattice 9) (identityLattice_isUnimodular 9) ?_
  rw [identityLattice_nine_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (4 : ℕ) = {1, 2, 3, 4} := by decide
  norm_num [hIcc, typeIOddRankSign]

/-- Rank-nine Type I identity-lattice ordinary genus mass in the rational mass
type. -/
theorem identityLattice_nine_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 9).ordinaryGenusMass = typeIConstant 9 := by
  exact Rat.cast_injective identityLattice_nine_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-ten Type I identity-lattice ordinary genus mass, routed through the
native dyadic local-factor computation. -/
theorem identityLattice_ten_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 10).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 10 : ℝ) := by
  refine ordinaryGenusMass_evenRank_oddHalf_eq_typeIConstant_of_localFactor
    (k := 2) (by norm_num) (identityLattice 10) (identityLattice_isUnimodular 10) ?_
  rw [identityLattice_ten_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (2 * 2 + 1 - 1 : ℕ) = {1, 2, 3, 4} := by decide
  norm_num [hIcc]

/-- Rank-ten Type I identity-lattice ordinary genus mass in the rational mass
type. -/
theorem identityLattice_ten_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 10).ordinaryGenusMass = typeIConstant 10 := by
  exact Rat.cast_injective identityLattice_ten_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-eleven Type I identity-lattice ordinary genus mass, routed through the
native dyadic local-factor computation. -/
theorem identityLattice_eleven_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 11).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 11 : ℝ) := by
  refine ordinaryGenusMass_oddRank_eq_typeIConstant_of_localFactor
    (r := 5) (by norm_num) (identityLattice 11) (identityLattice_isUnimodular 11) ?_
  rw [identityLattice_eleven_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (5 : ℕ) = {1, 2, 3, 4, 5} := by decide
  norm_num [hIcc, typeIOddRankSign]

/-- Rank-eleven Type I identity-lattice ordinary genus mass in the rational mass
type. -/
theorem identityLattice_eleven_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 11).ordinaryGenusMass = typeIConstant 11 := by
  exact Rat.cast_injective identityLattice_eleven_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-twelve Type I identity-lattice ordinary genus mass, routed through the
native dyadic local-factor computation. -/
theorem identityLattice_twelve_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 12).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 12 : ℝ) := by
  refine ordinaryGenusMass_evenRank_evenHalf_eq_typeIConstant_of_localFactor
    (m := 6) (by norm_num) (by decide) (identityLattice 12) (identityLattice_isUnimodular 12) ?_
  rw [identityLattice_twelve_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (6 - 1 : ℕ) = {1, 2, 3, 4, 5} := by decide
  norm_num [hIcc, typeIEvenRankSign]

/-- Rank-twelve Type I identity-lattice ordinary genus mass in the rational mass
type. -/
theorem identityLattice_twelve_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 12).ordinaryGenusMass = typeIConstant 12 := by
  exact Rat.cast_injective identityLattice_twelve_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-thirteen Type I identity-lattice ordinary genus mass, routed through
the native dyadic local-factor computation. -/
theorem identityLattice_thirteen_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 13).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 13 : ℝ) := by
  refine ordinaryGenusMass_oddRank_eq_typeIConstant_of_localFactor
    (r := 6) (by norm_num) (identityLattice 13) (identityLattice_isUnimodular 13) ?_
  rw [identityLattice_thirteen_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (6 : ℕ) = {1, 2, 3, 4, 5, 6} := by decide
  norm_num [hIcc, typeIOddRankSign]

/-- Rank-thirteen Type I identity-lattice ordinary genus mass in the rational
mass type. -/
theorem identityLattice_thirteen_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 13).ordinaryGenusMass = typeIConstant 13 := by
  exact Rat.cast_injective identityLattice_thirteen_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-fourteen Type I identity-lattice ordinary genus mass, routed through
the native dyadic local-factor computation. -/
theorem identityLattice_fourteen_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 14).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 14 : ℝ) := by
  refine ordinaryGenusMass_evenRank_oddHalf_eq_typeIConstant_of_localFactor
    (k := 3) (by norm_num) (identityLattice 14) (identityLattice_isUnimodular 14) ?_
  rw [identityLattice_fourteen_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (2 * 3 + 1 - 1 : ℕ) = {1, 2, 3, 4, 5, 6} := by
    decide
  norm_num [hIcc]

/-- Rank-fourteen Type I identity-lattice ordinary genus mass in the rational
mass type. -/
theorem identityLattice_fourteen_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 14).ordinaryGenusMass = typeIConstant 14 := by
  exact Rat.cast_injective identityLattice_fourteen_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-fifteen Type I identity-lattice ordinary genus mass, routed through
the native dyadic local-factor computation. -/
theorem identityLattice_fifteen_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 15).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 15 : ℝ) := by
  refine ordinaryGenusMass_oddRank_eq_typeIConstant_of_localFactor
    (r := 7) (by norm_num) (identityLattice 15) (identityLattice_isUnimodular 15) ?_
  rw [identityLattice_fifteen_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (7 : ℕ) = {1, 2, 3, 4, 5, 6, 7} := by decide
  norm_num [hIcc, typeIOddRankSign]

/-- Rank-fifteen Type I identity-lattice ordinary genus mass in the rational
mass type. -/
theorem identityLattice_fifteen_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 15).ordinaryGenusMass = typeIConstant 15 := by
  exact Rat.cast_injective identityLattice_fifteen_ordinaryGenusMass_real_eq_typeIConstant

/-- Rank-sixteen Type I identity-lattice ordinary genus mass, routed through
the native dyadic local-factor computation. -/
theorem identityLattice_sixteen_ordinaryGenusMass_real_eq_typeIConstant :
    (((identityLattice 16).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant 16 : ℝ) := by
  refine ordinaryGenusMass_evenRank_evenHalf_eq_typeIConstant_of_localFactor
    (m := 8) (by norm_num) (by decide) (identityLattice 16) (identityLattice_isUnimodular 16) ?_
  rw [identityLattice_sixteen_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (8 - 1 : ℕ) = {1, 2, 3, 4, 5, 6, 7} := by decide
  norm_num [hIcc, typeIEvenRankSign]

/-- Rank-sixteen Type I identity-lattice ordinary genus mass in the rational
mass type. -/
theorem identityLattice_sixteen_ordinaryGenusMass_eq_typeIConstant :
    (identityLattice 16).ordinaryGenusMass = typeIConstant 16 := by
  exact Rat.cast_injective identityLattice_sixteen_ordinaryGenusMass_real_eq_typeIConstant

/-- Odd-rank Type I identity-lattice ordinary genus mass, routed through the
closed dyadic local-factor formula. -/
theorem identityLattice_oddRank_ordinaryGenusMass_real_eq_typeIConstant
    (r : ℕ) (hr : 1 ≤ r) :
    (((identityLattice (2 * r + 1)).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant (2 * r + 1) : ℝ) := by
  refine ordinaryGenusMass_oddRank_eq_typeIConstant_of_localFactor
    hr (identityLattice (2 * r + 1)) (identityLattice_isUnimodular (2 * r + 1)) ?_
  exact identityLattice_massLocalFactor_two_oddRank_closed r hr

/-- Odd-rank Type I identity-lattice ordinary genus mass in the rational mass
type. -/
theorem identityLattice_oddRank_ordinaryGenusMass_eq_typeIConstant
    (r : ℕ) (hr : 1 ≤ r) :
    (identityLattice (2 * r + 1)).ordinaryGenusMass = typeIConstant (2 * r + 1) := by
  exact Rat.cast_injective
    (identityLattice_oddRank_ordinaryGenusMass_real_eq_typeIConstant r hr)

/-- Even-rank, odd-half-rank Type I identity-lattice ordinary genus mass, routed
through the closed dyadic local-factor formula. -/
theorem identityLattice_evenRank_oddHalf_ordinaryGenusMass_real_eq_typeIConstant
    (k : ℕ) (hk : k ≠ 0) :
    (((identityLattice (2 * (2 * k + 1))).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant (2 * (2 * k + 1)) : ℝ) := by
  refine ordinaryGenusMass_evenRank_oddHalf_eq_typeIConstant_of_localFactor
    hk (identityLattice (2 * (2 * k + 1)))
      (identityLattice_isUnimodular (2 * (2 * k + 1))) ?_
  exact identityLattice_massLocalFactor_two_evenRank_oddHalf_closed k hk

/-- Even-rank, odd-half-rank Type I identity-lattice ordinary genus mass in the
rational mass type. -/
theorem identityLattice_evenRank_oddHalf_ordinaryGenusMass_eq_typeIConstant
    (k : ℕ) (hk : k ≠ 0) :
    (identityLattice (2 * (2 * k + 1))).ordinaryGenusMass =
      typeIConstant (2 * (2 * k + 1)) := by
  exact Rat.cast_injective
    (identityLattice_evenRank_oddHalf_ordinaryGenusMass_real_eq_typeIConstant k hk)

/-- Even-rank, even-half-rank Type I identity-lattice ordinary genus mass, routed
through the closed dyadic local-factor formula. -/
theorem identityLattice_evenRank_evenHalf_ordinaryGenusMass_real_eq_typeIConstant
    {m : ℕ} (hm_one : 1 < m) (hm_even : Even m) :
    (((identityLattice (2 * m)).ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant (2 * m) : ℝ) := by
  refine ordinaryGenusMass_evenRank_evenHalf_eq_typeIConstant_of_localFactor
    hm_one hm_even (identityLattice (2 * m)) (identityLattice_isUnimodular (2 * m)) ?_
  exact identityLattice_massLocalFactor_two_evenRank_evenHalf_closed hm_one hm_even

/-- Even-rank, even-half-rank Type I identity-lattice ordinary genus mass in the
rational mass type. -/
theorem identityLattice_evenRank_evenHalf_ordinaryGenusMass_eq_typeIConstant
    {m : ℕ} (hm_one : 1 < m) (hm_even : Even m) :
    (identityLattice (2 * m)).ordinaryGenusMass = typeIConstant (2 * m) := by
  exact Rat.cast_injective
    (identityLattice_evenRank_evenHalf_ordinaryGenusMass_real_eq_typeIConstant
      hm_one hm_even)

/-- Type I identity-lattice ordinary genus mass in every rank `n ≥ 3`, routed
through the closed dyadic local-factor formula. -/
theorem identityLattice_ordinaryGenusMass_real_eq_typeIConstant_of_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    (((identityLattice n).ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant n : ℝ) := by
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with h0 | h1 | h2 | h3
  · have hdecomp : n = 2 * (n / 2) := by omega
    have hhalf : 1 < n / 2 := by omega
    have hhalf_even : Even (n / 2) := by
      exact ⟨n / 4, by omega⟩
    rw [hdecomp]
    exact identityLattice_evenRank_evenHalf_ordinaryGenusMass_real_eq_typeIConstant
      hhalf hhalf_even
  · have hdecomp : n = 2 * (n / 2) + 1 := by omega
    have hhalf : 1 ≤ n / 2 := by omega
    rw [hdecomp]
    exact identityLattice_oddRank_ordinaryGenusMass_real_eq_typeIConstant (n / 2) hhalf
  · have hdecomp : n = 2 * (2 * (n / 4) + 1) := by omega
    have hquart : n / 4 ≠ 0 := by omega
    rw [hdecomp]
    exact identityLattice_evenRank_oddHalf_ordinaryGenusMass_real_eq_typeIConstant
      (n / 4) hquart
  · have hdecomp : n = 2 * (n / 2) + 1 := by omega
    have hhalf : 1 ≤ n / 2 := by omega
    rw [hdecomp]
    exact identityLattice_oddRank_ordinaryGenusMass_real_eq_typeIConstant (n / 2) hhalf

/-- Type I identity-lattice ordinary genus mass in every rank `n ≥ 3`, in the
rational mass type. -/
theorem identityLattice_ordinaryGenusMass_eq_typeIConstant_of_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    (identityLattice n).ordinaryGenusMass = typeIConstant n := by
  exact Rat.cast_injective
    (identityLattice_ordinaryGenusMass_real_eq_typeIConstant_of_three_le hn)

/-- Type I identity-genus ordinary mass transported to any supplied same-genus
representative of the identity lattice.  This theorem keeps the same-genus
hypothesis explicit; it is not a classification of all Type I unimodular
lattices. -/
theorem ordinaryGenusMass_real_eq_typeIConstant_of_isSameGenus_identityLattice
    {n : ℕ} (hn : 3 ≤ n) {L : PositiveDefiniteIntegralLattice n}
    (h : L.IsSameGenus (identityLattice n)) :
    (((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant n : ℝ)) := by
  rw [ordinaryGenusMass_eq_of_isSameGenus h]
  exact identityLattice_ordinaryGenusMass_real_eq_typeIConstant_of_three_le hn

/-- Type I identity-genus ordinary mass transported to any supplied same-genus
representative of the identity lattice, in the rational mass type. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_isSameGenus_identityLattice
    {n : ℕ} (hn : 3 ≤ n) {L : PositiveDefiniteIntegralLattice n}
    (h : L.IsSameGenus (identityLattice n)) :
    L.ordinaryGenusMass = typeIConstant n := by
  rw [ordinaryGenusMass_eq_of_isSameGenus h]
  exact identityLattice_ordinaryGenusMass_eq_typeIConstant_of_three_le hn

/-- The closed Type I identity-lattice dyadic local factor transports to any
representative of the identity genus.  This is a local-factor statement, still
under an explicit same-genus hypothesis; it is not a classification theorem. -/
theorem massLocalFactor_two_eq_typeIClosedForm_of_isSameGenus_identityLattice
    {n : ℕ} (hn : 3 ≤ n) {L : PositiveDefiniteIntegralLattice n}
    (h : L.IsSameGenus (identityLattice n)) :
    L.massLocalFactor 2 =
      identityLatticeTypeILocalFactorClosedForm n := by
  rw [massLocalFactor_eq_of_isSameGenus h]
  exact identityLattice_massLocalFactor_two_eq_typeIClosedForm hn

/-- A supplied Type I same-genus classification gives the Type I dyadic
local-factor endpoint for every classified lattice. This keeps the classification
input explicit; no Type I classification is asserted here. -/
theorem massLocalFactor_two_eq_typeIClosedForm_of_typeI_sameGenus_identityLattice_classification
    {n : ℕ} (hn : 3 ≤ n)
    (hclass : ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular → L.HasOddNorm →
      L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hI : L.HasOddNorm) :
    L.massLocalFactor 2 =
      identityLatticeTypeILocalFactorClosedForm n :=
  massLocalFactor_two_eq_typeIClosedForm_of_isSameGenus_identityLattice
    hn (hclass L hU hI)

/-- The Type I dyadic local factor equals its closed form, under the external normalization
hypotheses `pairingDeterminant = 1` and an odd quadratic value, and under an
explicit supplied identity-genus classification. -/
theorem massLocalFactor_two_eq_typeIClosedForm_of_supplied_identity_genus_classification
    {n : ℕ} (hn : 3 ≤ n)
    (hclass : ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = 1 →
      (∃ x : Fin n → ℤ, Odd (L.quadForm x)) → L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    L.massLocalFactor 2 =
      identityLatticeTypeILocalFactorClosedForm n :=
  massLocalFactor_two_eq_typeIClosedForm_of_typeI_sameGenus_identityLattice_classification
    hn (fun L hU hI => hclass L hU hI) L hdet hodd

theorem massLocalFactor_two_eq_identity_of_typeIUnimodular
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hI : L.HasOddNorm) :
    L.massLocalFactor 2 = (identityLattice n).massLocalFactor 2 := by
  obtain ⟨certificate⟩ := UnimodularGenusClosure.normalizes_typeI_unimodular L hU hI
  have hidentity : (identityLattice n).pairingMatrix.map (Int.cast : ℤ → ZMod 8) = 1 := by
    simp
  exact (TypeIIModEightNativeTransport.localFactor_eq_of_gram_certificate
    (identityLattice n) L (identityLattice_isUnimodular n) hU
    (hidentity ▸ certificate)).symm

/-- The Type I dyadic factor from an actual finite mod-eight normalizer,
without a supplied genus classification. -/
theorem massLocalFactor_two_eq_typeIClosedForm
    {n : ℕ} (hn : 3 ≤ n)
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    L.massLocalFactor 2 =
      identityLatticeTypeILocalFactorClosedForm n :=
  (massLocalFactor_two_eq_identity_of_typeIUnimodular L hdet hodd).trans
    (identityLattice_massLocalFactor_two_eq_typeIClosedForm hn)

/-- A supplied Type I same-genus classification gives the real-valued Type I
ordinary mass endpoint for every classified lattice. This keeps the
classification input explicit; no Type I classification is asserted here. -/
theorem ordinaryGenusMass_real_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification
    {n : ℕ} (hn : 3 ≤ n)
    (hclass : ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular → L.HasOddNorm →
      L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hI : L.HasOddNorm) :
    (((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant n : ℝ)) :=
  ordinaryGenusMass_real_eq_typeIConstant_of_isSameGenus_identityLattice hn
    (hclass L hU hI)

/-- A supplied Type I same-genus classification gives the rational Type I
ordinary mass endpoint for every classified lattice. This keeps the
classification input explicit; no Type I classification is asserted here. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification
    {n : ℕ} (hn : 3 ≤ n)
    (hclass : ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular → L.HasOddNorm →
      L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hI : L.HasOddNorm) :
    L.ordinaryGenusMass = typeIConstant n :=
  ordinaryGenusMass_eq_typeIConstant_of_isSameGenus_identityLattice hn
    (hclass L hU hI)

/-- All-rank intrinsic Type I ordinary mass formula under supplied higher-rank
identity-genus classification.  The supplied classification is only used in
ranks at least three; ranks one and two use the closed low-rank endpoints, and
the Type I hypothesis excludes rank zero. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
    {n : ℕ}
    (hclass : 3 ≤ n → ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular →
      L.HasOddNorm → L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hI : L.HasOddNorm) :
    L.ordinaryGenusMass = typeIConstant n := by
  by_cases hn0 : n = 0
  · subst n
    exfalso
    exact not_hasOddNorm_rank_zero L hI
  by_cases hn1 : n = 1
  · subst n
    exact ordinaryGenusMass_eq_typeIConstant_of_rank_one_isUnimodular L hU
  by_cases hn2 : n = 2
  · subst n
    exact ordinaryGenusMass_eq_typeIConstant_of_rank_two_isUnimodular L hU
  have hn3 : 3 ≤ n := by omega
  exact ordinaryGenusMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification
    hn3 (hclass hn3) L hU hI

/-- Real-cast form of the all-rank intrinsic Type I ordinary mass formula under
supplied higher-rank identity-genus classification. -/
theorem ordinaryGenusMass_real_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
    {n : ℕ}
    (hclass : 3 ≤ n → ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular →
      L.HasOddNorm → L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hI : L.HasOddNorm) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant n : ℝ) := by
  exact_mod_cast
    (ordinaryGenusMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
      hclass L hU hI)

/-- Finite genus-sum form of the all-rank intrinsic Type I ordinary mass
formula under supplied higher-rank identity-genus classification. -/
theorem ordinaryGenusMass_literal_sum_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
    {n : ℕ}
    (hclass : 3 ≤ n → ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular →
      L.HasOddNorm → L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hI : L.HasOddNorm) :
    (∑ A : L.genus,
      ((Fintype.card (genusClassRepresentative L A).IsometryGroup : ℚ)⁻¹)) =
        typeIConstant n := by
  change L.ordinaryGenusMass = typeIConstant n
  exact ordinaryGenusMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
    hclass L hU hI

/-- Real-valued finite genus-sum form of the all-rank intrinsic Type I
ordinary mass formula under supplied higher-rank identity-genus classification. -/
theorem ordinaryGenusMass_literal_sum_real_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
    {n : ℕ}
    (hclass : 3 ≤ n → ∀ L : PositiveDefiniteIntegralLattice n, L.IsUnimodular →
      L.HasOddNorm → L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hI : L.HasOddNorm) :
    (((∑ A : L.genus,
      ((Fintype.card (genusClassRepresentative L A).IsometryGroup : ℚ)⁻¹)) : ℚ) : ℝ) =
        (typeIConstant n : ℝ) := by
  exact_mod_cast
    ordinaryGenusMass_literal_sum_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
      hclass L hU hI

/-- The Type I ordinary mass formula under the external normalization
hypotheses `pairingDeterminant = 1` and an odd quadratic value, and under an
explicit supplied identity-genus classification.  It does not assert that
arbitrary Type I unimodular lattices are in the identity genus. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_supplied_identity_genus_classification
    {n : ℕ} (hn : 3 ≤ n)
    (hclass : ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = 1 →
      (∃ x : Fin n → ℤ, Odd (L.quadForm x)) → L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    L.ordinaryGenusMass = typeIConstant n :=
  ordinaryGenusMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification
    hn (fun L hU hI => hclass L hU hI) L hdet hodd

/-- Positive-rank Type I ordinary mass formula.  Ranks one and two use the
closed low-rank endpoints; ranks at least three use the supplied
identity-genus classification input.  This theorem does not assert an
arbitrary higher-rank Type I classification. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_supplied_identity_genus_classification_pos
    {n : ℕ} (hnpos : 0 < n)
    (hclass : 3 ≤ n → ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = 1 →
      (∃ x : Fin n → ℤ, Odd (L.quadForm x)) → L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    L.ordinaryGenusMass = typeIConstant n := by
  by_cases hn1 : n = 1
  · subst n
    exact ordinaryGenusMass_eq_typeIConstant_of_rank_one L hdet hodd
  by_cases hn2 : n = 2
  · subst n
    exact ordinaryGenusMass_eq_typeIConstant_of_rank_two L hdet hodd
  have hn3 : 3 ≤ n := by omega
  exact ordinaryGenusMass_eq_typeIConstant_of_supplied_identity_genus_classification
    hn3 (hclass hn3) L hdet hodd

/-- All-rank Type I ordinary mass formula under supplied higher-rank
identity-genus classification.  The odd-vector hypothesis itself
excludes rank zero; ranks one and two use the closed low-rank endpoints, and
ranks at least three use the supplied classification input. -/
theorem ordinaryGenusMass_eq_typeIConstant_of_supplied_identity_genus_classification_allRank
    {n : ℕ}
    (hclass : 3 ≤ n → ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = 1 →
      (∃ x : Fin n → ℤ, Odd (L.quadForm x)) → L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    L.ordinaryGenusMass = typeIConstant n :=
  ordinaryGenusMass_eq_typeIConstant_of_typeI_sameGenus_identityLattice_classification_allRank
    (fun hn M hU hI => hclass hn M hU hI) L hdet hodd

/-- Real-cast form of the all-rank Type I ordinary mass formula under supplied
higher-rank identity-genus classification. -/
theorem ordinaryGenusMass_real_eq_typeIConstant_of_supplied_identity_genus_classification_allRank
    {n : ℕ}
    (hclass : 3 ≤ n → ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = 1 →
      (∃ x : Fin n → ℤ, Odd (L.quadForm x)) → L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant n : ℝ) := by
  exact_mod_cast
    (ordinaryGenusMass_eq_typeIConstant_of_supplied_identity_genus_classification_allRank
      hclass L hdet hodd)

/-- Finite genus-sum form of the all-rank supplied-classification
Type I ordinary mass formula.  The sum is the defining ordinary mass sum over
`L.genus`; the proof uses the all-rank ordinary-mass theorem. -/
theorem ordinaryGenusMass_literal_sum_eq_typeIConstant_of_supplied_identity_genus_classification_allRank
    {n : ℕ}
    (hclass : 3 ≤ n → ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = 1 →
      (∃ x : Fin n → ℤ, Odd (L.quadForm x)) → L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    (∑ A : L.genus,
      ((Fintype.card (genusClassRepresentative L A).IsometryGroup : ℚ)⁻¹)) =
        typeIConstant n := by
  change L.ordinaryGenusMass = typeIConstant n
  exact ordinaryGenusMass_eq_typeIConstant_of_supplied_identity_genus_classification_allRank
    hclass L hdet hodd

/-- Real-valued finite genus-sum form of the all-rank supplied-classification
Type I ordinary mass formula. -/
theorem ordinaryGenusMass_literal_sum_real_eq_typeIConstant_of_supplied_identity_genus_classification_allRank
    {n : ℕ}
    (hclass : 3 ≤ n → ∀ L : PositiveDefiniteIntegralLattice n, L.pairingDeterminant = 1 →
      (∃ x : Fin n → ℤ, Odd (L.quadForm x)) → L.IsSameGenus (identityLattice n))
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    (((∑ A : L.genus,
      ((Fintype.card (genusClassRepresentative L A).IsometryGroup : ℚ)⁻¹)) : ℚ) : ℝ) =
        (typeIConstant n : ℝ) := by
  exact_mod_cast
    ordinaryGenusMass_literal_sum_eq_typeIConstant_of_supplied_identity_genus_classification_allRank
      hclass L hdet hodd

theorem ordinaryGenusMass_real_eq_typeIConstant_of_typeIUnimodular_of_three_le
    {n : ℕ} (hn : 3 ≤ n) (L : PositiveDefiniteIntegralLattice n)
    (hU : L.IsUnimodular) (hI : L.HasOddNorm) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant n : ℝ) := by
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨half, hhalf⟩ := heven
    have hdecomp : n = 2 * half := by omega
    clear hhalf
    subst n
    rcases Nat.even_or_odd half with hhalfEven | hhalfOdd
    · apply ordinaryGenusMass_evenRank_evenHalf_eq_typeIConstant_of_localFactor
        (m := half) (by omega) hhalfEven L hU
      rw [massLocalFactor_two_eq_identity_of_typeIUnimodular L hU hI]
      exact identityLattice_massLocalFactor_two_evenRank_evenHalf_closed
        (by omega) hhalfEven
    · obtain ⟨quarter, hquarter⟩ := hhalfOdd
      have hdecomp : half = 2 * quarter + 1 := by omega
      clear hquarter
      subst half
      apply ordinaryGenusMass_evenRank_oddHalf_eq_typeIConstant_of_localFactor
        (k := quarter) (by omega) L hU
      rw [massLocalFactor_two_eq_identity_of_typeIUnimodular L hU hI]
      exact identityLattice_massLocalFactor_two_evenRank_oddHalf_closed
        quarter (by omega)
  · obtain ⟨half, hhalf⟩ := hodd
    have hdecomp : n = 2 * half + 1 := by omega
    clear hhalf
    subst n
    apply ordinaryGenusMass_oddRank_eq_typeIConstant_of_localFactor
      (r := half) (by omega) L hU
    rw [massLocalFactor_two_eq_identity_of_typeIUnimodular L hU hI]
    exact identityLattice_massLocalFactor_two_oddRank_closed half (by omega)

theorem ordinaryGenusMass_eq_typeIConstant_of_typeIUnimodular
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hI : L.HasOddNorm) :
    L.ordinaryGenusMass = typeIConstant n := by
  by_cases hn0 : n = 0
  · subst n
    exact False.elim (not_hasOddNorm_rank_zero L hI)
  by_cases hn1 : n = 1
  · subst n
    exact ordinaryGenusMass_eq_typeIConstant_of_rank_one_isUnimodular L hU
  by_cases hn2 : n = 2
  · subst n
    exact ordinaryGenusMass_eq_typeIConstant_of_rank_two_isUnimodular L hU
  exact Rat.cast_injective
    (ordinaryGenusMass_real_eq_typeIConstant_of_typeIUnimodular_of_three_le (by omega) L hU hI)

/-- Type I ordinary genus mass in every rank, from the finite normalizer and
the existing local-factor mass theorem, not from a genus-classification premise. -/
theorem ordinaryGenusMass_eq_typeIConstant
    {n : ℕ}
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    L.ordinaryGenusMass = typeIConstant n :=
  ordinaryGenusMass_eq_typeIConstant_of_typeIUnimodular L hdet hodd

/-- Finite genus-sum form of the Type I ordinary mass, without a classification
hypothesis. -/
theorem ordinaryGenusMass_literal_sum_eq_typeIConstant
    {n : ℕ}
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    (∑ A : L.genus,
      ((Fintype.card (genusClassRepresentative L A).IsometryGroup : ℚ)⁻¹)) =
        typeIConstant n := by
  change L.ordinaryGenusMass = typeIConstant n
  exact ordinaryGenusMass_eq_typeIConstant L hdet hodd

/-- Real-valued finite genus-sum form of the Type I mass, without a
classification hypothesis. -/
theorem ordinaryGenusMass_literal_sum_real_eq_typeIConstant
    {n : ℕ}
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    (((∑ A : L.genus,
      ((Fintype.card (genusClassRepresentative L A).IsometryGroup : ℚ)⁻¹)) : ℚ) : ℝ) =
        (typeIConstant n : ℝ) := by
  exact_mod_cast ordinaryGenusMass_literal_sum_eq_typeIConstant L hdet hodd

/-- Real-cast form of the Type I ordinary-mass theorem, without a classification
hypothesis. -/
theorem ordinaryGenusMass_real_eq_typeIConstant
    {n : ℕ}
    (L : PositiveDefiniteIntegralLattice n) (hdet : L.pairingDeterminant = 1)
    (hodd : ∃ x : Fin n → ℤ, Odd (L.quadForm x)) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant n : ℝ) := by
  exact_mod_cast ordinaryGenusMass_eq_typeIConstant L hdet hodd

#assert_standard_axioms massLocalFactor_two_eq_identity_of_typeIUnimodular
#assert_standard_axioms massLocalFactor_two_eq_typeIClosedForm
#assert_standard_axioms ordinaryGenusMass_eq_typeIConstant_of_typeIUnimodular
#assert_standard_axioms ordinaryGenusMass_eq_typeIConstant
#assert_standard_axioms ordinaryGenusMass_real_eq_typeIConstant
#assert_standard_axioms ordinaryGenusMass_literal_sum_eq_typeIConstant
#assert_standard_axioms ordinaryGenusMass_literal_sum_real_eq_typeIConstant

end PositiveDefiniteIntegralLattice

end
