import SMSFormula.Applications.Unimodular.GenusMass
import SMSFormula.Applications.Unimodular.Genus
import SMSFormula.Applications.Unimodular.DyadicE8CorrectionFiber
import SMSFormula.Applications.Unimodular.TypeIIDirectHMass

/-!
# E8 ordinary genus mass

This file records the first fully evaluated rank-eight Type II seed case.  It
uses the existing ordinary genus mass theorem, the existing analytic Type I
assembly at even/even half-rank, and the direct E8 dyadic local-factor count
from `DyadicE8CorrectionFiber`.  It does not assert uniqueness of the E8 genus
or identify an automorphism group order.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice
open UnimodularMass

/-- The closed dyadic local factor transports to any representative of the E8 genus. -/
theorem massLocalFactor_two_eq_e8_of_isSameGenus
    {L : PositiveDefiniteIntegralLattice 8} (h : L.IsSameGenus e8Lattice) :
    L.massLocalFactor 2 = (42525 / 256 : ℝ) := by
  rw [massLocalFactor_eq_of_isSameGenus h]
  exact e8Lattice_massLocalFactor_two_eq

/-- The E8 dyadic density in the shape used by the rank-eight Type II mass
assembly: the rank-eight Type I local-factor expression, multiplied by the
independent Type I/Type II Bernoulli-constant ratio. -/
theorem e8Lattice_massLocalFactor_two_eq_typeII_density_bridge :
    e8Lattice.massLocalFactor 2 =
      ((4 : ℝ) * (2 : ℝ) ^ (4 - 1 : ℕ) *
          ((Finset.Icc 1 (4 - 1 : ℕ)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ ((4 * (4 - 1)) / 2 : ℕ) /
          (((2 : ℚ) ^ (4 - 1 : ℕ) + typeIEvenRankSign (2 * 4) : ℚ) : ℝ)) *
        (((typeIConstant 8 : ℚ) : ℝ) / ((typeIIConstant 8 : ℚ) : ℝ)) := by
  rw [e8Lattice_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (4 - 1 : ℕ) = {1, 2, 3} := by decide
  norm_num [hIcc, typeIEvenRankSign, typeIConstant_eight, typeIIConstant_eight]

/-- The same E8 dyadic density bridge in the exact quotient form consumed by
`ordinaryGenusMass_evenRank_evenHalf_eq_typeIIConstant_of_localFactor`. -/
theorem e8Lattice_massLocalFactor_two_eq_typeII_localFactor_assembly_bridge :
    e8Lattice.massLocalFactor 2 =
      (((4 : ℝ) * (2 : ℝ) ^ (4 - 1 : ℕ) * (typeIConstant 8 : ℝ) *
        ((Finset.Icc 1 (4 - 1 : ℕ)).prod
          (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ ((4 * (4 - 1)) / 2 : ℕ)) /
        ((((2 : ℚ) ^ (4 - 1 : ℕ) + typeIEvenRankSign (2 * 4) : ℚ) : ℝ) *
          (typeIIConstant 8 : ℝ))) := by
  rw [e8Lattice_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (4 - 1 : ℕ) = {1, 2, 3} := by decide
  norm_num [hIcc, typeIEvenRankSign, typeIConstant_eight, typeIIConstant_eight]

/-- The native-local-factor E8 density bridge transported to any representative
of the E8 genus. -/
theorem massLocalFactor_two_typeII_localFactor_assembly_bridge_of_isSameGenus_e8
    {L : PositiveDefiniteIntegralLattice 8} (h : L.IsSameGenus e8Lattice) :
    L.massLocalFactor 2 =
      (((4 : ℝ) * (2 : ℝ) ^ (4 - 1 : ℕ) * (typeIConstant 8 : ℝ) *
        ((Finset.Icc 1 (4 - 1 : ℕ)).prod
          (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
          (4 : ℝ) ^ ((4 * (4 - 1)) / 2 : ℕ)) /
        ((((2 : ℚ) ^ (4 - 1 : ℕ) + typeIEvenRankSign (2 * 4) : ℚ) : ℝ) *
          (typeIIConstant 8 : ℝ))) := by
  rw [massLocalFactor_eq_of_isSameGenus h]
  exact e8Lattice_massLocalFactor_two_eq_typeII_localFactor_assembly_bridge

/-- The same E8 dyadic density bridge in the cutoff-product form consumed by
`ordinaryGenusMass_evenRank_evenHalf_typeIConstant_up_to_dyadic`: after the
closed dyadic factor is inverted, the rank-eight Type I assembly numerator
becomes the Type II constant with the elementary Type I sign denominator. -/
theorem e8Lattice_massPartialPrimeInverseProduct_two_typeII_density_bridge :
    massPartialPrimeInverseProduct e8Lattice 2 *
        ((4 : ℝ) * (2 : ℝ) ^ (4 - 1 : ℕ) * (typeIConstant 8 : ℝ) *
          ((Finset.Icc 1 (4 - 1 : ℕ)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ ((4 * (4 - 1)) / 2 : ℕ)) =
      (((2 : ℚ) ^ (4 - 1 : ℕ) + typeIEvenRankSign (2 * 4) : ℚ) : ℝ) *
        (typeIIConstant 8 : ℝ) := by
  rw [massPartialPrimeInverseProduct_two,
    e8Lattice_massLocalFactor_two_eq]
  have hIcc : Finset.Icc 1 (4 - 1 : ℕ) = {1, 2, 3} := by decide
  norm_num [hIcc, typeIEvenRankSign, typeIConstant_eight, typeIIConstant_eight]

/-- The cutoff-product E8 density bridge transported to any representative of
the E8 genus. -/
theorem massPartialPrimeInverseProduct_two_typeII_density_bridge_of_isSameGenus_e8
    {L : PositiveDefiniteIntegralLattice 8} (h : L.IsSameGenus e8Lattice) :
    massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (2 : ℝ) ^ (4 - 1 : ℕ) * (typeIConstant 8 : ℝ) *
          ((Finset.Icc 1 (4 - 1 : ℕ)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ ((4 * (4 - 1)) / 2 : ℕ)) =
      (((2 : ℚ) ^ (4 - 1 : ℕ) + typeIEvenRankSign (2 * 4) : ℚ) : ℝ) *
        (typeIIConstant 8 : ℝ) := by
  rw [massPartialPrimeInverseProduct_eq_of_isSameGenus h]
  exact e8Lattice_massPartialPrimeInverseProduct_two_typeII_density_bridge

/-- The E8 ordinary genus mass after evaluating the native dyadic factor. -/
theorem e8Lattice_ordinaryGenusMass_real :
    ((e8Lattice.ordinaryGenusMass : ℚ) : ℝ) = 1 / 696729600 := by
  have hm := ordinaryGenusMass_evenRank_evenHalf_typeIConstant_up_to_dyadic
    (m := 4) (by norm_num) (by decide) e8Lattice e8Lattice_isUnimodular
  rw [massPartialPrimeInverseProduct_two,
    e8Lattice_massLocalFactor_two_eq] at hm
  have hIcc : Finset.Icc 1 (4 - 1 : ℕ) = {1, 2, 3} := by decide
  norm_num [hIcc, typeIEvenRankSign, typeIConstant_eight] at hm
  linarith

/-- Equality in the actual rational genus-mass type, not a new mass definition. -/
theorem e8Lattice_ordinaryGenusMass :
    e8Lattice.ordinaryGenusMass = (1 / 696729600 : ℚ) := by
  have h : (e8Lattice.ordinaryGenusMass : ℝ) = ((1 / 696729600 : ℚ) : ℝ) := by
    norm_num
    exact e8Lattice_ordinaryGenusMass_real
  exact Rat.cast_injective h

/-- The E8 Type II endpoint recovered through the general cutoff-density
assembly interface. -/
theorem e8Lattice_ordinaryGenusMass_real_eq_typeIIConstant_of_cutoff_density :
    ((e8Lattice.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant 8 : ℝ) := by
  have h := ordinaryGenusMass_evenRank_evenHalf_eq_typeIIConstant_of_cutoff_density
    (m := 4) (by norm_num) (by decide) e8Lattice e8Lattice_isUnimodular
    (by
      simpa using e8Lattice_massPartialPrimeInverseProduct_two_typeII_density_bridge)
  simpa using h

/-- The E8 Type II endpoint recovered through the general native-local-factor
assembly interface. -/
theorem e8Lattice_ordinaryGenusMass_real_eq_typeIIConstant_of_localFactor :
    ((e8Lattice.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant 8 : ℝ) := by
  refine ordinaryGenusMass_evenRank_evenHalf_eq_typeIIConstant_of_localFactor
    (m := 4) (by norm_num) (by decide) e8Lattice e8Lattice_isUnimodular ?_
  simpa using e8Lattice_massLocalFactor_two_eq_typeII_localFactor_assembly_bridge

/-- The rank-eight Type II endpoint for any E8-genus representative, routed
through the native local-factor assembly interface. -/
theorem ordinaryGenusMass_real_eq_typeIIConstant_of_isSameGenus_e8_of_localFactor
    {L : PositiveDefiniteIntegralLattice 8} (h : L.IsSameGenus e8Lattice) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant 8 : ℝ) := by
  refine ordinaryGenusMass_evenRank_evenHalf_eq_typeIIConstant_of_localFactor
    (m := 4) (by norm_num) (by decide) L
    (PositiveDefiniteIntegralLattice.isUnimodular_of_isSameGenus h e8Lattice_isUnimodular) ?_
  simpa using massLocalFactor_two_typeII_localFactor_assembly_bridge_of_isSameGenus_e8 h

/-- The rank-eight E8 genus mass equals the closed Type II constant. -/
theorem e8Lattice_ordinaryGenusMass_eq_typeIIConstant :
    e8Lattice.ordinaryGenusMass = typeIIConstant 8 := by
  exact Rat.cast_injective e8Lattice_ordinaryGenusMass_real_eq_typeIIConstant_of_cutoff_density

/-- The rank-eight E8 genus endpoint transported to any same-genus representative. -/
theorem ordinaryGenusMass_eq_typeIIConstant_of_isSameGenus_e8
    {L : PositiveDefiniteIntegralLattice 8} (h : L.IsSameGenus e8Lattice) :
    L.ordinaryGenusMass = typeIIConstant 8 := by
  rw [ordinaryGenusMass_eq_of_isSameGenus h]
  exact e8Lattice_ordinaryGenusMass_eq_typeIIConstant

/-- The rank-eight Type II ordinary-mass endpoint now follows directly from the
general direct-H Type II route, so it needs no supplied E8 same-genus
classification. -/
theorem ordinaryGenusMass_eq_typeIIConstant_of_rank_eight_typeII
    (L : PositiveDefiniteIntegralLattice 8) (hU : L.IsUnimodular) (hII : L.HasEvenNorms) :
    L.ordinaryGenusMass = typeIIConstant 8 :=
  ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular L hU hII

/-- Real-cast form of the rank-eight Type II ordinary-mass formula. -/
theorem ordinaryGenusMass_real_eq_typeIIConstant_of_rank_eight_typeII
    (L : PositiveDefiniteIntegralLattice 8) (hU : L.IsUnimodular) (hII : L.HasEvenNorms) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant 8 : ℝ) :=
  congrArg (fun q : ℚ => (q : ℝ))
    (ordinaryGenusMass_eq_typeIIConstant_of_rank_eight_typeII L hU hII)

/-- A supplied rank-eight Type II same-genus classification gives the real-valued
Type II ordinary mass for every classified lattice.  The direct-H theorem above
does not need this classification input. -/
theorem ordinaryGenusMass_real_eq_typeIIConstant_of_rank_eight_typeII_sameGenus_classification
    (hclass : ∀ L : PositiveDefiniteIntegralLattice 8, L.IsUnimodular → L.HasEvenNorms →
      L.IsSameGenus e8Lattice)
    (L : PositiveDefiniteIntegralLattice 8) (hU : L.IsUnimodular) (hII : L.HasEvenNorms) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant 8 : ℝ) :=
  ordinaryGenusMass_real_eq_typeIIConstant_of_isSameGenus_e8_of_localFactor
    (hclass L hU hII)

/-- A supplied rank-eight Type II same-genus classification gives the rational
Type II ordinary mass for every classified lattice.  The direct-H theorem above
does not need this classification input. -/
theorem ordinaryGenusMass_eq_typeIIConstant_of_rank_eight_typeII_sameGenus_classification
    (hclass : ∀ L : PositiveDefiniteIntegralLattice 8, L.IsUnimodular → L.HasEvenNorms →
      L.IsSameGenus e8Lattice)
    (L : PositiveDefiniteIntegralLattice 8) (hU : L.IsUnimodular) (hII : L.HasEvenNorms) :
    L.ordinaryGenusMass = typeIIConstant 8 :=
  ordinaryGenusMass_eq_typeIIConstant_of_isSameGenus_e8 (hclass L hU hII)

end PositiveDefiniteIntegralLattice
