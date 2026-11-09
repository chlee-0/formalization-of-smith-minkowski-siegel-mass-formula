import SMSFormula.Applications.Unimodular.DirectPeeling.TargetBridge
import SMSFormula.Applications.Unimodular.LowRankMass
import SMSFormula.Applications.Unimodular.TypeIIObstruction
import SMSFormula.StandardAxiomsGuard

/-!
# Type II direct-H mass formula

This file exposes the direct hyperbolic
mod-eight normal form through the `PositiveDefiniteIntegralLattice` namespace.  The imported
`DirectPeeling.TargetBridge` supplies the finite `GramCongruenceCertificate`
construction; the theorems below state the resulting dyadic local-factor comparison and ordinary-mass
formula for arbitrary Type II classically unimodular lattices in positive rank
`8*k`, then use the Type II rank obstruction to state the ordinary-mass
formula in arbitrary rank notation.
-/

noncomputable section

open scoped BigOperators
open UnimodularMass

namespace PositiveDefiniteIntegralLattice

/-- The direct-H mod-eight normal form compares the dyadic local factor of every
Type II classically unimodular lattice in rank `8*k` with the checked seed. -/
theorem localFactor_eq_typeIISeed_of_typeIIUnimodular_directH
    (k : ℕ) (hk : 0 < k) (L : PositiveDefiniteIntegralLattice (8 * k))
    (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    L.massLocalFactor 2 =
      (typeIISeed k).massLocalFactor 2 :=
  TypeIIDirectPeeling.localFactor_eq_typeIISeed_of_typeIIUnimodular_directH k hk L hL hII

/-- The direct-H mod-eight normal form gives the Type II Bernoulli ordinary-mass
endpoint for every Type II classically unimodular lattice in positive rank `8*k`. -/
theorem ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular_directH
    (k : ℕ) (hk : 0 < k) (L : PositiveDefiniteIntegralLattice (8 * k))
    (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    L.ordinaryGenusMass = typeIIConstant (8 * k) :=
  TypeIIDirectPeeling.ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular_directH k hk L hL hII

/-- Real-cast form of the direct-H Type II ordinary-mass endpoint in rank `8*k`. -/
theorem ordinaryGenusMass_real_eq_typeIIConstant_of_typeIIUnimodular_directH
    (k : ℕ) (hk : 0 < k) (L : PositiveDefiniteIntegralLattice (8 * k))
    (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant (8 * k) : ℝ) := by
  exact_mod_cast
    (ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular_directH k hk L hL hII)

/-- Positive-rank version of the direct-H endpoint with the rank written as an
arbitrary `n`.  The Type II rank obstruction supplies the hidden multiple of
eight. -/
theorem ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular_pos
    {n : ℕ} (hn : 0 < n) (L : PositiveDefiniteIntegralLattice n)
    (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    L.ordinaryGenusMass = typeIIConstant n := by
  rcases eight_dvd_rank_of_isUnimodular_isTypeII L hL hII with ⟨k, rfl⟩
  have hk : 0 < k := by omega
  exact ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular_directH k hk L hL hII

/-- Real-cast positive-rank Type II ordinary-mass endpoint with arbitrary rank notation. -/
theorem ordinaryGenusMass_real_eq_typeIIConstant_of_typeIIUnimodular_pos
    {n : ℕ} (hn : 0 < n) (L : PositiveDefiniteIntegralLattice n)
    (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant n : ℝ) := by
  exact_mod_cast ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular_pos hn L hL hII

/-- Every classically unimodular Type II lattice has ordinary mass equal to the
Type II Bernoulli constant.  Rank zero uses the low-rank endpoint; positive rank
uses the direct-H mod-eight normal form after the rank obstruction. -/
theorem ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n)
    (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    L.ordinaryGenusMass = typeIIConstant n := by
  by_cases hn : n = 0
  · subst n
    exact ordinaryGenusMass_eq_typeIIConstant_of_rank_zero L
  · exact ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular_pos
      (Nat.pos_of_ne_zero hn) L hL hII

/-- Real-cast arbitrary-rank Type II ordinary-mass endpoint. -/
theorem ordinaryGenusMass_real_eq_typeIIConstant_of_typeIIUnimodular
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n)
    (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant n : ℝ) := by
  exact_mod_cast ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular L hL hII

/-- Literal finite genus-sum form of the intrinsic arbitrary-rank Type II
ordinary-mass endpoint.  Rank zero is included through the underlying all-rank
ordinary-mass theorem. -/
theorem ordinaryGenusMass_literal_sum_eq_typeIIConstant_of_typeIIUnimodular
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n)
    (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    (∑ A : L.genus,
      ((Fintype.card (genusClassRepresentative L A).IsometryGroup : ℚ)⁻¹)) =
        typeIIConstant n := by
  change L.ordinaryGenusMass = typeIIConstant n
  exact ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular L hL hII

/-- Real-valued literal finite genus-sum form of the intrinsic arbitrary-rank
Type II ordinary-mass endpoint. -/
theorem ordinaryGenusMass_literal_sum_real_eq_typeIIConstant_of_typeIIUnimodular
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n)
    (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    (((∑ A : L.genus,
      ((Fintype.card (genusClassRepresentative L A).IsometryGroup : ℚ)⁻¹)) : ℚ) : ℝ) =
        (typeIIConstant n : ℝ) := by
  exact_mod_cast
    ordinaryGenusMass_literal_sum_eq_typeIIConstant_of_typeIIUnimodular L hL hII

/-- The Type II ordinary-mass formula, written with the external normalization
hypotheses `pairingDeterminant = 1` and even quadratic values.  The divisibility
hypothesis is redundant: the Type II rank obstruction derives it from the other
hypotheses in positive rank. -/
theorem ordinaryGenusMass_eq_typeIIConstant
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (_hn : 0 < n) (_h8 : 8 ∣ n)
    (hdet : L.pairingDeterminant = 1) (heven : ∀ x, Even (L.quadForm x)) :
    L.ordinaryGenusMass = typeIIConstant n :=
  ordinaryGenusMass_eq_typeIIConstant_of_typeIIUnimodular L hdet heven

/-- Real-cast form of the Type II ordinary-mass formula. -/
theorem ordinaryGenusMass_real_eq_typeIIConstant
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hn : 0 < n) (h8 : 8 ∣ n)
    (hdet : L.pairingDeterminant = 1) (heven : ∀ x, Even (L.quadForm x)) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant n : ℝ) := by
  exact_mod_cast ordinaryGenusMass_eq_typeIIConstant L hn h8 hdet heven

/-- Finite genus-sum form of the Type II ordinary-mass formula.  This
exposes the defining ordinary mass sum over genus classes. -/
theorem ordinaryGenusMass_literal_sum_eq_typeIIConstant
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hn : 0 < n) (h8 : 8 ∣ n)
    (hdet : L.pairingDeterminant = 1) (heven : ∀ x, Even (L.quadForm x)) :
    (∑ A : L.genus,
      ((Fintype.card (genusClassRepresentative L A).IsometryGroup : ℚ)⁻¹)) =
        typeIIConstant n := by
  change L.ordinaryGenusMass = typeIIConstant n
  exact ordinaryGenusMass_eq_typeIIConstant L hn h8 hdet heven

/-- Real-valued finite genus-sum form of the Type II ordinary-mass
formula. -/
theorem ordinaryGenusMass_literal_sum_real_eq_typeIIConstant
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hn : 0 < n) (h8 : 8 ∣ n)
    (hdet : L.pairingDeterminant = 1) (heven : ∀ x, Even (L.quadForm x)) :
    (((∑ A : L.genus,
      ((Fintype.card (genusClassRepresentative L A).IsometryGroup : ℚ)⁻¹)) : ℚ) : ℝ) =
        (typeIIConstant n : ℝ) := by
  exact_mod_cast ordinaryGenusMass_literal_sum_eq_typeIIConstant L hn h8 hdet heven

/-- Positive-rank local-factor comparison with arbitrary rank notation.  The
returned `k` is forced by the Type II rank obstruction. -/
theorem exists_localFactor_eq_typeIISeed_of_typeIIUnimodular_pos
    {n : ℕ} (hn : 0 < n) (L : PositiveDefiniteIntegralLattice n)
    (hL : L.IsUnimodular) (hII : L.HasEvenNorms) :
    ∃ k : ℕ, n = 8 * k ∧ 0 < k ∧
      L.massLocalFactor 2 =
        (typeIISeed k).massLocalFactor 2 := by
  rcases eight_dvd_rank_of_isUnimodular_isTypeII L hL hII with ⟨k, rfl⟩
  have hk : 0 < k := by omega
  exact ⟨k, rfl, hk,
    localFactor_eq_typeIISeed_of_typeIIUnimodular_directH k hk L hL hII⟩

end PositiveDefiniteIntegralLattice
