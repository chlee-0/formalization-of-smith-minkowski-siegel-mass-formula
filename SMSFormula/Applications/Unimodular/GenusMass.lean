import SMSFormula.Applications.Unimodular.SpecialValues
import SMSFormula.Applications.Unimodular.Positivity
import SMSFormula.RationalSpecialOrthogonalMassFormula

/-!
# Ordinary genus mass assembly for unimodular lattices

This module connects the ordinary Schulze--Pillot mass theorem to
the unimodular good-prime and special-value reductions.  The dyadic local
factor is intentionally left as the explicit cutoff product
`massPartialPrimeInverseProduct L 2`; no dyadic density is evaluated
or inferred from the target Bernoulli formula.
-/

noncomputable section

namespace UnimodularMass

open PositiveDefiniteIntegralLattice

/-- In odd rank, the Schulze--Pillot product side with the dyadic cutoff and the
removed-`2` zeta-core good-prime tail is exactly the dyadic cutoff factor times
the extracted Bernoulli/archimedean expression. -/
lemma productSide_oddRank_removed_two_eq_extracted
    (r : ℕ) (L : PositiveDefiniteIntegralLattice (2 * r + 1)) :
    PositiveDefiniteIntegralLattice.massFormulaProductSide L
      (PositiveDefiniteIntegralLattice.massPartialPrimeInverseProduct L 2 *
        (Finset.Icc 1 r).prod
          (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
            (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))))) =
      PositiveDefiniteIntegralLattice.massPartialPrimeInverseProduct L 2 *
        ((bernoulliCore r : ℝ) *
          (oddRankExtractedPiProduct r * oddRankExtractedRationalProduct r)) := by
  unfold PositiveDefiniteIntegralLattice.massFormulaProductSide
  rw [archimedeanMassFactor_odd_eq_pi_rpow_extracted]
  rw [prod_zetaCoreRemovedTwo_eq_bernoulliCore_mul_pi_pow_remainder]
  unfold oddRankExtractedPiProduct oddRankExtractedRationalProduct
  ring

/-- In even rank, away from the rank-two endpoint, the Schulze--Pillot product
side with the dyadic cutoff, removed-`2` zeta-core tail, and Dirichlet-character
tail is exactly the dyadic cutoff factor times the extracted
Bernoulli/archimedean/character-tail expression. -/
lemma productSide_evenRank_removed_two_eq_extracted
    (r : ℕ) (hr : 1 ≤ r) (L : PositiveDefiniteIntegralLattice (2 * r)) :
    PositiveDefiniteIntegralLattice.massFormulaProductSide L
      (PositiveDefiniteIntegralLattice.massPartialPrimeInverseProduct L 2 *
        ((Finset.Icc 1 (r - 1)).prod
          (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
            (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) *
            PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor L 2 r)) =
      PositiveDefiniteIntegralLattice.massPartialPrimeInverseProduct L 2 *
        ((bernoulliCore (r - 1) : ℝ) *
          (evenRankExtractedPiProduct r * evenRankExtractedRationalProduct r *
            PositiveDefiniteIntegralLattice.goodPrimeEvenCharacterDirichletTailFactor L 2 r)) := by
  unfold PositiveDefiniteIntegralLattice.massFormulaProductSide
  rw [archimedeanMassFactor_even_eq_pi_rpow_extracted]
  rw [prod_zetaCoreRemovedTwo_eq_bernoulliCore_mul_pi_pow_remainder]
  have hs : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hpow_exp : (r - 1) * ((r - 1) + 1) = (r - 1) * r := by rw [hs]
  rw [hpow_exp]
  unfold evenRankExtractedPiProduct evenRankExtractedRationalProduct
  ring

end UnimodularMass

namespace PositiveDefiniteIntegralLattice

open UnimodularMass

/-- Odd-rank unimodular ordinary genus mass after the mass theorem,
with the dyadic local factor left explicit.  This is the Type I Bernoulli
constant bridge up to the remaining dyadic density comparison. -/
theorem ordinaryGenusMass_oddRank_typeIConstant_up_to_dyadic
    {r : ℕ} (hr : 1 ≤ r) (L : PositiveDefiniteIntegralLattice (2 * r + 1))
    (hL : L.IsUnimodular) :
    (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ) *
        ((L.ordinaryGenusMass : ℚ) : ℝ) =
      massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (2 : ℝ) ^ r * (typeIConstant (2 * r + 1) : ℝ) *
          ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (r * (r - 1) / 2 + r)) := by
  have hmass : ((L.ordinaryGenusMass : ℚ) : ℝ) =
      massFormulaProductSide L
        (massPartialPrimeInverseProduct L 2 *
          (Finset.Icc 1 r).prod
            (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
              (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))))) := by
    exact L.ordinaryGenusMass_eq_massFormulaProductSide
      (by omega : 3 ≤ 2 * r + 1)
      (unimodularOddExpandedProduct_pos (L := L) r)
      (massLocalInverseProductTendsTo_unimodular_odd_zeta_removed_two_of_two_mul_add_one
        (L := L) hL rfl)
  rw [hmass]
  rw [UnimodularMass.productSide_oddRank_removed_two_eq_extracted]
  have hspecial := UnimodularMass.oddRank_extracted_zetaCore_archimedean_typeIConstant r hr
  calc
    (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ) *
        (massPartialPrimeInverseProduct L 2 *
          ((bernoulliCore r : ℝ) *
            (UnimodularMass.oddRankExtractedPiProduct r *
              UnimodularMass.oddRankExtractedRationalProduct r)))
        = massPartialPrimeInverseProduct L 2 *
            ((((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ) *
              ((bernoulliCore r : ℝ) *
                (UnimodularMass.oddRankExtractedPiProduct r *
                  UnimodularMass.oddRankExtractedRationalProduct r))) := by
            ring
    _ = massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (2 : ℝ) ^ r * (typeIConstant (2 * r + 1) : ℝ) *
          ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (r * (r - 1) / 2 + r)) := by
            rw [hspecial]

/-- Even rank with odd half-rank, after the ordinary mass theorem.
The dyadic cutoff factor is still explicit; evaluating it is the remaining
local-density task. -/
theorem ordinaryGenusMass_evenRank_oddHalf_typeIConstant_up_to_dyadic
    {k : ℕ} (hk : k ≠ 0) (L : PositiveDefiniteIntegralLattice (2 * (2 * k + 1)))
    (hL : L.IsUnimodular) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) =
      massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (typeIConstant (2 * (2 * k + 1)) : ℝ) *
          ((Finset.Icc 1 (2 * k + 1 - 1)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2)) := by
  have hm_one : 1 < 2 * k + 1 := by omega
  have hmass : ((L.ordinaryGenusMass : ℚ) : ℝ) =
      massFormulaProductSide L
        (massPartialPrimeInverseProduct L 2 *
          ((Finset.Icc 1 (2 * k + 1 - 1)).prod
            (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
              (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) *
              goodPrimeEvenCharacterDirichletTailFactor L 2 (2 * k + 1))) := by
    exact L.ordinaryGenusMass_eq_massFormulaProductSide
      (by omega : 3 ≤ 2 * (2 * k + 1))
      (unimodularEvenExpandedProduct_pos_of_one_lt
        (L := L) hm_one rfl)
      (massLocalInverseProductTendsTo_unimodular_even_dirichlet_removed_two_of_two_mul
        (L := L) hL (by omega : 0 < 2 * k + 1) rfl)
  rw [hmass]
  rw [UnimodularMass.productSide_evenRank_removed_two_eq_extracted (hr := by omega)]
  have hspecial :=
    UnimodularMass.evenRank_extracted_mul_characterTail_oddHalf_typeIConstant
      (L := L) hL hk (by rfl)
  calc
    massPartialPrimeInverseProduct L 2 *
        ((bernoulliCore (2 * k + 1 - 1) : ℝ) *
          (UnimodularMass.evenRankExtractedPiProduct (2 * k + 1) *
            UnimodularMass.evenRankExtractedRationalProduct (2 * k + 1) *
              goodPrimeEvenCharacterDirichletTailFactor L 2 (2 * k + 1)))
        = massPartialPrimeInverseProduct L 2 *
            (((bernoulliCore (2 * k + 1 - 1) : ℝ) *
              (UnimodularMass.evenRankExtractedPiProduct (2 * k + 1) *
                UnimodularMass.evenRankExtractedRationalProduct (2 * k + 1) *
                  goodPrimeEvenCharacterDirichletTailFactor L 2 (2 * k + 1)))) := by
            ring
    _ = massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (typeIConstant (2 * (2 * k + 1)) : ℝ) *
          ((Finset.Icc 1 (2 * k + 1 - 1)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2)) := by
            rw [hspecial]

/-- Even rank with even half-rank, after the ordinary mass theorem.
The statement is cross-multiplied by the elementary Type I sign denominator;
the dyadic cutoff factor remains explicit. -/
theorem ordinaryGenusMass_evenRank_evenHalf_typeIConstant_up_to_dyadic
    {m : ℕ} (hm_one : 1 < m) (hm_even : Even m) (L : PositiveDefiniteIntegralLattice (2 * m))
    (hL : L.IsUnimodular) :
    (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) *
        ((L.ordinaryGenusMass : ℚ) : ℝ) =
      massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (2 : ℝ) ^ (m - 1) * (typeIConstant (2 * m) : ℝ) *
          ((Finset.Icc 1 (m - 1)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (m * (m - 1) / 2)) := by
  have hmass : ((L.ordinaryGenusMass : ℚ) : ℝ) =
      massFormulaProductSide L
        (massPartialPrimeInverseProduct L 2 *
          ((Finset.Icc 1 (m - 1)).prod
            (fun j => (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
              (1 - (2 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))) *
              goodPrimeEvenCharacterDirichletTailFactor L 2 m)) := by
    exact L.ordinaryGenusMass_eq_massFormulaProductSide
      (by omega : 3 ≤ 2 * m)
      (unimodularEvenExpandedProduct_pos_of_one_lt
        (L := L) hm_one rfl)
      (massLocalInverseProductTendsTo_unimodular_even_dirichlet_removed_two_of_two_mul
        (L := L) hL (by omega : 0 < m) rfl)
  rw [hmass]
  rw [UnimodularMass.productSide_evenRank_removed_two_eq_extracted (hr := by omega)]
  have hspecial :=
    UnimodularMass.evenRank_extracted_mul_characterTail_evenHalf_typeIConstant
      (L := L) hL hm_one hm_even (by rfl)
  calc
    (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) *
        (massPartialPrimeInverseProduct L 2 *
          ((bernoulliCore (m - 1) : ℝ) *
            (UnimodularMass.evenRankExtractedPiProduct m *
              UnimodularMass.evenRankExtractedRationalProduct m *
                goodPrimeEvenCharacterDirichletTailFactor L 2 m)))
        = massPartialPrimeInverseProduct L 2 *
            ((((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) *
              ((bernoulliCore (m - 1) : ℝ) *
                (UnimodularMass.evenRankExtractedPiProduct m *
                  UnimodularMass.evenRankExtractedRationalProduct m *
                    goodPrimeEvenCharacterDirichletTailFactor L 2 m))) := by
            ring
    _ = massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (2 : ℝ) ^ (m - 1) * (typeIConstant (2 * m) : ℝ) *
          ((Finset.Icc 1 (m - 1)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (m * (m - 1) / 2)) := by
            rw [hspecial]

/-- Conditional final odd-rank Type I ordinary genus mass formula.  The only
non-structural hypothesis is the explicit dyadic comparison left by
`ordinaryGenusMass_oddRank_typeIConstant_up_to_dyadic`. -/
theorem ordinaryGenusMass_oddRank_eq_typeIConstant_of_dyadic
    {r : ℕ} (hr : 1 ≤ r) (L : PositiveDefiniteIntegralLattice (2 * r + 1))
    (hL : L.IsUnimodular)
    (hdyadic :
      massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (2 : ℝ) ^ r *
          ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (r * (r - 1) / 2 + r)) =
        (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ)) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant (2 * r + 1) : ℝ) := by
  have hmass := ordinaryGenusMass_oddRank_typeIConstant_up_to_dyadic hr L hL
  have hden_pos := typeIOddRankSignDen_pos r hr
  have hden_ne : (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ) ≠ 0 :=
    ne_of_gt hden_pos
  have hrewrite :
      massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (2 : ℝ) ^ r * (typeIConstant (2 * r + 1) : ℝ) *
          ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (r * (r - 1) / 2 + r)) =
        (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ) *
          (typeIConstant (2 * r + 1) : ℝ) := by
    calc
      massPartialPrimeInverseProduct L 2 *
          ((4 : ℝ) * (2 : ℝ) ^ r * (typeIConstant (2 * r + 1) : ℝ) *
            ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
              (4 : ℝ) ^ (r * (r - 1) / 2 + r))
          = (massPartialPrimeInverseProduct L 2 *
              ((4 : ℝ) * (2 : ℝ) ^ r *
                ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
                  (4 : ℝ) ^ (r * (r - 1) / 2 + r))) *
                (typeIConstant (2 * r + 1) : ℝ) := by
              ring
      _ = (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ) *
            (typeIConstant (2 * r + 1) : ℝ) := by
              rw [hdyadic]
  rw [hrewrite] at hmass
  exact mul_left_cancel₀ hden_ne hmass

/-- Conditional final even-rank, odd half-rank Type I ordinary genus mass
formula.  The dyadic hypothesis is exactly the remaining cutoff/numerator
comparison. -/
theorem ordinaryGenusMass_evenRank_oddHalf_eq_typeIConstant_of_dyadic
    {k : ℕ} (hk : k ≠ 0) (L : PositiveDefiniteIntegralLattice (2 * (2 * k + 1)))
    (hL : L.IsUnimodular)
    (hdyadic :
      massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) *
          ((Finset.Icc 1 (2 * k + 1 - 1)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2)) = 1) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant (2 * (2 * k + 1)) : ℝ) := by
  have hmass := ordinaryGenusMass_evenRank_oddHalf_typeIConstant_up_to_dyadic hk L hL
  calc
    ((L.ordinaryGenusMass : ℚ) : ℝ)
        = massPartialPrimeInverseProduct L 2 *
          ((4 : ℝ) * (typeIConstant (2 * (2 * k + 1)) : ℝ) *
            ((Finset.Icc 1 (2 * k + 1 - 1)).prod
              (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
              (4 : ℝ) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2)) := hmass
    _ = (massPartialPrimeInverseProduct L 2 *
          ((4 : ℝ) *
            ((Finset.Icc 1 (2 * k + 1 - 1)).prod
              (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
              (4 : ℝ) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2))) *
            (typeIConstant (2 * (2 * k + 1)) : ℝ) := by
          ring
    _ = (typeIConstant (2 * (2 * k + 1)) : ℝ) := by
          rw [hdyadic]
          ring

/-- Conditional final even-rank, even half-rank Type I ordinary genus mass
formula.  The sign denominator is canceled using the positivity lemma from
`Constants.lean`. -/
theorem ordinaryGenusMass_evenRank_evenHalf_eq_typeIConstant_of_dyadic
    {m : ℕ} (hm_one : 1 < m) (hm_even : Even m) (L : PositiveDefiniteIntegralLattice (2 * m))
    (hL : L.IsUnimodular)
    (hdyadic :
      massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (2 : ℝ) ^ (m - 1) *
          ((Finset.Icc 1 (m - 1)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (m * (m - 1) / 2)) =
        (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ)) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant (2 * m) : ℝ) := by
  have hmass := ordinaryGenusMass_evenRank_evenHalf_typeIConstant_up_to_dyadic
    hm_one hm_even L hL
  have hden_pos := typeIEvenRankSignDen_pos m hm_one
  have hden_ne : (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) ≠ 0 :=
    ne_of_gt hden_pos
  have hrewrite :
      massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (2 : ℝ) ^ (m - 1) * (typeIConstant (2 * m) : ℝ) *
          ((Finset.Icc 1 (m - 1)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (m * (m - 1) / 2)) =
        (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) *
          (typeIConstant (2 * m) : ℝ) := by
    calc
      massPartialPrimeInverseProduct L 2 *
          ((4 : ℝ) * (2 : ℝ) ^ (m - 1) * (typeIConstant (2 * m) : ℝ) *
            ((Finset.Icc 1 (m - 1)).prod
              (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
              (4 : ℝ) ^ (m * (m - 1) / 2))
          = (massPartialPrimeInverseProduct L 2 *
              ((4 : ℝ) * (2 : ℝ) ^ (m - 1) *
                ((Finset.Icc 1 (m - 1)).prod
                  (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
                  (4 : ℝ) ^ (m * (m - 1) / 2))) *
                (typeIConstant (2 * m) : ℝ) := by
              ring
      _ = (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) *
            (typeIConstant (2 * m) : ℝ) := by
              rw [hdyadic]
  rw [hrewrite] at hmass
  exact mul_left_cancel₀ hden_ne hmass

/-- Conditional final even-rank, even half-rank Type II ordinary genus mass
formula in the cutoff-product form.  This is the assembly interface for a
direct Type II dyadic-density comparison: the density hypothesis is exactly the
right-hand side of
`ordinaryGenusMass_evenRank_evenHalf_typeIConstant_up_to_dyadic`, with the
rank-`2*m` Type I constant replaced by the independent Type II constant after
the elementary Type I sign denominator has been pulled out. -/
theorem ordinaryGenusMass_evenRank_evenHalf_eq_typeIIConstant_of_cutoff_density
    {m : ℕ} (hm_one : 1 < m) (hm_even : Even m) (L : PositiveDefiniteIntegralLattice (2 * m))
    (hL : L.IsUnimodular)
    (hdyadic :
      massPartialPrimeInverseProduct L 2 *
        ((4 : ℝ) * (2 : ℝ) ^ (m - 1) * (typeIConstant (2 * m) : ℝ) *
          ((Finset.Icc 1 (m - 1)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (m * (m - 1) / 2)) =
        (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) *
          (typeIIConstant (2 * m) : ℝ)) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant (2 * m) : ℝ) := by
  have hmass := ordinaryGenusMass_evenRank_evenHalf_typeIConstant_up_to_dyadic
    hm_one hm_even L hL
  have hden_pos := typeIEvenRankSignDen_pos m hm_one
  have hden_ne :
      (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) ≠ 0 :=
    ne_of_gt hden_pos
  rw [hdyadic] at hmass
  exact mul_left_cancel₀ hden_ne hmass

/-- Conditional final even-rank, even half-rank Type II ordinary genus mass
formula, stated with an explicit value of the native dyadic local factor.

This is the native-local-factor companion to
`ordinaryGenusMass_evenRank_evenHalf_eq_typeIIConstant_of_cutoff_density`: a
direct dyadic-density proof may establish this quotient form for
`L.massLocalFactor 2`, and the general mass assembly then yields
the independent Type II Bernoulli constant. -/
theorem ordinaryGenusMass_evenRank_evenHalf_eq_typeIIConstant_of_localFactor
    {m : ℕ} (hm_one : 1 < m) (hm_even : Even m) (L : PositiveDefiniteIntegralLattice (2 * m))
    (hL : L.IsUnimodular)
    (hlocal :
      L.massLocalFactor 2 =
        (((4 : ℝ) * (2 : ℝ) ^ (m - 1) * (typeIConstant (2 * m) : ℝ) *
          ((Finset.Icc 1 (m - 1)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (m * (m - 1) / 2)) /
          ((((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) *
            (typeIIConstant (2 * m) : ℝ)))) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIIConstant (2 * m) : ℝ) := by
  let B : ℝ :=
    ((4 : ℝ) * (2 : ℝ) ^ (m - 1) * (typeIConstant (2 * m) : ℝ) *
      ((Finset.Icc 1 (m - 1)).prod
        (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
        (4 : ℝ) ^ (m * (m - 1) / 2))
  let E : ℝ :=
    (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ) *
      (typeIIConstant (2 * m) : ℝ)
  have hlocalBE : L.massLocalFactor 2 = B / E := by
    simpa [B, E] using hlocal
  have hfac_pos : 0 < L.massLocalFactor 2 :=
    massLocalFactor_pos L 2
  have hfac_ne : L.massLocalFactor 2 ≠ 0 := ne_of_gt hfac_pos
  have hBne : B ≠ 0 := by
    intro hB
    have hzero : L.massLocalFactor 2 = 0 := by
      rw [hlocalBE]
      simp [hB]
    exact hfac_ne hzero
  have hEne : E ≠ 0 := by
    intro hE
    have hzero : L.massLocalFactor 2 = 0 := by
      rw [hlocalBE]
      simp [hE]
    exact hfac_ne hzero
  refine ordinaryGenusMass_evenRank_evenHalf_eq_typeIIConstant_of_cutoff_density
    hm_one hm_even L hL ?_
  rw [massPartialPrimeInverseProduct_two]
  change (L.massLocalFactor 2)⁻¹ * B = E
  rw [hlocalBE]
  field_simp [hBne, hEne]

/-- Conditional final odd-rank Type I ordinary genus mass formula, stated with
an explicit value of the native dyadic local factor. -/
theorem ordinaryGenusMass_oddRank_eq_typeIConstant_of_localFactor
    {r : ℕ} (hr : 1 ≤ r) (L : PositiveDefiniteIntegralLattice (2 * r + 1))
    (hL : L.IsUnimodular)
    (hlocal :
      L.massLocalFactor 2 =
        ((4 : ℝ) * (2 : ℝ) ^ r *
          ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (r * (r - 1) / 2 + r) /
          (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ))) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant (2 * r + 1) : ℝ) := by
  let A : ℝ :=
    ((4 : ℝ) * (2 : ℝ) ^ r *
      ((Finset.Icc 1 r).prod (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
        (4 : ℝ) ^ (r * (r - 1) / 2 + r))
  let D : ℝ := (((2 : ℚ) ^ r + typeIOddRankSign (2 * r + 1) : ℚ) : ℝ)
  have hDpos : 0 < D := by
    simpa [D] using typeIOddRankSignDen_pos r hr
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hfac_pos : 0 < L.massLocalFactor 2 :=
    massLocalFactor_pos L 2
  have hfac_ne : L.massLocalFactor 2 ≠ 0 := ne_of_gt hfac_pos
  have hAne : A ≠ 0 := by
    intro hA
    have hzero : L.massLocalFactor 2 = 0 := by
      rw [hlocal]
      simp [A, hA]
    exact hfac_ne hzero
  refine ordinaryGenusMass_oddRank_eq_typeIConstant_of_dyadic hr L hL ?_
  rw [massPartialPrimeInverseProduct_two]
  change (L.massLocalFactor 2)⁻¹ * A = D
  rw [hlocal]
  change (A / D)⁻¹ * A = D
  field_simp [hAne, hDne]

/-- Conditional final even-rank, odd half-rank Type I ordinary genus mass
formula, stated with an explicit value of the native dyadic local factor. -/
theorem ordinaryGenusMass_evenRank_oddHalf_eq_typeIConstant_of_localFactor
    {k : ℕ} (hk : k ≠ 0) (L : PositiveDefiniteIntegralLattice (2 * (2 * k + 1)))
    (hL : L.IsUnimodular)
    (hlocal :
      L.massLocalFactor 2 =
        ((4 : ℝ) *
          ((Finset.Icc 1 (2 * k + 1 - 1)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2))) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) =
      (typeIConstant (2 * (2 * k + 1)) : ℝ) := by
  let A : ℝ :=
    ((4 : ℝ) *
      ((Finset.Icc 1 (2 * k + 1 - 1)).prod
        (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
        (4 : ℝ) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2))
  have hfac_pos : 0 < L.massLocalFactor 2 :=
    massLocalFactor_pos L 2
  have hfac_ne : L.massLocalFactor 2 ≠ 0 := ne_of_gt hfac_pos
  have hlocal' :
      L.massLocalFactor 2 =
        ((4 : ℝ) *
          ((Finset.Icc 1 (2 * k)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ ((2 * k + 1) * (2 * k) / 2)) := by
    simpa using hlocal
  refine ordinaryGenusMass_evenRank_oddHalf_eq_typeIConstant_of_dyadic hk L hL ?_
  rw [massPartialPrimeInverseProduct_two]
  change (L.massLocalFactor 2)⁻¹ * A = 1
  dsimp [A]
  rw [← hlocal']
  exact inv_mul_cancel₀ hfac_ne

/-- Conditional final even-rank, even half-rank Type I ordinary genus mass
formula, stated with an explicit value of the native dyadic local factor. -/
theorem ordinaryGenusMass_evenRank_evenHalf_eq_typeIConstant_of_localFactor
    {m : ℕ} (hm_one : 1 < m) (hm_even : Even m) (L : PositiveDefiniteIntegralLattice (2 * m))
    (hL : L.IsUnimodular)
    (hlocal :
      L.massLocalFactor 2 =
        ((4 : ℝ) * (2 : ℝ) ^ (m - 1) *
          ((Finset.Icc 1 (m - 1)).prod
            (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
            (4 : ℝ) ^ (m * (m - 1) / 2) /
          (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ))) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = (typeIConstant (2 * m) : ℝ) := by
  let A : ℝ :=
    ((4 : ℝ) * (2 : ℝ) ^ (m - 1) *
      ((Finset.Icc 1 (m - 1)).prod
        (fun j => (2 : ℝ) ^ (2 * j) - 1)) /
        (4 : ℝ) ^ (m * (m - 1) / 2))
  let D : ℝ := (((2 : ℚ) ^ (m - 1) + typeIEvenRankSign (2 * m) : ℚ) : ℝ)
  have hDpos : 0 < D := by
    simpa [D] using typeIEvenRankSignDen_pos m hm_one
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hfac_pos : 0 < L.massLocalFactor 2 :=
    massLocalFactor_pos L 2
  have hfac_ne : L.massLocalFactor 2 ≠ 0 := ne_of_gt hfac_pos
  have hAne : A ≠ 0 := by
    intro hA
    have hzero : L.massLocalFactor 2 = 0 := by
      rw [hlocal]
      simp [A, hA]
    exact hfac_ne hzero
  refine ordinaryGenusMass_evenRank_evenHalf_eq_typeIConstant_of_dyadic hm_one hm_even L hL ?_
  rw [massPartialPrimeInverseProduct_two]
  change (L.massLocalFactor 2)⁻¹ * A = D
  rw [hlocal]
  change (A / D)⁻¹ * A = D
  field_simp [hAne, hDne]

end PositiveDefiniteIntegralLattice

end
