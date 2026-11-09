import SMSFormula.RationalSpecialOrthogonalMassFormula
import SMSFormula.Final
import SMSFormula.IntegralQuadraticFormFinal
import SMSFormula.IntegralQuadraticFormExplicitFinal
import SMSFormula.Applications.Unimodular.TypeITotalMass
import SMSFormula.Applications.Unimodular.TypeIITotalMass
import SMSFormula.MathlibMassFormula
import SMSFormula.StandardAxiomsGuard

/-!
# Main results: public index

This module is the entry point for readers and downstream projects.  It
imports the modules containing the main theorems, restates each of them with
its full signature (so that a change of hypotheses, normalization or
conclusion breaks this file), and checks that each depends only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Positive-definite integral lattices

`PositiveDefiniteIntegralLattice n` presents a positive-definite integral bilinear
lattice on the based module `ℤⁿ`. Its pairing matrix is G and its norm is
`q(x) = b(x,x)`. Its polar form has matrix 2G.

* `ordinaryGenusMass L = ∑_{[L'] ∈ genus(L)} 1 / |O(L')|`.
* `massLocalFactor L p` is the normalized local density
  `α_p(L) = normalizedLocalDensity L p`.  At any exponent `k` beyond
  `localDensityHenselExponent L p` it equals
  `½ · |2|_p^{-n} · |det(2F)|_p^{(1-n)/2} · p^{-k n(n-1)/2} · A_k`,
  where `A_k = associatedBilinearDualQuotientCount L p k` counts solutions of
  the self-representation congruence of `q` modulo the quotient by `p^k L^#`
  (`L^#` the dual for the polar form `2F`).  This is the normalization of
  R. Schulze-Pillot's survey of the mass formula
  (`normalizedLocalDensity_eq_associatedBilinearDualQuotientCount`).
  `massLocalInverseFactor L p = α_p(L)⁻¹`.
* `massPartialPrimeInverseProduct L N = ∏_{p ≤ N} α_p(L)⁻¹`, and
  `massLocalInverseProductTendsTo L P` says these partial products tend to `P`.
* `archimedeanMassFactor n = 2 π^{-n(n+1)/4} ∏_{j=1}^{n} Γ(j/2)`.
* `massFormulaProductSide L P = archimedeanMassFactor n * P`.

`PositiveDefiniteIntegralLattice.exists_massFormula_positiveRank` is the
mass theorem for every `1 ≤ n`. It produces one `P > 0` such that the partial
products over increasing primes tend to `P` and
`ordinaryGenusMass L = c(n) * (archimedeanMassFactor n * P)`, where
`c(n) = positiveRankMassCorrection n` is `1/2` when `n = 1` and `1` otherwise.
`exists_massFormula_of_two_le` gives the uncorrected classical formula
for every `2 ≤ n`. At rank one the limit `P` and the ordinary mass are both
`1/2`, while `archimedeanMassFactor 1` is two, so the uncorrected formula is
false at rank one. Rank zero is outside this theorem.
No unordered or absolute convergence is asserted.

`ordinaryGenusMass_eq_massFormulaProductSide` states the formula for
`n ≥ 3`. The explicit odd/even rank forms hold in their stated ranges and
insert the closed zeta/Dirichlet Euler tails after a
cutoff N containing every bad prime (`massBadPrimeSet L`).

## Integer-valued quadratic forms

`PositiveDefiniteIntegralQuadraticForm n` presents an integer-valued quadratic
form on `ℤ^n` by its integral polar matrix A with even diagonal. Its rational
quadratic matrix is A/2. Its `ordinaryGenusMass` is the direct full-O Q-class
sum. The comparison with the mass of `latticeOfPolarForm`, whose norm is 2Q,
is proved separately. `transportedOrdinaryGenusMass` records that comparison
explicitly. The main theorem uses the direct class sum.

## Unimodular lattices

`IsUnimodular L` means `pairingDeterminant L = 1` (so the polar discriminant is `2ⁿ`).
`HasOddNorm L` (some `q(x)` is odd) and `HasEvenNorms L` (all `q(x)` are even)
are parity predicates only; Type I/II unimodular means `IsUnimodular` together
with the respective parity predicate.  `totalTypeIClassMass n` and
`totalTypeIIClassMass n` sum `1/|O(L)|` over all isometry classes of Type I and
Type II unimodular lattices of rank `n`; they equal the explicit Bernoulli
constants `typeIConstant n` and `typeIIConstant n` in every rank.

## Worked examples

The modules under `SMSFormula.Applications.Examples` prove
`MassFormulaReleaseExamples.a2_intrinsic_ordinaryGenusMass`
(`1/12`, intrinsic integral-Q class sum),
`MassFormulaReleaseExamples.ternary_ordinaryGenusMass` (`3/8`, ordinary
full-O mass) and
`MassFormulaReleaseExamples.a4_intrinsic_ordinaryGenusMass` (`1/240`, intrinsic
integral-Q class sum). They are not imported by this index. Their intrinsic
genus comparison is separate from the transported mass interface.
-/

noncomputable section

open UnimodularMass

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## All positive ranks: the main theorem and its specializations -/

example (L : PositiveDefiniteIntegralLattice n) (hn : 1 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ L.massLocalInverseProductTendsTo P ∧
      ((L.ordinaryGenusMass : ℚ) : ℝ) =
        positiveRankMassCorrection n * (archimedeanMassFactor n * P) :=
  exists_massFormula_positiveRank L hn

example (L : PositiveDefiniteIntegralLattice n) (hn : 2 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ L.massLocalInverseProductTendsTo P ∧
      ((L.ordinaryGenusMass : ℚ) : ℝ) = archimedeanMassFactor n * P :=
  exists_massFormula_of_two_le L hn

example (L : PositiveDefiniteIntegralLattice 1) :
    L.massLocalInverseProductTendsTo (1 / 2 : ℝ) ∧
      ((L.ordinaryGenusMass : ℚ) : ℝ) =
        positiveRankMassCorrection 1 * (archimedeanMassFactor 1 * (1 / 2 : ℝ)) :=
  massFormula_positiveRank_rank_one L

example (L : PositiveDefiniteIntegralLattice n) (hn : 1 ≤ n) {P : ℝ}
    (hconv : L.massLocalInverseProductTendsTo P) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) =
      positiveRankMassCorrection n * (archimedeanMassFactor n * P) :=
  ordinaryGenusMass_eq_positiveRankMassFormula L hn hconv

example : positiveRankMassCorrection 1 = 1 / 2 := positiveRankMassCorrection_one

example (hn : 2 ≤ n) : positiveRankMassCorrection n = 1 :=
  positiveRankMassCorrection_of_two_le hn

#assert_standard_axioms exists_massFormula_positiveRank
#assert_standard_axioms exists_massFormula_of_two_le
#assert_standard_axioms massFormula_positiveRank_rank_one
#assert_standard_axioms ordinaryGenusMass_eq_positiveRankMassFormula
#assert_standard_axioms ordinaryGenusMass_eq_massFormula_of_two_le
#assert_standard_axioms not_exists_massLocalInverseProductTendsTo_and_ordinaryGenusMass_rank_one

/-! ## Definitions and their normalizations -/

example (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    massFormulaProductSide L P = archimedeanMassFactor n * P := rfl

example :
    archimedeanMassFactor n =
      2 * Real.rpow Real.pi (-((n : ℝ) * ((n : ℝ) + 1) / 4)) *
        (Finset.range n).prod (fun j => Real.Gamma (((j + 1 : ℕ) : ℝ) / 2)) := rfl

example (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    massLocalInverseProductTendsTo L P ↔
      Filter.Tendsto (fun N : ℕ => massPartialPrimeInverseProduct L N)
        Filter.atTop (nhds P) := Iff.rfl

example (L : PositiveDefiniteIntegralLattice n) (N : ℕ) :
    massPartialPrimeInverseProduct L N =
      (rationalPrimesUpTo N).prod (fun p => massLocalInverseFactorAtPrime L p) := rfl

example (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    massLocalInverseFactor L p = (normalizedLocalDensity L p)⁻¹ := rfl

example (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k) :
    normalizedLocalDensity L p =
      (((1 / 2 : ℚ) * twoPadicNormInvPow p n *
        ((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        (associatedBilinearDualQuotientCount L p k : ℚ) : ℚ) : ℝ) *
        gramDetPadicNormFactor L p :=
  normalizedLocalDensity_eq_associatedBilinearDualQuotientCount L p k hk

example (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    gramDetPadicNormFactor L p = ‖(L.polarDeterminant : ℤ_[p])‖ ^ (((1 : ℝ) - (n : ℝ)) / 2) := rfl

example (p : ℕ) : twoPadicNormInvPow p n = if p = 2 then (2 : ℚ) ^ n else 1 := rfl

example (L : PositiveDefiniteIntegralLattice n) :
    L.ordinaryGenusMass =
      ∑ C : L.genus,
        ((Fintype.card (genusClassRepresentative L C).IsometryGroup : ℚ)⁻¹) := rfl

/-! ## The mass formula for positive-definite integral lattices -/

example (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) = massFormulaProductSide L P :=
  ordinaryGenusMass_eq_massFormulaProductSide L hn hP hconv

example (L : PositiveDefiniteIntegralLattice n) (hn3 : 3 ≤ n) {N s : ℕ}
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s - 1) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) =
      massFormulaProductSide L (oddRankOrdinaryMassProductLimit L N s) :=
  ordinaryGenusMass_eq_massFormulaProductSide_oddRankProductLimit L hn3 hB hs hn

example (L : PositiveDefiniteIntegralLattice n) (hn3 : 3 ≤ n) {N s : ℕ}
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N) (hn : n = 2 * s) :
    ((L.ordinaryGenusMass : ℚ) : ℝ) =
      massFormulaProductSide L (evenRankOrdinaryMassProductLimit L N s) :=
  ordinaryGenusMass_eq_massFormulaProductSide_evenRankProductLimit L hn3 hB hn

#assert_standard_axioms ordinaryGenusMass_eq_massFormulaProductSide
#assert_standard_axioms ordinaryGenusMass_eq_massFormulaProductSide_ENNReal
#assert_standard_axioms ordinaryGenusMass_eq_massFormulaProductSide_oddRankProductLimit
#assert_standard_axioms ordinaryGenusMass_eq_massFormulaProductSide_evenRankProductLimit

/-! ## Unimodular lattices -/

example (L : PositiveDefiniteIntegralLattice n) : L.IsUnimodular ↔ L.pairingDeterminant = 1 := Iff.rfl

example (L : PositiveDefiniteIntegralLattice n) :
    L.HasOddNorm ↔ ∃ x : Fin n → ℤ, Odd (L.quadForm x) := Iff.rfl

example (L : PositiveDefiniteIntegralLattice n) :
    L.HasEvenNorms ↔ ∀ x : Fin n → ℤ, Even (L.quadForm x) := Iff.rfl

example (L : PositiveDefiniteIntegralLattice n) (hU : L.IsUnimodular) (hI : L.HasOddNorm) :
    L.IsSameGenus (identityLattice n) :=
  isSameGenus_identity_of_typeIUnimodular L hU hI

example (k : ℕ) (hk : 0 < k) (L : PositiveDefiniteIntegralLattice (8 * k))
    (hU : L.IsUnimodular) (hII : L.HasEvenNorms) :
    L.IsSameGenus (typeIISeed k) :=
  isSameGenus_typeIISeed_of_typeIIUnimodular k hk L hU hII

example (n : ℕ) : totalTypeIClassMass n = typeIConstant n :=
  totalTypeIClassMass_eq_typeIConstant

example (n : ℕ) : totalTypeIIClassMass n = typeIIConstant n :=
  totalTypeIIClassMass_eq_typeIIConstant n

#assert_standard_axioms isSameGenus_identity_of_typeIUnimodular
#assert_standard_axioms isSameGenus_typeIISeed_of_typeIIUnimodular
#assert_standard_axioms totalTypeIClassMass_eq_typeIConstant
#assert_standard_axioms totalTypeIClassMass_real_eq_typeIConstant
#assert_standard_axioms totalTypeIIClassMass_eq_typeIIConstant
#assert_standard_axioms totalTypeIIClassMass_real_eq_typeIIConstant

end PositiveDefiniteIntegralLattice

/-! ## Positive-definite integer-valued quadratic forms -/

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ}

example (H : PositiveDefiniteIntegralQuadraticForm n) :
    H.ordinaryGenusMass = H.latticeOfPolarForm.ordinaryGenusMass :=
  H.ordinaryGenusMass_eq_latticeOfPolarForm

example (H : PositiveDefiniteIntegralQuadraticForm n) (hn : 1 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ H.massLocalInverseProductTendsTo P ∧
      ((H.ordinaryGenusMass : ℚ) : ℝ) =
        PositiveDefiniteIntegralLattice.positiveRankMassCorrection n *
          (PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P) :=
  H.exists_massFormula_positiveRank hn

example (H : PositiveDefiniteIntegralQuadraticForm n) (hn : 2 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ H.massLocalInverseProductTendsTo P ∧
      ((H.ordinaryGenusMass : ℚ) : ℝ) = PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P :=
  H.exists_massFormula_of_two_le hn

#assert_standard_axioms exists_massFormula_positiveRank
#assert_standard_axioms exists_massFormula_of_two_le

example (H : PositiveDefiniteIntegralQuadraticForm n) (hn : 3 ≤ n) {P : ℝ} (hP : 0 < P)
    (hconv : H.massLocalInverseProductTendsTo P) :
    ((H.transportedOrdinaryGenusMass : ℚ) : ℝ) = H.massFormulaProductSide P :=
  H.transportedOrdinaryGenusMass_eq_massFormulaProductSide hn hP hconv

#assert_standard_axioms transportedOrdinaryGenusMass_eq_massFormulaProductSide
#assert_standard_axioms transportedOrdinaryGenusMass_eq_massFormulaProductSide_ENNReal
#assert_standard_axioms transportedOrdinaryGenusMass_eq_massFormulaProductSide_oddRankProductLimit
#assert_standard_axioms transportedOrdinaryGenusMass_eq_massFormulaProductSide_evenRankProductLimit

end PositiveDefiniteIntegralQuadraticForm

/-! ## Mathlib quadratic forms

The same theorems for `Q : QuadraticForm ℤ (Fin n → ℤ)` with `Q.PosDef`
(`SMSFormula.MathlibQuadraticForm`, `SMSFormula.MathlibMassFormula`). The mass of `Q` is the
direct Q-genus class sum with full-O weights. The polarization comparison is
proved separately. -/

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ}

example (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    massOfQuadraticForm Q hQ = (ofQuadraticForm Q hQ).ordinaryGenusMass := rfl

example (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    massOfQuadraticForm Q hQ = (ofQuadraticForm Q hQ).transportedOrdinaryGenusMass :=
  massOfQuadraticForm_eq_transportedOrdinaryGenusMass Q hQ

example (hn : 1 ≤ n) (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    ∃ P : ℝ, 0 < P ∧ (ofQuadraticForm Q hQ).massLocalInverseProductTendsTo P ∧
      ((massOfQuadraticForm Q hQ : ℚ) : ℝ) =
        PositiveDefiniteIntegralLattice.positiveRankMassCorrection n *
          (PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P) :=
  exists_massOfQuadraticForm_eq_positiveRank hn Q hQ

example (hn : 2 ≤ n) (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    ∃ P : ℝ, 0 < P ∧ (ofQuadraticForm Q hQ).massLocalInverseProductTendsTo P ∧
      ((massOfQuadraticForm Q hQ : ℚ) : ℝ) = PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P :=
  exists_massOfQuadraticForm_eq_of_two_le hn Q hQ

example (Q : QuadraticForm ℤ (Fin 1 → ℤ)) (hQ : Q.PosDef) :
    massOfQuadraticForm Q hQ = (1 / 2 : ℚ) := massOfQuadraticForm_eq_one_half_rank_one Q hQ

#assert_standard_axioms exists_massOfQuadraticForm_eq_positiveRank
#assert_standard_axioms exists_massOfQuadraticForm_eq_of_two_le
#assert_standard_axioms massOfQuadraticForm_eq_positiveRank
#assert_standard_axioms massOfQuadraticForm_eq_of_two_le
#assert_standard_axioms massOfQuadraticForm_eq_one_half_rank_one

example (hn : 3 ≤ n) (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    ∃ P : ℝ, 0 < P ∧ (ofQuadraticForm Q hQ).massLocalInverseProductTendsTo P ∧
      ((massOfQuadraticForm Q hQ : ℚ) : ℝ) = PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P :=
  exists_massOfQuadraticForm_eq hn Q hQ

example (L : PositiveDefiniteIntegralLattice n) :
    massOfQuadraticForm L.quadraticForm L.quadraticForm_posDef = L.ordinaryGenusMass :=
  massOfQuadraticForm_integralLattice L

#assert_standard_axioms equivQuadraticForm
#assert_standard_axioms exists_massOfQuadraticForm_eq
#assert_standard_axioms massOfQuadraticForm_eq_oddRankProductLimit
#assert_standard_axioms massOfQuadraticForm_eq_evenRankProductLimit
#assert_standard_axioms massOfQuadraticForm_integralLattice

end PositiveDefiniteIntegralQuadraticForm

namespace PositiveDefiniteIntegralLattice

open UnimodularMass

variable {n : ℕ}

example (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) (hev : IsClassicallyIntegral Q)
    (hdet : (halfPolarMatrix Q).det = 1) (hodd : ∃ x, Odd (Q x)) :
    (ofQuadraticForm Q hQ hev).IsSameGenus (identityLattice n) :=
  isSameGenus_identity_of_quadraticForm Q hQ hev hdet hodd

example (n : ℕ) :
    ∑ C : UnimodularTypeIIsometryClass n,
        ((Nat.card ((typeIClassRepresentative C).quadraticForm.IsometryEquiv
          (typeIClassRepresentative C).quadraticForm) : ℚ)⁻¹) = typeIConstant n :=
  sum_isometryEquiv_typeI_eq_typeIConstant n

#assert_standard_axioms equivQuadraticForm
#assert_standard_axioms isGlobalIsometry_iff_equivalent
#assert_standard_axioms natCard_isometryGroup
#assert_standard_axioms isSameGenus_identity_of_quadraticForm
#assert_standard_axioms isSameGenus_typeIISeed_of_quadraticForm
#assert_standard_axioms sum_isometryEquiv_typeI_eq_typeIConstant
#assert_standard_axioms sum_isometryEquiv_typeII_eq_typeIIConstant

end PositiveDefiniteIntegralLattice

/-! Axioms of the main theorems (checked above; printed here for the build log). -/

#print axioms PositiveDefiniteIntegralLattice.exists_massFormula_positiveRank
#print axioms PositiveDefiniteIntegralLattice.exists_massFormula_of_two_le
#print axioms PositiveDefiniteIntegralLattice.massFormula_positiveRank_rank_one
#print axioms PositiveDefiniteIntegralQuadraticForm.exists_massFormula_positiveRank
#print axioms PositiveDefiniteIntegralQuadraticForm.exists_massOfQuadraticForm_eq_positiveRank
#print axioms PositiveDefiniteIntegralQuadraticForm.exists_massOfQuadraticForm_eq_of_two_le
#print axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_massFormulaProductSide
#print axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_massFormulaProductSide_oddRankProductLimit
#print axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_massFormulaProductSide_evenRankProductLimit
#print axioms PositiveDefiniteIntegralQuadraticForm.transportedOrdinaryGenusMass_eq_massFormulaProductSide
#print axioms PositiveDefiniteIntegralLattice.isSameGenus_identity_of_typeIUnimodular
#print axioms PositiveDefiniteIntegralLattice.isSameGenus_typeIISeed_of_typeIIUnimodular
#print axioms PositiveDefiniteIntegralLattice.totalTypeIClassMass_eq_typeIConstant
#print axioms PositiveDefiniteIntegralLattice.totalTypeIIClassMass_eq_typeIIConstant
#print axioms PositiveDefiniteIntegralQuadraticForm.exists_massOfQuadraticForm_eq
#print axioms PositiveDefiniteIntegralQuadraticForm.massOfQuadraticForm_integralLattice
#print axioms PositiveDefiniteIntegralLattice.isSameGenus_identity_of_quadraticForm
#print axioms PositiveDefiniteIntegralLattice.isSameGenus_typeIISeed_of_quadraticForm
#print axioms PositiveDefiniteIntegralLattice.sum_isometryEquiv_typeI_eq_typeIConstant
#print axioms PositiveDefiniteIntegralLattice.sum_isometryEquiv_typeII_eq_typeIIConstant

end
