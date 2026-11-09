import SMSFormula.RationalCliffordGeneralSpinLatticePadicSimilitude
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorNormUnitValued

/-!
# Exact good-place integral spinor-norm image

At every completed odd-unimodular lattice place, the existing constructive
lower bound gives two integral spinor classes and integral Cartan--Dieudonne
puts the whole image inside the two unit square classes.  Equality of these
finite subgroups records the precise integral input needed to assemble local
general-Spin similitude lifts cofinally.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance integralGeneralSpinRangePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance integralGeneralSpinRangeSquareClassGroup
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Group (Rat.SquareClass ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :=
  (QuotientGroup.Quotient.commGroup
    (Subgroup.square (ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ))).toGroup

/-- Outside the explicit odd-unimodular bad set, the integral special-
orthogonal spinor-norm image is exactly the subgroup of p-adic unit square
classes. -/
theorem heightOnePadicSpecialOrthogonalIntegralSpinorNormRange_eq_padicUnitSquareClassSubgroup
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hv : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    (L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom
        v.1).range =
      Rat.padicUnitSquareClassSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
  let V := L.rationalQuadraticSpaceMatrix
  let U := Rat.padicUnitSquareClassSubgroup
    (Rat.HeightOneSpectrum.primesEquiv v.1).1
  let P :=
    V.cliffordSpinCandidateIntegralSpinorRangeGoodPlace_of_not_mem_badPlaces
      (by omega : 2 ≤ r + 2) v.1 hv
  have hle :
      (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v.1).range ≤ U :=
    P.spinorNormUnitValued
  have hcardU : Nat.card U = 2 :=
    Rat.natCard_padicUnitSquareClassSubgroup_eq_two
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 P.prime_ne_two
  letI : Finite U :=
    (Nat.card_pos_iff.mp (hcardU.symm ▸ (by norm_num : 0 < 2))).2
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hcardU]
  change 2 ≤ V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree v.1
  rw [heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_eq_two_of_not_mem_badPlaces
    L S v hv]

end PositiveDefiniteIntegralLattice
