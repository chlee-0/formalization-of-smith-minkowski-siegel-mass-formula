import SMSFormula.Applications.Unimodular.DyadicTypeI
import SMSFormula.RationalAdeleFiniteLocalResidueCount
import SMSFormula.StandardAxiomsGuard

noncomputable section
open Matrix BigOperators PositiveDefiniteIntegralLattice UnimodularMass

namespace StableIdentityComparisonSeedNativeAdapter

lemma two_mul_zmodFourLiftToZModEight_sub_intCast (a : ℤ) :
    (2 : ZMod 8) * (zmodFourLiftToZModEight (a : ZMod 4) - (a : ZMod 8)) = 0 := by
  rw [mul_sub, two_mul_zmodFourLiftToZModEight_intCast]
  norm_num

lemma zmod_eight_mul_eq_zero_of_two_mul_eq_zero (a b : ZMod 8)
    (ha : (2 : ZMod 8) * a = 0) (hb : (2 : ZMod 8) * b = 0) :
    a * b = 0 := by
  revert ha hb
  fin_cases a <;> fin_cases b <;> decide

lemma zmodFourLiftToZModEight_sub_intCast_mul_sub_intCast (a b : ℤ) :
    (zmodFourLiftToZModEight (a : ZMod 4) - (a : ZMod 8)) *
      (zmodFourLiftToZModEight (b : ZMod 4) - (b : ZMod 8)) = 0 := by
  exact zmod_eight_mul_eq_zero_of_two_mul_eq_zero _ _
    (two_mul_zmodFourLiftToZModEight_sub_intCast a)
    (two_mul_zmodFourLiftToZModEight_sub_intCast b)

lemma zmodQuadForm_lift_intCast_eq {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℤ) :
    L.zmodQuadForm 8 (fun i => zmodFourLiftToZModEight (x i : ZMod 4)) =
      L.zmodQuadForm 8 (fun i => (x i : ZMod 8)) := by
  classical
  let a : Fin n → ZMod 8 := fun i => (x i : ZMod 8)
  let d : Fin n → ZMod 8 := fun i => zmodFourLiftToZModEight (x i : ZMod 4) - a i
  have hlift : (fun i => zmodFourLiftToZModEight (x i : ZMod 4)) = fun i => a i + d i := by
    funext i
    simp [a, d]
  have htwo : ∀ i, (2 : ZMod 8) * d i = 0 := by
    intro i
    simpa [d, a] using two_mul_zmodFourLiftToZModEight_sub_intCast (x i)
  have hdd : ∀ i j, d i * d j = 0 := by
    intro i j
    simpa [d, a] using zmodFourLiftToZModEight_sub_intCast_mul_sub_intCast (x i) (x j)
  have hcross_swap :
      (∑ i, ∑ j, a i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * d j) =
        ∑ i, ∑ j, d i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * a j := by
    calc
      (∑ i, ∑ j, a i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * d j)
          = ∑ j, ∑ i, a i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * d j := by
            rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, a j * ((L.pairingMatrix j i : ℤ) : ZMod 8) * d i := by
            rfl
      _ = ∑ i, ∑ j, d i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * a j := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            have hs : L.pairingMatrix j i = L.pairingMatrix i j := by
              simpa using (L.form_symm.apply j i).symm
            rw [hs]
            ring
  have hcross :
      (∑ i, ∑ j, d i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * a j) +
        (∑ i, ∑ j, a i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * d j) = 0 := by
    rw [hcross_swap]
    rw [← two_mul]
    rw [show (2 : ZMod 8) * (∑ i, ∑ j, d i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * a j) =
        ∑ i, ∑ j, (2 : ZMod 8) * d i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * a j by
      simp [Finset.mul_sum]
      ring_nf]
    simp [htwo]
  have hddsum :
      (∑ i, ∑ j, d i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * d j) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    refine Finset.sum_eq_zero ?_
    intro j _
    have h := hdd i j
    calc
      d i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * d j =
          ((L.pairingMatrix i j : ℤ) : ZMod 8) * (d i * d j) := by ring
      _ = 0 := by rw [h]; ring
  rw [hlift]
  unfold PositiveDefiniteIntegralLattice.zmodQuadForm
  calc
    (∑ i, ∑ j,
        (a i + d i) * ((L.pairingMatrix i j : ℤ) : ZMod 8) * (a j + d j)) =
        (∑ i, ∑ j, a i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * a j) +
        ((∑ i, ∑ j, d i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * a j) +
        (∑ i, ∑ j, a i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * d j)) +
        (∑ i, ∑ j, d i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * d j) := by
          simp only [add_mul, mul_add, Finset.sum_add_distrib]
          ring
    _ = ∑ i, ∑ j, a i * ((L.pairingMatrix i j : ℤ) : ZMod 8) * a j := by
          rw [hcross, hddsum]
          ring

#assert_standard_axioms zmodQuadForm_lift_intCast_eq

end StableIdentityComparisonSeedNativeAdapter
