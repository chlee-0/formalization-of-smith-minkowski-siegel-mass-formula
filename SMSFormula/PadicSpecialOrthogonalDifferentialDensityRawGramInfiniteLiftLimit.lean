import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRawGramInfiniteLiftChain

/-!
# Entrywise p-adic limits of compatible raw Gram lift chains

This module turns one infinite compatible branch of complete raw Gram
solutions into a matrix over `PadicInt`.  The construction is deliberately
entrywise: below the prescribed base depth it uses the base representative,
and from that depth onward it uses the representatives stored by the branch.
The only conclusion here is exact recovery of every finite residue.  Gram
preservation and stabilizer membership are left to later modules.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Adjacent values of a compatible raw Gram branch have standard integral
representatives congruent modulo the lower prime-power depth. -/
theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.primePow_dvd_value_succ_val_sub
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X)
    (r : ℕ) (i j : Fin n) :
    (p : ℤ) ^ (k + r) ∣
      ((C.value (r + 1)).1 i j).val - ((C.value r).1 i j).val := by
  have hval := congrArg Subtype.val (C.succReduction r)
  rw [localPadicSpecialOrthogonalRawGramSolutionSuccReduction_val] at hval
  have hij := congrFun (congrFun hval i) j
  simp only [Matrix.map_apply] at hij
  have hcast :
      (((((C.value r).1 i j).val : ℕ) : ℤ) : ZMod (p ^ (k + r))) =
        (((((C.value (r + 1)).1 i j).val : ℕ) : ℤ) :
          ZMod (p ^ (k + r))) := by
    rw [ZMod.castHom_apply] at hij
    have hnat :
        ((((C.value r).1 i j).val : ℕ) : ZMod (p ^ (k + r))) =
          ((((C.value (r + 1)).1 i j).val : ℕ) : ZMod (p ^ (k + r))) := by
      have hleft :
          ((((C.value r).1 i j).val : ℕ) : ZMod (p ^ (k + r))) =
            (C.value r).1 i j := ZMod.natCast_zmod_val _
      have hright :
          (ZMod.cast ((C.value (r + 1)).1 i j) : ZMod (p ^ (k + r))) =
            ((((C.value (r + 1)).1 i j).val : ℕ) : ZMod (p ^ (k + r))) :=
        ZMod.cast_eq_val _
      exact hleft.trans (hij.symm.trans hright)
    exact_mod_cast hnat
  exact
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      (((C.value r).1 i j).val : ℤ)
      (((C.value (r + 1)).1 i j).val : ℤ)
      (p ^ (k + r))).1 hcast

/-- The shifted standard-representative sequence attached to one entry of an
infinite raw Gram branch.  It is constant at the base representative below
depth `k`, and at depth `k+r` it is the representative of `C.value r`. -/
def LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.representativeEntry
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X)
    (i j : Fin n) (m : ℕ) : ℤ :=
  if m < k then ((X.1 i j).val : ℕ)
  else (((C.value (m - k)).1 i j).val : ℕ)

@[simp] theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.representativeEntry_add
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X)
    (i j : Fin n) (r : ℕ) :
    C.representativeEntry i j (k + r) =
      (((C.value r).1 i j).val : ℕ) := by
  have hsub : k + r - k = r := by omega
  rw [LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.representativeEntry,
    if_neg (by omega), hsub]

/-- The shifted representative sequence has the exact adjacent divisibility
required by `PadicInt.ofIntSeq`, including the transition into the base
depth. -/
theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.pow_dvd_representativeEntry_succ_sub
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X)
    (i j : Fin n) (m : ℕ) :
    (p : ℤ) ^ m ∣ C.representativeEntry i j (m + 1) -
      C.representativeEntry i j m := by
  by_cases hm : m < k
  · by_cases hms : m + 1 < k
    · simp [LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.representativeEntry,
        hm, hms]
    · have heq : m + 1 = k := by omega
      have hsub : m + 1 - k = 0 := by omega
      have hzero : (C.value 0).1 i j = X.1 i j := by
        simpa using congrFun (congrFun (congrArg Subtype.val C.value_zero) i) j
      have hzeroVal : ((C.value 0).1 i j).val = (X.1 i j).val :=
        congrArg ZMod.val hzero
      have hnext : C.representativeEntry i j (m + 1) =
          (((X.1 i j).val : ℕ) : ℤ) := by
        rw [LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.representativeEntry,
          if_neg hms, hsub, hzeroVal]
      have hcurrent : C.representativeEntry i j m =
          (((X.1 i j).val : ℕ) : ℤ) := by
        rw [LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.representativeEntry,
          if_pos hm]
      rw [hnext, hcurrent, sub_self]
      exact dvd_zero _
  · have hkm : k ≤ m := Nat.le_of_not_gt hm
    have hadd : k + (m - k) = m := by omega
    have haddSucc : k + ((m - k) + 1) = m + 1 := by omega
    have hcurrent : C.representativeEntry i j m =
        (((C.value (m - k)).1 i j).val : ℕ) := by
      have hre := C.representativeEntry_add i j (m - k)
      simpa only [hadd] using hre
    have hnext : C.representativeEntry i j (m + 1) =
        (((C.value ((m - k) + 1)).1 i j).val : ℕ) := by
      have hre := C.representativeEntry_add i j ((m - k) + 1)
      simpa only [haddSucc] using hre
    rw [hnext, hcurrent]
    have hpow := C.primePow_dvd_value_succ_val_sub (m - k) i j
    simpa only [hadd] using hpow

/-- The entrywise p-adic limit of one infinite compatible raw Gram branch. -/
noncomputable def LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.padicLimit
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X) :
    Matrix (Fin n) (Fin n) ℤ_[p] :=
  fun i j =>
    PadicInt.ofIntSeq (C.representativeEntry i j)
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
        (C.representativeEntry i j) p
        (C.pow_dvd_representativeEntry_succ_sub i j))

/-- Reduction of the entrywise p-adic limit at depth `k+r` is literally the
corresponding entry of the branch. -/
theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.toZModPow_padicLimit
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X)
    (r : ℕ) (i j : Fin n) :
    PadicInt.toZModPow (k + r) (C.padicLimit i j) =
      (C.value r).1 i j := by
  rw [LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.padicLimit]
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
    (C.representativeEntry i j) p
    (C.pow_dvd_representativeEntry_succ_sub i j) (k + r)]
  rw [C.representativeEntry_add i j r]
  exact_mod_cast ZMod.natCast_zmod_val ((C.value r).1 i j)

/-- Matrix form of exact finite-residue recovery by the p-adic branch limit. -/
theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.map_toZModPow_padicLimit
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X)
    (r : ℕ) :
    C.padicLimit.map (PadicInt.toZModPow (k + r)) = (C.value r).1 := by
  ext i j
  exact C.toZModPow_padicLimit r i j

end PositiveDefiniteIntegralLattice
