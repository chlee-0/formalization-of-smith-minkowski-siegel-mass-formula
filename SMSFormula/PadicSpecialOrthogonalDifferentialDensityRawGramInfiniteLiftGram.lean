import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRawGramInfiniteLiftLimit

/-!
# Gram preservation by the p-adic limit of a raw Gram branch

Every finite value of a compatible raw branch satisfies the complete Gram
congruence at its own depth.  The certified residue theorem for the entrywise
p-adic limit transports this equation literally to `ZMod (p^(k+r))`.  Casting
a deeper equation down to an arbitrary exponent and applying
`PadicInt.ext_of_toZModPow` then gives the exact Gram identity over `PadicInt`.

No determinant, invertibility, or stabilizer-membership conclusion is made in
this module.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- At every branch depth, the complete Gram equation for the p-adic limit
maps to the literal raw Gram equation stored by that branch value. -/
theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.map_toZModPow_padicLimit_preserves_gram
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X)
    (r : ℕ) :
    (C.padicLimit.transpose * L.polarGramMatrix_padic p * C.padicLimit).map
        (PadicInt.toZModPow (k + r)) =
      (L.polarGramMatrix_padic p).map (PadicInt.toZModPow (k + r)) := by
  have hX := C.map_toZModPow_padicLimit r
  have hG :
      (L.polarGramMatrix_padic p).map (PadicInt.toZModPow (k + r)) =
        matrixMod L.polarGramMatrix (primePowModulus p (k + r)) := by
    ext i j
    simp [polarGramMatrix_padic, matrixMod, primePowModulus] <;> rfl
  have hraw :=
    (mem_gramCongruenceSolutionMatrices_iff).1 (C.value r).2
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hX, hG]
  exact hraw

/-- The entrywise p-adic limit of an infinite compatible complete raw branch
preserves the associated-bilinear Gram matrix exactly over `PadicInt`. -/
theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.padicLimit_preserves_gram
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X) :
    C.padicLimit.transpose * L.polarGramMatrix_padic p * C.padicLimit =
      L.polarGramMatrix_padic p := by
  ext i j
  apply PadicInt.ext_of_toZModPow.mp
  intro m
  have hdeep := C.map_toZModPow_padicLimit_preserves_gram m
  have hentry := congrFun (congrFun hdeep i) j
  have hle : m ≤ k + m := by omega
  let f : ZMod (p ^ (k + m)) →+* ZMod (p ^ m) :=
    ZMod.castHom (pow_dvd_pow p hle) _
  calc
    PadicInt.toZModPow m
        ((C.padicLimit.transpose * L.polarGramMatrix_padic p * C.padicLimit) i j) =
        f (PadicInt.toZModPow (k + m)
          ((C.padicLimit.transpose * L.polarGramMatrix_padic p * C.padicLimit) i j)) := by
            symm
            exact PadicInt.cast_toZModPow m (k + m) hle _
    _ = f (PadicInt.toZModPow (k + m) (L.polarGramMatrix_padic p i j)) :=
      congrArg f hentry
    _ = PadicInt.toZModPow m (L.polarGramMatrix_padic p i j) :=
      PadicInt.cast_toZModPow m (k + m) hle _

end PositiveDefiniteIntegralLattice
