import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRawGramInfiniteLiftUnit
import SMSFormula.LocalOrthogonalHaar

/-!
# Stabilizer represented by an infinite compatible raw Gram branch

This module packages the unit p-adic limit of an arbitrary infinite compatible
complete raw Gram branch as an element of the integral local lattice
stabilizer.  Its finite reductions are proved to be exactly the stored branch
values.  Consequently an infinite branch at the selected density depth is
equivalent to the existing full-initial stabilizer-lift predicate.

No cardinality or local gauge identity is asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

open Matrix

variable {n : ℕ}

/-- The p-adic limit of an infinite compatible raw Gram branch as an integral
general-linear element. -/
noncomputable def LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.padicLimitIntegralGL
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X) :
    GL (Fin n) ℤ_[p] :=
  C.isUnit_padicLimit.unit

@[simp] theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.padicLimitIntegralGL_val
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X) :
    C.padicLimitIntegralGL.1 = C.padicLimit := by
  exact IsUnit.unit_spec _

/-- The p-adic limit unit, mapped to the p-adic field and equipped with its
exact form equation, is an element of the integral local lattice stabilizer. -/
noncomputable def LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.padicLimitStabilizer
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X) :
    L.localPadicLatticeStabilizerSubgroup p := by
  let U : GL (Fin n) ℤ_[p] := C.padicLimitIntegralGL
  let Up : GL (Fin n) ℚ_[p] :=
    Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U
  have hformZ :
      U.1.transpose * L.pairingMatrix_padic p * U.1 = L.pairingMatrix_padic p := by
    simpa [U] using C.padicLimit_preserves_form
  have hformQ :
      Up.1.transpose * L.localPadicFormMatrix p * Up.1 =
        L.localPadicFormMatrix p := by
    have hmap := congrArg
      (RingHom.mapMatrix PadicInt.Coe.ringHom) hformZ
    change
      ((U.1.transpose * L.pairingMatrix_padic p * U.1).map
        PadicInt.Coe.ringHom) =
        (L.pairingMatrix_padic p).map PadicInt.Coe.ringHom at hmap
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
    simpa [Up, localPadicFormMatrix, pairingMatrix_padicField] using hmap
  let g : L.ConcreteLocalPadicOrthogonalGroup p := ⟨Up, hformQ⟩
  refine ⟨g, ?_⟩
  rw [L.mem_localPadicLatticeStabilizerSubgroup_iff p]
  constructor
  · intro i j
    change Up.1 i j ∈ PadicInt.subring p
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact (U.1 i j).property
  · intro i j
    change (Up⁻¹).1 i j ∈ PadicInt.subring p
    rw [show Up⁻¹ = Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom (U⁻¹) by
      simp [Up]]
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact ((U⁻¹).1 i j).property

/-- Recovering the integral general-linear realization of the constructed
stabilizer gives the original p-adic limit matrix literally. -/
@[simp] theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.integralGL_padicLimitStabilizer_val
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X) :
    (L.localPadicLatticeStabilizerIntegralGL p C.padicLimitStabilizer).1 =
      C.padicLimit := by
  ext i j
  apply PadicInt.ext
  change
    ((Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom
      C.padicLimitIntegralGL).1 i j) =
      ((C.padicLimit i j : ℤ_[p]) : ℚ_[p])
  rw [Matrix.GeneralLinearGroup.map_apply]
  congr 1

/-- Reduction of the constructed stabilizer at depth `k+r` is exactly the raw
Gram solution stored at height `r` of the branch. -/
theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.stabilizerReduction_val
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X)
    (r : ℕ) :
    (L.localPadicLatticeStabilizerReduction p (k + r)
      C.padicLimitStabilizer).1 = (C.value r).1 := by
  change
    (L.localPadicLatticeStabilizerIntegralGL p
      C.padicLimitStabilizer).1.map (PadicInt.toZModPow (k + r)) = _
  rw [C.integralGL_padicLimitStabilizer_val]
  exact C.map_toZModPow_padicLimit r

/-- At the base depth, the constructed stabilizer reduction recovers the
prescribed complete raw Gram solution. -/
theorem LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.stabilizerReduction_base_val
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X) :
    (L.localPadicLatticeStabilizerReduction p k C.padicLimitStabilizer).1 =
      X.1 := by
  have h := C.stabilizerReduction_val 0
  simpa only [Nat.add_zero, C.value_zero] using h

/-- An infinite compatible branch at the selected density depth supplies a
full-initial-value integral stabilizer lift of its prescribed base solution. -/
theorem hasFullInitialRawGramLift_of_infiniteLiftChain
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p)
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) X) :
    L.HasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift
      p X :=
  ⟨C.padicLimitStabilizer, C.stabilizerReduction_base_val⟩

/-- Full-initial-value stabilizer lifting is equivalent exactly to existence
of one coherent infinite compatible raw Gram branch above the selected base. -/
theorem hasFullInitialRawGramLift_iff_nonempty_infiniteLiftChain
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p) :
    L.HasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift p X ↔
      Nonempty
        (L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) X) := by
  constructor
  · intro hX
    exact
      ⟨L.localPadicSpecialOrthogonalRawGramInfiniteLiftChainOfFullInitialRawGramLift
        p X hX⟩
  · rintro ⟨C⟩
    exact L.hasFullInitialRawGramLift_of_infiniteLiftChain p X C

end PositiveDefiniteIntegralLattice
