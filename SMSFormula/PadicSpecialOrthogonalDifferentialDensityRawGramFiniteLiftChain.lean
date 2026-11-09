import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRawGramAdjacentCorrection
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRawGramInitialLiftBoundary

/-!
# Finite compatible raw Gram lift chains

This module packages finite towers of complete raw Gram solutions with literal
adjacent reductions.  Height one is identified with the already completed
radical-divisibility criterion.  A single integral p-adic stabilizer supplies
a compatible chain of every finite height by reducing the same element at all
depths.  No inverse-limit or compactness conclusion is asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A finite compatible raw Gram lift chain of height `r` above a prescribed
depth-`k` solution.  The successor constructor stores the next raw solution,
its literal adjacent reduction equality, and the remaining compatible tail. -/
def localPadicSpecialOrthogonalRawGramFiniteLiftChain
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (k r : ℕ) → L.localPadicSpecialOrthogonalRawGramSolution p k → Type
  | _, 0, _ => PUnit
  | k, r + 1, X =>
      Σ Y : {Y : L.localPadicSpecialOrthogonalRawGramSolution p (k + 1) //
        L.localPadicSpecialOrthogonalRawGramSolutionSuccReduction p k Y = X},
        L.localPadicSpecialOrthogonalRawGramFiniteLiftChain p (k + 1) r Y.1

/-- Height-zero compatible chains always exist. -/
theorem nonempty_localPadicSpecialOrthogonalRawGramFiniteLiftChain_zero
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k) :
    Nonempty (L.localPadicSpecialOrthogonalRawGramFiniteLiftChain p k 0 X) :=
  ⟨PUnit.unit⟩

/-- A height-one compatible chain is exactly an actual adjacent raw successor
over the prescribed base solution. -/
theorem nonempty_localPadicSpecialOrthogonalRawGramFiniteLiftChain_one_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k) :
    Nonempty (L.localPadicSpecialOrthogonalRawGramFiniteLiftChain p k 1 X) ↔
      ∃ Y : L.localPadicSpecialOrthogonalRawGramSolution p (k + 1),
        L.localPadicSpecialOrthogonalRawGramSolutionSuccReduction p k Y = X := by
  constructor
  · rintro ⟨⟨⟨Y, hY⟩, _⟩⟩
    exact ⟨Y, hY⟩
  · rintro ⟨Y, hY⟩
    exact ⟨⟨⟨Y, hY⟩, PUnit.unit⟩⟩

/-- The complete raw Gram solution obtained by reducing one integral p-adic
stabilizer at a chosen depth. -/
def localPadicSpecialOrthogonalRawGramSolutionOfStabilizer
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    L.localPadicSpecialOrthogonalRawGramSolution p k :=
  ⟨(L.localPadicLatticeStabilizerReduction p k g).1,
    L.localPadicLatticeStabilizerReduction_mem_gramCongruenceSolutionMatrices
      p k g⟩

/-- Reductions of the same integral p-adic stabilizer at adjacent depths are
literally compatible with the raw Gram successor-reduction map. -/
theorem localPadicSpecialOrthogonalRawGramSolutionOfStabilizer_succReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    L.localPadicSpecialOrthogonalRawGramSolutionSuccReduction p k
        (L.localPadicSpecialOrthogonalRawGramSolutionOfStabilizer p (k + 1) g) =
      L.localPadicSpecialOrthogonalRawGramSolutionOfStabilizer p k g := by
  apply Subtype.ext
  ext i j
  change
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
        (PadicInt.toZModPow (k + 1)
          (L.localPadicLatticeStabilizerIntegralGL p g i j)) =
      PadicInt.toZModPow k
        (L.localPadicLatticeStabilizerIntegralGL p g i j)
  exact PadicInt.cast_toZModPow k (k + 1) (Nat.le_succ k) _

/-- Reducing one integral p-adic stabilizer at all successive depths gives a
literal compatible raw Gram chain of every finite height. -/
def localPadicSpecialOrthogonalRawGramFiniteLiftChainOfStabilizer
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    (r : ℕ) →
      L.localPadicSpecialOrthogonalRawGramFiniteLiftChain p k r
        (L.localPadicSpecialOrthogonalRawGramSolutionOfStabilizer p k g)
  | 0 => PUnit.unit
  | r + 1 =>
      ⟨⟨L.localPadicSpecialOrthogonalRawGramSolutionOfStabilizer p (k + 1) g,
          L.localPadicSpecialOrthogonalRawGramSolutionOfStabilizer_succReduction
            p k g⟩,
        L.localPadicSpecialOrthogonalRawGramFiniteLiftChainOfStabilizer
          p (k + 1) g r⟩

/-- Every selected-depth raw solution with an actual integral p-adic
stabilizer lift admits compatible raw Gram chains of all finite heights. -/
theorem nonempty_finiteLiftChain_of_fullInitialRawGramLift
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p)
    (hX : L.HasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift
      p X) (r : ℕ) :
    Nonempty
      (L.localPadicSpecialOrthogonalRawGramFiniteLiftChain p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) r X) := by
  obtain ⟨g, hg⟩ := hX
  have hbase :
      L.localPadicSpecialOrthogonalRawGramSolutionOfStabilizer p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) g =
        X := by
    apply Subtype.ext
    exact hg
  rw [← hbase]
  exact
    ⟨L.localPadicSpecialOrthogonalRawGramFiniteLiftChainOfStabilizer p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) g r⟩

end PositiveDefiniteIntegralLattice
