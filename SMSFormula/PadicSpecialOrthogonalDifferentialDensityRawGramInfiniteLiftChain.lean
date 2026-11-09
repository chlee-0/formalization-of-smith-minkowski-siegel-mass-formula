import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRawGramFiniteLiftChain

/-!
# Infinite compatible raw Gram lift chains

This module names a single coherent branch of complete raw Gram solutions at
all depths above a prescribed base.  It defines tails and finite truncations,
and constructs such a branch by reducing one fixed integral p-adic stabilizer.
No inverse-limit, compactness, or converse lifting theorem is asserted.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- One infinite compatible branch of complete raw Gram solutions above `X`.
The value at height `r` lives at the literal depth `k+r`. -/
structure LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k) where
  value : (r : ℕ) → L.localPadicSpecialOrthogonalRawGramSolution p (k + r)
  value_zero : value 0 = X
  succReduction : ∀ r : ℕ,
    L.localPadicSpecialOrthogonalRawGramSolutionSuccReduction p (k + r)
        (value (r + 1)) = value r

/-- Truncation starting at an arbitrary height `s` of one infinite branch. -/
def LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.truncateFrom
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X)
    (s : ℕ) :
    (r : ℕ) →
      L.localPadicSpecialOrthogonalRawGramFiniteLiftChain p (k + s) r
        (C.value s)
  | 0 => PUnit.unit
  | r + 1 =>
      ⟨⟨C.value (s + 1), C.succReduction s⟩,
        C.truncateFrom (s + 1) r⟩

/-- Truncation of one infinite compatible branch to the existing finite chain
of height `r`. -/
def LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain.truncate
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : L.localPadicSpecialOrthogonalRawGramSolution p k}
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X) :
    (r : ℕ) → L.localPadicSpecialOrthogonalRawGramFiniteLiftChain p k r X :=
  fun r => C.value_zero ▸ C.truncateFrom 0 r

/-- An infinite compatible branch supplies a finite compatible chain of every
height, using one coherent family rather than unrelated existence witnesses. -/
theorem nonempty_finiteLiftChain_of_infiniteLiftChain
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalRawGramSolution p k)
    (C : L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k X)
    (r : ℕ) :
    Nonempty (L.localPadicSpecialOrthogonalRawGramFiniteLiftChain p k r X) :=
  ⟨C.truncate r⟩

/-- Reductions of one fixed integral p-adic stabilizer form an infinite
compatible raw Gram branch. -/
def localPadicSpecialOrthogonalRawGramInfiniteLiftChainOfStabilizer
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p k
      (L.localPadicSpecialOrthogonalRawGramSolutionOfStabilizer p k g) where
  value r :=
    L.localPadicSpecialOrthogonalRawGramSolutionOfStabilizer p (k + r) g
  value_zero := rfl
  succReduction r :=
    L.localPadicSpecialOrthogonalRawGramSolutionOfStabilizer_succReduction
      p (k + r) g

/-- A full selected-depth integral stabilizer lift supplies one infinite
compatible raw Gram branch retaining the prescribed initial matrix. -/
def localPadicSpecialOrthogonalRawGramInfiniteLiftChainOfFullInitialRawGramLift
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p)
    (hX : L.HasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift
      p X) :
    L.LocalPadicSpecialOrthogonalRawGramInfiniteLiftChain p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) X := by
  let g := Classical.choose hX
  have hg := Classical.choose_spec hX
  refine
    { value := fun r =>
        L.localPadicSpecialOrthogonalRawGramSolutionOfStabilizer p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p + r) g
      value_zero := ?_
      succReduction := ?_ }
  · apply Subtype.ext
    exact hg
  · intro r
    exact
      L.localPadicSpecialOrthogonalRawGramSolutionOfStabilizer_succReduction p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p + r) g

/-- In particular, a full initial stabilizer lift supplies all finite
truncations through one explicitly coherent infinite branch. -/
theorem nonempty_finiteLiftChain_of_fullInitialRawGramLift_via_infinite
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p)
    (hX : L.HasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift
      p X) (r : ℕ) :
    Nonempty
      (L.localPadicSpecialOrthogonalRawGramFiniteLiftChain p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) r X) :=
  L.nonempty_finiteLiftChain_of_infiniteLiftChain p
    (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) X
    (L.localPadicSpecialOrthogonalRawGramInfiniteLiftChainOfFullInitialRawGramLift
      p X hX) r

end PositiveDefiniteIntegralLattice
