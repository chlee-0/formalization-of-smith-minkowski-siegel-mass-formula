import SMSFormula.LocalOrthogonalHaar

/-!
# Local integral orientation

This module states the local integral orientation property used to pass from
ordinary to proper adelic genus representatives. It follows from
`LocalOrthogonalHaar.lean`, which constructs an
integral norm-generator reflection at every prime, including `p = 2`.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

open scoped Matrix

/-- Compatibility form of the local integral reflection theorem
in the project's `p`-adic matrix coordinates. -/
theorem exists_padicIntegralOrthogonal_det_neg_one_of_nonempty
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ R : GL (Fin n) ℤ_[p],
      R.1ᵀ * L.pairingMatrix_padic p * R.1 = L.pairingMatrix_padic p ∧
        R.1.det = -1 := by
  letI : NeZero n := ⟨by
    intro hn
    subst n
    exact Fin.elim0 (Classical.choice (inferInstance : Nonempty (Fin 0)))⟩
  exact L.exists_padicIntegralOrthogonal_det_neg_one p

end PositiveDefiniteIntegralLattice

end
