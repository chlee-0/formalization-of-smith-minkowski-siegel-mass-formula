import SMSFormula.Genus
import SMSFormula.RationalMatrixHasseMinkowski

/-!
# Hasse--Minkowski interface for the finite-adelic genus

This module provides the Hasse--Minkowski declaration used by the concrete
finite-adelic genus construction.  Its proof delegates to the direct
Hasse--Minkowski development in `SMSFormula.RationalMatrixHasseMinkowski`.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {n : ℕ}

/-- Hasse--Minkowski in matrix-congruence form over `ℚ`. -/
theorem isCongruent_rat_of_isCongruent_at_all_places
    (A B : Matrix (Fin n) (Fin n) ℚ)
    (hA_symm : A.IsSymm)
    (hB_symm : B.IsSymm)
    (hA_det : A.det ≠ 0)
    (hB_det : B.det ≠ 0)
    (hreal : (A.map (algebraMap ℚ ℝ)).IsCongruent
      (B.map (algebraMap ℚ ℝ)))
    (hpadic : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (A.map (algebraMap ℚ ℚ_[p])).IsCongruent
        (B.map (algebraMap ℚ ℚ_[p]))) :
    A.IsCongruent B :=
  Rat.isCongruent_rat_of_isCongruent_real_and_padic
    A B hA_symm hB_symm hA_det hB_det hreal hpadic

end Matrix
