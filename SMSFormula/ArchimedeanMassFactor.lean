import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import SMSFormula.StandardAxiomsGuard

noncomputable section

namespace PositiveDefiniteIntegralLattice

/-- The archimedean factor appearing in the ordinary
Schulze--Pillot-normalized mass formula over `ℚ`.  The product is indexed by
`j = 1, ..., n` via `Finset.range n`. -/
def archimedeanMassFactor (n : ℕ) : ℝ :=
  2 * Real.rpow Real.pi (-((n : ℝ) * ((n : ℝ) + 1) / 4)) *
    (Finset.range n).prod
      (fun j => Real.Gamma (((j + 1 : ℕ) : ℝ) / 2))

lemma archimedeanMassFactor_pos (n : ℕ) :
    0 < archimedeanMassFactor n := by
  refine mul_pos (mul_pos (by norm_num) ?_) ?_
  · exact Real.rpow_pos_of_pos Real.pi_pos _
  · refine Finset.prod_pos ?_
    intro j hj
    exact Real.Gamma_pos_of_pos (by positivity)

#assert_standard_axioms archimedeanMassFactor
#assert_standard_axioms archimedeanMassFactor_pos

end PositiveDefiniteIntegralLattice
