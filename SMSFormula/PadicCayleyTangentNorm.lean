import SMSFormula.PadicCayleyTangentFactor

/-!
# Norm of the intrinsic p-adic Cayley tangent determinant

The determinant of the intrinsic Cayley tangent factor has norm
`‖2‖_p ^ d`.  This norm is one at every odd prime and is `2 ^ (-d)` at the
dyadic place.

No top-form or measure transport, chart gluing, or stabilizer-volume
calculation is introduced.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The norm of the intrinsic Cayley tangent determinant is the corresponding
power of the p-adic norm of `2`. -/
theorem norm_det_skewAdjointPadicCayleyTangentFactor
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTangentFactor F p).toLinearMap‖ =
      ‖(2 : ℚ_[p])‖ ^
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) := by
  rw [det_skewAdjointPadicCayleyTangentFactor, norm_pow]

/-- The p-adic norm of `2` is one away from the dyadic place. -/
theorem norm_two_padic_eq_one_of_ne_two
    (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    ‖(2 : ℚ_[p])‖ = 1 := by
  apply Padic.norm_natCast_eq_one_iff.mpr
  apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
  intro hp_dvd
  have hp_eq_two_rev : 2 = p :=
    (Nat.Prime.dvd_iff_eq Nat.prime_two
      (Fact.out : Nat.Prime p).ne_one).mp hp_dvd
  exact hp_two hp_eq_two_rev.symm

/-- At every odd prime, the intrinsic Cayley tangent determinant has norm
one. -/
theorem norm_det_skewAdjointPadicCayleyTangentFactor_of_ne_two
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTangentFactor F p).toLinearMap‖ = 1 := by
  rw [norm_det_skewAdjointPadicCayleyTangentFactor,
    norm_two_padic_eq_one_of_ne_two p hp_two, one_pow]

/-- The dyadic norm of `2` is `2⁻¹`. -/
theorem norm_two_dyadic :
    ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
  exact Padic.norm_p

/-- At the dyadic place, the intrinsic Cayley tangent determinant has norm
`2 ^ (-d)`. -/
theorem norm_det_skewAdjointPadicCayleyTangentFactor_two
    (F : Matrix ι ι ℚ) :
    ‖LinearMap.det
        (skewAdjointPadicCayleyTangentFactor F 2).toLinearMap‖ =
      (2 : ℝ) ^
        (-(Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) : ℤ)) := by
  rw [norm_det_skewAdjointPadicCayleyTangentFactor, norm_two_dyadic,
    ← zpow_natCast, inv_zpow, ← zpow_neg]

end Matrix
