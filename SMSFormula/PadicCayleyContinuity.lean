import SMSFormula.PadicCayleyDomainOpenness

/-!
# Continuity of the p-adic Cayley maps

The nonsingular matrix inverse is continuous on the matrix-unit locus by its
determinant-inverse times adjugate formula. This proves continuity of the
ambient Cayley formulas on their explicit domains and, by restriction,
continuity of the two packaged maps underlying the algebraic Cayley
equivalence.

No homeomorphism, measure transport, chart gluing, or stabilizer-volume
calculation is introduced.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Nonsingular matrix inverse is continuous on the p-adic matrix-unit
locus, in the existing matrix product topology. -/
theorem continuousOn_padicNonsingInv
    (p : ℕ) [Fact (Nat.Prime p)] :
    ContinuousOn
      (fun A : Matrix ι ι ℚ_[p] ↦ A⁻¹)
      {A | IsUnit A} := by
  intro A hA
  have hAdetUnit : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hAdet : A.det ≠ 0 := isUnit_iff_ne_zero.mp hAdetUnit
  have hcontinuous :
      ContinuousAt
        (fun B : Matrix ι ι ℚ_[p] ↦ B.det⁻¹ • B.adjugate) A :=
    (continuous_id.matrix_det.continuousAt.inv₀ hAdet).smul
      continuous_id.matrix_adjugate.continuousAt
  apply hcontinuous.continuousWithinAt.congr_of_mem _ hA
  intro B hB
  have hBdetUnit : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det B).mp hB
  rw [B.nonsing_inv_apply hBdetUnit]
  congr 1
  simp

/-- The ambient p-adic Cayley forward formula is continuous on its explicit
source. -/
theorem continuousOn_padicCayleyForwardMatrix
    (p : ℕ) [Fact (Nat.Prime p)] :
    ContinuousOn
      (padicCayleyForwardMatrix (ι := ι) p)
      (padicCayleySource p) := by
  have hnum :
      Continuous (fun X : Matrix ι ι ℚ_[p] ↦ 1 + X) := by fun_prop
  have hden :
      Continuous (fun X : Matrix ι ι ℚ_[p] ↦ 1 - X) := by fun_prop
  have hinv :
      ContinuousOn
        (fun X : Matrix ι ι ℚ_[p] ↦ (1 - X)⁻¹)
        (padicCayleySource p) :=
    (continuousOn_padicNonsingInv p).comp hden.continuousOn
      (fun _ hX ↦ hX)
  exact hnum.continuousOn.mul hinv

/-- The ambient p-adic Cayley inverse formula is continuous on its explicit
inverse domain. -/
theorem continuousOn_padicCayleyInverseMatrix
    (p : ℕ) [Fact (Nat.Prime p)] :
    ContinuousOn
      (padicCayleyInverseMatrix (ι := ι) p)
      (padicCayleyInverseDomain p) := by
  have hden :
      Continuous (fun g : Matrix ι ι ℚ_[p] ↦ g + 1) := by fun_prop
  have hnum :
      Continuous (fun g : Matrix ι ι ℚ_[p] ↦ g - 1) := by fun_prop
  have hinv :
      ContinuousOn
        (fun g : Matrix ι ι ℚ_[p] ↦ (g + 1)⁻¹)
        (padicCayleyInverseDomain p) :=
    (continuousOn_padicNonsingInv p).comp hden.continuousOn
      (fun _ hg ↦ hg)
  exact hinv.mul hnum.continuousOn

/-- The packaged p-adic Cayley forward map is continuous between its explicit
source and special-orthogonal inverse domain. -/
theorem continuous_skewAdjointPadicCayleySpecialOrthogonalTarget
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (hF : F.det ≠ 0) :
    Continuous
      (skewAdjointPadicCayleySpecialOrthogonalTarget F p hF) := by
  have hcoe :
      Continuous
        (fun X : skewAdjointPadicCayleySource F p ↦
          (X.1 : Matrix ι ι ℚ_[p])) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hforward :
      Continuous
        (fun X : skewAdjointPadicCayleySource F p ↦
          padicCayleyForwardMatrix p (X.1 : Matrix ι ι ℚ_[p])) := by
    simpa only [Function.comp_def] using
      (continuousOn_padicCayleyForwardMatrix p).comp_continuous hcoe
        (fun X ↦ X.2)
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact hforward

/-- The packaged p-adic Cayley inverse map is continuous from the explicit
special-orthogonal inverse domain to the transported skew-adjoint source. -/
theorem continuous_padicCayleySpecialOrthogonalInverseSource
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Continuous
      (padicCayleySpecialOrthogonalInverseSource F p) := by
  have hcoe :
      Continuous
        (fun g : padicCayleySpecialOrthogonalInverseDomain F p ↦
          (g.1 : Matrix ι ι ℚ_[p])) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hinverse :
      Continuous
        (fun g : padicCayleySpecialOrthogonalInverseDomain F p ↦
          padicCayleyInverseMatrix p (g.1 : Matrix ι ι ℚ_[p])) := by
    simpa only [Function.comp_def] using
      (continuousOn_padicCayleyInverseMatrix p).comp_continuous hcoe
        (fun g ↦ g.2)
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact hinverse

end Matrix
