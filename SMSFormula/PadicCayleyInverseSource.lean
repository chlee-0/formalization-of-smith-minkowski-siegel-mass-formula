import SMSFormula.PadicCayleyInverseSkewAdjoint

/-!
# Inverse p-adic Cayley points in the forward source

The inverse Cayley matrix of a special-orthogonal inverse-domain point is
already packaged in the transported skew-adjoint model. The ambient inverse
domain-to-source theorem supplies the remaining unit condition, giving a
point of the explicit forward Cayley source.

No forward/inverse equivalence, topology, local equivalence, measure
transport, chart gluing, or stabilizer-volume calculation is introduced.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The packaged inverse skew-adjoint matrix satisfies the explicit forward
source unit condition. -/
theorem padicCayleySpecialOrthogonalInverseSkewAdjoint_mem_source
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    (padicCayleySpecialOrthogonalInverseSkewAdjoint F p g :
        Matrix ι ι ℚ_[p]) ∈ padicCayleySource p := by
  let gm : Matrix ι ι ℚ_[p] := g.1
  have hg : gm ∈ padicCayleyInverseDomain p := g.2
  have hsource := padicCayleyInverseMatrix_mem_source p gm hg
  rw [coe_padicCayleySpecialOrthogonalInverseSkewAdjoint]
  change IsUnit (1 - (gm + 1)⁻¹ * (gm - 1))
  simpa only [padicCayleySource, padicCayleyInverseMatrix] using hsource

/-- The inverse Cayley formula, packaged in the explicit transported
skew-adjoint forward source. -/
def padicCayleySpecialOrthogonalInverseSource
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    padicCayleySpecialOrthogonalInverseDomain F p →
      skewAdjointPadicCayleySource F p :=
  fun g ↦
    ⟨padicCayleySpecialOrthogonalInverseSkewAdjoint F p g,
      padicCayleySpecialOrthogonalInverseSkewAdjoint_mem_source F p g⟩

@[simp]
theorem coe_padicCayleySpecialOrthogonalInverseSource
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (g : padicCayleySpecialOrthogonalInverseDomain F p) :
    ((padicCayleySpecialOrthogonalInverseSource F p g).1 :
        Matrix ι ι ℚ_[p]) =
      (((g.1 : specialOrthogonalMatrixSet
          (F.map (algebraMap ℚ ℚ_[p]))) : Matrix ι ι ℚ_[p]) + 1)⁻¹ *
        (((g.1 : specialOrthogonalMatrixSet
          (F.map (algebraMap ℚ ℚ_[p]))) : Matrix ι ι ℚ_[p]) - 1) :=
  rfl

end Matrix
