import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCentralFiberTransportedSourceRecovery

/-! # Pointwise membership in transported p-adic source overlaps -/

noncomputable section

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)
variable (p : ℕ) [Fact (Nat.Prime p)]

/-- Inverse presentation sends every point of the transported ambient source
overlap to the literal block pullback source. -/
theorem ambientToBlockGeneralSpinIntrinsicPoint_mem_blockPadicCentralFiberSourceOverlap
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : P.transportedAmbientPadicCentralFiberSourceOverlap p hx) :
    P.ambientToBlockGeneralSpinIntrinsicPoint ℚ_[p] hx g.1 ∈
      P.blockPadicCentralFiberSourceOverlap p hx := by
  unfold blockPadicCentralFiberSourceOverlap
  change P.blockToAmbientGeneralSpinIntrinsicPoint ℚ_[p] hx
      (P.ambientToBlockGeneralSpinIntrinsicPoint ℚ_[p] hx g.1) ∈
    P.transportedAmbientPadicCentralFiberSourceOverlap p hx
  rw [P.blockToAmbientGeneralSpinIntrinsicPoint_ambientToBlock]
  exact g.2

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
