import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicOverlapCarrierRoundtrip

/-! # Common-source preimages for native overlap source carriers -/

noncomputable section

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

theorem exists_blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource_preimage
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (z : (P.blockSpace hx).CliffordGeneralSpinHorizontalExceptionalProduct S ×
      (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralTail S)
    (hz : z ∈ P.blockFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S) :
    ∃ g, P.blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS g = z := by
  let exceptional :=
    P.blockFiniteExceptionalPadicCentralFiberSourceOverlapOfCarrier hx S
      ⟨z.1, hz.1⟩
  let g : P.BlockFiniteAdelicPresentationOverlapCylinderSource S hx := (exceptional, z.2)
  refine ⟨g, ?_⟩
  apply Prod.ext
  · exact P.blockFiniteExceptionalOverlapToExceptionalProduct_ofCarrier hx hS
      ⟨z.1, hz.1⟩
  · rfl

theorem exists_ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource_preimage
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (z : V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S)
    (hz : z ∈ P.ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S) :
    ∃ g, P.ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS g = z := by
  let exceptional :=
    P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapOfCarrier hx S
      ⟨z.1, hz.1⟩
  let g : P.AmbientFiniteAdelicPresentationOverlapCylinderSource S hx :=
    (exceptional, z.2)
  refine ⟨g, ?_⟩
  apply Prod.ext
  · exact P.ambientFiniteExceptionalOverlapToExceptionalProduct_ofCarrier hx hS
      ⟨z.1, hz.1⟩
  · rfl

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
