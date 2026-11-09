import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicOverlapCarrierPreimage
import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCentralFiberSourceOverlapMembership

/-! # Common presentation sources land in native overlap carriers -/

noncomputable section

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance overlapCarrierSourceDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance overlapCarrierSourcePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

theorem blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource_mem_carrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (g : P.BlockFiniteAdelicPresentationOverlapCylinderSource S hx) :
    P.blockFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS g ∈
      P.blockFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S := by
  constructor
  · intro v _
    change
      P.blockFiniteExceptionalOverlapToExceptionalProduct hx hS g.1 v ∈
        P.blockPadicCentralFiberSourceOverlap
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
    rw [P.blockFiniteExceptionalOverlapToExceptionalProduct_apply hx hS g.1 v]
    exact
      P.ambientToBlockGeneralSpinIntrinsicPoint_mem_blockPadicCentralFiberSourceOverlap
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
        (g.1 (P.blockFiniteExceptionalPlaceEquiv hx hS v))
  · exact Set.mem_univ _

theorem ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource_mem_carrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (g : P.AmbientFiniteAdelicPresentationOverlapCylinderSource S hx) :
    P.ambientFiniteAdelicPresentationOverlapCylinderToExceptionalTailSource hx hS g ∈
      P.ambientFiniteAdelicPresentationOverlapCylinderSourceCarrier hx S := by
  constructor
  · intro v _
    change
      P.ambientFiniteExceptionalOverlapToExceptionalProduct hx hS g.1 v ∈
        P.transportedAmbientPadicCentralFiberSourceOverlap
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
    rw [P.ambientFiniteExceptionalOverlapToExceptionalProduct_apply hx hS g.1 v]
    exact (g.1 (P.ambientFiniteExceptionalPlaceEquiv hx hS v)).2
  · exact Set.mem_univ _

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
