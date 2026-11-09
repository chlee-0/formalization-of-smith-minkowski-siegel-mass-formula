import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicOverlapCarrierDefs

/-! # Exceptional overlap source round trips -/

noncomputable section

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance overlapCarrierRoundtripDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance overlapCarrierRoundtripPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance overlapCarrierRoundtripSubtypePrimeFact
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) (v : {v // v ∈ S}) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v.1).2⟩

set_option backward.isDefEq.respectTransparency false in
theorem blockFiniteExceptionalOverlapToExceptionalProduct_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (g : P.FiniteExceptionalPadicCentralFiberSourceOverlap S hx)
    (v : {v // v ∈ S ∪
      (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
    P.blockFiniteExceptionalOverlapToExceptionalProduct hx hS g v =
      P.ambientToBlockGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] hx
        (g (P.blockFiniteExceptionalPlaceEquiv hx hS v)).1 := by
  rfl

theorem ambientFiniteExceptionalOverlapToExceptionalProduct_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (g : P.FiniteExceptionalPadicCentralFiberSourceOverlap S hx)
    (v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
    P.ambientFiniteExceptionalOverlapToExceptionalProduct hx hS g v =
      (g (P.ambientFiniteExceptionalPlaceEquiv hx hS v)).1 := by
  rfl

theorem blockFiniteExceptionalOverlapToExceptionalProduct_ofCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (z : {z // z ∈
      P.blockFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S}) :
    P.blockFiniteExceptionalOverlapToExceptionalProduct hx hS
        (P.blockFiniteExceptionalPadicCentralFiberSourceOverlapOfCarrier hx S z) =
      z.1 := by
  funext v
  unfold blockFiniteExceptionalOverlapToExceptionalProduct
    blockFiniteExceptionalPadicCentralFiberSourceOverlapOfCarrier
  exact P.ambientToBlockGeneralSpinIntrinsicPoint_blockToAmbient
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] hx _

theorem ambientFiniteExceptionalOverlapToExceptionalProduct_ofCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (z : {z // z ∈
      P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S}) :
    P.ambientFiniteExceptionalOverlapToExceptionalProduct hx hS
        (P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapOfCarrier hx S z) =
      z.1 := by
  funext v
  rfl

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
