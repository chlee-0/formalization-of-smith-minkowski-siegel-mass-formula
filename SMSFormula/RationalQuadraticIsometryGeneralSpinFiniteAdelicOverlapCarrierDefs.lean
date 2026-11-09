import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicBlockCoherentOverlapRestriction

/-! # Source definitions for finite-adelic presentation overlap carriers -/

noncomputable section

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance overlapCarrierDefsDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance overlapCarrierDefsPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Convert a native block exceptional tuple satisfying the pulled-back
overlap condition to the common ambient overlap tuple. -/
def blockFiniteExceptionalPadicCentralFiberSourceOverlapOfCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : {z // z ∈
      P.blockFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S}) :
    P.FiniteExceptionalPadicCentralFiberSourceOverlap S hx :=
  fun v ↦
    let vb : {w // w ∈ S ∪
        (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces} :=
      ⟨v.1, Finset.mem_union_left _ v.2⟩
    ⟨P.blockToAmbientGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] hx (z.1 vb),
      z.2 vb (Set.mem_univ vb)⟩

/-- Convert an ambient exceptional tuple satisfying the overlap condition to
the common overlap tuple. -/
def ambientFiniteExceptionalPadicCentralFiberSourceOverlapOfCarrier
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (z : {z // z ∈
      P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapCarrier hx S}) :
    P.FiniteExceptionalPadicCentralFiberSourceOverlap S hx :=
  fun v ↦
    let va : {w // w ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces} :=
      ⟨v.1, Finset.mem_union_left _ v.2⟩
    ⟨z.1 va, z.2 va (Set.mem_univ va)⟩

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
