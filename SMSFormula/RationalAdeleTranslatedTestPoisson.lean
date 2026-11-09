import SMSFormula.RationalAdeleTranslatedTestWeylPoisson
import SMSFormula.RationalAdeleTranslatedCarrierSandwich

/-!
# Poisson at a unit-preimage carrier, and the recognition of the translated test

The assembly holds for any subgroup carrier sandwiched between `N Zhat^n` and `N^-1 Zhat^n`.  The
carrier that actually occurs is the preimage of the integral finite adele vectors under a finite
adelic matrix unit, and the sandwich supplies the `N`.  This file records the identity for that
carrier, which is the one Poisson statement the geometric covariance was reduced to.

Negative scope: this is Poisson at a carrier of that shape -- a statement about one test.  Reading
it as the geometric covariance additionally uses the carrier identification, to see the translated
test as such a test, and the existing intertwining; neither is invoked here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Poisson in Weyl form at the preimage carrier of a finite adelic matrix unit -- the shape the
translated standard test has, by the carrier identification. -/
theorem tsum_polarGaussianTensor_unitPreimageCarrier_poisson_weyl
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    (M : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ) :
    (∑' q : Fin n → ℚ,
        polarRealGaussian L b
            (rationalAdeleVectorRealPart n (rationalAdeleVectorDiagonal n q)) *
          {y : Fin n → RationalFiniteAdele | (M.1).mulVec y ∈ integralFiniteAdeleVectors n}.indicator
            (1 : (Fin n → RationalFiniteAdele) → ℂ)
            (rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n q))) =
      ∑' y : Fin n → ℚ,
        L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (fun x ↦ polarRealGaussian L b (rationalAdeleVectorRealPart n x) *
            {y : Fin n → RationalFiniteAdele |
                (M.1).mulVec y ∈ integralFiniteAdeleVectors n}.indicator
              (1 : (Fin n → RationalFiniteAdele) → ℂ)
              (rationalAdeleVectorFinitePart n x))
          (rationalAdeleVectorDiagonal n y) := by
  obtain ⟨N, hN, hlow, hhigh⟩ := exists_natScale_translatedCarrier_sandwich M
  haveI : NeZero (N * N) := ⟨Nat.mul_ne_zero hN hN⟩
  exact RationalQuadraticSpaceMatrix.tsum_polarGaussianTensor_wideSandwichCarrier_poisson_weyl
    L hb hN (fun {x y} hx hy ↦ add_mem_translatedCarrier M.1 hx hy)
    (fun {x} hx ↦ neg_mem_translatedCarrier M.1 hx) hlow hhigh

/-- The recognition: the translated standard test is of that shape, so its rational-diagonal theta
equals the rational-diagonal theta of its polar Weyl transform, at the original width. -/
theorem tsum_polarGaussianLatticeTest_translate_poisson_weyl
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    (h : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    (∑' q : Fin n → ℚ, rationalAdeleVectorPolarGaussianLatticeTest L b
        (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n q))) =
      ∑' y : Fin n → ℚ,
        L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (fun x ↦ rationalAdeleVectorPolarGaussianLatticeTest L b (h.1.1.1.mulVec x))
          (rationalAdeleVectorDiagonal n y) := by
  classical
  have htest : (fun x : Fin n → RationalAdele ↦
      rationalAdeleVectorPolarGaussianLatticeTest L b (h.1.1.1.mulVec x)) =
      fun x ↦ polarRealGaussian L b (rationalAdeleVectorRealPart n x) *
        {y : Fin n → RationalFiniteAdele |
            (((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2.1.1 :
              (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ).1).mulVec y ∈
              integralFiniteAdeleVectors n}.indicator
          (1 : (Fin n → RationalFiniteAdele) → ℂ)
          (rationalAdeleVectorFinitePart n x) := by
    funext x
    rw [rationalAdeleVectorPolarGaussianLatticeTest_concreteFullAdelicSpecialOrthogonal_mulVec]
    congr 1
    by_cases hx : ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2.1.1.1).mulVec
        (rationalAdeleVectorFinitePart n x) ∈ integralFiniteAdeleVectors n
    · rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_mem hx,
        Set.indicator_of_mem (by exact hx)]
      rfl
    · rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx,
        Set.indicator_of_notMem (by exact hx)]
  rw [htest]
  refine Eq.trans (tsum_congr fun q ↦ congrFun htest (rationalAdeleVectorDiagonal n q)) ?_
  exact tsum_polarGaussianTensor_unitPreimageCarrier_poisson_weyl L hb
    ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2.1.1)

end PositiveDefiniteIntegralLattice

end
