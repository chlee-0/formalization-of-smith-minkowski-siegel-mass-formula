import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeCutoffFinite
import SMSFormula.RationalAdeleCompactOpenCosetPoisson

/-!
# The translated standard test: the real factor is untouched, only the carrier moves

For an adelic orthogonal `g`, the translate of the polar
Gaussian--lattice test is the same real Gaussian times the indicator of a moved finite carrier:
`Phi o g^-1 = f_(bC) 1_(K_g)`.  This file proves exactly that, from three existing facts -- the
real and finite projections commute with the adelic matrix action, and the polar Gaussian is
invariant under a real special orthogonal matrix.

Two further points the answer flags as pitfalls are checked here.  The moved carrier is an
additive subgroup containing the origin, not an affine coset: an affine carrier would introduce
extra character factors.  And the carrier is derived, not chosen: it is literally the preimage of
the existing integral finite adele vectors under the finite component.

Negative scope: the compact open sandwich is not proved here, no decomposition into level-`N`
classes is given, and no Poisson identity for this test follows yet.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The translate of the standard test by a concrete full-adelic special
orthogonal point keeps the real Gaussian factor exactly and moves only the finite carrier. -/
theorem rationalAdeleVectorPolarGaussianLatticeTest_concreteFullAdelicSpecialOrthogonal_mulVec
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ)
    (h : L.ConcreteFullAdelicSpecialOrthogonalGroup) (x : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianLatticeTest L b (h.1.1.1.mulVec x) =
      polarRealGaussian L b (rationalAdeleVectorRealPart n x) *
        RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator
          (((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2.1.1.1).mulVec
            (rationalAdeleVectorFinitePart n x)) := by
  unfold rationalAdeleVectorPolarGaussianLatticeTest
  rw [L.rationalAdeleVectorRealPart_concreteFullAdelicSpecialOrthogonal_mulVec,
    L.rationalAdeleVectorFinitePart_concreteFullAdelicSpecialOrthogonal_mulVec,
    RationalQuadraticSpaceMatrix.polarRealGaussian_realSpecialOrthogonal L b
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).1]

/-! ## The moved carrier is an additive subgroup, not an affine coset -/

/-- The origin lies in the moved carrier. -/
theorem zero_mem_translatedCarrier (M : Matrix (Fin n) (Fin n) RationalFiniteAdele) :
    M.mulVec (0 : Fin n → RationalFiniteAdele) ∈ integralFiniteAdeleVectors n := by
  rw [Matrix.mulVec_zero]
  intro i
  simpa using (integralFiniteAdeleSubring).zero_mem

/-- The moved carrier is closed under addition. -/
theorem add_mem_translatedCarrier (M : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    {y z : Fin n → RationalFiniteAdele}
    (hy : M.mulVec y ∈ integralFiniteAdeleVectors n)
    (hz : M.mulVec z ∈ integralFiniteAdeleVectors n) :
    M.mulVec (y + z) ∈ integralFiniteAdeleVectors n := by
  rw [Matrix.mulVec_add]
  intro i
  exact (integralFiniteAdeleSubring).add_mem (hy i) (hz i)

/-- The moved carrier is closed under negation. -/
theorem neg_mem_translatedCarrier (M : Matrix (Fin n) (Fin n) RationalFiniteAdele)
    {y : Fin n → RationalFiniteAdele}
    (hy : M.mulVec y ∈ integralFiniteAdeleVectors n) :
    M.mulVec (-y) ∈ integralFiniteAdeleVectors n := by
  rw [Matrix.mulVec_neg]
  intro i
  exact (integralFiniteAdeleSubring).neg_mem (hy i)

/-- For a unit the moved carrier is literally the image of the integral vectors under the inverse,
so it is `g_f^-1` times the standard carrier and nothing else. -/
theorem mulVec_mem_integral_iff_mem_inv_image
    (M : (Matrix (Fin n) (Fin n) RationalFiniteAdele)ˣ) (y : Fin n → RationalFiniteAdele) :
    (M.1).mulVec y ∈ integralFiniteAdeleVectors n ↔
      y ∈ (fun z ↦ (↑M⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdele).mulVec z) ''
        integralFiniteAdeleVectors n := by
  constructor
  · intro hy
    refine ⟨(M.1).mulVec y, hy, ?_⟩
    show (↑M⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdele).mulVec ((M.1).mulVec y) = y
    rw [Matrix.mulVec_mulVec]
    simp
  · rintro ⟨z, hz, rfl⟩
    show (M.1).mulVec ((↑M⁻¹ : Matrix (Fin n) (Fin n) RationalFiniteAdele).mulVec z) ∈ _
    rw [Matrix.mulVec_mulVec]
    simpa [← Units.val_mul] using hz

end PositiveDefiniteIntegralLattice

end
