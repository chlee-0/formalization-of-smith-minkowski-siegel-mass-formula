import SMSFormula.RationalAdeleTranslatedTestPoisson
import SMSFormula.RationalAdeleOrthogonalFourierCovariance

/-!
# The geometric covariance for the standard test

The rational-diagonal theta of the translated standard test equals the rational-diagonal theta of
its polar Weyl transform (the recognition step).  The existing intertwining
`W(Phi o g^-1) = (W Phi) o g^-1` moves the translation out of the Weyl operator.  Composing the two
gives, at every concrete full-adelic special orthogonal point, that the theta of the standard test
equals the theta of the Weyl transform of the standard test -- both evaluated at that point.

That is the geometric covariance the route needed, for the standard test and its polar transform.

Negative scope: this is the theta kernel identity at each group point.  It is not a statement about
the cutoff-normalized functional `I_V`, and the four names stay distinct: nothing here integrates
over the quotient, compares with the Eisenstein side, or evaluates a Tamagawa number.
-/

noncomputable section

open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The geometric covariance: at every concrete full-adelic special orthogonal point, the
rational-diagonal theta of the standard test equals that of its polar Weyl transform. -/
theorem tsum_polarGaussianLatticeTest_weyl_covariance
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re)
    (h : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    (∑' q : Fin n → ℚ, rationalAdeleVectorPolarGaussianLatticeTest L b
        (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n q))) =
      ∑' y : Fin n → ℚ,
        L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L b)
          (h.1.1.1.mulVec (rationalAdeleVectorDiagonal n y)) := by
  rw [tsum_polarGaussianLatticeTest_translate_poisson_weyl L hb h]
  refine tsum_congr fun y ↦ ?_
  have hmat : ((L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.symm h).1⁻¹.1⁻¹).1 =
      h.1.1.1 := by
    simp [L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_symm_apply_matrix]
  have hint := L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator_fullAdelicOrthogonal
    ((L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.symm h).1⁻¹)
    (rationalAdeleVectorPolarGaussianLatticeTest L b) (rationalAdeleVectorDiagonal n y)
  rw [hmat] at hint
  exact hint

end PositiveDefiniteIntegralLattice

end
