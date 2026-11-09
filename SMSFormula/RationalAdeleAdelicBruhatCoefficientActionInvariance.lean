import SMSFormula.RationalCliffordGeneralSpinAdelicPointHaar
import SMSFormula.RationalAdeleRankOneFiniteOnlyDilationBruhat

/-!
# The adelic Bruhat coefficient is action invariant

This file proves `A_{Phi o T_g} = A_Phi`.  `RationalAdeleValuePushforwardActionInvariance` proved
the abstract form -- any weight depending only on the quadratic value rides along the action.  Here
that abstract statement is made literal for the coefficient this repository actually uses, namely
`rationalAdeleRankOneAdelicBruhatCoefficient`, the `W N(a)` value at zero.

Two steps, and the first is the structural reason for the second.

* The unipotent operator commutes with the action: `N(a)(Phi o g) = (N(a) Phi) o g`.  This is just
  the value invariance, since the quadratic phase sees only `Q`.
* Hence the coefficient is the integral of a value-weighted test, and the Haar invariance of the
  acting group gives `A_{Phi o g} = A_Phi` for every adelic parameter `a` and every test, with no
  integrability hypothesis: both sides are the same Bochner integral, so they agree even where the
    integral is undefined and returns zero.  The same then holds for the value density, which is a
  functional of the coefficient family.

Negative scope: nothing here asserts that `A_Phi` is integrable in `a` (see
`RationalAdeleAdelicBruhatL1Class` for the tests where it is); nothing here evaluates a coefficient;
and the invariance is of the coefficient, not of any weighted measure -- see the note in
`RationalAdeleValuePushforwardActionInvariance`.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The `W N(a)` value at zero is the value-weighted integral of the test: the polar matrix sends
`0` to `0`, so the Fourier character contributes nothing and only the quadratic phase survives. -/
theorem rationalAdeleRankOneAdelicBruhatCoefficient_eq_integral
    (V : RationalQuadraticSpaceMatrix n) (Phi : (Fin n → RationalAdele) → ℂ)
    (a : RationalAdele) :
    V.rationalAdeleRankOneAdelicBruhatCoefficient Phi a =
      ∫ x, Phi x * (V.rationalAdeleRankOneQuadraticPhase a x : ℂ)
        ∂(rationalAdeleCoordinateAddHaarMeasure n) := by
  rw [rationalAdeleRankOneAdelicBruhatCoefficient, rationalAdeleRankOneWeylOperator]
  simp [Fourier.fourierIntegral, VectorFourier.fourierIntegral,
    rationalAdeleRankOneUnipotentOperator, mul_comm]

/-- Structural reason: the elementary unipotent operator commutes with the action of the acting
group, because its quadratic phase depends on the point only through the preserved value. -/
theorem rationalAdeleRankOneUnipotentOperator_comp_fullAdelicCliffordGeneralSpin
    (V : RationalQuadraticSpaceMatrix n) (g : V.FullAdelicCliffordGeneralSpinGroup)
    (a : RationalAdele) (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneUnipotentOperator a (fun x ↦ Phi (g.matrixPoint.1 *ᵥ x)) =
      fun x ↦ V.rationalAdeleRankOneUnipotentOperator a Phi (g.matrixPoint.1 *ᵥ x) := by
  funext x
  show (V.rationalAdeleRankOneQuadraticPhase a x : ℂ) * Phi (g.matrixPoint.1 *ᵥ x) =
    (V.rationalAdeleRankOneQuadraticPhase a (g.matrixPoint.1 *ᵥ x) : ℂ) *
      Phi (g.matrixPoint.1 *ᵥ x)
  rw [rationalAdeleRankOneQuadraticPhase, rationalAdeleRankOneQuadraticPhase,
    V.fullAdelicQuadraticFormValue_cliffordGeneralSpin g x]

end RationalQuadraticSpaceMatrix

end
