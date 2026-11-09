import SMSFormula.RationalAdeleRationalDilationHaar
import SMSFormula.RationalAdeleRankOneWeilGenerators

/-!
# Finite-only dilation covariance of the rank-one Fourier operator

This file lets the finite-only rational adelic diagonal act on the
full-adelic vector test carrier by precomposition.  The exact coordinate Haar
pushforward from `RationalAdeleFiniteOnlyDilationHaar` then gives

```text
W (D_m Phi) = m^n * D_(m^-1) (W Phi).
```

The factor `m^n` remains; unlike a full rational diagonal, no
real modulus cancels it.  This is a direct integral calculation and not a
generic Weil-representation relation.  The same concrete dilation scales the
quadratic argument by the square of the finite-only diagonal, which gives the
corresponding exact covariance with the unipotent operator.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped FourierTransform ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## Covariance with the quadratic phase -/

/-- The native adelic quadratic form scales quadratically under scalar
multiplication on the actual vector carrier. -/
theorem fullAdelicQuadraticFormValue_smul
    (V : RationalQuadraticSpaceMatrix n)
    (c : RationalAdele) (x : Fin n → RationalAdele) :
    V.fullAdelicQuadraticFormValue (c • x) = c ^ 2 *
      V.fullAdelicQuadraticFormValue x := by
  unfold fullAdelicQuadraticFormValue
  simpa only [pow_two, smul_eq_mul] using
    (V.commutativeScalarExtensionQuadraticForm RationalAdele).map_smul c x

/-! ## Covariance with the polar Fourier operator -/

end RationalQuadraticSpaceMatrix

end
