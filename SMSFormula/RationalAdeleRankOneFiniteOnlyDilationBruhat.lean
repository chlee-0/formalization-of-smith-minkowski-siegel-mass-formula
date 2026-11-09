import SMSFormula.RationalAdeleRankOneFiniteOnlyDilationFourier

/-!
# Finite-only dilation of the concrete adelic Bruhat coefficient

The rational cusp coefficient was defined only at diagonal rational
unipotent parameters.  A finite-only dilation carries such a parameter out of
that diagonal, so this file exposes the same literal zero-frequency expression
for an arbitrary adelic parameter:

```text
B_A(Phi,a) = (W (N(a) Phi))(0).
```

Quadratic homogeneity and the already proved Fourier Jacobian then give

```text
B_A(D_m Phi,a) = m^n * B_A(Phi,g_m^(-2)*a).
```

This is the exact local Bruhat orbit on the existing test carrier.  It does
not sum the new adelic-parameter family, descend an Eisenstein functional to
`A/Q`, assert a shell scaling law, or prove boundedness.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The actual `W N(a)` zero-frequency value for an arbitrary adelic
unipotent parameter. -/
noncomputable def rationalAdeleRankOneAdelicBruhatCoefficient
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) (a : RationalAdele) : ℂ :=
  V.rationalAdeleRankOneWeylOperator
    (V.rationalAdeleRankOneUnipotentOperator a Phi) 0

/-- Restriction to a rational diagonal parameter is the existing rational
Bruhat coefficient literally. -/
@[simp]
theorem rationalAdeleRankOneAdelicBruhatCoefficient_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) (t : ℚ) :
    V.rationalAdeleRankOneAdelicBruhatCoefficient Phi
        (algebraMap ℚ RationalAdele t) =
      V.rationalAdeleRankOneBruhatCoefficient Phi t :=
  rfl

end RationalQuadraticSpaceMatrix

end
