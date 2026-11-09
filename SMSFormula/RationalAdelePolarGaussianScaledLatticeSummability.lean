import SMSFormula.RationalFiniteAdeleStandardFamilyRationalDiagonal
import SMSFormula.RationalAdeleVectorPolarThetaSpecialization
import SMSFormula.RationalAdeleRealCuspGaussianMajorant

/-!
# The polar Gaussian real factor on the scaled rational lattice

The rational-diagonal collapse for the standard compact finite family left one
explicit hypothesis: absolute summability of the supplied real factor along the
`c`-divided lattice.  This file discharges it for the actual polar Gaussian real
factor used by the orbit, at every complex width with positive real part.

The mechanism is that dividing the argument by `c` is exactly a width change:

```text
polarRealGaussian L b (x / c) = polarRealGaussian L (b / c^2) x.
```

So the scaled-lattice question is the integer-lattice question at width
`b / c^2`, whose real part stays positive.  Norms only see the real part of the
width, so the existing positive-real-scale lattice summability applies.

No theta transformation, Poisson identity, shifted-Gaussian evaluation, new
Gaussian family, lattice, representative or Haar normalization is introduced.
The finite factor is untouched.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## Norms only see the real part of the width -/

/-- The existing explicit norm formula already shows that only the real part of
the width matters.  No new norm computation is introduced. -/
theorem norm_polarRealGaussian (L : PositiveDefiniteIntegralLattice n) (b : ℂ) (x : Fin n → ℝ) :
    ‖polarRealGaussian L b x‖ = ‖polarRealGaussian L ((b.re : ℝ) : ℂ) x‖ := by
  rw [norm_polarRealGaussian_eq_native_exp, norm_polarRealGaussian_eq_native_exp,
    Complex.ofReal_re]

/-! ## Dividing the argument is a width change -/

theorem realCoordinateGaussian_div (d : ℕ) (b : ℂ) {c : ℝ} (hc : c ≠ 0)
    (x : Fin d → ℝ) :
    realCoordinateGaussian d b (fun i => x i / c) =
      realCoordinateGaussian d (b / (c : ℂ) ^ 2) x := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  rw [realCoordinateGaussian, realCoordinateGaussian]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  push_cast
  field_simp

theorem polarRealGaussian_div (L : PositiveDefiniteIntegralLattice n) (b : ℂ) {c : ℝ} (hc : c ≠ 0)
    (x : Fin n → ℝ) :
    polarRealGaussian L b (fun i => x i / c) =
      polarRealGaussian L (b / (c : ℂ) ^ 2) x := by
  have hmul : L.polarRealSqrtMatrix.mulVec (fun i => x i / c) =
      fun i => (L.polarRealSqrtMatrix.mulVec x) i / c := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  show realCoordinateGaussian n b (L.polarRealSqrtMatrix.mulVec (fun i => x i / c)) =
    realCoordinateGaussian n (b / (c : ℂ) ^ 2) (L.polarRealSqrtMatrix.mulVec x)
  rw [hmul, realCoordinateGaussian_div n b hc]

/-! ## Summability on the scaled lattice -/

theorem summable_norm_polarRealGaussian_integerVector
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    Summable fun z : Fin n → ℤ => ‖polarRealGaussian L (a : ℂ) (integerVectorReal z)‖ := by
  have hshift := (summable_shiftedMatrixGaussianSummand_zero
    L.rationalQuadraticSpaceMatrix.realPolarMatrix
    L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef ha).norm
  refine hshift.congr fun z => ?_
  have hx : rationalRealVector n (fun i => (z i : ℚ)) = integerVectorReal z := by
    funext i
    simp [rationalRealVector, integerVectorReal]
  rw [← hx, polarRealGaussian_integerVector L a z]

/-- The actual polar Gaussian real factor is absolutely summable along the
`c`-divided rational lattice, at every complex width with positive real part.
This discharges the real-factor hypothesis of the diagonal collapse. -/
theorem summable_norm_polarRealGaussian_rationalScaledIntegerVector
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {c : ℕ} (hc : c ≠ 0) :
    Summable fun m : Fin n → ℤ =>
      ‖polarRealGaussian L b
        (rationalRealVector n (rationalScaledIntegerVector c m))‖ := by
  have hcR : ((c : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have hsq : ((((c : ℝ)) : ℂ)) ^ 2 = ((((c : ℝ)) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hwidth : (b / ((((c : ℝ)) : ℂ)) ^ 2).re = b.re / ((c : ℝ)) ^ 2 := by
    rw [hsq, Complex.div_ofReal_re]
  have hpos : 0 < (b / ((((c : ℝ)) : ℂ)) ^ 2).re := by
    rw [hwidth]
    exact div_pos hb (by positivity)
  have hmain := summable_norm_polarRealGaussian_integerVector L hpos
  refine hmain.congr fun m => ?_
  have harg : rationalRealVector n (rationalScaledIntegerVector c m) =
      fun i => integerVectorReal m i / ((c : ℝ)) := by
    funext i
    simp [rationalRealVector, rationalScaledIntegerVector, integerVectorReal]
  rw [harg, polarRealGaussian_div L b hcR,
    norm_polarRealGaussian L (b / ((((c : ℝ)) : ℂ)) ^ 2)]

/-! ## The orbit theta sum converges -/

/-- Unconditional convergence of the rational-diagonal theta sum for the actual
polar Gaussian real factor tensored with any member of the standard compact
finite family.  No Poisson identity is asserted. -/
theorem summable_rationalAdeleVectorDiagonal_polarGaussianTensor
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    Summable fun q : Fin n → ℚ =>
      polarRealGaussian L b
          (rationalAdeleVectorRealPart n (rationalAdeleVectorDiagonal n q)) *
        f (rationalAdeleVectorFinitePart n (rationalAdeleVectorDiagonal n q)) :=
  summable_rationalAdeleVectorDiagonal_realFiniteTensor hc hd hcarried hperiodic
    (summable_norm_polarRealGaussian_rationalScaledIntegerVector L hb hc)

/-- The same convergence on the generator-output side, at its explicit scales. -/
theorem summable_rationalAdeleVectorDiagonal_polarGaussianTensor_finiteWeylUnipotent
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) {b : ℂ} (hb : 0 < b.re) {c d : ℕ}
    (hc : c ≠ 0) (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    Summable fun w : Fin n → ℚ =>
      polarRealGaussian L b (rationalRealVector n w) *
        standardFiniteFourier
          (fun x =>
            (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) * f x)
          (rationalFiniteAdeleVectorDiagonal n w) :=
  summable_rationalDiagonal_mul_finiteWeylUnipotent L t hc hd hcarried hperiodic
    (summable_norm_polarRealGaussian_rationalScaledIntegerVector L hb
      (mul_ne_zero (mul_ne_zero t.den_nz hc) hd))

end RationalQuadraticSpaceMatrix
