import SMSFormula.RationalAdeleCongruenceClassPoisson
import SMSFormula.RationalAdeleRealFiniteTensorOperators
import SMSFormula.RationalFiniteAdeleQuadraticGaussAnnihilatorContainment

/-!
# The actual polar frequency map preserves the standard compact family

The old integral Gram matrix preserves the integral lattice. Its integral
adjugate clears the inverse with the explicit factor `|polarDeterminant L|`. Consequently
pullback by the polar matrix sends scales `(c,d)` to `(c*|polarDeterminant L|,d)`;
the actual polar Fourier output has scales `(d*|polarDeterminant L|,c)`.
These are support/period bounds, not Haar normalizations or uniform orbit bounds.
-/

noncomputable section
open PositiveDefiniteIntegralLattice Matrix MeasureTheory
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ}

/-- Integral polar matrices preserve the old standard integral lattice. -/
theorem finiteAdelicPolarMatrix_mulVec_mem_integral
    (L : PositiveDefiniteIntegralLattice n) {x : Fin n → RationalFiniteAdele}
    (hx : x ∈ integralFiniteAdeleVectors n) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x ∈
      integralFiniteAdeleVectors n := by
  rw [L.rationalQuadraticSpaceMatrix_finiteAdelicPolarMatrix_eq_map_polarGramMatrix]
  exact integralFiniteAdeleVectors_mulVec_intMatrix L.polarGramMatrix x hx

/-- The old integral adjugate identity bounds the polar preimage by the
`|polarDeterminant L|`-divided standard lattice. No inverse representative is chosen. -/
theorem polarDeterminant_nsmul_mem_integral_of_polar_mulVec_mem
    (L : PositiveDefiniteIntegralLattice n) {x : Fin n → RationalFiniteAdele}
    (hx : L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x ∈
      integralFiniteAdeleVectors n) :
    L.polarDeterminant.natAbs • x ∈ integralFiniteAdeleVectors n := by
  rw [L.rationalQuadraticSpaceMatrix_finiteAdelicPolarMatrix_eq_map_polarGramMatrix] at hx
  have h := integralFiniteAdeleVectors_mulVec_intMatrix L.polarGramMatrix.adjugate _ hx
  have hadj : L.polarGramMatrix.adjugate.map (algebraMap ℤ RationalFiniteAdele) *
      L.polarGramMatrix.map (algebraMap ℤ RationalFiniteAdele) =
      L.polarDeterminant • (1 : Matrix (Fin n) (Fin n) RationalFiniteAdele) := by
    rw [← Matrix.map_mul, Matrix.adjugate_mul]
    change (L.polarDeterminant • (1 : Matrix (Fin n) (Fin n) ℤ)).map _ = _
    simpa using Matrix.map_smul (algebraMap ℤ RationalFiniteAdele) L.polarDeterminant
      (fun a => map_zsmul (algebraMap ℤ RationalFiniteAdele) L.polarDeterminant a)
      (1 : Matrix (Fin n) (Fin n) ℤ)
  rw [Matrix.mulVec_mulVec, hadj, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have hdisc : (L.polarDeterminant.natAbs : ℤ) = L.polarDeterminant := Int.natAbs_of_nonneg L.polarDeterminant_pos.le
  rw [← hdisc, natCast_zsmul] at h
  exact h

/-- Polar pullback retains the period scale; integrality, not a group-Haar
claim, is the reason. -/
theorem IsStandardPeriodic.polar_mulVec (L : PositiveDefiniteIntegralLattice n)
    {d : ℕ} {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hf : IsStandardPeriodic d f) :
    IsStandardPeriodic d (fun x => f (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x)) := by
  intro x u hu
  dsimp only
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  exact hf _ _ (finiteAdelicPolarMatrix_mulVec_mem_integral L hu)

/-- The discriminant factor bounds the carrier after polar pullback. -/
theorem IsStandardCarried.polar_mulVec (L : PositiveDefiniteIntegralLattice n)
    {c : ℕ} {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hf : IsStandardCarried c f) :
    IsStandardCarried (c * L.polarDeterminant.natAbs)
      (fun x => f (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x)) := by
  intro x hx
  apply hf
  intro hmem
  apply hx
  have hpolar : L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec (c • x) ∈
      integralFiniteAdeleVectors n := by
    rw [Matrix.mulVec_smul]
    exact hmem
  have h := polarDeterminant_nsmul_mem_integral_of_polar_mulVec_mem L hpolar
  simpa only [smul_smul, mul_comm L.polarDeterminant.natAbs c] using h

/-- Exact family bounds for the actual finite polar Fourier factor. -/
theorem standardFiniteFourier_polar_mulVec_scales (L : PositiveDefiniteIntegralLattice n)
    {c d : ℕ} {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    IsStandardCarried (d * L.polarDeterminant.natAbs)
      (fun x => standardFiniteFourier f (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x)) ∧
    IsStandardPeriodic c
      (fun x => standardFiniteFourier f (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x)) :=
  ⟨hperiodic.isStandardCarried_standardFiniteFourier.polar_mulVec L,
    hcarried.isStandardPeriodic_standardFiniteFourier.polar_mulVec L⟩

/-- Phase followed by the full polar Fourier factor keeps its parameter
denominator and discriminant support factors. -/
theorem standardFiniteFourier_phase_polar_mulVec_scales
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ)
    {c d : ℕ} {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    IsStandardCarried ((t.den * c * d) * L.polarDeterminant.natAbs)
      (fun x => standardFiniteFourier
        (fun y => (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t y : ℂ) * f y)
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x)) ∧
    IsStandardPeriodic c
      (fun x => standardFiniteFourier
        (fun y => (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t y : ℂ) * f y)
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x)) :=
  ⟨(isStandardCarried_finiteWeylUnipotent L t hcarried hperiodic).polar_mulVec L,
    (isStandardPeriodic_finiteWeylUnipotent L.rationalQuadraticSpaceMatrix t hcarried).polar_mulVec L⟩

theorem IsStandardCarried.const_mul {c : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardCarried c f) (a : ℂ) :
    IsStandardCarried c (fun x => a * f x) := by
  intro x hx
  dsimp only
  rw [hf x hx, mul_zero]

theorem IsStandardPeriodic.const_mul {d : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardPeriodic d f) (a : ℂ) :
    IsStandardPeriodic d (fun x => a * f x) := by
  intro x u hu
  dsimp only
  rw [hf x u hu]

/-- The full polar output is L1 on the original finite Haar. -/
theorem integrable_standardFiniteFourier_polar_mulVec
    (L : PositiveDefiniteIntegralLattice n) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    Integrable
      (fun x => standardFiniteFourier f (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x))
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  have hs := standardFiniteFourier_polar_mulVec_scales L hcarried hperiodic
  exact integrable_of_isStandardCarried_isStandardPeriodic
    (mul_ne_zero hd (Int.natAbs_ne_zero.mpr L.polarDeterminant_pos.ne')) hc hs.1 hs.2

end RationalQuadraticSpaceMatrix
