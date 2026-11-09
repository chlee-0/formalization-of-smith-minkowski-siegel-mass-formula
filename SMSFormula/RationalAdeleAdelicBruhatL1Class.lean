import SMSFormula.RationalAdeleAdelicBruhatCoefficientActionInvariance
import SMSFormula.RationalAdeleRankOneAdelicBruhatIntegrable

/-!
# The class of tests with an L1 adelic Bruhat coefficient

The analytic statement `A_Phi in L^1(A)` is wanted on a determining positive-bump space, not
merely at the Gaussian.  The repository proves it at the polar Gaussian--lattice test, at positive
scale and rank at least five.

This file records the structure of the set where it holds, so that extending it is
only about enlarging a known stable class rather than re-proving an estimate test by test.  Write
`IsAdelicBruhatL1 V Phi` for `Phi` integrable with `A_Phi` integrable.  Then:

* the class is a complex subspace -- the coefficient is additive on integrable tests and
  homogeneous with no hypothesis at all;
* the class is invariant under the acting group, for free, by the action invariance of the
  coefficient: the coefficient of a translate is literally the coefficient, and the action preserves
  the coordinate Haar, so it preserves integrability of the test as well;
* it contains every positive-scale polar Gaussian--lattice test at rank at least five.

So the known class already contains the complex span of the whole group orbit of the standard
tests.  Negative scope: this is not a determining positive-bump space.  Span
and orbit closure are structural facts; no claim is made that the class separates measures on the
value line, and no new analytic estimate is proved here.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The complex quadratic phase at a fixed adelic parameter is continuous. -/
theorem continuous_quadraticPhase_complex (V : RationalQuadraticSpaceMatrix n)
    (a : RationalAdele) :
    Continuous (fun x : Fin n → RationalAdele ↦
      ((V.rationalAdeleRankOneQuadraticPhase a x : Circle) : ℂ)) := by
  have hphase : Continuous (fun x : Fin n → RationalAdele ↦
      V.rationalAdeleRankOneQuadraticPhase a x) := by
    show Continuous (fun x : Fin n → RationalAdele ↦
      rationalAdeleFourierChar (a * V.fullAdelicQuadraticFormValue x))
    exact continuous_rationalAdeleFourierChar.comp
      (continuous_const.mul V.continuous_fullAdelicQuadraticFormValue)
  exact hphase.subtype_val

/-- The phase has modulus one, so it never destroys integrability of a test. -/
theorem integrable_mul_quadraticPhase (V : RationalQuadraticSpaceMatrix n) (a : RationalAdele)
    {Phi : (Fin n → RationalAdele) → ℂ}
    (hPhi : Integrable Phi (rationalAdeleCoordinateAddHaarMeasure n)) :
    Integrable (fun x ↦ Phi x * (V.rationalAdeleRankOneQuadraticPhase a x : ℂ))
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  have hbdd : ∀ x : Fin n → RationalAdele,
      ‖((V.rationalAdeleRankOneQuadraticPhase a x : Circle) : ℂ)‖ ≤ 1 :=
    fun x ↦ le_of_eq (by simp)
  simpa [mul_comm] using
    hPhi.bdd_mul (V.continuous_quadraticPhase_complex a).aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)

/-- Additivity of the coefficient, on integrable tests. -/
theorem rationalAdeleRankOneAdelicBruhatCoefficient_add
    (V : RationalQuadraticSpaceMatrix n) {Phi Psi : (Fin n → RationalAdele) → ℂ}
    (hPhi : Integrable Phi (rationalAdeleCoordinateAddHaarMeasure n))
    (hPsi : Integrable Psi (rationalAdeleCoordinateAddHaarMeasure n)) :
    V.rationalAdeleRankOneAdelicBruhatCoefficient (Phi + Psi) =
      V.rationalAdeleRankOneAdelicBruhatCoefficient Phi +
        V.rationalAdeleRankOneAdelicBruhatCoefficient Psi := by
  funext a
  simp only [Pi.add_apply]
  rw [V.rationalAdeleRankOneAdelicBruhatCoefficient_eq_integral,
    V.rationalAdeleRankOneAdelicBruhatCoefficient_eq_integral,
    V.rationalAdeleRankOneAdelicBruhatCoefficient_eq_integral]
  show ∫ x, (Phi x + Psi x) * (V.rationalAdeleRankOneQuadraticPhase a x : ℂ)
      ∂(rationalAdeleCoordinateAddHaarMeasure n) = _
  simp only [add_mul]
  exact integral_add (V.integrable_mul_quadraticPhase a hPhi)
    (V.integrable_mul_quadraticPhase a hPsi)

/-- Homogeneity of the coefficient, with no hypothesis whatsoever. -/
theorem rationalAdeleRankOneAdelicBruhatCoefficient_const_smul
    (V : RationalQuadraticSpaceMatrix n) (c : ℂ) (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneAdelicBruhatCoefficient (c • Phi) =
      c • V.rationalAdeleRankOneAdelicBruhatCoefficient Phi := by
  funext a
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [V.rationalAdeleRankOneAdelicBruhatCoefficient_eq_integral,
    V.rationalAdeleRankOneAdelicBruhatCoefficient_eq_integral]
  show ∫ x, c * Phi x * (V.rationalAdeleRankOneQuadraticPhase a x : ℂ)
      ∂(rationalAdeleCoordinateAddHaarMeasure n) = _
  simp only [mul_assoc]
  exact integral_const_mul _ _

/-- The L1 class: an integrable test whose
adelic Bruhat coefficient is integrable in the adelic parameter. -/
def IsAdelicBruhatL1 (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) : Prop :=
  Integrable Phi (rationalAdeleCoordinateAddHaarMeasure n) ∧
    Integrable (V.rationalAdeleRankOneAdelicBruhatCoefficient Phi) rationalAdeleAddHaarMeasure

theorem IsAdelicBruhatL1.add {V : RationalQuadraticSpaceMatrix n}
    {Phi Psi : (Fin n → RationalAdele) → ℂ}
    (hPhi : V.IsAdelicBruhatL1 Phi) (hPsi : V.IsAdelicBruhatL1 Psi) :
    V.IsAdelicBruhatL1 (Phi + Psi) := by
  refine ⟨hPhi.1.add hPsi.1, ?_⟩
  rw [V.rationalAdeleRankOneAdelicBruhatCoefficient_add hPhi.1 hPsi.1]
  exact hPhi.2.add hPsi.2

theorem IsAdelicBruhatL1.const_smul {V : RationalQuadraticSpaceMatrix n}
    {Phi : (Fin n → RationalAdele) → ℂ} (hPhi : V.IsAdelicBruhatL1 Phi) (c : ℂ) :
    V.IsAdelicBruhatL1 (c • Phi) := by
  refine ⟨hPhi.1.smul c, ?_⟩
  rw [V.rationalAdeleRankOneAdelicBruhatCoefficient_const_smul]
  exact hPhi.2.smul c

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {rank : ℕ}

/-- The class is non-empty, and non-trivially so: the existing rank-at-least-five estimate at the
polar Gaussian--lattice test is exactly a membership statement. -/
theorem isAdelicBruhatL1_polarGaussianLatticeTest (lattice : PositiveDefiniteIntegralLattice rank)
    {scale : ℝ} (hscale : 0 < scale) (hrank : 5 ≤ rank) :
    lattice.rationalQuadraticSpaceMatrix.IsAdelicBruhatL1
      (rationalAdeleVectorPolarGaussianLatticeTest lattice (scale : ℂ)) :=
  ⟨integrable_rationalAdeleVectorPolarGaussianLatticeTest (by simpa using hscale) lattice,
    lattice.integrable_rationalAdeleRankOneAdelicBruhatCoefficient_polarGaussianLattice
      hscale hrank⟩

end PositiveDefiniteIntegralLattice

end
