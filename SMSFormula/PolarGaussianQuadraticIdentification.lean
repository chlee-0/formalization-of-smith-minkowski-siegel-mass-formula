import SMSFormula.RationalAdeleVectorPolarGaussian
import SMSFormula.ShiftedGaussianQuadratic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The real polar Gaussian is an abstract shifted Gaussian

The determining-core layer is stated abstractly over a quadratic form, so that the real polar
Gaussian of this library can be recognized as a member rather than re-derived.  This file proves
that identification.

The form. The exact polar matrix `C = 2F` is symmetric and positive definite, both already proved
here, so it defines a quadratic form `Q_L x = x . (C x)` through mathlib's bilinear-to-quadratic
construction.  It is continuous, being a finite sum of products of coordinates, and positive
definite in the quadratic-form sense, which is the one place the abstract separation argument needs
definiteness.

The identification.  `polarRealGaussian L b x` is the standard coordinate Gaussian evaluated at the
polar square root of `x`; collapsing the coordinate product into a single exponential and applying
the square-root identity `(S x) . (S y) = x . (C y)` turns it into `exp(-pi b Q_L x)`.  So
at a real width it is exactly the abstract shifted Gaussian of width `pi b`, centered at the origin,
with the ambient map the identity -- and that map is injective, which is the abstract separation's
other hypothesis.  Both hypotheses of the determining-core conclusion therefore hold for
`polarRealGaussian`.

Scope.  This identifies the archimedean factor at the origin.  The adelic test family also carries a
finite-adelic carrier indicator and shifted centers, neither of which is addressed here; nothing is
proved about the adelic test, no measure is compared, and the remaining adelic hypotheses of the
abstract criteria -- class membership and the uniform sup bound -- are not treated.  The
identification is at a real width: at a complex width the value is not a real exponential and the
abstract family does not contain it.
-/

noncomputable section

open Matrix MeasureTheory SMSFormula.ShiftedGaussian

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## The polar quadratic form -/

/-- The polar quadratic form: the exact polar matrix read as a quadratic form. -/
def polarQuadraticForm (L : PositiveDefiniteIntegralLattice n) : QuadraticForm ℝ (Fin n → ℝ) :=
  (Matrix.toBilin' L.rationalQuadraticSpaceMatrix.realPolarMatrix).toQuadraticMap

theorem polarQuadraticForm_apply (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℝ) :
    L.polarQuadraticForm x =
      dotProduct x (L.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec x) := by
  simp [polarQuadraticForm, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply']

/-- It is continuous: a finite sum of products of coordinates. -/
theorem continuous_polarQuadraticForm (L : PositiveDefiniteIntegralLattice n) :
    Continuous (L.polarQuadraticForm) := by
  have : (L.polarQuadraticForm : (Fin n → ℝ) → ℝ) = fun x ↦
      ∑ i, ∑ j, x i * (L.rationalQuadraticSpaceMatrix.realPolarMatrix i j * x j) := by
    funext x
    rw [polarQuadraticForm_apply]
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [this]
  exact continuous_finset_sum _ fun i _ ↦ continuous_finset_sum _ fun j _ ↦
    ((continuous_apply i).mul (continuous_const.mul (continuous_apply j)))

/-- And positive definite, which is the one place the abstract separation uses definiteness. -/
theorem posDef_polarQuadraticForm (L : PositiveDefiniteIntegralLattice n) : L.polarQuadraticForm.PosDef := by
  intro x hx
  have h := L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.dotProduct_mulVec_pos hx
  rwa [polarQuadraticForm_apply, ← star_trivial x]

/-! ## The coordinate Gaussian collapses to one exponential -/

/-- The coordinate product is one exponential at a real width: the product of the coordinatewise
Gaussians is the exponential of the negated sum of squares. -/
theorem realCoordinateGaussian_ofReal (b : ℝ) (y : Fin n → ℝ) :
    realCoordinateGaussian n (b : ℂ) y =
      ((Real.exp (-(Real.pi * b) * dotProduct y y) : ℝ) : ℂ) := by
  simp only [realCoordinateGaussian]
  have hterm : ∀ i : Fin n, Complex.exp (-Real.pi * (b : ℂ) * (y i : ℂ) ^ 2) =
      ((Real.exp (-(Real.pi * b) * (y i) ^ 2) : ℝ) : ℂ) := by
    intro i
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp only [hterm, ← Complex.ofReal_prod, ← Real.exp_sum]
  norm_cast
  rw [dotProduct, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-! ## The identification -/

/-- The recognition, paid: at a real width the repository's own polar real Gaussian is the abstract
shifted Gaussian of the polar quadratic form, of width `pi b`, centered at the origin, with the
ambient map the identity. -/
theorem polarRealGaussian_eq_quadraticShiftedGaussian (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (x : Fin n → ℝ) :
    polarRealGaussian L (b : ℂ) x =
      ((quadraticShiftedGaussian L.polarQuadraticForm L.continuous_polarQuadraticForm
        (Real.pi * b) (ContinuousMap.id (Fin n → ℝ)) 0 x : ℝ) : ℂ) := by
  have hx : dotProduct (L.polarRealSqrtMatrix.mulVec x) (L.polarRealSqrtMatrix.mulVec x) =
      L.polarQuadraticForm ((ContinuousMap.id (Fin n → ℝ)) x - 0) := by
    have h0 : ((ContinuousMap.id (Fin n → ℝ)) x - 0) = x := by simp
    rw [h0, polarQuadraticForm_apply, L.dotProduct_polarRealSqrtMatrix_mulVec x x]
  rw [polarRealGaussian, realCoordinateGaussian_ofReal, quadraticShiftedGaussian_apply, hx]

/-- The ambient map is injective, the abstract separation's other hypothesis, so both are
discharged for the repository's own object. -/
theorem injective_id_realCoordinates :
    Function.Injective (ContinuousMap.id (Fin n → ℝ)) := fun _ _ h ↦ h

end PositiveDefiniteIntegralLattice
