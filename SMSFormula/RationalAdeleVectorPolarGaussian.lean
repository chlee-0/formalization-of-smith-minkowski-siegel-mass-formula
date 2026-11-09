import SMSFormula.RationalAdeleVectorPolarDeterminant
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Real Gaussian transform for the rational-adelic polar matrix

For a positive lattice-backed quadratic form, this file uses the canonical
positive matrix square root of the exact polar matrix `C = 2F`.  It proves
that this square root converts the polar quadratic exponent and frequency to
the standard coordinate Gaussian, while its determinant contributes exactly
the reciprocal scale `det(C)⁻¹ᐟ²` for the repository's fixed coordinate
Lebesgue measure.

The resulting theorem is the real positive-definite matrix Gaussian Fourier
formula needed before adjoining the finite polar-dual lattice indicator.  No
new chart, chosen diagonalization, shell decomposition, orbital distribution,
or Tamagawa-number assertion is introduced.
-/

noncomputable section

open Matrix MeasureTheory
open scoped FourierTransform MatrixOrder

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Product of the standard real Fourier character on a finite coordinate
space. -/
noncomputable def realCoordinateFourierChar (d : ℕ) :
    AddChar (Fin d → ℝ) Circle where
  toFun x := ∏ i, Real.fourierChar (x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, AddChar.map_add_eq_mul]
    exact Finset.prod_mul_distrib

theorem realCoordinateFourierChar_mul_eq_dotProduct
    (x y : Fin n → ℝ) :
    realCoordinateFourierChar n (x * y) =
      Real.fourierChar (dotProduct x y) := by
  change (∏ i, Real.fourierChar (x i * y i)) =
    Real.fourierChar (∑ i, x i * y i)
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        AddChar.map_add_eq_mul, ih]

theorem realCoordinateFourierChar_neg_mul_eq_dotProduct
    (x y : Fin n → ℝ) :
    realCoordinateFourierChar n (-(x * y)) =
      Real.fourierChar (-dotProduct x y) := by
  have hvec : -(x * y) = (-x) * y := by
    ext i
    simp
  rw [hvec, realCoordinateFourierChar_mul_eq_dotProduct]
  congr 1
  simp

theorem continuous_realCoordinateFourierChar (d : ℕ) :
    Continuous (realCoordinateFourierChar d) := by
  simpa [realCoordinateFourierChar] using
    (continuous_finset_prod Finset.univ fun i _ ↦
      Real.continuous_fourierChar.comp (continuous_apply i))

noncomputable def realCoordinateGaussian (d : ℕ) (b : ℂ) (x : Fin d → ℝ) : ℂ :=
  ∏ i, Complex.exp (-Real.pi * b * (x i : ℂ) ^ 2)

/-- Coordinatewise product of the certified scalar Gaussian Fourier values. -/
noncomputable def realCoordinateGaussianFourierProduct
    (d : ℕ) (b : ℂ) (w : Fin d → ℝ) : ℂ :=
  ∏ i, 1 / b ^ (1 / 2 : ℂ) *
    Complex.exp (-Real.pi / b * (w i : ℂ) ^ 2)

theorem continuous_realCoordinateGaussian (d : ℕ) (b : ℂ) :
    Continuous (realCoordinateGaussian d b) := by
  apply continuous_finset_prod Finset.univ
  intro i _hi
  exact Complex.continuous_exp.comp (by fun_prop)

theorem integrable_realCoordinateGaussian
    {b : ℂ} (hb : 0 < b.re) (d : ℕ) :
    Integrable (realCoordinateGaussian d b)
      (volume : Measure (Fin d → ℝ)) := by
  change Integrable
    (fun x : Fin d → ℝ ↦
      ∏ i, Complex.exp (-Real.pi * b * (x i : ℂ) ^ 2))
    (volume : Measure (Fin d → ℝ))
  rw [volume_pi]
  let f : Fin d → ℝ → ℂ := fun _ x ↦
    Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)
  have hf : ∀ i, Integrable (f i) (volume : Measure ℝ) := by
    intro i
    have hpi : 0 < ((Real.pi : ℂ) * b).re := by
      simpa using mul_pos Real.pi_pos hb
    convert integrable_cexp_quadratic hpi 0 0 using 1
    funext x
    dsimp [f]
    congr 1
    ring
  simpa only [f] using Integrable.fintype_prod hf

/-- Exact Fourier formula for the standard real coordinate Gaussian on the
literal product Lebesgue measure. -/
theorem realCoordinate_fourierIntegral_gaussian
    {b : ℂ} (hb : 0 < b.re) (d : ℕ) (w : Fin d → ℝ) :
    Fourier.fourierIntegral (realCoordinateFourierChar d)
        (volume : Measure (Fin d → ℝ))
        (realCoordinateGaussian d b) w =
      realCoordinateGaussianFourierProduct d b w := by
  rw [Fourier.fourierIntegral_def, volume_pi]
  have hintegrand :
      (fun v : Fin d → ℝ ↦
        realCoordinateFourierChar d (-(v * w)) •
          realCoordinateGaussian d b v) =
      (fun v : Fin d → ℝ ↦
        ∏ i, Real.fourierChar (-(v i * w i)) •
          Complex.exp (-Real.pi * b * (v i : ℂ) ^ 2)) := by
    funext v
    simp only [realCoordinateFourierChar, realCoordinateGaussian,
      Circle.smul_def, smul_eq_mul]
    change Circle.coeHom (∏ i, Real.fourierChar (-(v i * w i))) *
        ∏ i, Complex.exp (-Real.pi * b * (v i : ℂ) ^ 2) = _
    rw [map_prod]
    change (∏ i, (Real.fourierChar (-(v i * w i)) : ℂ)) *
        ∏ i, Complex.exp (-Real.pi * b * (v i : ℂ) ^ 2) = _
    rw [Finset.prod_mul_distrib]
  rw [hintegrand]
  calc
    (∫ v : Fin d → ℝ,
        ∏ i, Real.fourierChar (-(v i * w i)) •
          Complex.exp (-Real.pi * b * (v i : ℂ) ^ 2)
        ∂Measure.pi (fun _ : Fin d ↦ (volume : Measure ℝ))) =
      ∏ i, ∫ v : ℝ, Real.fourierChar (-(v * w i)) •
        Complex.exp (-Real.pi * b * (v : ℂ) ^ 2) :=
      integral_fintype_prod_eq_prod
        (μ := fun _ : Fin d ↦ (volume : Measure ℝ))
        (fun i (v : ℝ) ↦ Real.fourierChar (-(v * w i)) •
          Complex.exp (-Real.pi * b * (v : ℂ) ^ 2))
    _ = realCoordinateGaussianFourierProduct d b w := by
      apply Finset.prod_congr rfl
      intro i _hi
      change Fourier.fourierIntegral Real.fourierChar volume
        (fun x : ℝ ↦ Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)) (w i) = _
      have h := congrFun (fourier_gaussian_pi hb) (w i)
      rw [Real.fourier_real_eq] at h
      simpa only [Circle.smul_def, smul_eq_mul] using h

/-- Canonical positive square root of the lattice-backed real polar matrix. -/
noncomputable def polarRealSqrtMatrix (L : PositiveDefiniteIntegralLattice n) :
    Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt L.rationalQuadraticSpaceMatrix.realPolarMatrix

theorem polarRealSqrtMatrix_posDef (L : PositiveDefiniteIntegralLattice n) :
    L.polarRealSqrtMatrix.PosDef :=
  by
    simpa [polarRealSqrtMatrix] using
      L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.isStrictlyPositive.sqrt.posDef

theorem polarRealSqrtMatrix_isSymm (L : PositiveDefiniteIntegralLattice n) :
    L.polarRealSqrtMatrix.IsSymm := by
  have h := L.polarRealSqrtMatrix_posDef.posSemidef.isHermitian.eq
  simpa [conjTranspose, transpose] using h

theorem polarRealSqrtMatrix_mul_self (L : PositiveDefiniteIntegralLattice n) :
    L.polarRealSqrtMatrix * L.polarRealSqrtMatrix =
      L.rationalQuadraticSpaceMatrix.realPolarMatrix := by
  simpa [polarRealSqrtMatrix] using
    CFC.sqrt_mul_sqrt_self
      L.rationalQuadraticSpaceMatrix.realPolarMatrix
      L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.posSemidef.nonneg

theorem polarRealSqrtMatrix_det (L : PositiveDefiniteIntegralLattice n) :
    L.polarRealSqrtMatrix.det = (L.polarRealDeterminantScale : ℝ) := by
  rw [polarRealSqrtMatrix,
    L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.posSemidef.det_sqrt]
  rw [RCLike.sqrt_of_nonneg
    (le_of_lt L.rationalQuadraticSpaceMatrix_realPolarMatrix_det_pos)]
  rfl

theorem polarRealSqrtMatrix_det_pos (L : PositiveDefiniteIntegralLattice n) :
    0 < L.polarRealSqrtMatrix.det := by
  rw [L.polarRealSqrtMatrix_det]
  exact_mod_cast L.polarRealDeterminantScale_pos

theorem map_polarRealSqrtMatrix_volume (L : PositiveDefiniteIntegralLattice n) :
    Measure.map (Matrix.toLin' L.polarRealSqrtMatrix)
        (volume : Measure (Fin n → ℝ)) =
      ENNReal.ofReal (L.polarRealDeterminantScale : ℝ)⁻¹ •
        (volume : Measure (Fin n → ℝ)) := by
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi
    (ne_of_gt L.polarRealSqrtMatrix_det_pos),
    L.polarRealSqrtMatrix_det,
    abs_of_pos (inv_pos.mpr (by exact_mod_cast L.polarRealDeterminantScale_pos))]

/-- The canonical square root converts the standard dot product to the exact
polar pairing. -/
theorem dotProduct_polarRealSqrtMatrix_mulVec
    (L : PositiveDefiniteIntegralLattice n) (x y : Fin n → ℝ) :
    dotProduct (L.polarRealSqrtMatrix.mulVec x)
        (L.polarRealSqrtMatrix.mulVec y) =
      dotProduct x
        (L.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec y) := by
  rw [dotProduct_comm, dotProduct_mulVec]
  have hvec :
      (L.polarRealSqrtMatrix.mulVec y) ᵥ* L.polarRealSqrtMatrix =
        L.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec y := by
    have hv : ∀ v : Fin n → ℝ,
        v ᵥ* L.polarRealSqrtMatrix = L.polarRealSqrtMatrix.mulVec v := by
      intro v
      nth_rw 1 [← L.polarRealSqrtMatrix_isSymm.eq]
      exact vecMul_transpose L.polarRealSqrtMatrix v
    rw [hv, mulVec_mulVec, L.polarRealSqrtMatrix_mul_self]
  rw [hvec, dotProduct_comm]

/-- Positive-definite matrix Gaussian written canonically as a standard
coordinate Gaussian after the polar square root. -/
noncomputable def polarRealGaussian
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ) (x : Fin n → ℝ) : ℂ :=
  realCoordinateGaussian n b (L.polarRealSqrtMatrix.mulVec x)

noncomputable def polarRealGaussianFourierProduct
    (L : PositiveDefiniteIntegralLattice n) (b : ℂ) (y : Fin n → ℝ) : ℂ :=
  (L.polarRealDeterminantScale : ℂ)⁻¹ *
    realCoordinateGaussianFourierProduct n b
      (L.polarRealSqrtMatrix.mulVec y)

theorem integrable_polarRealGaussian
    {b : ℂ} (hb : 0 < b.re) (L : PositiveDefiniteIntegralLattice n) :
    Integrable (polarRealGaussian L b)
      (volume : Measure (Fin n → ℝ)) := by
  have hstd := integrable_realCoordinateGaussian hb n
  have hmap := L.map_polarRealSqrtMatrix_volume
  have hstdmap : Integrable (realCoordinateGaussian n b)
      (Measure.map (Matrix.toLin' L.polarRealSqrtMatrix)
        (volume : Measure (Fin n → ℝ))) := by
    rw [hmap]
    exact hstd.smul_measure ENNReal.ofReal_ne_top
  have hmeas : AEMeasurable
      (Matrix.toLin' L.polarRealSqrtMatrix)
      (volume : Measure (Fin n → ℝ)) :=
    (Matrix.toLin' L.polarRealSqrtMatrix).continuous_of_finiteDimensional.measurable.aemeasurable
  have hcomp := (integrable_map_measure
    hstdmap.aestronglyMeasurable hmeas).mp hstdmap
  simpa [polarRealGaussian] using hcomp

/-- Exact positive-definite matrix Gaussian Fourier formula for the fixed
coordinate measure and exact polar frequency `Cy`. -/
theorem polarReal_fourierIntegral_gaussian
    {b : ℂ} (hb : 0 < b.re) (L : PositiveDefiniteIntegralLattice n)
    (y : Fin n → ℝ) :
    Fourier.fourierIntegral (realCoordinateFourierChar n)
        (volume : Measure (Fin n → ℝ))
        (polarRealGaussian L b)
        (L.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec y) =
      polarRealGaussianFourierProduct L b y := by
  rw [Fourier.fourierIntegral_def]
  let S := L.polarRealSqrtMatrix
  let g : (Fin n → ℝ) → ℂ := fun z ↦
    realCoordinateFourierChar n
        (-(z * L.polarRealSqrtMatrix.mulVec y)) •
      realCoordinateGaussian n b z
  have hintegrand :
      (fun x : Fin n → ℝ ↦
        realCoordinateFourierChar n
            (-(x *
              L.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec y)) •
          polarRealGaussian L b x) =
      fun x ↦ g (L.polarRealSqrtMatrix.mulVec x) := by
    funext x
    have hdot := L.dotProduct_polarRealSqrtMatrix_mulVec x y
    simp only [g, polarRealGaussian]
    rw [realCoordinateFourierChar_neg_mul_eq_dotProduct,
      realCoordinateFourierChar_neg_mul_eq_dotProduct, hdot]
  rw [hintegrand]
  have hmap := L.map_polarRealSqrtMatrix_volume
  have hmeas : AEMeasurable
      (Matrix.toLin' L.polarRealSqrtMatrix)
      (volume : Measure (Fin n → ℝ)) :=
    (Matrix.toLin' L.polarRealSqrtMatrix).continuous_of_finiteDimensional.measurable.aemeasurable
  have hgcont : Continuous g := by
    apply Continuous.smul
    · exact continuous_realCoordinateFourierChar n |>.comp (by fun_prop)
    · exact continuous_realCoordinateGaussian n b
  have hchange :
      (∫ z : Fin n → ℝ, g z
          ∂Measure.map (Matrix.toLin' L.polarRealSqrtMatrix)
            (volume : Measure (Fin n → ℝ))) =
        ∫ x : Fin n → ℝ, g (L.polarRealSqrtMatrix.mulVec x) := by
    simpa only [Matrix.toLin'_apply] using
      integral_map hmeas hgcont.aestronglyMeasurable
  rw [← hchange, hmap, integral_smul_measure]
  rw [show (ENNReal.ofReal
      (L.polarRealDeterminantScale : ℝ)⁻¹).toReal =
      (L.polarRealDeterminantScale : ℝ)⁻¹ by
    rw [ENNReal.toReal_ofReal]
    exact le_of_lt (inv_pos.mpr (by exact_mod_cast
      L.polarRealDeterminantScale_pos))]
  rw [Complex.real_smul]
  dsimp [g]
  rw [← Fourier.fourierIntegral_def,
    realCoordinate_fourierIntegral_gaussian hb]
  simp only [polarRealGaussianFourierProduct,
    coe_polarRealDeterminantScale, Complex.ofReal_inv]

end PositiveDefiniteIntegralLattice
