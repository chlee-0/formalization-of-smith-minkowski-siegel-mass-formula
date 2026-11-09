import SMSFormula.RationalAdeleRankOneQuadraticPhase
import SMSFormula.RationalAdeleVectorPolarThetaSpecialization

/-!
# Specialized rational rank-one Weil generators

This file packages only the two generators needed by the authorized
rank-one argument on the repository's actual adelic vector carrier.  The
unipotent generator is the already normalized quadratic phase.  The Weyl
generator is the polar Fourier integral for the fixed coordinate Haar and
the literal polar matrix `2F`.

The rational unipotent generator acts trivially on every rational diagonal
theta summand.  On the concrete polar Gaussian--lattice test, the Weyl
generator is the already computed Fourier product and its rational-diagonal
theta sum satisfies the exact Poisson identity.  We also expose the literal
`w n(t)` value at zero which will be the nontrivial summand in the later
`B(ℚ) \ SL₂(ℚ) ≃ ℙ¹(ℚ)` Eisenstein--Siegel series.

No sum over rational parabolic cosets, convergence assertion, generic Weil
representation, Weil index, Eisenstein functional, or Siegel--Weil theorem is
introduced here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## The quadratic-phase generator -/

/-- Additivity of the quadratic phase in its adelic unipotent parameter. -/
theorem rationalAdeleRankOneQuadraticPhase_add
    (V : RationalQuadraticSpaceMatrix n)
    (a b : RationalAdele) (x : Fin n → RationalAdele) :
    V.rationalAdeleRankOneQuadraticPhase (a + b) x =
      V.rationalAdeleRankOneQuadraticPhase a x *
        V.rationalAdeleRankOneQuadraticPhase b x := by
  unfold rationalAdeleRankOneQuadraticPhase
  rw [add_mul, AddChar.map_add_eq_mul]

/-- The elementary unipotent operators compose by addition of parameters. -/
theorem rationalAdeleRankOneUnipotentOperator_add
    (V : RationalQuadraticSpaceMatrix n)
    (a b : RationalAdele)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneUnipotentOperator (a + b) Phi =
      V.rationalAdeleRankOneUnipotentOperator a
        (V.rationalAdeleRankOneUnipotentOperator b Phi) := by
  funext x
  rw [rationalAdeleRankOneUnipotentOperator,
    rationalAdeleRankOneUnipotentOperator,
    rationalAdeleRankOneUnipotentOperator,
    V.rationalAdeleRankOneQuadraticPhase_add]
  simp only [Circle.coe_mul]
  ring

/-- The zero-parameter unipotent operator is literally the identity. -/
@[simp]
theorem rationalAdeleRankOneUnipotentOperator_zero
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneUnipotentOperator 0 Phi = Phi := by
  funext x
  simp [rationalAdeleRankOneUnipotentOperator,
    rationalAdeleRankOneQuadraticPhase]

/-- Multiplication by the unit-norm quadratic phase preserves integrability
for the fixed coordinate additive Haar. -/
theorem integrable_rationalAdeleRankOneUnipotentOperator
    (V : RationalQuadraticSpaceMatrix n)
    (a : RationalAdele)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (hPhi : Integrable Phi (rationalAdeleCoordinateAddHaarMeasure n)) :
    Integrable (V.rationalAdeleRankOneUnipotentOperator a Phi)
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  unfold rationalAdeleRankOneUnipotentOperator
  apply hPhi.bdd_mul
  · have hcontinuous : Continuous
      (fun x : Fin n → RationalAdele ↦
          (V.rationalAdeleRankOneQuadraticPhase a x : ℂ)) :=
      (V.continuous_rationalAdeleRankOneQuadraticPhase.comp
        (continuous_const.prodMk continuous_id)).subtype_val
    exact hcontinuous.aestronglyMeasurable
  · filter_upwards
    intro x
    exact le_of_eq (Circle.norm_coe _)

/-- A rational unipotent parameter acts trivially at every rational diagonal
vector.  This is the exact generator relation used before summing theta. -/
@[simp]
theorem rationalAdeleRankOneUnipotentOperator_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n)
    (t : ℚ) (Phi : (Fin n → RationalAdele) → ℂ)
    (x : Fin n → ℚ) :
    V.rationalAdeleRankOneUnipotentOperator
        (algebraMap ℚ RationalAdele t) Phi
        (rationalAdeleVectorDiagonal n x) =
      Phi (rationalAdeleVectorDiagonal n x) := by
  rw [rationalAdeleRankOneUnipotentOperator]
  change
    (V.rationalAdeleRankOneQuadraticPhase (algebraMap ℚ RationalAdele t)
      (fun i => algebraMap ℚ RationalAdele (x i)) : ℂ) *
        Phi (rationalAdeleVectorDiagonal n x) = _
  rw [
    V.rationalAdeleRankOneQuadraticPhase_rationalDiagonal]
  have hphase :
      rationalAdeleScaledFourierChar (V.nativeRationalQuadraticForm x)
          (algebraMap ℚ RationalAdele t) = 1 := by
    apply rationalAdeleScaledFourierChar_eq_one_of_mem_diagonal
    exact ⟨t, rfl⟩
  rw [hphase]
  simp

/-- Consequently every rational-diagonal theta sum is invariant under a
rational unipotent generator.  No summability hypothesis is needed for this
termwise identity. -/
theorem tsum_rationalAdeleRankOneUnipotentOperator_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n)
    (t : ℚ) (Phi : (Fin n → RationalAdele) → ℂ) :
    (∑' x : Fin n → ℚ,
      V.rationalAdeleRankOneUnipotentOperator
        (algebraMap ℚ RationalAdele t) Phi
        (rationalAdeleVectorDiagonal n x)) =
      ∑' x : Fin n → ℚ, Phi (rationalAdeleVectorDiagonal n x) := by
  apply tsum_congr
  intro x
  exact V.rationalAdeleRankOneUnipotentOperator_rationalDiagonal t Phi x

/-! ## The polar Fourier/Weyl generator -/

/-- The specialized global Weyl generator: Fourier transformation through
the literal polar pairing `xᵀ(2F)y` and the already normalized coordinate
additive Haar. -/
noncomputable def rationalAdeleRankOneWeylOperator
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    (Fin n → RationalAdele) → ℂ :=
  fun y ↦
    Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
      (rationalAdeleCoordinateAddHaarMeasure n) Phi
      (V.fullAdelicPolarMatrix.mulVec y)

/-- Exact action of the Weyl generator on the concrete polar
Gaussian--lattice test.  All determinant and dual-lattice factors remain in
the existing Fourier product. -/
theorem rationalAdeleRankOneWeylOperator_polarGaussianLattice
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
        (rationalAdeleVectorPolarGaussianLatticeTest L b) =
      rationalAdeleVectorPolarGaussianLatticeFourierProduct L b := by
  funext y
  exact rationalAdeleVectorPolar_fourierIntegral_gaussianLattice hb L y

/-- The concrete rational theta is invariant under the Weyl generator by the
already proved finite-dimensional polar Poisson theorem. -/
theorem tsum_rationalAdeleRankOneWeylOperator_polarGaussianLattice
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    (∑' x : Fin n → ℚ,
      rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)
        (rationalAdeleVectorDiagonal n x)) =
      ∑' x : Fin n → ℚ,
        L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))
          (rationalAdeleVectorDiagonal n x) := by
  simpa only [rationalAdeleRankOneWeylOperator] using
    rationalAdeleVectorPolarGaussianLattice_poisson L ha

/-! ## The open Eisenstein-series summand -/

/-- The literal `w n(t)` value at zero.  These are the terms indexed by the
finite rational points in the later rank-one Eisenstein--Siegel series.  The
definition deliberately does not assert convergence of their sum. -/
noncomputable def rationalAdeleRankOneBruhatCoefficient
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) (t : ℚ) : ℂ :=
  V.rationalAdeleRankOneWeylOperator
    (V.rationalAdeleRankOneUnipotentOperator
      (algebraMap ℚ RationalAdele t) Phi) 0

/-- At `t = 0`, the Bruhat coefficient is the untwisted polar Fourier value
at zero. -/
@[simp]
theorem rationalAdeleRankOneBruhatCoefficient_zero
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneBruhatCoefficient Phi 0 =
      V.rationalAdeleRankOneWeylOperator Phi 0 := by
  simp [rationalAdeleRankOneBruhatCoefficient]

/-- The untwisted Bruhat coefficient of the concrete polar test is the
Fourier product at zero. -/
theorem rationalAdeleRankOneBruhatCoefficient_zero_polarGaussianLattice
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
        (rationalAdeleVectorPolarGaussianLatticeTest L b) 0 =
      rationalAdeleVectorPolarGaussianLatticeFourierProduct L b 0 := by
  rw [rationalAdeleRankOneBruhatCoefficient_zero,
    rationalAdeleRankOneWeylOperator_polarGaussianLattice L hb]

/-- Every rationally twisted concrete polar test occurring in a Bruhat
coefficient is integrable for the fixed coordinate Haar. -/
theorem integrable_rationalAdeleRankOneUnipotentOperator_polarGaussianLattice
    (L : PositiveDefiniteIntegralLattice n) {b : ℂ} (hb : 0 < b.re) (t : ℚ) :
    Integrable
      (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneUnipotentOperator
        (algebraMap ℚ RationalAdele t)
        (rationalAdeleVectorPolarGaussianLatticeTest L b))
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  exact L.rationalQuadraticSpaceMatrix
    |>.integrable_rationalAdeleRankOneUnipotentOperator
      (algebraMap ℚ RationalAdele t)
      (rationalAdeleVectorPolarGaussianLatticeTest L b)
      (integrable_rationalAdeleVectorPolarGaussianLatticeTest hb L)

end RationalQuadraticSpaceMatrix

end
