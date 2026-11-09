import SMSFormula.RationalAdeleVectorShiftedGaussianFiniteTheta
import SMSFormula.RationalAdeleVectorPolarPoissonReduction

/-!
# Intrinsic polar-dual theta specialization

This file specializes the finite-dimensional positive-definite matrix theta
identity to the standard rational integral lattice and its intrinsic polar
dual.  Both reindexings are canonical: integer coordinates are recovered by
the rational floor, and the dual lattice is carried to the standard lattice
by the existing polar general-linear element.

No lattice representative, inverse-matrix chart, shell distribution, or
Tamagawa-number statement is introduced.
-/

noncomputable section

open Matrix Set

namespace PositiveDefiniteIntegralLattice

/-- Integer coordinate vectors are canonically equivalent to integral
rational coordinate vectors. -/
def integerVectorEquivRationalIntegral (n : ℕ) :
    (Fin n → ℤ) ≃ {q : Fin n → ℚ // q ∈ rationalIntegralVectors n} where
  toFun z := ⟨fun i => (z i : ℚ), by
    intro i
    exact ⟨z i, rfl⟩⟩
  invFun q := fun i => (q.1 i).floor
  left_inv z := by
    ext i
    exact Rat.floor_intCast (z i)
  right_inv q := by
    apply Subtype.ext
    funext i
    obtain ⟨z, hz⟩ := q.2 i
    have hfloor := congrArg Rat.floor hz
    calc
      ((q.1 i).floor : ℚ) = (z : ℚ) := by
        exact_mod_cast hfloor.symm
      _ = q.1 i := hz

@[simp]
theorem integerVectorEquivRationalIntegral_apply
    (n : ℕ) (z : Fin n → ℤ) :
    (integerVectorEquivRationalIntegral n z).1 = fun i => (z i : ℚ) :=
  rfl

/-- The polar matrix itself gives the canonical equivalence from its
intrinsic rational dual lattice to the standard integral rational lattice. -/
def _root_.RationalQuadraticSpaceMatrix.rationalPolarDualEquivIntegral
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n) :
    {q : Fin n → ℚ // q ∈ V.rationalPolarDualVectors} ≃
      {z : Fin n → ℚ // z ∈ rationalIntegralVectors n} :=
  let E :=
    (Matrix.GeneralLinearGroup.toLin V.polarMatrixGeneralLinear).toLinearEquiv
  { toFun := fun q => ⟨V.polarMatrix.mulVec q.1, q.2⟩
    invFun := fun z => ⟨E.symm z.1, by
      change E (E.symm z.1) ∈ rationalIntegralVectors n
      rw [E.apply_symm_apply]
      exact z.2⟩
    left_inv := by
      intro q
      apply Subtype.ext
      change E.symm (E q.1) = q.1
      exact E.symm_apply_apply q.1
    right_inv := by
      intro z
      apply Subtype.ext
      change E (E.symm z.1) = z.1
      exact E.apply_symm_apply z.1 }

@[simp]
theorem _root_.RationalQuadraticSpaceMatrix.rationalPolarDualEquivIntegral_apply
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
    (q : {q : Fin n → ℚ // q ∈ V.rationalPolarDualVectors}) :
    (V.rationalPolarDualEquivIntegral q).1 = V.polarMatrix.mulVec q.1 :=
  rfl

/-! ## Pointwise Gaussian identifications -/

theorem realCoordinateGaussian_eq_exp_dotProduct
    (n : ℕ) (b : ℂ) (x : Fin n → ℝ) :
    realCoordinateGaussian n b x =
      Complex.exp
        (-Real.pi * b * ((dotProduct x x : ℝ) : ℂ)) := by
  rw [realCoordinateGaussian, ← Complex.exp_sum]
  congr 1
  simp only [dotProduct]
  push_cast
  simp [Finset.mul_sum, pow_two]

theorem polarRealGaussian_integerVector
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (a : ℝ) (z : Fin n → ℤ) :
    polarRealGaussian L (a : ℂ)
        (rationalRealVector n (fun i => (z i : ℚ))) =
      shiftedMatrixGaussianSummand
        L.rationalQuadraticSpaceMatrix.realPolarMatrix (a : ℂ) 0 z := by
  rw [polarRealGaussian, realCoordinateGaussian_eq_exp_dotProduct,
    shiftedMatrixGaussianSummand]
  have hx : rationalRealVector n (fun i => (z i : ℚ)) =
      integerVectorReal z := by
    funext i
    simp [rationalRealVector, integerVectorReal]
  rw [hx, L.dotProduct_polarRealSqrtMatrix_mulVec]
  simp

theorem realCoordinateGaussianFourierProduct_of_pos
    (n : ℕ) {a : ℝ} (ha : 0 < a) (w : Fin n → ℝ) :
    realCoordinateGaussianFourierProduct n (a : ℂ) w =
      (1 / (Real.sqrt a : ℂ)) ^ n *
        Complex.exp
          (-Real.pi / (a : ℂ) * ((dotProduct w w : ℝ) : ℂ)) := by
  have hhalf : (a : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) := by
    simpa using cpow_half_ofReal_mul_eq_sqrt ha (by norm_num : (0 : ℝ) < 1)
  rw [realCoordinateGaussianFourierProduct,
    Finset.prod_mul_distrib, ← Complex.exp_sum]
  simp only [hhalf, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  simp only [dotProduct]
  push_cast
  simp [Finset.mul_sum, pow_two]

private theorem sqrt_pow_of_nonneg (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt (a ^ n) = Real.sqrt a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg ha n), ih, pow_succ]

theorem polarFourier_scalar_eq_shiftedMatrixThetaNormalization
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    (L.polarRealDeterminantScale : ℂ)⁻¹ *
        (1 / (Real.sqrt a : ℂ)) ^ n =
      shiftedMatrixThetaNormalization
        L.rationalQuadraticSpaceMatrix.realPolarMatrix a := by
  rw [shiftedMatrixThetaNormalization]
  have hdet :
      Real.sqrt
          (a ^ n *
            L.rationalQuadraticSpaceMatrix.realPolarMatrix.det) =
        Real.sqrt a ^ n * (L.polarRealDeterminantScale : ℝ) := by
    rw [Real.sqrt_mul (pow_nonneg ha.le n),
      sqrt_pow_of_nonneg a ha.le n,
      coe_polarRealDeterminantScale]
  simp only [Fintype.card_fin, hdet]
  push_cast
  simp [one_div, inv_pow]

theorem realPolarMatrix_mulVec_rationalRealVector
    {n : ℕ} (V : RationalQuadraticSpaceMatrix n) (q : Fin n → ℚ) :
    V.realPolarMatrix.mulVec (rationalRealVector n q) =
      rationalRealVector n (V.polarMatrix.mulVec q) := by
  ext i
  change
    (∑ j, ((V.polarMatrix i j : ℚ) : ℝ) * (q j : ℝ)) =
      ((∑ j, V.polarMatrix i j * q j : ℚ) : ℝ)
  push_cast
  rfl

theorem polarRealGaussianFourierProduct_of_mulVec_eq_integerVector
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (x : Fin n → ℝ) (z : Fin n → ℤ)
    (hx : L.rationalQuadraticSpaceMatrix.realPolarMatrix.mulVec x =
      integerVectorReal z) :
    polarRealGaussianFourierProduct L (a : ℂ) x =
      shiftedMatrixThetaNormalization
          L.rationalQuadraticSpaceMatrix.realPolarMatrix a *
        centeredMatrixGaussianSummand
          L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
          (1 / a) 0 z := by
  let C := L.rationalQuadraticSpaceMatrix.realPolarMatrix
  have hC : C.PosDef :=
    L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef
  have hdet : IsUnit C.det :=
    (isUnit_iff_ne_zero.mpr hC.det_pos.ne')
  have hinv : C⁻¹.mulVec (integerVectorReal z) = x := by
    rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul C hdet,
      Matrix.one_mulVec]
  have hquad :
      dotProduct (integerVectorReal z)
          (C⁻¹.mulVec (integerVectorReal z)) =
        dotProduct (L.polarRealSqrtMatrix.mulVec x)
          (L.polarRealSqrtMatrix.mulVec x) := by
    rw [hinv, ← hx, dotProduct_comm,
      L.dotProduct_polarRealSqrtMatrix_mulVec]
  rw [polarRealGaussianFourierProduct,
    realCoordinateGaussianFourierProduct_of_pos n ha,
    ← mul_assoc,
    polarFourier_scalar_eq_shiftedMatrixThetaNormalization L ha,
    centeredMatrixGaussianSummand]
  simp only [Pi.zero_apply, sub_zero]
  change
    shiftedMatrixThetaNormalization C a *
        Complex.exp
          (-Real.pi / (a : ℂ) *
            ((dotProduct (L.polarRealSqrtMatrix.mulVec x)
              (L.polarRealSqrtMatrix.mulVec x) : ℝ) : ℂ)) =
      shiftedMatrixThetaNormalization C a *
        Complex.exp
          (-Real.pi * ((1 / a : ℝ) : ℂ) *
            ((dotProduct (integerVectorReal z)
              (C⁻¹.mulVec (integerVectorReal z)) : ℝ) : ℂ))
  rw [hquad]
  congr 1
  apply congrArg Complex.exp
  push_cast
  field_simp [ha.ne']

theorem polarRealGaussianFourierProduct_dualIntegerVector
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (q : Fin n → ℚ) (z : Fin n → ℤ)
    (hq : L.rationalQuadraticSpaceMatrix.polarMatrix.mulVec q =
      fun i => (z i : ℚ)) :
    polarRealGaussianFourierProduct L (a : ℂ)
        (rationalRealVector n q) =
      shiftedMatrixThetaNormalization
          L.rationalQuadraticSpaceMatrix.realPolarMatrix a *
        centeredMatrixGaussianSummand
          L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
          (1 / a) 0 z := by
  apply polarRealGaussianFourierProduct_of_mulVec_eq_integerVector L ha
  rw [realPolarMatrix_mulVec_rationalRealVector, hq]
  funext i
  simp [rationalRealVector, integerVectorReal]

/-! ## Intrinsic theta reindexing and Poisson specialization -/

theorem rationalAdeleVectorPolarStandardTheta_eq_integerTheta
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (a : ℝ) :
    rationalAdeleVectorPolarStandardTheta L (a : ℂ) =
      ∑' z : Fin n → ℤ,
        shiftedMatrixGaussianSummand
          L.rationalQuadraticSpaceMatrix.realPolarMatrix (a : ℂ) 0 z := by
  rw [rationalAdeleVectorPolarStandardTheta,
    ← (integerVectorEquivRationalIntegral n).tsum_eq]
  apply tsum_congr
  intro z
  exact polarRealGaussian_integerVector L a z

theorem rationalAdeleVectorPolarDualTheta_eq_centeredIntegerTheta
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    rationalAdeleVectorPolarDualTheta L (a : ℂ) =
      shiftedMatrixThetaNormalization
          L.rationalQuadraticSpaceMatrix.realPolarMatrix a *
        ∑' z : Fin n → ℤ,
          centeredMatrixGaussianSummand
            L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
            (1 / a) 0 z := by
  let E : (Fin n → ℤ) ≃
      {q : Fin n → ℚ //
        q ∈ L.rationalQuadraticSpaceMatrix.rationalPolarDualVectors} :=
    (integerVectorEquivRationalIntegral n).trans
      L.rationalQuadraticSpaceMatrix.rationalPolarDualEquivIntegral.symm
  rw [rationalAdeleVectorPolarDualTheta, ← E.tsum_eq]
  calc
    (∑' z : Fin n → ℤ,
        polarRealGaussianFourierProduct L (a : ℂ)
          (rationalRealVector n (E z).1)) =
        ∑' z : Fin n → ℤ,
          shiftedMatrixThetaNormalization
              L.rationalQuadraticSpaceMatrix.realPolarMatrix a *
            centeredMatrixGaussianSummand
              L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
              (1 / a) 0 z := by
      apply tsum_congr
      intro z
      apply polarRealGaussianFourierProduct_dualIntegerVector L ha
      have h :=
        L.rationalQuadraticSpaceMatrix.rationalPolarDualEquivIntegral.apply_symm_apply
          (integerVectorEquivRationalIntegral n z)
      exact congrArg Subtype.val h
    _ = _ := tsum_mul_left

theorem rationalAdeleVectorPolarStandardTheta_eq_dualTheta
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    rationalAdeleVectorPolarStandardTheta L (a : ℂ) =
      rationalAdeleVectorPolarDualTheta L (a : ℂ) := by
  rw [rationalAdeleVectorPolarStandardTheta_eq_integerTheta,
    rationalAdeleVectorPolarDualTheta_eq_centeredIntegerTheta L ha]
  exact tsum_shiftedMatrixGaussianSummand_zero_eq_centered_inv
    n L.rationalQuadraticSpaceMatrix.realPolarMatrix
      L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef ha

/-- Rational-diagonal Poisson summation for the exact polar character and the
native Gaussian--lattice test at every positive real scale. -/
theorem rationalAdeleVectorPolarGaussianLattice_poisson
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) :
    (∑' q : Fin n → ℚ,
        rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)
          (rationalAdeleVectorDiagonal n q)) =
      ∑' q : Fin n → ℚ,
        Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
          (rationalAdeleCoordinateAddHaarMeasure n)
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))
          (L.rationalQuadraticSpaceMatrix.fullAdelicPolarMatrix.mulVec
            (rationalAdeleVectorDiagonal n q)) := by
  apply
    (rationalAdeleVectorPolarGaussianLattice_poisson_iff_euclideanTheta
      (b := (a : ℂ)) (by simpa using ha) L).2
  exact rationalAdeleVectorPolarStandardTheta_eq_dualTheta L ha

end PositiveDefiniteIntegralLattice
