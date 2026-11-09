import SMSFormula.RationalAdeleRationalDilationHaar
import SMSFormula.RationalAdeleVectorPolarDeterminant
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.MeasureTheory.Integral.Marginal

/-!
# Rational matrix invariance of coordinate adelic Haar

The product formula already proves that multiplication by any nonzero rational
scalar preserves the fixed additive Haar on the full rational adeles.  This
file upgrades that statement to every invertible rational matrix on a finite
coordinate vector space.

Diagonal matrices reduce coordinatewise to rational scalar dilation.
Transvections preserve the product Haar directly: after freezing every
coordinate except the sheared one, their action is a Haar translation.
Mathlib's diagonal--transvection induction then gives the result for every
rational matrix with nonzero determinant.

This is an additive change-of-variables theorem only.  It does not assert
Fourier inversion, a Weil-representation relation, or a new Haar
normalization.
-/

noncomputable section

open Matrix MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The actual action of a rational matrix on the full-adelic coordinate
carrier. -/
def rationalMatrixFullAdelicMulVec
    (M : Matrix (Fin n) (Fin n) ℚ)
    (x : Fin n → RationalAdele) : Fin n → RationalAdele :=
  (M.map (algebraMap ℚ RationalAdele)).mulVec x

@[simp]
theorem rationalMatrixFullAdelicMulVec_apply
    (M : Matrix (Fin n) (Fin n) ℚ)
    (x : Fin n → RationalAdele) :
    rationalMatrixFullAdelicMulVec M x =
      (M.map (algebraMap ℚ RationalAdele)).mulVec x :=
  rfl

private theorem measurable_rationalMatrixFullAdelicMulVec
    (M : Matrix (Fin n) (Fin n) ℚ) :
    Measurable (rationalMatrixFullAdelicMulVec M) := by
  apply Continuous.measurable
  unfold rationalMatrixFullAdelicMulVec
  apply continuous_pi
  intro i
  simp only [Matrix.mulVec, dotProduct]
  apply continuous_finset_sum
  intro j _hj
  exact continuous_const.mul (continuous_apply j)

/-- A rational transvection preserves the literal product of the fixed scalar
adelic Haar. -/
theorem measurePreserving_rationalMatrixFullAdelicMulVec_transvection
    (t : Matrix.TransvectionStruct (Fin n) ℚ) :
    MeasurePreserving
      (rationalMatrixFullAdelicMulVec t.toMatrix)
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  rw [rationalAdeleCoordinateAddHaarMeasure_eq_pi]
  have ht : Measurable (rationalMatrixFullAdelicMulVec t.toMatrix) :=
    measurable_rationalMatrixFullAdelicMulVec t.toMatrix
  refine ⟨ht, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (univ.pi s) :=
    .pi countable_univ fun i _ ↦ hs i
  simp_rw [← pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {t.i}
    ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with
  | mk t_i t_j t_hij t_c =>
      have hmap :
          (Matrix.transvection t_i t_j t_c).map
              (algebraMap ℚ RationalAdele) =
            Matrix.transvection t_i t_j
              (algebraMap ℚ RationalAdele t_c) := by
        ext i j
        simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply,
          Matrix.one_apply, Matrix.single_apply, map_add]
        split_ifs <;> simp_all
      simp only [rationalMatrixFullAdelicMulVec,
        Matrix.TransvectionStruct.toMatrix_mk, hmap]
      simpa [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
        Matrix.single_mulVec, t_hij.symm, ← Function.update_add] using
        (lintegral_add_right_eq_self
          (fun xᵢ ↦ indicator (univ.pi s) 1
            (Function.update x t_i xᵢ))
          (algebraMap ℚ RationalAdele t_c * x t_j))

private theorem measurePreserving_rationalMatrixFullAdelicMulVec_diagonal
    (D : Fin n → ℚ)
    (hD : Matrix.det (Matrix.diagonal D) ≠ 0) :
    MeasurePreserving
      (rationalMatrixFullAdelicMulVec (Matrix.diagonal D))
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  have hDi : ∀ i, D i ≠ 0 := by
    intro i
    have hp : ∏ i, D i ≠ 0 := by simpa using hD
    exact Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)
  rw [rationalAdeleCoordinateAddHaarMeasure_eq_pi]
  convert measurePreserving_pi
    (fun _ : Fin n ↦ rationalAdeleAddHaarMeasure)
    (fun _ : Fin n ↦ rationalAdeleAddHaarMeasure)
    (fun i ↦ measurePreserving_rationalAdele_rationalDilation (D i) (hDi i)) using 1
  funext x i
  have hmap :
      (Matrix.diagonal D).map (algebraMap ℚ RationalAdele) =
        Matrix.diagonal (fun i ↦ algebraMap ℚ RationalAdele (D i)) := by
    ext j k
    simp only [Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [rationalMatrixFullAdelicMulVec, hmap,
    Matrix.mulVec_diagonal]

/-- Every invertible rational matrix preserves the fixed coordinate Haar on
the full rational adeles.  The real determinant modulus and all finite
determinant moduli have cancelled through the rational product formula already
contained in scalar dilation. -/
theorem measurePreserving_rationalMatrixFullAdelicMulVec
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : Matrix.det M ≠ 0) :
    MeasurePreserving
      (rationalMatrixFullAdelicMulVec M)
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun A ↦ MeasurePreserving
      (rationalMatrixFullAdelicMulVec A)
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n)) M hM
  · exact measurePreserving_rationalMatrixFullAdelicMulVec_diagonal
  · exact measurePreserving_rationalMatrixFullAdelicMulVec_transvection
  · intro A B _hA _hB hA hB
    have hcomp := hA.comp hB
    convert hcomp using 1
    funext x
    simp only [Function.comp_apply, rationalMatrixFullAdelicMulVec]
    rw [Matrix.map_mul, Matrix.mulVec_mulVec]

theorem map_rationalAdeleCoordinateAddHaarMeasure_rationalMatrix
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : Matrix.det M ≠ 0) :
    Measure.map (rationalMatrixFullAdelicMulVec M)
        (rationalAdeleCoordinateAddHaarMeasure n) =
      rationalAdeleCoordinateAddHaarMeasure n :=
  (measurePreserving_rationalMatrixFullAdelicMulVec M hM).map_eq

/-- In particular, the exact polar matrix `2F` is Haar preserving on the
full-adelic coordinate carrier. -/
theorem measurePreserving_fullAdelicPolarMatrix_mulVec
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurePreserving
      (fun x : Fin n → RationalAdele ↦ V.fullAdelicPolarMatrix.mulVec x)
      (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) := by
  simpa [RationalQuadraticSpaceMatrix.fullAdelicPolarMatrix,
    rationalMatrixFullAdelicMulVec] using
    measurePreserving_rationalMatrixFullAdelicMulVec V.polarMatrix
      V.polarMatrix_det_ne_zero

end PositiveDefiniteIntegralLattice

end
