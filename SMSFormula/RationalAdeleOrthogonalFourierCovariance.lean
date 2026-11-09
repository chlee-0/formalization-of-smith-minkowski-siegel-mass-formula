import SMSFormula.RationalAdeleOverlapTranspose
import SMSFormula.RationalAdeleRankOneMatrixFourierCovariance

/-!
# Adelic orthogonal Fourier contragredience, and the Weyl intertwining

Given Haar invariance, the adelic orthogonal action is a measure-preserving measurable
equivalence of the coordinate space, which is the only input the existing rational-matrix Fourier
contragredience proof uses.  The same change of variables therefore runs for every full-adelic
orthogonal matrix.

The consequence is the intertwining the geometric covariance needs: the existing Weyl operator,
whose kernel carries the polar matrix `C`, satisfies `W(Phi o g^-1) = (W Phi) o g^-1`, because the
form relation gives `g^T C = C g^-1` exactly.

Negative scope: no Poisson identity at a general `GSpin` point follows.  The existing Poisson is
proved on the Gaussian/finite family, and `Phi o g^-1` for an adelic orthogonal `g` is not in
that family, so the theta covariance still needs a Poisson statement for the translated test.
-/

noncomputable section

open Matrix MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The coordinate character of a negated coordinatewise product is the scalar character of the
negated dot product. -/
theorem rationalAdeleCoordinateFourierChar_neg_mul (d : ℕ) (u w : Fin d → RationalAdele) :
    rationalAdeleCoordinateFourierChar d (-(u * w)) =
      rationalAdeleFourierChar (-(dotProduct u w)) := by
  rw [rationalAdeleCoordinateFourierChar_eq_sum]
  congr 1
  simp only [Pi.neg_apply, Pi.mul_apply, Finset.sum_neg_distrib]
  rfl

/-- The contragredient pairing for a full-adelic matrix unit. -/
theorem dotProduct_fullAdelicUnit_inverseTranspose
    (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) (x w : Fin n → RationalAdele) :
    dotProduct (g.1.mulVec x) (((g⁻¹).1)ᵀ.mulVec w) = dotProduct x w := by
  rw [dotProduct_mulVec_transpose, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Units.inv_mul, Matrix.transpose_one, Matrix.one_mulVec]

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

open PositiveDefiniteIntegralLattice

/-- The adelic contragredience: the base coordinate Fourier integral is contragredient under
every full-adelic orthogonal matrix.  The proof is the existing rational change of variables,
available because the action preserves the fixed coordinate Haar. -/
theorem fullAdelicOrthogonal_fourierIntegral_comp (V : RationalQuadraticSpaceMatrix n)
    (g : V.fullAdelicOrthogonalMatrixSubgroup) (Phi : (Fin n → RationalAdele) → ℂ) :
    Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
        (rationalAdeleCoordinateAddHaarMeasure n)
        (fun x ↦ Phi (g.1.1.mulVec x)) =
      fun w ↦ Fourier.fourierIntegral (rationalAdeleCoordinateFourierChar n)
        (rationalAdeleCoordinateAddHaarMeasure n) Phi (((g.1⁻¹).1)ᵀ.mulVec w) := by
  funext w
  simp only [Fourier.fourierIntegral_def]
  set e := fullAdelicMatrixUnitMeasurableEquiv g.1 with he'
  have he : MeasurePreserving e (rationalAdeleCoordinateAddHaarMeasure n)
      (rationalAdeleCoordinateAddHaarMeasure n) :=
    V.fullAdelicOrthogonal_measurePreserving_coordinateHaar g
  set target : (Fin n → RationalAdele) → ℂ := fun z ↦
    rationalAdeleCoordinateFourierChar n (-(z * (((g.1⁻¹).1)ᵀ.mulVec w))) • Phi z with htarget
  calc (∫ x, rationalAdeleCoordinateFourierChar n (-(x * w)) • Phi (g.1.1.mulVec x)
        ∂(rationalAdeleCoordinateAddHaarMeasure n))
      = ∫ x, target (e x) ∂(rationalAdeleCoordinateAddHaarMeasure n) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        show rationalAdeleCoordinateFourierChar n (-(x * w)) • Phi (g.1.1.mulVec x) =
          rationalAdeleCoordinateFourierChar n
              (-((g.1.1.mulVec x) * (((g.1⁻¹).1)ᵀ.mulVec w))) • Phi (g.1.1.mulVec x)
        congr 1
        rw [rationalAdeleCoordinateFourierChar_neg_mul,
          rationalAdeleCoordinateFourierChar_neg_mul,
          dotProduct_fullAdelicUnit_inverseTranspose]
    _ = ∫ z, target z ∂(rationalAdeleCoordinateAddHaarMeasure n) := he.integral_comp' target

/-- The form relation, in the form the Weyl kernel needs. -/
theorem fullAdelicOrthogonal_transpose_mul_polarMatrix (V : RationalQuadraticSpaceMatrix n)
    (g : V.fullAdelicOrthogonalMatrixSubgroup) :
    g.1.1ᵀ * V.fullAdelicPolarMatrix = V.fullAdelicPolarMatrix * (g.1⁻¹).1 := by
  have hconj := V.fullAdelicOrthogonal_polarMatrix_conj g
  have hginv : g.1.1 * (g.1⁻¹).1 = 1 := Units.mul_inv g.1
  calc g.1.1ᵀ * V.fullAdelicPolarMatrix
      = (g.1.1ᵀ * V.fullAdelicPolarMatrix * g.1.1) * (g.1⁻¹).1 := by
        rw [Matrix.mul_assoc (g.1.1ᵀ * V.fullAdelicPolarMatrix), hginv, Matrix.mul_one]
    _ = V.fullAdelicPolarMatrix * (g.1⁻¹).1 := by rw [hconj]

/-- The Weyl intertwining: the existing Weyl operator commutes with the adelic orthogonal action.
This is the geometric-covariance input, and it needs the polar matrix inside the Weyl kernel. -/
theorem rationalAdeleRankOneWeylOperator_fullAdelicOrthogonal
    (V : RationalQuadraticSpaceMatrix n) (g : V.fullAdelicOrthogonalMatrixSubgroup)
    (Phi : (Fin n → RationalAdele) → ℂ) (y : Fin n → RationalAdele) :
    V.rationalAdeleRankOneWeylOperator (fun x ↦ Phi ((g.1⁻¹).1.mulVec x)) y =
      V.rationalAdeleRankOneWeylOperator Phi ((g.1⁻¹).1.mulVec y) := by
  have hinvmem : g.1⁻¹ ∈ V.fullAdelicOrthogonalMatrixSubgroup := inv_mem g.2
  have hcontra := V.fullAdelicOrthogonal_fourierIntegral_comp ⟨g.1⁻¹, hinvmem⟩ Phi
  rw [rationalAdeleRankOneWeylOperator, rationalAdeleRankOneWeylOperator]
  have h1 := congrFun hcontra (V.fullAdelicPolarMatrix.mulVec y)
  simp only [inv_inv] at h1
  rw [h1, Matrix.mulVec_mulVec, V.fullAdelicOrthogonal_transpose_mul_polarMatrix g,
    ← Matrix.mulVec_mulVec]

end RationalQuadraticSpaceMatrix

end
