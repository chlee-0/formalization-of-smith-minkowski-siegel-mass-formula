import SMSFormula.SpecialOrthogonalRealLatticeReference

/-!
# Congruence transport of skew-adjoint differential normalizations

A rational change of basis transports the skew-adjoint tangent space by
matrix conjugation. The fixed invariant top differential, however, is defined
using a separately chosen `Module.finBasis` for each form matrix. Congruence
therefore contributes an explicit nonzero determinant comparing those two
bases; it is not definitionally volume preserving.

The final theorem gives the corresponding real additive-Haar pushforward for
arbitrary bases and a continuous linear equivalence. It is the
measure-theoretic scale needed before a form-congruence argument can be used
in the global real differential measure.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : ℕ}

def skewAdjointCongruenceForm (F : Matrix (Fin n) (Fin n) ℚ)
    (W : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  (W : Matrix (Fin n) (Fin n) ℚ)ᵀ * F *
    (W : Matrix (Fin n) (Fin n) ℚ)

def skewAdjointCongruenceLinearEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    skewAdjointMatricesLieSubalgebra F ≃ₗ[ℚ]
      skewAdjointMatricesLieSubalgebra (skewAdjointCongruenceForm F W) where
  toFun X := by
    refine ⟨(W⁻¹ : Matrix (Fin n) (Fin n) ℚ) * X.1 *
      (W : Matrix (Fin n) (Fin n) ℚ), ?_⟩
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_neg]
    simp only [skewAdjointCongruenceForm]
    have hX := X.property
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule] at hX
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      Matrix.mul_neg] at hX
    have hAB :
        (W : Matrix (Fin n) (Fin n) ℚ) *
            (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hBTAT :
        (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)ᵀ *
            (W : Matrix (Fin n) (Fin n) ℚ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]
    have hrhs :
        ((W : Matrix (Fin n) (Fin n) ℚ)ᵀ * F *
              (W : Matrix (Fin n) (Fin n) ℚ)) *
            ((W⁻¹ : Matrix (Fin n) (Fin n) ℚ) * X.1 *
              (W : Matrix (Fin n) (Fin n) ℚ)) =
          (W : Matrix (Fin n) (Fin n) ℚ)ᵀ * (F * X.1) *
            (W : Matrix (Fin n) (Fin n) ℚ) := by
      calc
        _ = (W : Matrix (Fin n) (Fin n) ℚ)ᵀ * F *
              ((W : Matrix (Fin n) (Fin n) ℚ) *
                (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)) * X.1 *
              (W : Matrix (Fin n) (Fin n) ℚ) := by noncomm_ring
        _ = _ := by rw [hAB]; simp [Matrix.mul_assoc]
    calc
      ((W⁻¹ : Matrix (Fin n) (Fin n) ℚ) * X.1 *
          (W : Matrix (Fin n) (Fin n) ℚ))ᵀ *
          ((W : Matrix (Fin n) (Fin n) ℚ)ᵀ * F *
            (W : Matrix (Fin n) (Fin n) ℚ)) =
        (W : Matrix (Fin n) (Fin n) ℚ)ᵀ * X.1ᵀ *
          ((W⁻¹ : Matrix (Fin n) (Fin n) ℚ)ᵀ *
            (W : Matrix (Fin n) (Fin n) ℚ)ᵀ) * F *
          (W : Matrix (Fin n) (Fin n) ℚ) := by
            simp only [Matrix.transpose_mul]
            noncomm_ring
      _ = (W : Matrix (Fin n) (Fin n) ℚ)ᵀ * (X.1ᵀ * F) *
          (W : Matrix (Fin n) (Fin n) ℚ) := by
            rw [hBTAT]
            simp [Matrix.mul_assoc]
      _ = (W : Matrix (Fin n) (Fin n) ℚ)ᵀ * (-(F * X.1)) *
          (W : Matrix (Fin n) (Fin n) ℚ) := by rw [hX]
      _ = -(((W : Matrix (Fin n) (Fin n) ℚ)ᵀ * F *
          (W : Matrix (Fin n) (Fin n) ℚ)) *
        ((W⁻¹ : Matrix (Fin n) (Fin n) ℚ) * X.1 *
          (W : Matrix (Fin n) (Fin n) ℚ))) := by rw [hrhs]; simp
  invFun Y := by
    refine ⟨(W : Matrix (Fin n) (Fin n) ℚ) * Y.1 *
      (W⁻¹ : Matrix (Fin n) (Fin n) ℚ), ?_⟩
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_neg]
    have hY := Y.property
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule] at hY
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      Matrix.mul_neg] at hY
    simp only [skewAdjointCongruenceForm, Matrix.mul_assoc] at hY
    simp only [skewAdjointCongruenceForm]
    have hBA :
        (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) *
            (W : Matrix (Fin n) (Fin n) ℚ) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hATBT :
        (W : Matrix (Fin n) (Fin n) ℚ)ᵀ *
            (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one]
    have hAB :
        (W : Matrix (Fin n) (Fin n) ℚ) *
            (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hBTAT :
        (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)ᵀ *
            (W : Matrix (Fin n) (Fin n) ℚ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]
    have hcore :
        Y.1ᵀ * ((W : Matrix (Fin n) (Fin n) ℚ)ᵀ * F) =
          -((W : Matrix (Fin n) (Fin n) ℚ)ᵀ *
            (F * ((W : Matrix (Fin n) (Fin n) ℚ) * Y.1 *
              (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)))) := by
      calc
        Y.1ᵀ * ((W : Matrix (Fin n) (Fin n) ℚ)ᵀ * F) =
            (Y.1ᵀ * ((W : Matrix (Fin n) (Fin n) ℚ)ᵀ *
              (F * (W : Matrix (Fin n) (Fin n) ℚ)))) *
                (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) := by
          calc
            _ = (Y.1ᵀ * ((W : Matrix (Fin n) (Fin n) ℚ)ᵀ * F)) *
                ((W : Matrix (Fin n) (Fin n) ℚ) *
                  (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)) := by
                    rw [show (W : Matrix (Fin n) (Fin n) ℚ) *
                      (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) = 1 by
                        rw [← Matrix.GeneralLinearGroup.coe_inv,
                          ← Matrix.GeneralLinearGroup.coe_mul,
                          mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]]
                    simp
            _ = _ := by noncomm_ring
        _ = -(((W : Matrix (Fin n) (Fin n) ℚ)ᵀ *
              (F * ((W : Matrix (Fin n) (Fin n) ℚ) * Y.1))) *
                (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)) := by
                  rw [hY]
                  simp [Matrix.mul_assoc]
        _ = _ := by simp [Matrix.mul_assoc]
    calc
      ((W : Matrix (Fin n) (Fin n) ℚ) * Y.1 *
          (W⁻¹ : Matrix (Fin n) (Fin n) ℚ))ᵀ * F =
        (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)ᵀ *
          (Y.1ᵀ * ((W : Matrix (Fin n) (Fin n) ℚ)ᵀ * F)) := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ =
        (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)ᵀ *
          (-((W : Matrix (Fin n) (Fin n) ℚ)ᵀ *
            (F * ((W : Matrix (Fin n) (Fin n) ℚ) * Y.1 *
              (W⁻¹ : Matrix (Fin n) (Fin n) ℚ))))) := by rw [hcore]
      _ = -(F * ((W : Matrix (Fin n) (Fin n) ℚ) * Y.1 *
          (W⁻¹ : Matrix (Fin n) (Fin n) ℚ))) := by
            simp only [Matrix.mul_neg, Matrix.mul_assoc]
            rw [← Matrix.mul_assoc
              (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)ᵀ
              (W : Matrix (Fin n) (Fin n) ℚ)ᵀ, hBTAT,
              Matrix.one_mul]
  left_inv X := by
    apply Subtype.ext
    have hAB : (W : Matrix (Fin n) (Fin n) ℚ) *
        (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    calc
      (W : Matrix (Fin n) (Fin n) ℚ) *
          ((W⁻¹ : Matrix (Fin n) (Fin n) ℚ) * X.1 *
            (W : Matrix (Fin n) (Fin n) ℚ)) *
          (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) =
        ((W : Matrix (Fin n) (Fin n) ℚ) *
          (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)) * X.1 *
          ((W : Matrix (Fin n) (Fin n) ℚ) *
            (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)) := by noncomm_ring
      _ = X.1 := by rw [hAB]; simp
  right_inv Y := by
    apply Subtype.ext
    have hBA : (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) *
        (W : Matrix (Fin n) (Fin n) ℚ) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    calc
      (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) *
          ((W : Matrix (Fin n) (Fin n) ℚ) * Y.1 *
            (W⁻¹ : Matrix (Fin n) (Fin n) ℚ)) *
          (W : Matrix (Fin n) (Fin n) ℚ) =
        ((W⁻¹ : Matrix (Fin n) (Fin n) ℚ) *
          (W : Matrix (Fin n) (Fin n) ℚ)) * Y.1 *
          ((W⁻¹ : Matrix (Fin n) (Fin n) ℚ) *
            (W : Matrix (Fin n) (Fin n) ℚ)) := by noncomm_ring
      _ = Y.1 := by rw [hBA]; simp
  map_add' X Y := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_skewAdjointCongruenceLinearEquiv_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ)
    (X : skewAdjointMatricesLieSubalgebra F) :
    (skewAdjointCongruenceLinearEquiv F W X :
      Matrix (Fin n) (Fin n) ℚ) =
      (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) * X.1 *
        (W : Matrix (Fin n) (Fin n) ℚ) :=
  rfl

@[simp]
theorem coe_skewAdjointCongruenceLinearEquiv_symm_apply
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ)
    (Y : skewAdjointMatricesLieSubalgebra
      (skewAdjointCongruenceForm F W)) :
    ((skewAdjointCongruenceLinearEquiv F W).symm Y :
      Matrix (Fin n) (Fin n) ℚ) =
      (W : Matrix (Fin n) (Fin n) ℚ) * Y.1 *
        (W⁻¹ : Matrix (Fin n) (Fin n) ℚ) :=
  rfl

/-- Congruence preserves the rational dimension of the skew-adjoint tangent
space. -/
theorem finrank_skewAdjointCongruenceForm
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) =
      Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (skewAdjointCongruenceForm F W)) :=
  (skewAdjointCongruenceLinearEquiv F W).finrank_eq

/-- The source fixed basis transported by congruence and reindexed by the
common tangent dimension. -/
def skewAdjointCongruenceTransportedFinBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra
          (skewAdjointCongruenceForm F W))))
      ℚ
      (skewAdjointMatricesLieSubalgebra
        (skewAdjointCongruenceForm F W)) :=
  ((skewAdjointFinBasis F).map
      (skewAdjointCongruenceLinearEquiv F W)).reindex
    (Fin.castOrderIso (finrank_skewAdjointCongruenceForm F W))

/-- The rational determinant comparing the congruence-transported source
basis with the independently fixed target basis. -/
def skewAdjointCongruenceDetScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) : ℚ :=
  (skewAdjointFinBasis (skewAdjointCongruenceForm F W)).det
    (skewAdjointCongruenceTransportedFinBasis F W)

/-- The congruence comparison determinant cannot vanish. -/
theorem skewAdjointCongruenceDetScalar_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    skewAdjointCongruenceDetScalar F W ≠ 0 := by
  rw [skewAdjointCongruenceDetScalar,
    ← Module.Basis.det_basis
      (skewAdjointCongruenceTransportedFinBasis F W)
      (skewAdjointFinBasis (skewAdjointCongruenceForm F W)),
    ← LinearEquiv.coe_det]
  exact Units.ne_zero _

/-- Evaluation of the target invariant top differential on the transported
source basis is exactly the explicit congruence determinant. -/
theorem skewAdjointDetForm_apply_congruenceTransportedFinBasis
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    skewAdjointDetForm (skewAdjointCongruenceForm F W)
        (skewAdjointCongruenceTransportedFinBasis F W) =
      skewAdjointCongruenceDetScalar F W :=
  rfl

end Matrix

namespace Module.Basis

open MeasureTheory

variable {ι E E' : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E'] [BorelSpace E']
  [SecondCountableTopology E'] [SigmaCompactSpace E']

theorem map_addHaar_eq_inv_abs_det_smul
    (b : Basis ι ℝ E) (b' : Basis ι ℝ E') (e : E ≃L[ℝ] E') :
    Measure.map e b.addHaar =
      (Real.toNNReal |b'.det (fun i => e (b i))|)⁻¹ • b'.addHaar := by
  rw [Module.Basis.map_addHaar]
  let q := b'.det (fun i => e (b i))
  have hq : q ≠ 0 := by
    change b'.det (b.map e.toLinearEquiv) ≠ 0
    rw [← Module.Basis.det_basis (b.map e.toLinearEquiv) b']
    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  have hqabs : 0 < |q| := abs_pos.mpr hq
  rw [(b.map e.toLinearEquiv).addHaar_eq_iff]
  rw [Measure.smul_apply]
  rw [ENNReal.smul_def, smul_eq_mul]
  rw [Module.Basis.coe_parallelepiped]
  rw [Measure.addHaar_parallelepiped]
  change (↑((Real.toNNReal |q|)⁻¹) * ENNReal.ofReal |q|) = 1
  simp only [ENNReal.ofReal]
  rw [ENNReal.coe_inv]
  exact ENNReal.inv_mul_cancel
    (ENNReal.coe_ne_zero.mpr (by
      exact ne_of_gt (Real.toNNReal_pos.mpr hqabs)))
    ENNReal.coe_ne_top
  exact ne_of_gt (Real.toNNReal_pos.mpr hqabs)

end Module.Basis

namespace Matrix

variable {n : ℕ}

local instance skewAdjointCongruenceRealSourceMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))) :=
  borel _

local instance skewAdjointCongruenceRealSourceBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))) :=
  ⟨rfl⟩

local instance skewAdjointCongruenceRealSourceSubmoduleMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance skewAdjointCongruenceRealSourceSubmoduleBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- Scalar extension of the rational congruence equivalence to the real
skew-adjoint tangent models. -/
def skewAdjointRealCongruenceLinearEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule ≃ₗ[ℝ]
      (skewAdjointMatricesLieSubalgebra
        ((skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  (skewAdjointScalarExtensionEquiv (K := ℝ) F).symm ≪≫ₗ
    LinearEquiv.baseChange ℚ ℝ _ _
      (skewAdjointCongruenceLinearEquiv F W) ≪≫ₗ
    skewAdjointScalarExtensionEquiv (K := ℝ)
      (skewAdjointCongruenceForm F W)

/-- The real scalar extension of rational congruence is continuous in both
directions. -/
def skewAdjointRealCongruenceContinuousLinearEquiv
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
      (skewAdjointMatricesLieSubalgebra
        ((skewAdjointCongruenceForm F W).map
          (algebraMap ℚ ℝ))).toSubmodule :=
  (skewAdjointRealCongruenceLinearEquiv F W).toContinuousLinearEquiv

/-- The inverse real tangent congruence has its underlying continuous linear
map as Frechet derivative. This theorem keeps the base-change construction
opaque for later chain-rule proofs. -/
theorem hasFDerivAt_skewAdjointRealCongruenceContinuousLinearEquiv_symm
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ)
    (y : (skewAdjointMatricesLieSubalgebra
      ((skewAdjointCongruenceForm F W).map
        (algebraMap ℚ ℝ))).toSubmodule) :
    HasFDerivAt
      (skewAdjointRealCongruenceContinuousLinearEquiv F W).symm
      (skewAdjointRealCongruenceContinuousLinearEquiv
        F W).symm.toContinuousLinearMap y :=
  (skewAdjointRealCongruenceContinuousLinearEquiv F W).symm.hasFDerivAt

/-- A real linear equivalence between scalar-extended skew-adjoint models
forces equality of the dimensions of their defining rational tangent
spaces. -/
theorem finrank_skewAdjoint_eq_of_real_linearEquiv
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (e :
      (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
        (skewAdjointMatricesLieSubalgebra
          (F'.map (algebraMap ℚ ℝ))).toSubmodule) :
    Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) =
      Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F') := by
  rw [← finrank_skewAdjointScalarExtension_real F,
    ← finrank_skewAdjointScalarExtension_real F']
  exact e.toLinearEquiv.finrank_eq

/-- The source real differential basis, reindexed to the rational tangent
dimension of the target. -/
def skewAdjointRealLinearEquivSourceBasis
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (e :
      (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
        (skewAdjointMatricesLieSubalgebra
          (F'.map (algebraMap ℚ ℝ))).toSubmodule) :
    Module.Basis
      (Fin (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra F')))
      ℝ
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  (skewAdjointScalarExtensionFinBasis (K := ℝ) F).reindex
    (Fin.castOrderIso
      (finrank_skewAdjoint_eq_of_real_linearEquiv F F' e))

/-- The real determinant comparing the image of the source rational
differential basis with the target rational differential basis. -/
def skewAdjointRealLinearEquivDetScalar
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (e :
      (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
        (skewAdjointMatricesLieSubalgebra
          (F'.map (algebraMap ℚ ℝ))).toSubmodule) : ℝ :=
  (skewAdjointScalarExtensionFinBasis (K := ℝ) F').det
    (fun i => e (skewAdjointRealLinearEquivSourceBasis F F' e i))

/-- The real differential-basis comparison determinant is nonzero. -/
theorem skewAdjointRealLinearEquivDetScalar_ne_zero
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (e :
      (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
        (skewAdjointMatricesLieSubalgebra
          (F'.map (algebraMap ℚ ℝ))).toSubmodule) :
    skewAdjointRealLinearEquivDetScalar F F' e ≠ 0 := by
  rw [skewAdjointRealLinearEquivDetScalar]
  change
    (skewAdjointScalarExtensionFinBasis (K := ℝ) F').det
      ((skewAdjointRealLinearEquivSourceBasis F F' e).map
        e.toLinearEquiv) ≠ 0
  let b :=
    (skewAdjointRealLinearEquivSourceBasis F F' e).map e.toLinearEquiv
  let b' := skewAdjointScalarExtensionFinBasis (K := ℝ) F'
  have hdet :
      LinearMap.det
        (b'.equiv b (Equiv.refl _)).toLinearMap ≠ 0 := by
    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  have hdetBasis : b'.det b ≠ 0 := by
    intro hzero
    apply hdet
    exact (Module.Basis.det_basis b b').trans hzero
  exact hdetBasis

set_option backward.isDefEq.respectTransparency false in
/-- A continuous linear equivalence transports the real differential
coordinate measure by the reciprocal absolute determinant comparing the two
rationally normalized bases. -/
theorem map_skewAdjointRealCoordinateDetMeasure_linearEquiv
    (F F' : Matrix (Fin n) (Fin n) ℚ)
    (e :
      (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule ≃L[ℝ]
        (skewAdjointMatricesLieSubalgebra
          (F'.map (algebraMap ℚ ℝ))).toSubmodule) :
    Measure.map e (skewAdjointRealCoordinateDetMeasure F 0) =
      (Real.toNNReal
        |skewAdjointRealLinearEquivDetScalar F F' e|)⁻¹ •
        skewAdjointRealCoordinateDetMeasure F' 0 := by
  rw [skewAdjointRealCoordinateDetMeasure_eq_addHaar,
    skewAdjointRealCoordinateDetMeasure_eq_addHaar,
    skewAdjointRealBasisHaarMeasure,
    skewAdjointRealBasisHaarMeasure,
    ← Module.Basis.addHaar_reindex
      (skewAdjointScalarExtensionFinBasis (K := ℝ) F)
      (Fin.castOrderIso
        (finrank_skewAdjoint_eq_of_real_linearEquiv F F' e)).toEquiv]
  exact Module.Basis.map_addHaar_eq_inv_abs_det_smul
    (skewAdjointRealLinearEquivSourceBasis F F' e)
    (skewAdjointScalarExtensionFinBasis (K := ℝ) F') e

/-- The determinant scale of the real congruence map relative to the
independently fixed rational bases of its source and target. -/
def skewAdjointRealCongruenceDetScalar
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) : ℝ :=
  skewAdjointRealLinearEquivDetScalar F
    (skewAdjointCongruenceForm F W)
    (skewAdjointRealCongruenceContinuousLinearEquiv F W)

/-- The real congruence comparison determinant cannot vanish. -/
theorem skewAdjointRealCongruenceDetScalar_ne_zero
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    skewAdjointRealCongruenceDetScalar F W ≠ 0 :=
  skewAdjointRealLinearEquivDetScalar_ne_zero F
    (skewAdjointCongruenceForm F W)
    (skewAdjointRealCongruenceContinuousLinearEquiv F W)

/-- Rational congruence transports the real differential coordinate measure
by the reciprocal absolute determinant comparing the two fixed rational
skew-adjoint bases. -/
theorem map_skewAdjointRealCoordinateDetMeasure_congruence
    (F : Matrix (Fin n) (Fin n) ℚ) (W : GL (Fin n) ℚ) :
    Measure.map (skewAdjointRealCongruenceContinuousLinearEquiv F W)
        (skewAdjointRealCoordinateDetMeasure F 0) =
      (Real.toNNReal |skewAdjointRealCongruenceDetScalar F W|)⁻¹ •
        skewAdjointRealCoordinateDetMeasure
          (skewAdjointCongruenceForm F W) 0 :=
  map_skewAdjointRealCoordinateDetMeasure_linearEquiv F
    (skewAdjointCongruenceForm F W)
    (skewAdjointRealCongruenceContinuousLinearEquiv F W)

end Matrix
