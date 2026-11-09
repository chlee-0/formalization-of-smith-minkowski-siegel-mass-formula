import SMSFormula.SkewAdjointBaseChange
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Real coordinate measure from the skew-adjoint determinant form

This file applies Mathlib's real `AlternatingMap.measure` construction to the
rationally normalized determinant form on the skew-adjoint coordinate model.
It does not construct a measure on the special orthogonal group.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

namespace AlternatingMap

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
  {d : ℕ} [Fact (Module.finrank ℝ G = d)]

/-- Scaling a real top alternating form scales its induced measure by the
absolute value of the scalar. -/
theorem measure_smul_real (c : ℝ) (ω : G [⋀^Fin d]→ₗ[ℝ] ℝ) :
    (c • ω).measure = ENNReal.ofReal |c| • ω.measure := by
  rw [AlternatingMap.measure, AlternatingMap.measure]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, nnnorm_mul,
    ENNReal.smul_def]
  rw [smul_smul, ENNReal.coe_mul]
  rw [← Real.enorm_eq_ofReal_abs]
  rfl

end AlternatingMap

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance skewAdjointRealMeasurableSpace
    (F : Matrix ι ι ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  borel _

local instance skewAdjointRealBorelSpace
    (F : Matrix ι ι ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  ⟨rfl⟩

/-- The real scalar extension has the rank of the fixed rational
skew-adjoint basis. -/
theorem finrank_skewAdjointScalarExtension_real
    (F : Matrix ι ι ℚ) :
    Module.finrank ℝ
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℝ))).toSubmodule =
      Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) := by
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis
      (skewAdjointScalarExtensionFinBasis (K := ℝ) F)

/-- The additive Haar measure normalized by the rationally transported real
skew-adjoint basis. -/
def skewAdjointRealBasisHaarMeasure
    (F : Matrix ι ι ℚ) :
    Measure
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule :=
  @Module.Basis.addHaar _ _ _ _ _
    (skewAdjointRealMeasurableSpace F)
    (skewAdjointRealBorelSpace F)
    (skewAdjointScalarExtensionFinBasis (K := ℝ) F)

set_option backward.isDefEq.respectTransparency false in
/-- The real additive measure induced by the rationally normalized
skew-adjoint coordinate top form. -/
def skewAdjointRealCoordinateDetMeasure
    (F : Matrix ι ι ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    Measure
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule := by
  letI : Fact
      (Module.finrank ℝ
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule =
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) :=
    ⟨finrank_skewAdjointScalarExtension_real F⟩
  exact
    (skewAdjointScalarExtensionCoordinateDetForm (K := ℝ) F x).toAlternatingMap.measure

set_option backward.isDefEq.respectTransparency false in
/-- The real coordinate measure induced after rationally scaling the fixed
skew-adjoint determinant form. -/
def skewAdjointRealRationalSmulCoordinateDetMeasure
    (F : Matrix ι ι ℚ) (q : ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    Measure
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℝ))).toSubmodule := by
  letI : Fact
      (Module.finrank ℝ
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule =
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) :=
    ⟨finrank_skewAdjointScalarExtension_real F⟩
  exact
    ((q : ℝ) •
      (skewAdjointScalarExtensionCoordinateDetForm
        (K := ℝ) F x).toAlternatingMap).measure

set_option backward.isDefEq.respectTransparency false in
/-- Rational rescaling of the determinant form contributes its real absolute
value to the induced coordinate measure. -/
theorem skewAdjointRealRationalSmulCoordinateDetMeasure_eq_smul
    (F : Matrix ι ι ℚ) (q : ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    skewAdjointRealRationalSmulCoordinateDetMeasure F q x =
      ENNReal.ofReal |(q : ℝ)| • skewAdjointRealCoordinateDetMeasure F x := by
  letI : Fact
      (Module.finrank ℝ
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule =
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) :=
    ⟨finrank_skewAdjointScalarExtension_real F⟩
  rw [skewAdjointRealRationalSmulCoordinateDetMeasure,
    skewAdjointRealCoordinateDetMeasure,
    AlternatingMap.measure_smul_real]

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate-form measure gives volume one to the parallelepiped of
the rationally transported real skew-adjoint basis. -/
theorem skewAdjointRealCoordinateDetMeasure_parallelepiped
    (F : Matrix ι ι ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    skewAdjointRealCoordinateDetMeasure F x
        (_root_.parallelepiped
          (skewAdjointScalarExtensionFinBasis (K := ℝ) F)) = 1 := by
  letI : Fact
      (Module.finrank ℝ
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule =
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) :=
    ⟨finrank_skewAdjointScalarExtension_real F⟩
  rw [skewAdjointRealCoordinateDetMeasure,
    AlternatingMap.measure_parallelepiped]
  change ENNReal.ofReal
      |skewAdjointScalarExtensionCoordinateDetForm (K := ℝ) F x
        (skewAdjointScalarExtensionFinBasis (K := ℝ) F)| = 1
  rw [skewAdjointScalarExtensionCoordinateDetForm_apply_finBasis]
  norm_num

/-- The normalized basis parallelepiped has volume equal to the real absolute
value of the rational rescaling scalar. -/
theorem skewAdjointRealRationalSmulCoordinateDetMeasure_parallelepiped
    (F : Matrix ι ι ℚ) (q : ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    skewAdjointRealRationalSmulCoordinateDetMeasure F q x
        (_root_.parallelepiped
          (skewAdjointScalarExtensionFinBasis (K := ℝ) F)) =
      ENNReal.ofReal |(q : ℝ)| := by
  rw [skewAdjointRealRationalSmulCoordinateDetMeasure_eq_smul,
    Measure.smul_apply,
    skewAdjointRealCoordinateDetMeasure_parallelepiped, smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- The measure induced by the normalized coordinate top form is exactly the
additive Haar measure normalized by the transported rational basis. -/
theorem skewAdjointRealCoordinateDetMeasure_eq_addHaar
    (F : Matrix ι ι ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    skewAdjointRealCoordinateDetMeasure F x =
      skewAdjointRealBasisHaarMeasure F := by
  letI : Fact
      (Module.finrank ℝ
          (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℝ))).toSubmodule =
        Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) :=
    ⟨finrank_skewAdjointScalarExtension_real F⟩
  letI : SigmaFinite (skewAdjointRealCoordinateDetMeasure F x) := by
    rw [skewAdjointRealCoordinateDetMeasure]
    infer_instance
  letI : Measure.IsAddLeftInvariant
      (skewAdjointRealCoordinateDetMeasure F x) := by
    rw [skewAdjointRealCoordinateDetMeasure]
    infer_instance
  rw [skewAdjointRealBasisHaarMeasure, eq_comm,
    Module.Basis.addHaar_eq_iff]
  exact skewAdjointRealCoordinateDetMeasure_parallelepiped F x

set_option backward.isDefEq.respectTransparency false in
/-- The normalized real coordinate-form measure is an additive Haar measure,
stated without installing a global measure instance. -/
theorem skewAdjointRealCoordinateDetMeasure_isAddHaarMeasure
    (F : Matrix ι ι ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    Measure.IsAddHaarMeasure
      (skewAdjointRealCoordinateDetMeasure F x) := by
  rw [skewAdjointRealCoordinateDetMeasure_eq_addHaar,
    skewAdjointRealBasisHaarMeasure]
  infer_instance

/-- The normalized real coordinate-form measure is sigma-finite, stated
without installing a global measure instance. -/
theorem skewAdjointRealCoordinateDetMeasure_sigmaFinite
    (F : Matrix ι ι ℚ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℝ))).toSubmodule) :
    SigmaFinite (skewAdjointRealCoordinateDetMeasure F x) := by
  rw [skewAdjointRealCoordinateDetMeasure_eq_addHaar,
    skewAdjointRealBasisHaarMeasure]
  infer_instance

end Matrix
