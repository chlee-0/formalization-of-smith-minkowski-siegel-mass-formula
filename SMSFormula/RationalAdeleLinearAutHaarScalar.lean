import SMSFormula.RationalAdeleTransposePairing

/-!
# The Haar scalar of a full-adelic linear automorphism

This is the first step of the overlap argument for adelic orthogonal Haar invariance.
A full-adelic matrix unit acts on the
coordinate space as a topological additive automorphism, so the pushforward of the fixed
coordinate Haar is again an additive Haar measure, hence a positive scalar multiple of it.  That
scalar is recorded here, together with the algebra that argument uses: integral transport,
multiplicativity, the value at one and at an inverse, and conjugation invariance -- the last
needing no assumption that the conjugating matrix preserves the measure.

The payoff already available: for a full-adelic orthogonal matrix the conjugation
`g^T = C g^-1 C^-1` gives `c(g^T) * c(g) = 1`.  The remaining half of the argument is the transpose
symmetry `c(M^T) = c(M)`, which the overlap argument supplies; it is not proved here.

Negative scope: no Fourier transform, no overlap integral, and no proof that any adelic
orthogonal matrix preserves the Haar.  The scalar is constructed, not evaluated.
-/

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A full-adelic matrix acts as an additive monoid hom on the coordinate space. -/
def fullAdelicMatrixMulVecAddHom (M : Matrix (Fin n) (Fin n) RationalAdele) :
    (Fin n → RationalAdele) →+ (Fin n → RationalAdele) where
  toFun x := M.mulVec x
  map_zero' := Matrix.mulVec_zero M
  map_add' x y := Matrix.mulVec_add M x y

@[simp]
theorem fullAdelicMatrixMulVecAddHom_apply (M : Matrix (Fin n) (Fin n) RationalAdele)
    (x : Fin n → RationalAdele) :
    fullAdelicMatrixMulVecAddHom M x = M.mulVec x := rfl

/-- A full-adelic matrix unit acts as a homeomorphism of the coordinate space. -/
def fullAdelicMatrixUnitHomeomorph (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    (Fin n → RationalAdele) ≃ₜ (Fin n → RationalAdele) where
  toEquiv := (fullAdelicMatrixUnitMeasurableEquiv g).toEquiv
  continuous_toFun := continuous_fullAdelicMatrixMulVec _
  continuous_invFun := continuous_fullAdelicMatrixMulVec _

/-- The pushforward of the fixed coordinate Haar under a matrix unit is again an additive Haar
measure. -/
instance isAddHaarMeasure_map_fullAdelicMatrixUnit
    (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    (Measure.map (fun x : Fin n → RationalAdele ↦ g.1.mulVec x)
      (rationalAdeleCoordinateAddHaarMeasure n)).IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_map (rationalAdeleCoordinateAddHaarMeasure n)
    (fullAdelicMatrixMulVecAddHom g.1)
    (continuous_fullAdelicMatrixMulVec _)
    (fullAdelicMatrixUnitHomeomorph g).surjective
    (fullAdelicMatrixUnitHomeomorph g).isClosedEmbedding.tendsto_cocompact

/-- The Haar scalar of a full-adelic matrix unit. -/
def fullAdelicMatrixUnitHaarScalar (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) : ℝ≥0 :=
  Measure.addHaarScalarFactor
    (Measure.map (fun x : Fin n → RationalAdele ↦ g.1.mulVec x)
      (rationalAdeleCoordinateAddHaarMeasure n))
    (rationalAdeleCoordinateAddHaarMeasure n)

/-- The defining transport: the pushforward is that scalar times the fixed Haar. -/
theorem map_fullAdelicMatrixUnit_eq_smul (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    Measure.map (fun x : Fin n → RationalAdele ↦ g.1.mulVec x)
        (rationalAdeleCoordinateAddHaarMeasure n) =
      fullAdelicMatrixUnitHaarScalar g • rationalAdeleCoordinateAddHaarMeasure n :=
  Measure.isAddLeftInvariant_eq_smul_of_regular _ _

/-- Scalars are determined by their action on the fixed Haar, because the standard coordinate
block has mass one. -/
theorem nnreal_smul_coordinateHaar_injective {a b : ℝ≥0}
    (h : a • rationalAdeleCoordinateAddHaarMeasure n =
      b • rationalAdeleCoordinateAddHaarMeasure n) : a = b := by
  have hval := congrArg
    (fun mu : Measure (Fin n → RationalAdele) ↦ mu (rationalAdeleCoordinateStandardBlock n)) h
  simp only [Measure.smul_apply,
    rationalAdeleCoordinateAddHaarMeasure_standardBlock] at hval
  simpa [ENNReal.smul_def] using hval

@[simp]
theorem fullAdelicMatrixUnitHaarScalar_one :
    fullAdelicMatrixUnitHaarScalar (1 : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) = 1 := by
  refine nnreal_smul_coordinateHaar_injective (n := n) ?_
  rw [← map_fullAdelicMatrixUnit_eq_smul, one_smul]
  have hid : (fun x : Fin n → RationalAdele ↦
      (1 : (Matrix (Fin n) (Fin n) RationalAdele)ˣ).1.mulVec x) = id := by
    funext x
    simp
  rw [hid, Measure.map_id]

/-- Multiplicativity of the Haar scalar. -/
theorem fullAdelicMatrixUnitHaarScalar_mul
    (g h : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    fullAdelicMatrixUnitHaarScalar (g * h) =
      fullAdelicMatrixUnitHaarScalar g * fullAdelicMatrixUnitHaarScalar h := by
  refine nnreal_smul_coordinateHaar_injective (n := n) ?_
  rw [← map_fullAdelicMatrixUnit_eq_smul]
  have hcomp : (fun x : Fin n → RationalAdele ↦ (g * h).1.mulVec x) =
      (fun x : Fin n → RationalAdele ↦ g.1.mulVec x) ∘
        (fun x : Fin n → RationalAdele ↦ h.1.mulVec x) := by
    funext x
    simp only [Function.comp_apply, Units.val_mul]
    rw [Matrix.mulVec_mulVec]
  rw [hcomp, ← Measure.map_map (continuous_fullAdelicMatrixMulVec _).measurable
    (continuous_fullAdelicMatrixMulVec _).measurable,
    map_fullAdelicMatrixUnit_eq_smul h, Measure.map_smul,
    map_fullAdelicMatrixUnit_eq_smul g, smul_smul, mul_comm]

/-- The Haar scalar is never zero. -/
theorem fullAdelicMatrixUnitHaarScalar_ne_zero
    (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    fullAdelicMatrixUnitHaarScalar g ≠ 0 := by
  have hmul : fullAdelicMatrixUnitHaarScalar g * fullAdelicMatrixUnitHaarScalar g⁻¹ = 1 := by
    rw [← fullAdelicMatrixUnitHaarScalar_mul, mul_inv_cancel,
      fullAdelicMatrixUnitHaarScalar_one]
  intro h0
  rw [h0, zero_mul] at hmul
  exact zero_ne_one hmul

@[simp]
theorem fullAdelicMatrixUnitHaarScalar_inv (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    fullAdelicMatrixUnitHaarScalar g⁻¹ = (fullAdelicMatrixUnitHaarScalar g)⁻¹ := by
  have hmul : fullAdelicMatrixUnitHaarScalar g⁻¹ * fullAdelicMatrixUnitHaarScalar g = 1 := by
    rw [← fullAdelicMatrixUnitHaarScalar_mul, inv_mul_cancel,
      fullAdelicMatrixUnitHaarScalar_one]
  exact eq_inv_of_mul_eq_one_left hmul

/-- Conjugation invariance: no assumption that the conjugating unit preserves the measure. -/
theorem fullAdelicMatrixUnitHaarScalar_conj
    (p g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    fullAdelicMatrixUnitHaarScalar (p * g * p⁻¹) = fullAdelicMatrixUnitHaarScalar g := by
  rw [fullAdelicMatrixUnitHaarScalar_mul, fullAdelicMatrixUnitHaarScalar_mul,
    fullAdelicMatrixUnitHaarScalar_inv,
    mul_comm (fullAdelicMatrixUnitHaarScalar p) (fullAdelicMatrixUnitHaarScalar g),
    mul_assoc, mul_inv_cancel₀ (fullAdelicMatrixUnitHaarScalar_ne_zero p), mul_one]

/-- The scalar is one exactly when the action preserves the fixed Haar. -/
theorem fullAdelicMatrixUnitHaarScalar_eq_one_iff
    (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    fullAdelicMatrixUnitHaarScalar g = 1 ↔
      MeasurePreserving (fun x : Fin n → RationalAdele ↦ g.1.mulVec x)
        (rationalAdeleCoordinateAddHaarMeasure n)
        (rationalAdeleCoordinateAddHaarMeasure n) := by
  constructor
  · intro h
    refine ⟨(continuous_fullAdelicMatrixMulVec _).measurable, ?_⟩
    rw [map_fullAdelicMatrixUnit_eq_smul, h, one_smul]
  · intro h
    refine nnreal_smul_coordinateHaar_injective (n := n) ?_
    rw [← map_fullAdelicMatrixUnit_eq_smul, h.map_eq, one_smul]

/-- The transpose of a full-adelic matrix unit is a unit. -/
def fullAdelicMatrixUnitTranspose (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    (Matrix (Fin n) (Fin n) RationalAdele)ˣ where
  val := g.1ᵀ
  inv := (g⁻¹).1ᵀ
  val_inv := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

@[simp]
theorem fullAdelicMatrixUnitTranspose_val (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    (fullAdelicMatrixUnitTranspose g).1 = g.1ᵀ := rfl

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

open PositiveDefiniteIntegralLattice

/-- The full-adelic polar matrix as a unit, with the image of the rational inverse as its
inverse. -/
def fullAdelicPolarMatrixUnit (V : RationalQuadraticSpaceMatrix n) :
    (Matrix (Fin n) (Fin n) RationalAdele)ˣ where
  val := V.fullAdelicPolarMatrix
  inv := V.polarMatrix⁻¹.map (algebraMap ℚ RationalAdele)
  val_inv := V.fullAdelicPolarMatrix_mul_inv_map
  inv_val := V.fullAdelicPolarMatrix_inv_map_mul

/-- The reciprocal relation: for a full-adelic orthogonal matrix the Haar scalars of `g` and of
its transpose are reciprocal.  Only the conjugation `g^T = C g^-1 C^-1` is used. -/
theorem fullAdelicOrthogonal_haarScalar_transpose_mul_self
    (V : RationalQuadraticSpaceMatrix n) (g : V.fullAdelicOrthogonalMatrixSubgroup) :
    fullAdelicMatrixUnitHaarScalar (fullAdelicMatrixUnitTranspose g.1) *
        fullAdelicMatrixUnitHaarScalar g.1 = 1 := by
  have hunit : fullAdelicMatrixUnitTranspose g.1 =
      V.fullAdelicPolarMatrixUnit * g.1⁻¹ * (V.fullAdelicPolarMatrixUnit)⁻¹ := by
    apply Units.ext
    show g.1.1ᵀ = (V.fullAdelicPolarMatrixUnit).1 * (g.1⁻¹).1 *
      ((V.fullAdelicPolarMatrixUnit)⁻¹).1
    exact V.fullAdelicOrthogonal_transpose_eq g
  rw [hunit, fullAdelicMatrixUnitHaarScalar_conj, fullAdelicMatrixUnitHaarScalar_inv]
  exact inv_mul_cancel₀ (fullAdelicMatrixUnitHaarScalar_ne_zero g.1)

end RationalQuadraticSpaceMatrix

end
