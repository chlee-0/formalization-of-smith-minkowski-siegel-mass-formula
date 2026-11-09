import SMSFormula.RationalAdeleAdditiveQuotientCharacter
import SMSFormula.RationalAdeleVectorPolarPairing
import SMSFormula.RationalCliffordGeneralSpinAllRationalShellIndex

/-!
# The rational rank-one adelic quadratic phase

This file isolates the unipotent phase needed by the authorized rational
rank-one Weil argument.  It evaluates the existing rational quadratic form on
the actual full adelic vector carrier and applies the already normalized
global additive character.

On rational diagonal vectors the phase has the rational frequency
`q_V(x)`.  It therefore descends in the additive parameter to the literal
compact quotient `𝔸_ℚ / ℚ`.  The descended phase is constant on every literal
rational norm fiber, and its shifted probability-Haar integral is the exact
Kronecker delta selecting a prescribed rational norm.

No Weil representation, Schwartz space, Fourier invariance, convergence
claim, or Siegel--Weil theorem is introduced here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The existing rational quadratic form evaluated on the native full adelic
vector carrier. -/
def fullAdelicQuadraticFormValue
    (V : RationalQuadraticSpaceMatrix n)
    (x : Fin n → RationalAdele) : RationalAdele :=
  V.commutativeScalarExtensionQuadraticForm RationalAdele x

/-- The full adelic quadratic value is the expected matrix expression. -/
theorem fullAdelicQuadraticFormValue_eq_dotProduct
    (V : RationalQuadraticSpaceMatrix n)
    (x : Fin n → RationalAdele) :
    V.fullAdelicQuadraticFormValue x =
      dotProduct x (V.fullAdelicFormMatrix.mulVec x) := by
  simp [fullAdelicQuadraticFormValue,
    commutativeScalarExtensionQuadraticForm,
    commutativeScalarExtensionFormMatrix, fullAdelicFormMatrix,
    Matrix.toQuadraticMap', Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']

/-- The adelic quadratic value is continuous on the native finite-coordinate
carrier. -/
theorem continuous_fullAdelicQuadraticFormValue
    (V : RationalQuadraticSpaceMatrix n) :
    Continuous V.fullAdelicQuadraticFormValue := by
  have hfun : V.fullAdelicQuadraticFormValue =
      fun x => dotProduct x (V.fullAdelicFormMatrix.mulVec x) := by
    funext x
    exact V.fullAdelicQuadraticFormValue_eq_dotProduct x
  rw [hfun]
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

/-- Scalar extension sends the rational quadratic value to the literal
adelic quadratic value of the rational diagonal vector. -/
theorem fullAdelicQuadraticFormValue_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ) :
    V.fullAdelicQuadraticFormValue
        (fun i => algebraMap ℚ RationalAdele (x i)) =
      algebraMap ℚ RationalAdele (V.nativeRationalQuadraticForm x) := by
  simp [fullAdelicQuadraticFormValue, nativeRationalQuadraticForm, quadraticForm,
    commutativeScalarExtensionQuadraticForm,
    commutativeScalarExtensionFormMatrix, Matrix.toQuadraticMap',
    Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct, map_sum]

/-- The rank-one quadratic phase on the actual adelic vector carrier. -/
def rationalAdeleRankOneQuadraticPhase
    (V : RationalQuadraticSpaceMatrix n)
    (a : RationalAdele) (x : Fin n → RationalAdele) : Circle :=
  rationalAdeleFourierChar (a * V.fullAdelicQuadraticFormValue x)

/-- The quadratic phase is jointly continuous in its additive parameter and
adelic vector. -/
theorem continuous_rationalAdeleRankOneQuadraticPhase
    (V : RationalQuadraticSpaceMatrix n) :
    Continuous (fun p : RationalAdele × (Fin n → RationalAdele) ↦
      V.rationalAdeleRankOneQuadraticPhase p.1 p.2) := by
  exact continuous_rationalAdeleFourierChar.comp
    (continuous_fst.mul
      (V.continuous_fullAdelicQuadraticFormValue.comp continuous_snd))

/-- The corresponding elementary unipotent operator on complex-valued test
functions.  Analytic stability hypotheses are deliberately left to the
specialized test-function layer. -/
def rationalAdeleRankOneUnipotentOperator
    (V : RationalQuadraticSpaceMatrix n)
    (a : RationalAdele)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    (Fin n → RationalAdele) → ℂ :=
  fun x ↦ (V.rationalAdeleRankOneQuadraticPhase a x : ℂ) * Phi x

/-- On a rational diagonal vector, the native adelic phase is exactly the
rational-frequency global character. -/
theorem rationalAdeleRankOneQuadraticPhase_rationalDiagonal
    (V : RationalQuadraticSpaceMatrix n)
    (a : RationalAdele) (x : Fin n → ℚ) :
    V.rationalAdeleRankOneQuadraticPhase a
        (fun i => algebraMap ℚ RationalAdele (x i)) =
      rationalAdeleScaledFourierChar (V.nativeRationalQuadraticForm x) a := by
  rw [rationalAdeleRankOneQuadraticPhase,
    V.fullAdelicQuadraticFormValue_rationalDiagonal,
    rationalAdeleScaledFourierChar_apply, mul_comm]

/-- The quadratic phase of a rational vector, with its additive parameter
already descended to `𝔸_ℚ / ℚ`. -/
def rationalAdeleModRationalQuadraticPhase
    (V : RationalQuadraticSpaceMatrix n)
    (x : Fin n → ℚ) (a : RationalAdeleModRational) : Circle :=
  rationalAdeleModRationalFourierChar
    (V.nativeRationalQuadraticForm x) a

theorem continuous_rationalAdeleModRationalQuadraticPhase
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ) :
    Continuous (V.rationalAdeleModRationalQuadraticPhase x) :=
  continuous_rationalAdeleModRationalFourierChar _

/-- The quotient phase pulls back to the native adelic phase on every
rational diagonal vector. -/
theorem rationalAdeleModRationalQuadraticPhase_quotientMap
    (V : RationalQuadraticSpaceMatrix n)
    (x : Fin n → ℚ) (a : RationalAdele) :
    V.rationalAdeleModRationalQuadraticPhase x
        (rationalAdeleModRationalQuotientMap a) =
      V.rationalAdeleRankOneQuadraticPhase a
        (fun i => algebraMap ℚ RationalAdele (x i)) := by
  rw [rationalAdeleModRationalQuadraticPhase,
    rationalAdeleModRationalFourierChar_mk,
    V.rationalAdeleRankOneQuadraticPhase_rationalDiagonal]

/-- The descended phase is constant on a literal represented-norm fiber. -/
theorem rationalAdeleModRationalQuadraticPhase_of_mem_fiber
    (V : RationalQuadraticSpaceMatrix n)
    (b : V.RepresentedNonzeroRationalNorm)
    (x : b.rationalVectorFiber V) (a : RationalAdeleModRational) :
    V.rationalAdeleModRationalQuadraticPhase x.1 a =
      rationalAdeleModRationalFourierChar b.1 a := by
  rw [rationalAdeleModRationalQuadraticPhase, x.property]

/-- The shifted quotient phase used to extract the coefficient at a prescribed
rational norm. -/
def rationalAdeleModRationalNormExtractionPhase
    (V : RationalQuadraticSpaceMatrix n)
    (b : ℚ) (x : Fin n → ℚ) (a : RationalAdeleModRational) : Circle :=
  rationalAdeleModRationalFourierChar
    (V.nativeRationalQuadraticForm x - b) a

theorem continuous_rationalAdeleModRationalNormExtractionPhase
    (V : RationalQuadraticSpaceMatrix n)
    (b : ℚ) (x : Fin n → ℚ) :
    Continuous (V.rationalAdeleModRationalNormExtractionPhase b x) :=
  continuous_rationalAdeleModRationalFourierChar _

/-- Pointwise rational norm extraction by the compact quotient character. -/
theorem integral_rationalAdeleModRationalNormExtractionPhase
    (V : RationalQuadraticSpaceMatrix n)
    (b : ℚ) (x : Fin n → ℚ) :
    ∫ a, (V.rationalAdeleModRationalNormExtractionPhase b x a : ℂ)
        ∂rationalAdeleModRationalProbabilityHaarMeasure =
      if V.nativeRationalQuadraticForm x = b then 1 else 0 := by
  change
    (∫ a, (rationalAdeleModRationalFourierChar
      (V.nativeRationalQuadraticForm x - b) a : ℂ)
      ∂rationalAdeleModRationalProbabilityHaarMeasure) = _
  rw [integral_rationalAdeleModRationalFourierChar]
  by_cases h : V.nativeRationalQuadraticForm x = b
  · rw [if_pos h, if_pos (sub_eq_zero.mpr h)]
  · rw [if_neg h, if_neg (sub_ne_zero.mpr h)]

end RationalQuadraticSpaceMatrix

end
