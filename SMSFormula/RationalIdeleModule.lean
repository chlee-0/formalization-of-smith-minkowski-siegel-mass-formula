import SMSFormula.RationalIdeleFiniteModule

/-!
# The rational idele module

The real--finite splitting of rational ideles and the finite module give the
usual positive idelic module.  This file keeps the construction on the
literal adelic carrier used by intrinsic `GSpin`, proves the rational product
formula, and records the squaring law responsible for the index two in the
crossed comparison.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

/-- The positive module of a rational idele, written through the literal
real--finite splitting. -/
def rationalIdeleModuleNNReal (a : RationalAdeleˣ) : ℝ≥0 :=
  ‖((rationalAdeleUnitsRealFiniteContinuousEquiv a).1 : ℝ)‖₊ *
    finiteIdeleModuleNNReal
      (rationalAdeleUnitsRealFiniteContinuousEquiv a).2

theorem rationalIdeleModuleNNReal_mul (a b : RationalAdeleˣ) :
    rationalIdeleModuleNNReal (a * b) =
      rationalIdeleModuleNNReal a * rationalIdeleModuleNNReal b := by
  simp only [rationalIdeleModuleNNReal, map_mul, Prod.fst_mul, Prod.snd_mul,
    Units.val_mul, nnnorm_mul, finiteIdeleModuleNNReal_mul]
  ac_rfl

theorem rationalIdeleModuleNNReal_one : rationalIdeleModuleNNReal 1 = 1 := by
  simp [rationalIdeleModuleNNReal, finiteIdeleModuleNNReal_one]

theorem rationalIdeleModuleNNReal_ne_zero (a : RationalAdeleˣ) :
    rationalIdeleModuleNNReal a ≠ 0 := by
  rw [rationalIdeleModuleNNReal]
  exact mul_ne_zero (ne_of_gt (nnnorm_pos.mpr (Units.ne_zero _)))
    (finiteIdeleModuleNNReal_ne_zero _)

/-- The rational idele module as a multiplicative homomorphism to positive
nonnegative-real units. -/
def rationalIdeleModuleHom : RationalAdeleˣ →* ℝ≥0ˣ where
  toFun a := Units.mk0 (rationalIdeleModuleNNReal a)
    (rationalIdeleModuleNNReal_ne_zero a)
  map_one' := by
    apply Units.ext
    exact rationalIdeleModuleNNReal_one
  map_mul' a b := by
    apply Units.ext
    exact rationalIdeleModuleNNReal_mul a b

@[simp]
theorem coe_rationalIdeleModuleHom (a : RationalAdeleˣ) :
    (rationalIdeleModuleHom a : ℝ≥0) = rationalIdeleModuleNNReal a :=
  rfl

/-- The full idelic module is trivial on the rational diagonal. -/
theorem rationalIdeleModuleNNReal_rationalUnitDiagonal (q : ℚˣ) :
    rationalIdeleModuleNNReal (rationalUnitFullAdelicDiagonalHom q) = 1 := by
  apply ENNReal.coe_injective
  rw [ENNReal.coe_one]
  change
    (‖(((rationalAdeleUnitsRealFiniteContinuousEquiv
        (rationalUnitFullAdelicDiagonalHom q)).1 : ℝ))‖₊ : ℝ≥0∞) *
      (finiteIdeleModuleNNReal
        (rationalAdeleUnitsRealFiniteContinuousEquiv
          (rationalUnitFullAdelicDiagonalHom q)).2 : ℝ≥0∞) = 1
  rw [rationalAdeleUnitsRealFiniteContinuousEquiv_rationalUnitDiagonal]
  change (‖((q : ℚ) : ℝ)‖₊ : ℝ≥0∞) *
    (finiteIdeleModuleNNReal
      (rationalUnitFiniteAdelicDiagonalHom q) : ℝ≥0∞) = 1
  have hnorm : (‖((q : ℚ) : ℝ)‖₊ : ℝ≥0∞) =
      ENNReal.ofReal |((q : ℚ) : ℝ)| := by
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  rw [hnorm]
  exact rationalUnitDiagonal_finiteIdeleModule_productFormula q

/-- The idele module turns squaring into literal squaring of the positive
module. -/
theorem rationalIdeleModuleNNReal_sq (a : RationalAdeleˣ) :
    rationalIdeleModuleNNReal (a ^ 2) =
      rationalIdeleModuleNNReal a ^ 2 := by
  rw [pow_two, rationalIdeleModuleNNReal_mul, pow_two]

/-- The logarithmic idele module used by compact cutoffs. -/
def rationalIdeleLogModule (a : RationalAdeleˣ) : ℝ :=
  Real.log (rationalIdeleModuleNNReal a : ℝ)

theorem rationalIdeleLogModule_mul (a b : RationalAdeleˣ) :
    rationalIdeleLogModule (a * b) =
      rationalIdeleLogModule a + rationalIdeleLogModule b := by
  unfold rationalIdeleLogModule
  rw [rationalIdeleModuleNNReal_mul, NNReal.coe_mul]
  exact Real.log_mul
    (NNReal.coe_ne_zero.mpr (rationalIdeleModuleNNReal_ne_zero a))
    (NNReal.coe_ne_zero.mpr (rationalIdeleModuleNNReal_ne_zero b))

theorem rationalIdeleLogModule_rationalUnitDiagonal (q : ℚˣ) :
    rationalIdeleLogModule (rationalUnitFullAdelicDiagonalHom q) = 0 := by
  rw [rationalIdeleLogModule,
    rationalIdeleModuleNNReal_rationalUnitDiagonal, NNReal.coe_one,
    Real.log_one]

/-- The literal scalar squaring map doubles the logarithmic module. -/
theorem rationalIdeleLogModule_sq (a : RationalAdeleˣ) :
    rationalIdeleLogModule (a ^ 2) = 2 * rationalIdeleLogModule a := by
  rw [pow_two, rationalIdeleLogModule_mul]
  ring

end RationalQuadraticSpaceMatrix
