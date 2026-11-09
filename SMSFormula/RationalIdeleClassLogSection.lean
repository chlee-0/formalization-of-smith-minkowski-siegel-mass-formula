import SMSFormula.RationalIdeleClassModule

/-!
# A logarithmic section of rational idele classes

The real exponential, with all finite components equal to one, gives a
continuous section of the logarithmic module on rational idele classes.  In
particular that module is onto `R`; combined with its squaring law, this
isolates the literal dilation-by-two map used in the crossed cutoff.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

/-- The positive real unit with value `exp t`. -/
def realExpUnit (t : ℝ) : ℝˣ :=
  Units.mk0 (Real.exp t) (Real.exp_ne_zero t)

@[simp]
theorem coe_realExpUnit (t : ℝ) : (realExpUnit t : ℝ) = Real.exp t :=
  rfl

theorem continuous_realExpUnit : Continuous realExpUnit := by
  apply Units.continuous_iff.mpr
  constructor
  · exact Real.continuous_exp
  · change Continuous (fun t : ℝ => (Real.exp t)⁻¹)
    simpa only [← Real.exp_neg] using
      Real.continuous_exp.comp continuous_neg

/-- The full idele having real component `exp t` and trivial finite
component. -/
def rationalIdeleLogSection (t : ℝ) : RationalAdeleˣ :=
  rationalAdeleUnitsRealFiniteContinuousEquiv.symm (realExpUnit t, 1)

theorem rationalAdeleUnitsRealFiniteContinuousEquiv_logSection (t : ℝ) :
    rationalAdeleUnitsRealFiniteContinuousEquiv
        (rationalIdeleLogSection t) =
      (realExpUnit t, 1) :=
  rationalAdeleUnitsRealFiniteContinuousEquiv.apply_symm_apply _

theorem continuous_rationalIdeleLogSection :
    Continuous rationalIdeleLogSection := by
  exact rationalAdeleUnitsRealFiniteContinuousEquiv.symm.continuous.comp
    (continuous_realExpUnit.prodMk continuous_const)

theorem rationalIdeleModuleNNReal_logSection (t : ℝ) :
    rationalIdeleModuleNNReal (rationalIdeleLogSection t) =
      ‖Real.exp t‖₊ := by
  unfold rationalIdeleModuleNNReal
  rw [rationalAdeleUnitsRealFiniteContinuousEquiv_logSection]
  simp [finiteIdeleModuleNNReal_one]

theorem rationalIdeleLogModule_logSection (t : ℝ) :
    rationalIdeleLogModule (rationalIdeleLogSection t) = t := by
  rw [rationalIdeleLogModule, rationalIdeleModuleNNReal_logSection]
  change Real.log ‖Real.exp t‖ = t
  rw [Real.norm_of_nonneg (Real.exp_pos t).le, Real.log_exp]

/-- The logarithmic section on the rational idele-class quotient. -/
def rationalIdeleClassLogSection (t : ℝ) : RationalIdeleClassGroup :=
  QuotientGroup.mk' rationalIdeleDiagonalSubgroup
    (rationalIdeleLogSection t)

theorem continuous_rationalIdeleClassLogSection :
    Continuous rationalIdeleClassLogSection :=
  continuous_quot_mk.comp continuous_rationalIdeleLogSection

theorem rationalIdeleClassLogModule_logSection (t : ℝ) :
    rationalIdeleClassLogModule (rationalIdeleClassLogSection t) = t := by
  exact rationalIdeleLogModule_logSection t

theorem rationalIdeleClassLogModule_surjective :
    Function.Surjective rationalIdeleClassLogModule := by
  intro t
  exact ⟨rationalIdeleClassLogSection t,
    rationalIdeleClassLogModule_logSection t⟩

end RationalQuadraticSpaceMatrix
