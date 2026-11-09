import SMSFormula.RationalIdeleClassLogSection

/-!
# Splitting rational idele classes by the logarithmic module

The exponential idele-class section is a continuous homomorphism from the
additive real line.  It therefore splits the rational idele-class group as
the product of the kernel of the logarithmic module and its real logarithmic
coordinate.  This is the carrier-level decomposition needed to compare Haar
measure with Lebesgue measure in the crossed `GSpin` cutoff.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

@[simp]
theorem rationalIdeleLogSection_zero :
    rationalIdeleLogSection 0 = 1 := by
  apply rationalAdeleUnitsRealFiniteContinuousEquiv.injective
  simp [rationalIdeleLogSection, realExpUnit]

theorem rationalIdeleLogSection_add (s t : ℝ) :
    rationalIdeleLogSection (s + t) =
      rationalIdeleLogSection s * rationalIdeleLogSection t := by
  apply rationalAdeleUnitsRealFiniteContinuousEquiv.injective
  simp [rationalIdeleLogSection, realExpUnit, Real.exp_add]

@[simp]
theorem rationalIdeleClassLogSection_zero :
    rationalIdeleClassLogSection 0 = 1 := by
  simp [rationalIdeleClassLogSection]

theorem rationalIdeleClassLogSection_add (s t : ℝ) :
    rationalIdeleClassLogSection (s + t) =
      rationalIdeleClassLogSection s * rationalIdeleClassLogSection t := by
  simp only [rationalIdeleClassLogSection, rationalIdeleLogSection_add,
    map_mul]

/-- The real logarithmic section as a multiplicative homomorphism from the
additive real line. -/
def rationalIdeleClassLogSectionHom :
    Multiplicative ℝ →* RationalIdeleClassGroup where
  toFun t := rationalIdeleClassLogSection t.toAdd
  map_one' := rationalIdeleClassLogSection_zero
  map_mul' s t := rationalIdeleClassLogSection_add s.toAdd t.toAdd

theorem continuous_rationalIdeleClassLogSectionHom :
    Continuous rationalIdeleClassLogSectionHom :=
  continuous_rationalIdeleClassLogSection

/-- The logarithmic module as a multiplicative homomorphism to the additive
real line written multiplicatively. -/
def rationalIdeleClassLogModuleHom :
    RationalIdeleClassGroup →* Multiplicative ℝ where
  toFun c := Multiplicative.ofAdd (rationalIdeleClassLogModule c)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp [rationalIdeleClassLogModule, rationalIdeleClassModuleHom]
  map_mul' a b := congrArg Multiplicative.ofAdd
    (rationalIdeleClassLogModule_mul a b)

theorem continuous_rationalIdeleClassLogModuleHom :
    Continuous rationalIdeleClassLogModuleHom :=
  continuous_rationalIdeleClassLogModule

/-- Norm-one rational idele classes, equivalently the kernel of the
logarithmic module. -/
abbrev RationalIdeleClassNormOne :=
  rationalIdeleClassLogModuleHom.ker

/-- Split an idele class into its norm-one part and logarithmic coordinate. -/
def rationalIdeleClassLogSplitMulEquiv :
    RationalIdeleClassGroup ≃* RationalIdeleClassNormOne × Multiplicative ℝ where
  toFun c :=
    (⟨rationalIdeleClassLogSection (-rationalIdeleClassLogModule c) * c, by
      change Multiplicative.ofAdd
          (rationalIdeleClassLogModule
            (rationalIdeleClassLogSection (-rationalIdeleClassLogModule c) * c)) = 1
      apply Multiplicative.toAdd.injective
      simp [rationalIdeleClassLogModule_mul,
        rationalIdeleClassLogModule_logSection]⟩,
      Multiplicative.ofAdd (rationalIdeleClassLogModule c))
  invFun x := rationalIdeleClassLogSection x.2.toAdd * x.1
  left_inv c := by
    change rationalIdeleClassLogSection (rationalIdeleClassLogModule c) *
        (rationalIdeleClassLogSection (-rationalIdeleClassLogModule c) * c) = c
    rw [← mul_assoc, ← rationalIdeleClassLogSection_add]
    rw [add_neg_cancel, rationalIdeleClassLogSection_zero]
    change (1 : RationalIdeleClassGroup) * c = c
    exact one_mul c
  right_inv x := by
    rcases x with ⟨k, t⟩
    apply Prod.ext
    · apply Subtype.ext
      change rationalIdeleClassLogSection
          (-rationalIdeleClassLogModule
            (rationalIdeleClassLogSection t.toAdd * (k : RationalIdeleClassGroup))) *
          (rationalIdeleClassLogSection t.toAdd * (k : RationalIdeleClassGroup)) = k
      have hk : rationalIdeleClassLogModule (k : RationalIdeleClassGroup) = 0 := by
        have := k.property
        exact congrArg Multiplicative.toAdd this
      simp [rationalIdeleClassLogModule_mul,
        rationalIdeleClassLogModule_logSection, hk]
      rw [← mul_assoc, ← rationalIdeleClassLogSection_add]
      rw [neg_add_cancel, rationalIdeleClassLogSection_zero]
      change (1 : RationalIdeleClassGroup) * (k : RationalIdeleClassGroup) = k
      exact one_mul (k : RationalIdeleClassGroup)
    · apply Multiplicative.toAdd.injective
      have hk : rationalIdeleClassLogModule (k : RationalIdeleClassGroup) = 0 := by
        have := k.property
        exact congrArg Multiplicative.toAdd this
      simp [rationalIdeleClassLogModule_mul,
        rationalIdeleClassLogModule_logSection, hk]
  map_mul' a b := by
    apply Prod.ext
    · apply Subtype.ext
      change rationalIdeleClassLogSection
          (-rationalIdeleClassLogModule (a * b)) * (a * b) =
        (rationalIdeleClassLogSection (-rationalIdeleClassLogModule a) * a) *
          (rationalIdeleClassLogSection (-rationalIdeleClassLogModule b) * b)
      rw [rationalIdeleClassLogModule_mul, neg_add,
        rationalIdeleClassLogSection_add]
      exact mul_mul_mul_comm
        (rationalIdeleClassLogSection (-rationalIdeleClassLogModule a))
        (rationalIdeleClassLogSection (-rationalIdeleClassLogModule b)) a b
    · apply Multiplicative.toAdd.injective
      exact rationalIdeleClassLogModule_mul a b

/-- The logarithmic splitting is a homeomorphism for the existing quotient
topology and the subtype topology on the norm-one kernel. -/
def rationalIdeleClassLogSplitContinuousMulEquiv :
    RationalIdeleClassGroup ≃ₜ* RationalIdeleClassNormOne × Multiplicative ℝ :=
  ContinuousMulEquiv.mk'
    { toEquiv := rationalIdeleClassLogSplitMulEquiv.toEquiv
      continuous_toFun := by
        apply Continuous.prodMk
        · exact Continuous.subtype_mk
            ((continuous_rationalIdeleClassLogSection.comp
                continuous_rationalIdeleClassLogModule.neg).mul continuous_id) _
        · exact continuous_rationalIdeleClassLogModule
      continuous_invFun := by
        exact (continuous_rationalIdeleClassLogSection.comp continuous_snd).mul
          (continuous_subtype_val.comp continuous_fst) }
    rationalIdeleClassLogSplitMulEquiv.map_mul

@[simp]
theorem rationalIdeleClassLogSplitContinuousMulEquiv_apply_log
    (c : RationalIdeleClassGroup) :
    (rationalIdeleClassLogSplitContinuousMulEquiv c).2.toAdd =
      rationalIdeleClassLogModule c :=
  rfl

end RationalQuadraticSpaceMatrix
