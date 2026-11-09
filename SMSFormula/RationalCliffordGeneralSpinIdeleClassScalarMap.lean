import SMSFormula.RationalCliffordGeneralSpinQuotientLogCutoff

/-!
# Central idele classes in the adelic general-Spin quotient

The literal central scalar inclusion descends from rational ideles to the
rational adelic `GSpin` quotient.  Composing with the descended similitude
map is exactly squaring on rational idele classes.  Consequently the
logarithmic module doubles on this horizontal crossed-diagram arrow.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Rational scalar extension commutes with the central scalar inclusion in
intrinsic general Spin. -/
theorem rational_fullAdelic_diagonal_generalSpinScalar
    (q : ℚˣ) :
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele
        (rationalUnitFullAdelicDiagonalHom q) =
      V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ q) := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V RationalAdele
  apply Units.ext
  rfl

/-- The central idele map into the rational adelic general-Spin quotient. -/
def rationalIdeleClassToFullAdelicCliffordGeneralSpinLeftQuotient :
    RationalIdeleClassGroup →
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Quot.lift
    (fun a => V.fullAdelicCliffordGeneralSpinLeftQuotientMap
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a)) (by
        intro a b hab
        have habq : QuotientGroup.mk' rationalIdeleDiagonalSubgroup a =
            QuotientGroup.mk' rationalIdeleDiagonalSubgroup b :=
          Quotient.sound hab
        have hdiv : a / b ∈ rationalIdeleDiagonalSubgroup :=
          (QuotientGroup.eq_iff_div_mem).mp habq
        rcases hdiv with ⟨q, hq⟩
        have hab' : a = rationalUnitFullAdelicDiagonalHom q * b := by
          calc
            a = (a / b) * b := by simp
            _ = rationalUnitFullAdelicDiagonalHom q * b := by rw [hq]
        rw [hab']
        change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele
              (rationalUnitFullAdelicDiagonalHom q * b)) =
          V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele b)
        rw [map_mul,
          V.rational_fullAdelic_diagonal_generalSpinScalar]
        exact leftCosetMap_gamma_mul
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
          ⟨V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
              (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ q),
            ⟨CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ q, rfl⟩⟩
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele b))

@[simp]
theorem rationalIdeleClassToFullAdelicCliffordGeneralSpinLeftQuotient_mk
    (a : RationalAdeleˣ) :
    V.rationalIdeleClassToFullAdelicCliffordGeneralSpinLeftQuotient
        (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a) :=
  rfl

theorem continuous_rationalIdeleClassToFullAdelicCliffordGeneralSpinLeftQuotient :
    Continuous V.rationalIdeleClassToFullAdelicCliffordGeneralSpinLeftQuotient := by
  apply Continuous.quotient_lift
  exact V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap.continuous.comp
    V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom

/-- The crossed composite along central scalars is literal squaring on
rational idele classes. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_scalar
    (c : RationalIdeleClassGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
        (V.rationalIdeleClassToFullAdelicCliffordGeneralSpinLeftQuotient c) =
      c ^ 2 := by
  induction c using QuotientGroup.induction_on with
  | _ a =>
    change QuotientGroup.mk' rationalIdeleDiagonalSubgroup
        (V.fullAdelicCliffordGeneralSpinSimilitudeHom
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a)) =
      (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a) ^ 2
    change QuotientGroup.mk' rationalIdeleDiagonalSubgroup (a ^ 2) =
      (QuotientGroup.mk' rationalIdeleDiagonalSubgroup a) ^ 2
    exact map_pow _ a 2

/-- The quotient logarithmic module doubles along the central scalar map. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientLogModule_scalar
    (c : RationalIdeleClassGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
        (V.rationalIdeleClassToFullAdelicCliffordGeneralSpinLeftQuotient c) =
      2 * rationalIdeleClassLogModule c := by
  rw [fullAdelicCliffordGeneralSpinLeftQuotientLogModule,
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_scalar,
    rationalIdeleClassLogModule_sq]

/-- On the logarithmic real section the crossed scalar arrow is exactly
dilation by two. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientLogModule_scalar_logSection
    (t : ℝ) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
        (V.rationalIdeleClassToFullAdelicCliffordGeneralSpinLeftQuotient
          (rationalIdeleClassLogSection t)) = 2 * t := by
  rw [V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_scalar,
    rationalIdeleClassLogModule_logSection]

end RationalQuadraticSpaceMatrix
