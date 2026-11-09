import SMSFormula.RationalCliffordGeneralSpinLatticeFiniteAdelicSimilitude
import SMSFormula.RationalCliffordGeneralSpinLatticeRealSimilitude

/-!
# Full-adelic similitudes of the lattice intrinsic general-Spin group

The literal real--finite splitting combines the positive real similitude
image with finite-adelic surjectivity.  Hence the full-adelic image is exactly
the ideles whose real component is positive.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

/-- Rational ideles positive at the unique real place. -/
def positiveRationalAdeleUnitsSubgroup : Subgroup RationalAdeleˣ :=
  (positiveRealUnitsSubgroup.prod ⊤).comap
    rationalAdeleUnitsRealFiniteContinuousEquiv.toMonoidHom

theorem mem_positiveRationalAdeleUnitsSubgroup_iff
    (a : RationalAdeleˣ) :
    a ∈ positiveRationalAdeleUnitsSubgroup ↔
      0 < ((rationalAdeleUnitsRealFiniteContinuousEquiv a).1 : ℝ) := by
  change
    (rationalAdeleUnitsRealFiniteContinuousEquiv a).1 ∈ positiveRealUnitsSubgroup ∧
      (rationalAdeleUnitsRealFiniteContinuousEquiv a).2 ∈
        (⊤ : Subgroup RationalFiniteAdeleˣ) ↔ _
  simp [positiveRealUnitsSubgroup]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

/-- The full-adelic intrinsic general-Spin similitude image is exactly the
ideles positive at the real place. -/
theorem range_fullAdelicCliffordGeneralSpinSimilitudeHom_eq_positive
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom.range =
      RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup := by
  let V := L.rationalQuadraticSpaceMatrix
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    rw [RationalQuadraticSpaceMatrix.mem_positiveRationalAdeleUnitsSubgroup_iff]
    change 0 <
      ((RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv
        (V.fullAdelicCliffordGeneralSpinSimilitudeHom x)).1 : ℝ)
    rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_similitude]
    exact RationalQuadraticSpaceMatrix.realCliffordGeneralSpinSimilitude_pos L
      (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv x).1
  · intro ha
    rw [RationalQuadraticSpaceMatrix.mem_positiveRationalAdeleUnitsSubgroup_iff] at ha
    change 0 <
      ((RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv a).1 : ℝ)
      at ha
    let ar :=
      (RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv a).1
    let af :=
      (RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv a).2
    obtain ⟨xr, hxr⟩ :=
      RationalQuadraticSpaceMatrix.exists_realCliffordGeneralSpin_similitude_eq_of_pos
        L ar ha
    obtain ⟨xf, hxf⟩ :=
      finiteAdelicCliffordGeneralSpinSimilitudeHom_surjective L hr af
    let x : V.FullAdelicCliffordGeneralSpinGroup :=
      V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm (xr, xf)
    refine ⟨x, ?_⟩
    apply RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv.injective
    rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_similitude]
    rw [show V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv x = (xr, xf) by
      exact V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply
        (xr, xf)]
    change
      (V.realCliffordGeneralSpinSimilitudeHom xr,
        V.finiteAdelicCliffordGeneralSpinSimilitudeHom xf) =
      RationalQuadraticSpaceMatrix.rationalAdeleUnitsRealFiniteContinuousEquiv a
    rw [hxr, hxf]

end PositiveDefiniteIntegralLattice
