import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellMeasurableWeil
import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellQuotientInvariant

/-!
# The native shell measure is invariant under the acting group

The shell measure is the pushforward of the native Riesz quotient measure along the existing
homogeneous-space bijection, and that quotient measure is already proved invariant under left
multiplication by every ambient full-adelic `GSpin` point.  Transporting the statement gives
invariance of the shell measure itself, under the literal matrix action on shell vectors.

Together with the existing transitivity of the acting group on the full-adelic shell, this is
the invariance half of the uniqueness input that the common-shell bridge needs: any other
invariant measure on the shell can then differ only by a scalar.

Negative scope: invariance and transitivity do not by themselves identify the shell measure
with the fiber density of the vector Haar.  No disintegration is constructed here, no scalar is
determined, and uniqueness itself is not invoked.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance fullAdelicShellMeasureInvariantCopyInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance fullAdelicShellMeasureInvariantCopyFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance fullAdelicShellMeasureInvariantCopyT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance fullAdelicShellMeasureInvariantCopySourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance fullAdelicShellMeasureInvariantCopySourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance fullAdelicShellMeasureInvariantCopySourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance fullAdelicShellMeasureInvariantCopySourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellMeasureInvariantCopyStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance fullAdelicShellMeasureInvariantCopyQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance fullAdelicShellMeasureInvariantCopyQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellMeasureInvariantCopyQuotientLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instLocallyCompactSpace
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance fullAdelicShellMeasureInvariantCopyQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance fullAdelicShellMeasureInvariantCopyQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

noncomputable local instance fullAdelicShellMeasureInvariantCopyTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance fullAdelicShellMeasureInvariantCopyTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

/-- Translation of the shell by an ambient full-adelic `GSpin` point, defined through the
existing homogeneous-space bijection. -/
noncomputable def fullAdelicNonisotropicLastShellTranslate
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup) :
    W.nonisotropicLastQuadraticShell a ha RationalAdele →
      W.nonisotropicLastQuadraticShell a ha RationalAdele :=
  fun x => W.fullAdelicNonisotropicLastShellQuotientMap a ha
    (g • (W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm x)

/-- The translate intertwines the quotient map, by construction. -/
theorem fullAdelicNonisotropicLastShellTranslate_quotientMap
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (q : W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :
    W.fullAdelicNonisotropicLastShellTranslate a ha g
        (W.fullAdelicNonisotropicLastShellQuotientMap a ha q) =
      W.fullAdelicNonisotropicLastShellQuotientMap a ha (g • q) := by
  rw [fullAdelicNonisotropicLastShellTranslate]
  congr 1
  exact congrArg (fun y => g • y)
    ((W.fullAdelicNonisotropicLastShellQuotientEquiv a ha).symm_apply_apply q)

/-- The abstract translate is the literal matrix action on shell vectors. -/
theorem coe_fullAdelicNonisotropicLastShellTranslate
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup)
    (x : W.nonisotropicLastQuadraticShell a ha RationalAdele) :
    (W.fullAdelicNonisotropicLastShellTranslate a ha g x).1 =
      g.matrixPoint.1 *ᵥ x.1 := by
  obtain ⟨h, rfl⟩ :=
    CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective
      W a ha x
  have hq : W.fullAdelicNonisotropicLastShellQuotientMap a ha (QuotientGroup.mk h) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele h :=
    rfl
  rw [← hq, W.fullAdelicNonisotropicLastShellTranslate_quotientMap a ha g (QuotientGroup.mk h)]
  show (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele (g * h)).1 = _
  exact CliffordGeneralSpinIntrinsicPoint.coe_nonisotropicLastShellOrbitMap_mul W a ha g h

theorem measurable_fullAdelicNonisotropicLastShellTranslate
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup) :
    Measurable (W.fullAdelicNonisotropicLastShellTranslate a ha g) := by
  let e : W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha ≃ₜ
      W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha := Homeomorph.smul g
  refine Measurable.comp
    ((W.continuous_fullAdelicNonisotropicLastShellQuotientMap a ha).measurable) ?_
  exact Measurable.comp e.continuous.measurable
    (W.measurable_fullAdelicNonisotropicLastShellQuotientEquiv_symm a ha)

/-- The invariance.  The native shell measure is unchanged by the acting group. -/
theorem map_fullAdelicNonisotropicLastShellMeasure_translate
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup) :
    Measure.map (W.fullAdelicNonisotropicLastShellTranslate a ha g)
        (W.fullAdelicNonisotropicLastShellMeasure a ha) =
      W.fullAdelicNonisotropicLastShellMeasure a ha := by
  let e : W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha ≃ₜ
      W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha := Homeomorph.smul g
  have hqmap : Measurable (W.fullAdelicNonisotropicLastShellQuotientMap a ha) :=
    (W.continuous_fullAdelicNonisotropicLastShellQuotientMap a ha).measurable
  have hsmul : Measurable
      (fun q : W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha => g • q) :=
    e.continuous.measurable
  have hcomp : (W.fullAdelicNonisotropicLastShellTranslate a ha g) ∘
        (W.fullAdelicNonisotropicLastShellQuotientMap a ha) =
      (W.fullAdelicNonisotropicLastShellQuotientMap a ha) ∘
        (fun q : W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha => g • q) :=
    funext fun q => W.fullAdelicNonisotropicLastShellTranslate_quotientMap a ha g q
  rw [fullAdelicNonisotropicLastShellMeasure,
    Measure.map_map (W.measurable_fullAdelicNonisotropicLastShellTranslate a ha g) hqmap,
    hcomp, ← Measure.map_map hqmap hsmul,
    W.map_fullAdelicNonisotropicLastShellQuotientMeasure_smul a ha g]

end RationalQuadraticSpaceMatrix

end
