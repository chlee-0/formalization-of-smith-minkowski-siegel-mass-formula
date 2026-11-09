import SMSFormula.RationalCliffordGeneralSpinBlockFullAdelicStabilizerHaar
import SMSFormula.RationalCliffordGeneralSpinRawVerticalCrossedCutoff

/-!
# The Spin coefficient on a nonisotropic block stabilizer

The natural complement embedding descends from the lower rational adelic
`GSpin` quotient to the block rational adelic `GSpin` quotient.  It preserves
the logarithmic similitude coordinate exactly.  Transporting the
vertical Spin fibers through this quotient map therefore keeps their
lower-rank Spin mass, and the crossed logarithmic cutoff has no coefficient
beyond the common idele-class cutoff and that Spin volume.

No idele lift or representative is chosen here: the construction only
maps the lower-rank vertical fiber measures.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000

variable {n : ℕ}

/-- The complement block embedding descended to the existing rational adelic
left quotients. -/
def fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.FullAdelicCliffordGeneralSpinLeftQuotient →
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinLeftQuotient :=
  Quot.lift
    (fun x =>
      (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientMap
          (W.nonisotropicLastComplementGeneralSpinPoint
            a ha RationalAdele x)) (by
      intro x y hxy
      rcases hxy with ⟨gamma, rfl⟩
      rcases gamma.2 with ⟨q, hq⟩
      have hgamma :
          (gamma : W.FullAdelicCliffordGeneralSpinGroup) =
            W.rationalCliffordGeneralSpinFullAdelicDiagonalHom q :=
        hq.symm
      change (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientMap
            (W.nonisotropicLastComplementGeneralSpinPoint
              a ha RationalAdele x) =
        (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientMap
            ((W.nonisotropicLastComplementGeneralSpinPointHom
              a ha RationalAdele)
              ((gamma : W.FullAdelicCliffordGeneralSpinGroup) * x))
      rw [(W.nonisotropicLastComplementGeneralSpinPointHom
        a ha RationalAdele).map_mul, hgamma]
      have hdiag :=
        W.nonisotropicLastComplementGeneralSpinPoint_naturality
          a ha (Algebra.ofId ℚ RationalAdele) q
      have hdiag' :
          (W.nonisotropicLastComplementGeneralSpinPointHom a ha RationalAdele)
              (W.rationalCliffordGeneralSpinFullAdelicDiagonalHom q) =
            (W.nonisotropicLastExtension a ha).rationalCliffordGeneralSpinFullAdelicDiagonalHom
                (W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ q) := by
        change
          W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele
              (CliffordGeneralSpinIntrinsicPoint.map W
                (Algebra.ofId ℚ RationalAdele) q) =
            CliffordGeneralSpinIntrinsicPoint.map
              (W.nonisotropicLastExtension a ha)
              (Algebra.ofId ℚ RationalAdele)
              (W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ q)
        exact hdiag.symm
      rw [hdiag']
      exact (leftCosetMap_gamma_mul
        ((W.nonisotropicLastExtension a ha).rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)
        ⟨(W.nonisotropicLastExtension a ha).rationalCliffordGeneralSpinFullAdelicDiagonalHom
              (W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ q),
          ⟨W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ q, rfl⟩⟩
        (W.nonisotropicLastComplementGeneralSpinPoint
          a ha RationalAdele x)).symm)

@[simp]
theorem fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap_mk
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (x : W.FullAdelicCliffordGeneralSpinGroup) :
    W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap a ha
        (W.fullAdelicCliffordGeneralSpinLeftQuotientMap x) =
      (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientMap
          (W.nonisotropicLastComplementGeneralSpinPoint
            a ha RationalAdele x) :=
  rfl

/-- The descended block quotient map is continuous for the existing quotient
topologies. -/
theorem continuous_fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Continuous
      (W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
        a ha) := by
  apply Continuous.quotient_lift
  exact
    (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap.continuous.comp
        (W.continuous_nonisotropicLastComplementGeneralSpinPoint
          a ha RationalAdele)

/-- The descended complement quotient map preserves the logarithmic
similitude coordinate exactly. -/
@[simp]
theorem fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap_logModule
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (z : W.FullAdelicCliffordGeneralSpinLeftQuotient) :
    (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientLogModule
          (W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
            a ha z) =
      W.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z := by
  induction z using Quot.inductionOn with
  | _ x =>
      change
        (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientLogModule
            ((W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientMap
              (W.nonisotropicLastComplementGeneralSpinPoint
                a ha RationalAdele x)) =
          W.fullAdelicCliffordGeneralSpinLeftQuotientLogModule
            (W.fullAdelicCliffordGeneralSpinLeftQuotientMap x)
      rw [(W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientLogModule_mk,
        W.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_mk]
      change
        rationalIdeleLogModule
            (W.nonisotropicLastComplementGeneralSpinPoint
              a ha RationalAdele x).similitude =
          rationalIdeleLogModule x.similitude
      rw [W.nonisotropicLastComplementGeneralSpinPoint_similitude]

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- A lower-rank vertical Spin fiber transported into the block quotient
through the certified complement map. -/
def nonisotropicLastComplementVerticalSpinFiberMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (D : W.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      W.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    Measure ((W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinLeftQuotient) :=
  Measure.map
    (W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap a ha)
    (D.verticalSpinFiberMeasure W hsurj c)

@[simp]
theorem nonisotropicLastComplementVerticalSpinFiberMeasure_univ
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (D : W.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      W.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    D.nonisotropicLastComplementVerticalSpinFiberMeasure
        W a ha hsurj c Set.univ =
      D.spinTamagawaNumberENNReal := by
  rw [nonisotropicLastComplementVerticalSpinFiberMeasure,
    Measure.map_apply_of_aemeasurable
      (W.continuous_fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
        a ha).measurable.aemeasurable MeasurableSet.univ]
  simp

/-- On one transported block-stabilizer fiber, a logarithmic cutoff is its
base idele-class value times the literal lower-rank Spin quotient volume. -/
theorem lintegral_nonisotropicLastComplementVerticalSpinFiberMeasure_logCutoff
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (D : W.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      W.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f
        ((W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
        ∂D.nonisotropicLastComplementVerticalSpinFiberMeasure
          W a ha hsurj c) =
      f (rationalIdeleClassLogModule c) *
        D.spinTamagawaNumberENNReal := by
  rw [nonisotropicLastComplementVerticalSpinFiberMeasure]
  change
    (∫⁻ z,
      (f ∘
        (W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientLogModule) z
        ∂Measure.map
          (W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap a ha)
          (D.verticalSpinFiberMeasure W hsurj c)) = _
  rw [lintegral_map'
    (hf.comp
      ((W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable)).aemeasurable
    (W.continuous_fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
      a ha).measurable.aemeasurable]
  simpa only [Function.comp_apply,
    W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap_logModule,
    verticalSpinFiberLogCutoffLIntegral] using
      D.verticalSpinFiberLogCutoffLIntegral_eq W hsurj c f hf

/-- The transported block-stabilizer crossed logarithmic integral over the
existing rational idele-class Haar. -/
def nonisotropicLastComplementVerticalCrossedLogCutoffLIntegral
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (D : W.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      W.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ c : RationalIdeleClassGroup,
    ∫⁻ z, f
        ((W.nonisotropicLastExtension a ha).fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
        ∂D.nonisotropicLastComplementVerticalSpinFiberMeasure
          W a ha hsurj c
      ∂rationalIdeleClassHaarMeasure

/-- The block-stabilizer crossed cutoff has the common idele-class cutoff and
the lower-rank Spin quotient volume as its sole nontrivial coefficient. -/
theorem nonisotropicLastComplementVerticalCrossedLogCutoffLIntegral_eq
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (D : W.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      W.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    D.nonisotropicLastComplementVerticalCrossedLogCutoffLIntegral
        W a ha hsurj f =
      rationalIdeleClassLogCutoffLIntegral f *
        D.spinTamagawaNumberENNReal := by
  rw [nonisotropicLastComplementVerticalCrossedLogCutoffLIntegral]
  simp_rw [D.lintegral_nonisotropicLastComplementVerticalSpinFiberMeasure_logCutoff
    W a ha hsurj _ f hf]
  change (∫⁻ c : RationalIdeleClassGroup,
      (f ∘ rationalIdeleClassLogModule) c * D.spinTamagawaNumberENNReal
        ∂rationalIdeleClassHaarMeasure) = _
  rw [lintegral_mul_const _
    (hf.comp continuous_rationalIdeleClassLogModule.measurable)]
  rfl

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
