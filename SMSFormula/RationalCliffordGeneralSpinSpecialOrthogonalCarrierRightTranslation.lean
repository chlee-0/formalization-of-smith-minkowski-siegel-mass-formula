import SMSFormula.RationalCliffordGeneralSpinVerticalSpecialOrthogonalProjection
import SMSFormula.RationalCliffordGeneralSpinLatticeFiniteSpinClassHorizontalConcrete
import SMSFormula.RationalCliffordSpinCandidateLatticeSpecialOrthogonalQuotientRightTranslation

/-!
# Transport of special-orthogonal quotient right invariance

An arbitrary right-invariant measure on the concrete lattice `SO` quotient
remains right invariant after transport to the rational-quadratic-space
quotient carrier.  This carrier lemma keeps the large lattice raw datum out of
the transport calculation.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

theorem map_rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure_rightMul
    (L : PositiveDefiniteIntegralLattice n)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (μ : Measure L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient)
    (hμ : Measure.map
        (L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul
          (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv x)) μ =
      μ) :
    Measure.map
        (L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientRightMul
          x)
        (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μ) =
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μ := by
  let E := L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv
  let xc := L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv x
  unfold rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure
  rw [Measure.map_map
    (L.rationalQuadraticSpaceMatrix.measurable_fullAdelicSpecialOrthogonalLeftQuotientRightMul
      x) E.symm.measurable]
  have hcomm :
      L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientRightMul
          x ∘
          L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv.symm =
        L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv.symm ∘
          L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul
            (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv x) := by
    funext q
    change
      L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientRightMul
          x
          (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv.symm q) =
        L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv.symm
          (L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul
            (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv x) q)
    apply L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv.injective
    rw [Equiv.apply_symm_apply]
    simpa only [Equiv.apply_symm_apply] using
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_rightMul
        x (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv.symm q)
  rw [hcomm, ← Measure.map_map E.symm.measurable
    (L.measurable_concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul xc), hμ]

end PositiveDefiniteIntegralLattice
