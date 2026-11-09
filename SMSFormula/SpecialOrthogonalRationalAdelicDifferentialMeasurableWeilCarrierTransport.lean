import SMSFormula.SpecialOrthogonalFullAdelicDifferentialMeasurableWeilQuotient
import SMSFormula.SpecialOrthogonalRationalAdelicWeilCarrierTransport

/-!
# Carrier transport for the measurable differential Weil interface

The measurable-integrand Weil quotient predicate is unchanged by the
exact concrete/general rational special-orthogonal carrier equivalences.
Specializing this transport carries the concrete
differential quotient measure to the general rational quadratic-space
presentation.

No quotient volume is evaluated.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A concrete measurable Weil identity transports to the general rational
quadratic-space carriers. -/
theorem
    isLeftMeasurableWeilQuotientMeasure_rationalQuadraticSpaceMatrix_of_concrete
    (L : PositiveDefiniteIntegralLattice n)
    (μG : Measure L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (μX : Measure L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient)
    (hWeil :
      IsLeftMeasurableWeilQuotientMeasure
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup μG μX) :
    IsLeftMeasurableWeilQuotientMeasure
      (L.rationalQuadraticSpaceMatrix
        |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
      (Measure.map
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm
        μG)
      (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μX) where
  lintegral_leftPeriodize_eq f hf := by
    let eG :=
      L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv
        |>.toMeasurableEquiv
    let eX :=
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv
    calc
      ∫⁻ C,
          leftPeriodize
            (L.rationalQuadraticSpaceMatrix
              |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
            f C
          ∂L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μX =
          ∫⁻ D,
            leftPeriodize
              (L.rationalQuadraticSpaceMatrix
                |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
              f (eX.symm D)
            ∂μX := by
              exact lintegral_map_equiv _ eX.symm
      _ =
          ∫⁻ D,
            leftPeriodize
              L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
              (fun x => f (eG.symm x)) D
            ∂μX := by
              apply lintegral_congr
              intro D
              have h :=
                L.leftPeriodize_rationalQuadraticSpaceMatrix_equiv
                  (fun x => f (eG.symm x)) (eX.symm D)
              have hfun :
                  (fun x =>
                    f
                      (eG.symm
                        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv
                          x))) = f := by
                funext x
                exact congrArg f (eG.symm_apply_apply x)
              have hquot :
                  L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv
                      (eX.symm D) = D :=
                eX.apply_symm_apply D
              rw [hfun, hquot] at h
              exact h
      _ = ∫⁻ x, f (eG.symm x) ∂μG :=
        hWeil.lintegral_leftPeriodize_eq _
          (hf.comp eG.symm.measurable)
      _ = ∫⁻ y, f y ∂Measure.map eG.symm μG := by
        exact (lintegral_map_equiv f eG.symm).symm

/-- The sound measurable Weil quotient predicate is equivalent on the
concrete and inverse-transported general rational carriers. -/
theorem
    isLeftMeasurableWeilQuotientMeasure_concrete_iff_rationalQuadraticSpaceMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (μG : Measure L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (μX : Measure L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient) :
    IsLeftMeasurableWeilQuotientMeasure
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup μG μX ↔
      IsLeftMeasurableWeilQuotientMeasure
        (L.rationalQuadraticSpaceMatrix
          |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
        (Measure.map
          (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm
          μG)
        (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μX) := by
  constructor
  · exact
      L.isLeftMeasurableWeilQuotientMeasure_rationalQuadraticSpaceMatrix_of_concrete
        μG μX
  · intro hWeil
    refine ⟨?_⟩
    intro f hf
    let eG :=
      L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv
        |>.toMeasurableEquiv
    let eX :=
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv
    calc
      ∫⁻ D,
          leftPeriodize
            L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f D
          ∂μX =
          ∫⁻ C,
            leftPeriodize
              L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f
              (eX C)
            ∂Measure.map eX.symm μX := by
              simpa using
                (lintegral_map_equiv
                  (fun C =>
                    leftPeriodize
                      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f
                      (eX C))
                  eX.symm).symm
      _ =
          ∫⁻ C,
            leftPeriodize
              (L.rationalQuadraticSpaceMatrix
                |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
              (fun y => f (eG y)) C
            ∂Measure.map eX.symm μX := by
              apply lintegral_congr
              intro C
              exact
                (L.leftPeriodize_rationalQuadraticSpaceMatrix_equiv f C).symm
      _ = ∫⁻ y, f (eG y) ∂Measure.map eG.symm μG :=
        hWeil.lintegral_leftPeriodize_eq _
          (hf.comp eG.measurable)
      _ = ∫⁻ x, f x ∂μG := by
        simpa using lintegral_map_equiv (fun y => f (eG y)) eG.symm

/-- The internally certified concrete differential quotient measure
transports to a sound measurable Weil quotient measure on the general
rational quadratic-space carriers. -/
theorem
    rationalQuadraticSpaceMatrixFullAdelicDifferentialQuotientMeasure_isLeftMeasurableWeilQuotientMeasure
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    IsLeftMeasurableWeilQuotientMeasure
      (L.rationalQuadraticSpaceMatrix
        |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P)
      (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure
        (L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P)) := by
  exact
    L.isLeftMeasurableWeilQuotientMeasure_rationalQuadraticSpaceMatrix_of_concrete
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P)
      (L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure P)
      (L.concreteFullAdelicSpecialOrthogonalDifferentialQuotientMeasure_isLeftMeasurableWeilQuotientMeasure
        inst hP)

end PositiveDefiniteIntegralLattice
