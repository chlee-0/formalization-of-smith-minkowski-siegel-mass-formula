import SMSFormula.SpecialOrthogonalRationalAdelicDifferentialHaar

/-!
# Carrier transport for the rational special-orthogonal Weil interface

This module proves that left preperiodization, descended periodization, and
the project-local left Weil quotient property are unchanged by the exact
general/concrete carrier identifications attached to an integral lattice.

No quotient measure is selected.  In particular, the results transport only
an already supplied Weil identity and assert no quotient volume, Tamagawa
value, reference-Haar comparison, or basis specialization.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private theorem leftPreperiodize_equiv_of_subgroup_map
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (Gamma : Subgroup G) (Delta : Subgroup H)
    (hmap : Gamma.map e.toMonoidHom = Delta)
    (f : H → ℝ≥0∞) (y : G) :
    leftPreperiodize Gamma (fun x => f (e x)) y =
      leftPreperiodize Delta f (e y) := by
  unfold leftPreperiodize
  let eGamma : Gamma ≃ Delta :=
    ((e.subgroupMap Gamma).trans
      (MulEquiv.subgroupCongr hmap)).toEquiv
  calc
    (∑' gamma : Gamma, f (e ((gamma : G) * y))) =
        ∑' gamma : Gamma,
          f (((eGamma gamma : Delta) : H) * e y) := by
            apply tsum_congr
            intro gamma
            rw [map_mul]
            rfl
    _ = ∑' delta : Delta, f ((delta : H) * e y) := by
      exact eGamma.tsum_eq
        (fun delta : Delta => f ((delta : H) * e y))

/-- Ambient left preperiodization commutes with the exact full-adelic and
diagonal-subgroup carrier equivalences. -/
theorem leftPreperiodize_rationalQuadraticSpaceMatrix_equiv
    (L : PositiveDefiniteIntegralLattice n)
    (f : L.ConcreteFullAdelicSpecialOrthogonalGroup → ℝ≥0∞)
    (y :
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) :
    leftPreperiodize
        (L.rationalQuadraticSpaceMatrix
          |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
        (fun x =>
          f
            (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv
              x))
        y =
      leftPreperiodize
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv y) := by
  exact
    leftPreperiodize_equiv_of_subgroup_map
      L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv
      (L.rationalQuadraticSpaceMatrix
        |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
      L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
      L.rationalQuadraticSpaceMatrix_diagonalSubgroup_map f y

/-- Descended left periodization commutes with the exact full-adelic and
left-quotient carrier equivalences. -/
theorem leftPeriodize_rationalQuadraticSpaceMatrix_equiv
    (L : PositiveDefiniteIntegralLattice n)
    (f : L.ConcreteFullAdelicSpecialOrthogonalGroup → ℝ≥0∞)
    (C :
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    leftPeriodize
        (L.rationalQuadraticSpaceMatrix
          |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
        (fun x =>
          f
            (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv
              x))
        C =
      leftPeriodize
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f
        (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv C) := by
  refine Quot.inductionOn C ?_
  intro y
  change
    leftPeriodize
        (L.rationalQuadraticSpaceMatrix
          |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
        (fun x =>
          f
            (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv
              x))
        (L.rationalQuadraticSpaceMatrix
          |>.fullAdelicSpecialOrthogonalLeftQuotientMap y) =
      leftPeriodize
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f
        (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv
          (L.rationalQuadraticSpaceMatrix
            |>.fullAdelicSpecialOrthogonalLeftQuotientMap y))
  rw [L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_mk]
  change
    leftPreperiodize
        (L.rationalQuadraticSpaceMatrix
          |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
        (fun x =>
          f
            (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv
              x))
        y =
      leftPreperiodize
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup f
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv y)
  exact L.leftPreperiodize_rationalQuadraticSpaceMatrix_equiv f y

/-- An already supplied concrete Weil identity transports to the general
rational quadratic-space carriers. -/
theorem isLeftWeilQuotientMeasure_rationalQuadraticSpaceMatrix_of_concrete
    (L : PositiveDefiniteIntegralLattice n)
    (μG : Measure L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (μX : Measure L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient)
    (hWeil :
      IsLeftWeilQuotientMeasure
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup μG μX) :
    IsLeftWeilQuotientMeasure
      (L.rationalQuadraticSpaceMatrix
        |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
      (Measure.map
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm
        μG)
      (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μX) where
  lintegral_leftPeriodize_eq f := by
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
                      (eX.symm D) = D := by
                exact eX.apply_symm_apply D
              rw [hfun, hquot] at h
              exact h
      _ = ∫⁻ x, f (eG.symm x) ∂μG :=
        hWeil.lintegral_leftPeriodize_eq _
      _ = ∫⁻ y, f y ∂Measure.map eG.symm μG := by
        exact (lintegral_map_equiv f eG.symm).symm

/-- Conversely, a Weil identity for the inverse-transported measures on the
general carriers implies the original concrete Weil identity. -/
theorem isLeftWeilQuotientMeasure_concrete_iff_rationalQuadraticSpaceMatrix
    (L : PositiveDefiniteIntegralLattice n)
    (μG : Measure L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (μX : Measure L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient) :
    IsLeftWeilQuotientMeasure
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup μG μX ↔
      IsLeftWeilQuotientMeasure
        (L.rationalQuadraticSpaceMatrix
          |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
        (Measure.map
          (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv).symm
          μG)
        (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μX) := by
  constructor
  · exact
      L.isLeftWeilQuotientMeasure_rationalQuadraticSpaceMatrix_of_concrete
        μG μX
  · intro hWeil
    refine ⟨?_⟩
    intro f
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
      _ = ∫⁻ x, f x ∂μG := by
        simpa using lintegral_map_equiv (fun y => f (eG y)) eG.symm

/-- Differential-Haar specialization of the carrier-independent Weil
transport theorem.  The concrete quotient measure and its Weil hypothesis
remain explicit. -/
theorem
    isLeftWeilQuotientMeasure_rationalQuadraticSpaceMatrix_differential_of_concrete
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ)
    (μX : Measure L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient)
    (hWeil :
      IsLeftWeilQuotientMeasure
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
        (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) μX) :
    IsLeftWeilQuotientMeasure
      (L.rationalQuadraticSpaceMatrix
        |>.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
      (L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P)
      (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasure μX) := by
  exact
    L.isLeftWeilQuotientMeasure_rationalQuadraticSpaceMatrix_of_concrete
      (L.fullAdelicSpecialOrthogonalDifferentialMeasure P) μX hWeil

end PositiveDefiniteIntegralLattice
