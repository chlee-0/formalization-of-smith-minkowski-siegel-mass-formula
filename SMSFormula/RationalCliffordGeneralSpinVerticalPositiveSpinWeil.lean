import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveWeilBind
import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveIdeleQuotient

/-!
# Spin Weil reduction inside the positive-idele vertical periodization

The rational `GSpin` diagonal has already been reindexed as the positive
rational idèle diagonal followed by the rational Spin diagonal.  This file
isolates the corresponding coset representative and moves the inner Spin sum
through the raw Spin quotient integral by the exact Spin measurable-Weil
identity.

No carrier restriction, local chart, measurable idèle-class representative,
or normalization coefficient is introduced here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2000000

local instance verticalPositiveSpinWeilDiagonalImageNormal
    (L : PositiveDefiniteIntegralLattice n) :
    (L.rationalQuadraticSpaceMatrix.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin).Normal := by
  rw [L.rationalQuadraticSpaceMatrix.range_rationalCliffordSpinCandidateDiagonalToGeneralSpin_eq_ker]
  infer_instance

/-- An explicit quotient-by-subgroup decomposition whose inverse is literally
`(xi, h) |-> Quotient.out xi * h`.  This avoids exposing the proof casts in
the generic noncanonical equivalence when the Spin Weil integrand is formed. -/
def rationalGeneralSpinDiagonalEquivQuotientSpinImageExplicit
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ≃
      (L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
          L.rationalQuadraticSpaceMatrix.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin) ×
        L.rationalQuadraticSpaceMatrix.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin where
  toFun gamma :=
    let V := L.rationalQuadraticSpaceMatrix
    let H := V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin
    let xi := QuotientGroup.mk' H gamma
    (xi, ⟨(Quotient.out xi)⁻¹ * gamma, by
      apply QuotientGroup.eq.mp
      change QuotientGroup.mk (Quotient.out xi) = QuotientGroup.mk gamma
      rw [QuotientGroup.out_eq']
      rfl⟩)
  invFun p := Quotient.out p.1 * p.2
  left_inv gamma := by
    simp
  right_inv p := by
    rcases p with ⟨xi, h⟩
    let V := L.rationalQuadraticSpaceMatrix
    let H := V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin
    have hfirst : QuotientGroup.mk' H (Quotient.out xi * (h :
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) = xi := by
      change QuotientGroup.mk (Quotient.out xi * (h :
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) = xi
      rw [QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.out_eq']
    apply Prod.ext
    · exact hfirst
    · apply Subtype.ext
      change (Quotient.out
          (QuotientGroup.mk' H (Quotient.out xi * (h :
            V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup))))⁻¹ *
          (Quotient.out xi * h) = h
      rw [hfirst]
      simp

/-- The rational `GSpin` diagonal is explicitly equivalent to positive
rational idèle diagonal times rational Spin diagonal.  The inverse has the
literal product form needed by Spin periodization. -/
def rationalGeneralSpinDiagonalEquivPositiveIdeleSpinExplicit
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) :
    L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ≃
      positiveRationalIdeleDiagonalSubgroup ×
        L.rationalQuadraticSpaceMatrix.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :=
  (rationalGeneralSpinDiagonalEquivQuotientSpinImageExplicit L).trans
    (Equiv.prodCongr
      (rationalGeneralSpinDiagonalQuotientEquivPositiveRationalIdeleDiagonal L hn)
      L.rationalQuadraticSpaceMatrix.rationalCliffordSpinCandidateDiagonalEquivImageInGeneralSpin.symm)

/-- The rational `GSpin` diagonal representative selected for a positive
rational idèle diagonal point. -/
def rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (eta : positiveRationalIdeleDiagonalSubgroup) :
    L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
  Quotient.out
    ((rationalGeneralSpinDiagonalQuotientEquivPositiveRationalIdeleDiagonal
        L hn).symm eta)

/-- The inverse of the explicit positive-idèle/Spin diagonal equivalence is
the selected coset representative followed by the embedded Spin point. -/
theorem rationalGeneralSpinDiagonalEquivPositiveIdeleSpinExplicit_symm_apply
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (eta : positiveRationalIdeleDiagonalSubgroup)
    (sigma : L.rationalQuadraticSpaceMatrix.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup) :
    let V := L.rationalQuadraticSpaceMatrix
    (rationalGeneralSpinDiagonalEquivPositiveIdeleSpinExplicit L hn).symm
        (eta, sigma) =
      rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele L hn eta *
        V.rationalCliffordSpinCandidateDiagonalToGeneralSpin sigma := rfl

/-- Reindex every rational `GSpin` sum by the explicit positive-idèle/Spin
equivalence. -/
theorem tsum_rationalCliffordGeneralSpinDiagonal_eq_positiveIdele_spin_explicit
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (F : L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup →
      ℝ≥0∞) :
    let V := L.rationalQuadraticSpaceMatrix
    (∑' gamma, F gamma) =
      ∑' eta : positiveRationalIdeleDiagonalSubgroup,
        ∑' sigma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
          F (rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele
              L hn eta *
            V.rationalCliffordSpinCandidateDiagonalToGeneralSpin sigma) := by
  let V := L.rationalQuadraticSpaceMatrix
  let e := rationalGeneralSpinDiagonalEquivPositiveIdeleSpinExplicit L hn
  calc
    (∑' gamma, F gamma) = ∑' p, F (e.symm p) := (e.symm.tsum_eq F).symm
    _ = ∑' eta, ∑' sigma, F (e.symm (eta, sigma)) := by
      rw [ENNReal.tsum_prod']
    _ = _ := by
      apply tsum_congr
      intro eta
      apply tsum_congr
      intro sigma
      rw [rationalGeneralSpinDiagonalEquivPositiveIdeleSpinExplicit_symm_apply]

/-! ## Pointwise Spin periodization -/

/-- For a positive rational-idèle diagonal branch, the ambient function on
`GSpin(A)` pulled back to `Spin(A)`. -/
def verticalPositiveSpinWeilIntegrand
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (eta : positiveRationalIdeleDiagonalSubgroup)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞) :
    L.rationalQuadraticSpaceMatrix.FullAdelicCliffordSpinCandidateGroup →
      ℝ≥0∞ :=
  fun y =>
    f ((rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele
          L hn eta :
        L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) *
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g))

theorem measurable_verticalPositiveSpinWeilIntegrand
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (eta : positiveRationalIdeleDiagonalSubgroup)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    {f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞}
    (hf : Measurable f) :
    Measurable (verticalPositiveSpinWeilIntegrand L hn eta g f) := by
  exact hf.comp
    ((continuous_const.mul
      ((L.rationalQuadraticSpaceMatrix
          |>.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom
            RationalAdele).mul continuous_const)).measurable)

/-- Pointwise, the rational `GSpin` periodization along a translated Spin
quotient is the positive rational-idèle sum of rational Spin
periodizations. -/
theorem leftPeriodize_GSpin_rightMul_spinQuotient_eq_tsum_positiveIdele_spin
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (q : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordSpinCandidateLeftQuotient)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞) :
    let V := L.rationalQuadraticSpaceMatrix
    leftPeriodize V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g
          (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin q)) =
      ∑' eta : positiveRationalIdeleDiagonalSubgroup,
        leftPeriodize V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
          (verticalPositiveSpinWeilIntegrand L hn eta g f) q := by
  let V := L.rationalQuadraticSpaceMatrix
  induction q using Quot.inductionOn with
  | _ y =>
    change
      (∑' gamma : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
        f ((gamma : V.FullAdelicCliffordGeneralSpinGroup) *
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g))) =
        ∑' eta : positiveRationalIdeleDiagonalSubgroup,
          ∑' sigma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
            verticalPositiveSpinWeilIntegrand L hn eta g f
              ((sigma : V.FullAdelicCliffordSpinCandidateGroup) * y)
    rw [tsum_rationalCliffordGeneralSpinDiagonal_eq_positiveIdele_spin_explicit
      L hn]
    apply tsum_congr
    intro eta
    apply tsum_congr
    intro sigma
    unfold verticalPositiveSpinWeilIntegrand
    rw [map_mul]
    change
      f ((rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele
            L hn eta : V.FullAdelicCliffordGeneralSpinGroup) *
          V.fullAdelicCliffordSpinCandidateToGeneralSpinHom sigma *
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g)) = _
    simp only [mul_assoc]
    rfl

/-! ## The inner Spin Weil identity -/

/-- Integrating the pointwise decomposition over the raw Spin quotient
removes the rational Spin periodization by the already certified raw Spin
Weil identity.  The positive rational-idèle sum remains explicit. -/
theorem CliffordSpinCandidateRawOnoTamagawaData.lintegral_spinQuotient_GSpin_periodization_eq
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    ∫⁻ q : V.FullAdelicCliffordSpinCandidateLeftQuotient,
        leftPeriodize V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
          (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g
            (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin q))
        ∂D.spinData.quotientMeasure =
      ∑' eta : positiveRationalIdeleDiagonalSubgroup,
        ∫⁻ y : V.FullAdelicCliffordSpinCandidateGroup,
          verticalPositiveSpinWeilIntegrand L hn eta g f y
          ∂D.spinData.adelicMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  letI : Countable V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :=
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup_countable
  letI : Countable positiveRationalUnitsSubgroup :=
    Function.Injective.countable
      (f := fun q : positiveRationalUnitsSubgroup => ((q : ℚˣ) : ℚ)) (by
        intro q r hqr
        apply Subtype.ext
        apply Units.ext
        exact hqr)
  letI : Countable positiveRationalIdeleDiagonalSubgroup :=
    Countable.of_equiv positiveRationalUnitsSubgroup
      positiveRationalUnitsEquivPositiveRationalIdeleDiagonal
  have hterm : ∀ eta : positiveRationalIdeleDiagonalSubgroup,
      AEMeasurable
        (leftPeriodize V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
          (verticalPositiveSpinWeilIntegrand L hn eta g f))
        D.spinData.quotientMeasure := by
    intro eta
    have hi : Measurable (verticalPositiveSpinWeilIntegrand L hn eta g f) :=
      measurable_verticalPositiveSpinWeilIntegrand L hn eta g hf
    exact (leftPeriodize_measurable_map_of_leftPreperiodize
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
      (leftPreperiodize_measurable_of_countable
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup hi)).aemeasurable
  calc
    ∫⁻ q : V.FullAdelicCliffordSpinCandidateLeftQuotient,
        leftPeriodize V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f
          (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul g
            (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin q))
        ∂D.spinData.quotientMeasure =
      ∫⁻ q : V.FullAdelicCliffordSpinCandidateLeftQuotient,
        ∑' eta : positiveRationalIdeleDiagonalSubgroup,
          leftPeriodize V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
            (verticalPositiveSpinWeilIntegrand L hn eta g f) q
        ∂D.spinData.quotientMeasure := by
          apply lintegral_congr
          intro q
          exact leftPeriodize_GSpin_rightMul_spinQuotient_eq_tsum_positiveIdele_spin
            L hn q g f
    _ = ∑' eta : positiveRationalIdeleDiagonalSubgroup,
        ∫⁻ q : V.FullAdelicCliffordSpinCandidateLeftQuotient,
          leftPeriodize V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
            (verticalPositiveSpinWeilIntegrand L hn eta g f) q
          ∂D.spinData.quotientMeasure := by
            rw [lintegral_tsum hterm]
    _ = ∑' eta : positiveRationalIdeleDiagonalSubgroup,
        ∫⁻ y : V.FullAdelicCliffordSpinCandidateGroup,
          verticalPositiveSpinWeilIntegrand L hn eta g f y
          ∂D.spinData.adelicMeasure := by
            apply tsum_congr
            intro eta
            exact D.spinData.isMeasurableWeilQuotientMeasure
              |>.lintegral_leftPeriodize_eq
                (verticalPositiveSpinWeilIntegrand L hn eta g f)
                (measurable_verticalPositiveSpinWeilIntegrand L hn eta g hf)

/-- The complete section-free positive-idèle/Spin Weil expansion of the
ambient periodized vertical bind.  The only outer coefficient is the already
certified comparison from the independently chosen idèle-class Haar to the
differential Weil quotient. -/
theorem CliffordSpinCandidateRawOnoTamagawaData.lintegral_periodizedVerticalSpinFiberHaarBoundMeasure_eq_positiveSpinWeil
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (f :
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    ∫⁻ x, f x
        ∂V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) =
      (rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) *
        ∫⁻ a : positiveRationalAdeleUnitsSubgroup,
          ∑' eta : positiveRationalIdeleDiagonalSubgroup,
            ∫⁻ y : V.FullAdelicCliffordSpinCandidateGroup,
              verticalPositiveSpinWeilIntegrand L hn eta
                (V.verticalGeneralSpinRepresentative hsurj
                  (positiveRationalIdeleToIdeleClassHom a)) f y
              ∂D.spinData.adelicMeasure
          ∂(positiveRationalIdeleDifferentialHaarMeasure.restrict
            positiveRationalIdeleMeasurableFundamentalDomainSubtype) := by
  let V := L.rationalQuadraticSpaceMatrix
  dsimp only [V]
  rw [D.lintegral_periodizedVerticalSpinFiberHaarBoundMeasure_eq_positiveWeil
    L hn hsurj f hf]
  congr 1
  apply lintegral_congr
  intro a
  exact D.lintegral_spinQuotient_GSpin_periodization_eq L hn
    (V.verticalGeneralSpinRepresentative hsurj
      (positiveRationalIdeleToIdeleClassHom a)) f hf

end RationalQuadraticSpaceMatrix
