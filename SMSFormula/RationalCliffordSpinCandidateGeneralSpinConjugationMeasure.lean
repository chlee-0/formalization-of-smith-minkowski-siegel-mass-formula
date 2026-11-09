import SMSFormula.RationalCliffordSpinCandidateGeneralSpinConjugation
import SMSFormula.RationalCliffordSpinCandidateLeftQuotientRightTranslation

/-!
# Raw Spin measure invariance under rational general-Spin conjugation

Rational `GSpin` conjugation has square equal to an inner automorphism by a
rational Spin point.  This specialized identity fixes the Haar comparison
scalar at one without using the possibly infinite total Spin quotient volume.
The resulting ambient invariance is then transported through the exact
measurable Weil quotient.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open Topology
open TopologicalSpace
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- Central scalar points commute with every intrinsic general-Spin point. -/
private theorem scalarGroupHom_comm
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : Aˣ) (g : V.CliffordGeneralSpinIntrinsicPoint A) :
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z * g =
      g * CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V A
  apply Units.ext
  change algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) (z : A) *
      (g.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) =
    (g.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) *
      algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) (z : A)
  exact Algebra.commutes (z : A) _

/-- The rational Spin point measuring the square of rational `GSpin`
conjugation. -/
def rationalCliffordGeneralSpinConjugationSquareSpin
    (gamma : V.RationalCliffordGeneralSpinGroup) :
    V.RationalCliffordSpinCandidateGroup :=
  Classical.choose (by
    have hker :
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ
              (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ gamma)⁻¹ *
            gamma ^ 2 ∈
          (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ).ker := by
      change CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ
              (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ gamma)⁻¹ *
            gamma ^ 2) = 1
      simp
    rw [← V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker ℚ] at hker
    exact hker)

/-- The chosen rational Spin point has the literal scalar-normalized square as
its intrinsic general-Spin image. -/
@[simp]
theorem cliffordSpinCandidateToCliffordGeneralSpinHom_conjugationSquareSpin
    (gamma : V.RationalCliffordGeneralSpinGroup) :
    V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ
        (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma) =
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ
          (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ gamma)⁻¹ *
        gamma ^ 2 :=
  Classical.choose_spec (by
    have hker :
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ
              (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ gamma)⁻¹ *
            gamma ^ 2 ∈
          (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ).ker := by
      change CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ
              (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ gamma)⁻¹ *
            gamma ^ 2) = 1
      simp
    rw [← V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker ℚ] at hker
    exact hker)

/-- The square of a rational `GSpin` point is its central similitude scalar
times a rational Spin point. -/
theorem rationalCliffordGeneralSpin_sq_eq_scalar_mul_conjugationSquareSpin
    (gamma : V.RationalCliffordGeneralSpinGroup) :
    gamma ^ 2 =
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ
          (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ gamma) *
        V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ
          (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma) := by
  rw [V.cliffordSpinCandidateToCliffordGeneralSpinHom_conjugationSquareSpin]
  rw [map_inv]
  simp

/-- If the square of a general-Spin point is a central scalar times a Spin
point, then squaring its conjugation action gives the corresponding inner Spin
automorphism. -/
theorem cliffordSpinCandidateGeneralSpinConjugation_sq_of_sq_eq_scalar_mul
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : V.CliffordGeneralSpinIntrinsicPoint A)
    (z : Aˣ) (s x : V.CliffordSpinCandidateGroup A)
    (hs : g ^ 2 =
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z *
        V.cliffordSpinCandidateToCliffordGeneralSpinHom A s) :
    V.cliffordSpinCandidateGeneralSpinConjugation A g
        (V.cliffordSpinCandidateGeneralSpinConjugation A g x) =
      s⁻¹ * x * s := by
  apply V.cliffordSpinCandidateToCliffordGeneralSpinHom_injective A
  simp only [V.cliffordSpinCandidateToCliffordGeneralSpinHom_conjugation,
    map_mul, map_inv]
  have hzconj :
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z)⁻¹ *
            V.cliffordSpinCandidateToCliffordGeneralSpinHom A x *
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z =
        V.cliffordSpinCandidateToCliffordGeneralSpinHom A x := by
    rw [← map_inv,
      V.scalarGroupHom_comm A z⁻¹
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom A x)]
    simp [mul_assoc]
  calc
    g⁻¹ * (g⁻¹ *
          V.cliffordSpinCandidateToCliffordGeneralSpinHom A x * g) * g =
        (g ^ 2)⁻¹ *
          V.cliffordSpinCandidateToCliffordGeneralSpinHom A x * g ^ 2 := by
            simp [pow_two, mul_assoc]
    _ = (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z *
            V.cliffordSpinCandidateToCliffordGeneralSpinHom A s)⁻¹ *
          V.cliffordSpinCandidateToCliffordGeneralSpinHom A x *
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z *
              V.cliffordSpinCandidateToCliffordGeneralSpinHom A s) := by
          rw [hs]
    _ = (V.cliffordSpinCandidateToCliffordGeneralSpinHom A s)⁻¹ *
          V.cliffordSpinCandidateToCliffordGeneralSpinHom A x *
            V.cliffordSpinCandidateToCliffordGeneralSpinHom A s := by
          rw [mul_inv_rev]
          calc
            (((V.cliffordSpinCandidateToCliffordGeneralSpinHom A s)⁻¹ *
                    (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z)⁻¹) *
                  V.cliffordSpinCandidateToCliffordGeneralSpinHom A x) *
                (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z *
                  V.cliffordSpinCandidateToCliffordGeneralSpinHom A s) =
                (V.cliffordSpinCandidateToCliffordGeneralSpinHom A s)⁻¹ *
                    ((CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z)⁻¹ *
                        V.cliffordSpinCandidateToCliffordGeneralSpinHom A x *
                      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z) *
                  V.cliffordSpinCandidateToCliffordGeneralSpinHom A s := by
                    simp only [mul_assoc]
            _ = _ := by rw [hzconj]

/-- Squaring rational general-Spin conjugation gives the inner automorphism by
the distinguished rational Spin point. -/
theorem cliffordSpinCandidateGeneralSpinConjugation_sq
    (gamma : V.RationalCliffordGeneralSpinGroup)
    (x : V.RationalCliffordSpinCandidateGroup) :
    V.cliffordSpinCandidateGeneralSpinConjugation ℚ gamma
        (V.cliffordSpinCandidateGeneralSpinConjugation ℚ gamma x) =
      (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma)⁻¹ * x *
        V.rationalCliffordGeneralSpinConjugationSquareSpin gamma := by
  apply V.cliffordSpinCandidateGeneralSpinConjugation_sq_of_sq_eq_scalar_mul ℚ
    gamma
    (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ gamma)
    (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma)
  exact V.rationalCliffordGeneralSpin_sq_eq_scalar_mul_conjugationSquareSpin gamma

/-- The same square-to-inner identity on the full adelic Spin carrier. -/
theorem fullAdelic_cliffordSpinCandidateGeneralSpinConjugation_sq
    (gamma : V.RationalCliffordGeneralSpinGroup)
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
        (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
          (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) x) =
      (V.rationalCliffordSpinCandidateFullAdelicDiagonalHom
          (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma))⁻¹ * x *
        V.rationalCliffordSpinCandidateFullAdelicDiagonalHom
          (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma) := by
  let g := V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma
  let z := rationalUnitFullAdelicDiagonalHom
    (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ gamma)
  let s := V.rationalCliffordSpinCandidateFullAdelicDiagonalHom
    (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma)
  apply V.cliffordSpinCandidateGeneralSpinConjugation_sq_of_sq_eq_scalar_mul
    RationalAdele g z s
  have h := congrArg V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
    (V.rationalCliffordGeneralSpin_sq_eq_scalar_mul_conjugationSquareSpin gamma)
  change V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma ^ 2 =
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele
        (rationalUnitFullAdelicDiagonalHom
          (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ gamma)) *
      V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele
        (V.rationalCliffordSpinCandidateFullAdelicDiagonalHom
          (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma))
  rw [V.rational_fullAdelic_diagonal_generalSpinScalar]
  rw [show
    V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele
        (V.rationalCliffordSpinCandidateFullAdelicDiagonalHom
          (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma)) =
      V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ
          (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma)) from
    V.rational_fullAdelic_diagonal_candidateToGeneralSpin
      (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma)]
  simpa only [map_pow, map_mul] using h

/-- Rational `GSpin` conjugation permutes the actual rational Spin diagonal
subgroup inside full adelic Spin. -/
def rationalCliffordSpinCandidateFullAdelicDiagonalConjugationEquiv
    (gamma : V.RationalCliffordGeneralSpinGroup) :
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup ≃
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup where
  toFun delta := ⟨
    V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
      (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) delta,
    by
      rcases delta.property with ⟨d, hd⟩
      refine ⟨V.cliffordSpinCandidateGeneralSpinConjugation ℚ gamma d, ?_⟩
      simpa only [hd] using
        V.rational_fullAdelic_diagonal_generalSpinConjugation gamma d⟩
  invFun delta := ⟨
    V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
      (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma⁻¹) delta,
    by
      rcases delta.property with ⟨d, hd⟩
      refine ⟨V.cliffordSpinCandidateGeneralSpinConjugation ℚ gamma⁻¹ d, ?_⟩
      simpa only [hd] using
        V.rational_fullAdelic_diagonal_generalSpinConjugation gamma⁻¹ d⟩
  left_inv delta := by
    apply Subtype.ext
    simpa only [map_inv] using
      (V.cliffordSpinCandidateGeneralSpinConjugationMulEquiv RationalAdele
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)).left_inv delta
  right_inv delta := by
    apply Subtype.ext
    simpa only [map_inv] using
      (V.cliffordSpinCandidateGeneralSpinConjugationMulEquiv RationalAdele
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)).right_inv delta

/-- A continuous group automorphism whose square is inner preserves every
two-sided Haar measure.  The Haar comparison scalar is determined on one positive
finite compact set; no finite total mass is required. -/
theorem map_eq_self_of_continuousMulEquiv_sq_eq_inner
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [Measure.IsHaarMeasure mu]
    [Measure.IsMulRightInvariant mu]
    (e : G ≃ₜ* G) (s : G)
    (hsq : ∀ x, e (e x) = s⁻¹ * x * s) :
    Measure.map e mu = mu := by
  letI : Measure.IsHaarMeasure (Measure.map e mu) :=
    e.toMulEquiv.isHaarMeasure_map mu e.continuous e.symm.continuous
  let c : ℝ≥0∞ := Measure.haarScalarFactor (Measure.map e mu) mu
  have hc : Measure.map e mu = c • mu :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hinner : Measure.map (fun x : G => s⁻¹ * x * s) mu = mu := by
    rw [show (fun x : G => s⁻¹ * x * s) =
        (fun y : G => s⁻¹ * y) ∘ (fun x : G => x * s) by
          funext x
          simp only [Function.comp_apply, mul_assoc]]
    rw [← Measure.map_map (measurable_const_mul s⁻¹) (measurable_mul_const s)]
    rw [MeasureTheory.map_mul_right_eq_self,
      MeasureTheory.map_mul_left_eq_self]
  have hdouble : Measure.map e (Measure.map e mu) = c ^ 2 • mu := by
    rw [hc, Measure.map_smul, hc, smul_smul, pow_two]
  have hmapmap :
      Measure.map (fun x : G => e x)
          (Measure.map (fun x : G => e x) mu) =
        Measure.map (fun x : G => e (e x)) mu := by
    have he : Measurable (fun x : G => e x) := e.continuous.measurable
    rw [Measure.map_map he he]
    rfl
  have hmapinner : Measure.map (fun x : G => e (e x)) mu = mu := by
    rw [show (fun x : G => e (e x)) = fun x => s⁻¹ * x * s by
      funext x
      exact hsq x]
    exact hinner
  have mueq : mu = c ^ 2 • mu := by
    change Measure.map (fun x : G => e x)
        (Measure.map (fun x : G => e x) mu) = c ^ 2 • mu at hdouble
    rw [hmapmap, hmapinner] at hdouble
    exact hdouble
  have K : PositiveCompacts G := Classical.arbitrary _
  have hc_mass : c ^ 2 * mu K = 1 ^ 2 * mu K := by
    conv_rhs => rw [mueq]
    simp
  have hc_sq : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj
      (Measure.measure_pos_of_nonempty_interior mu K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1 hc_mass
  have hc_one : c = 1 :=
    (ENNReal.pow_right_strictMono two_ne_zero).injective hc_sq
  rw [hc, hc_one, one_smul]

namespace CliffordSpinCandidateRawOnoTamagawaData

/-- The raw full-adelic Spin Haar measure is invariant under conjugation by
every rational intrinsic general-Spin point.  The proof determines the Haar scalar
on one positive finite compact set after squaring conjugation to a rational
Spin inner automorphism; it does not use finite total Spin mass. -/
theorem map_spin_adelicMeasure_rationalGeneralSpinConjugation
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (gamma : V.RationalCliffordGeneralSpinGroup) :
    Measure.map
        (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
          (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma))
        D.spinData.adelicMeasure =
      D.spinData.adelicMeasure := by
  letI : Measure.IsInvInvariant D.spinData.adelicMeasure :=
    D.spinRaw.adelicMeasure_isInvInvariant
  letI : Measure.IsHaarMeasure D.spinData.adelicMeasure := by
    rw [D.spinRaw.adelicMeasure_eq]
    exact V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_isHaarMeasure
      D.spinFiniteScale D.spinRaw.volumeProductCertificate
  letI : Measure.IsMulLeftInvariant D.spinData.adelicMeasure := by
    infer_instance
  letI : Measure.IsMulRightInvariant D.spinData.adelicMeasure :=
    Measure.isMulRightInvariant_of_isInvInvariant D.spinData.adelicMeasure
  let conj :=
    V.cliffordSpinCandidateGeneralSpinConjugationContinuousMulEquiv
      RationalAdele
      (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
  let s := V.rationalCliffordSpinCandidateFullAdelicDiagonalHom
    (V.rationalCliffordGeneralSpinConjugationSquareSpin gamma)
  exact map_eq_self_of_continuousMulEquiv_sq_eq_inner
    D.spinData.adelicMeasure conj s (fun x =>
      V.fullAdelic_cliffordSpinCandidateGeneralSpinConjugation_sq gamma x)

/-- The raw rational adelic Spin quotient measure is invariant under the
explicit quotient automorphism induced by rational `GSpin` conjugation.  The
proof reindexes the actual rational Spin diagonal in the measurable Weil
formula and uses the ambient conjugation theorem above; no finite quotient
mass or quotient-Haar uniqueness scalar is suppressed. -/
theorem map_spin_quotientMeasure_rationalGeneralSpinConjugation
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (gamma : V.RationalCliffordGeneralSpinGroup) :
    Measure.map
        (V.fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
          gamma)
        D.spinData.quotientMeasure =
      D.spinData.quotientMeasure := by
  letI : Countable V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :=
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup_countable
  let translated := Measure.map
    (V.fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
      gamma)
    D.spinData.quotientMeasure
  have htranslated : IsLeftMeasurableWeilQuotientMeasure
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
      D.spinData.adelicMeasure translated := by
    constructor
    intro f hf
    have hpre : Measurable
        (leftPreperiodize
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f) :=
      leftPreperiodize_measurable_of_countable
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup hf
    have hperiod : Measurable
        (leftPeriodize
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f) :=
      leftPeriodize_measurable_map_of_leftPreperiodize
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup hpre
    rw [lintegral_map' hperiod.aemeasurable
      (V.measurable_fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
        gamma).aemeasurable]
    let conj : V.FullAdelicCliffordSpinCandidateGroup →
        V.FullAdelicCliffordSpinCandidateGroup :=
      V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
    let fx : V.FullAdelicCliffordSpinCandidateGroup → ℝ≥0∞ := fun y => f (conj y)
    have hconj : Measurable conj :=
      (V.continuous_cliffordSpinCandidateGeneralSpinConjugation RationalAdele
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)).measurable
    have hfx : Measurable fx := hf.comp hconj
    have hperiodConjugate :
        (leftPeriodize
            V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f) ∘
            V.fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
              gamma =
          leftPeriodize
            V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup fx := by
      funext q
      induction q using Quot.inductionOn with
      | _ y =>
        change leftPreperiodize
            V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f (conj y) =
          leftPreperiodize
            V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup fx y
        unfold leftPreperiodize fx
        let e := V.rationalCliffordSpinCandidateFullAdelicDiagonalConjugationEquiv
          gamma
        calc
          (∑' delta : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
              f ((delta : V.FullAdelicCliffordSpinCandidateGroup) * conj y)) =
              ∑' delta : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
                f ((e delta : V.FullAdelicCliffordSpinCandidateGroup) * conj y) := by
                exact (e.tsum_eq (fun delta =>
                  f ((delta : V.FullAdelicCliffordSpinCandidateGroup) * conj y))).symm
          _ = ∑' delta : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
                f (conj ((delta : V.FullAdelicCliffordSpinCandidateGroup) * y)) := by
                apply tsum_congr
                intro delta
                change f (conj delta * conj y) = f (conj (delta * y))
                exact congrArg f
                  ((V.cliffordSpinCandidateGeneralSpinConjugationMulEquiv
                    RationalAdele
                    (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
                    ).map_mul delta y).symm
    change (∫⁻ a,
      ((leftPeriodize
          V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup f) ∘
        V.fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
          gamma) a ∂D.spinData.quotientMeasure) = _
    rw [hperiodConjugate]
    rw [D.spinData.isMeasurableWeilQuotientMeasure.lintegral_leftPeriodize_eq fx hfx]
    calc
      (∫⁻ y, fx y ∂D.spinData.adelicMeasure) =
          ∫⁻ y, f y ∂Measure.map conj D.spinData.adelicMeasure := by
        rw [lintegral_map' hf.aemeasurable hconj.aemeasurable]
      _ = ∫⁻ y, f y ∂D.spinData.adelicMeasure := by
        rw [show Measure.map conj D.spinData.adelicMeasure =
            D.spinData.adelicMeasure by
          simpa only [conj] using
            map_spin_adelicMeasure_rationalGeneralSpinConjugation
              (V := V) D gamma]
  have htranslatedEq := htranslated.eq_leftQuotientFundamentalDomainMeasure
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup rfl
    V.measurableSet_fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain
    V.existsUnique_rationalDiagonal_smul_mem_measurableFundamentalDomain
  have horiginalEq :=
    D.spinData.isMeasurableWeilQuotientMeasure
      |>.eq_leftQuotientFundamentalDomainMeasure
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup rfl
        V.measurableSet_fullAdelicCliffordSpinCandidateMeasurableFundamentalDomain
        V.existsUnique_rationalDiagonal_smul_mem_measurableFundamentalDomain
  simpa only [translated] using htranslatedEq.trans horiginalEq.symm

end CliffordSpinCandidateRawOnoTamagawaData

end RationalQuadraticSpaceMatrix
