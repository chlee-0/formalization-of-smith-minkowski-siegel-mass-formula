import SMSFormula.RationalRealUnitSquareBranchChangeOfVariables
import SMSFormula.RationalIdeleDifferentialSquareModulus
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite exceptional horizontal chart disintegration

The completed real and p-adic square-branch calculations are assembled here
on an actual finite exceptional product of horizontal `GSpin` identity charts.
The componentwise scalar/Spin splitting map sends the product of the fixed
local horizontal source measures to the finite product of the literal local
square moduli times ambient scalar Haar and Spin source measure.

The real chart is included as a separate factor.  On measurable rectangles,
the product of all displayed scalar coefficients is exactly one as soon as
the finite exceptional set contains the dyadic place.  This is the first
carrier-level real/dyadic cancellation: it is a finite product statement, not
an Euler product and not a two-sheet coefficient.

No restricted-product transition, good compact factorization, ambient
`GSpin -> SO` disintegration, or quotient comparison is asserted here.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000

local instance horizontalExceptionalChartPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalExceptionalChartDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance horizontalExceptionalChartRealUnitMeasurableSpace :
    MeasurableSpace ℝˣ := borel _

noncomputable local instance horizontalExceptionalChartRealUnitBorelSpace :
    BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance horizontalExceptionalChartPadicUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance horizontalExceptionalChartPadicUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance horizontalExceptionalChartPadicUnitSecondCountable
    (p : ℕ) [Fact (Nat.Prime p)] : SecondCountableTopology ℚ_[p]ˣ := by
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[p] × ℚ_[p]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

noncomputable local instance horizontalExceptionalChartRealSOMeasurableSpace :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance horizontalExceptionalChartRealSOBorelSpace :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

noncomputable local instance horizontalExceptionalChartPadicSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance horizontalExceptionalChartPadicSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance horizontalExceptionalChartRealGSpinMeasurableSpace :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℝ) := borel _

noncomputable local instance horizontalExceptionalChartRealGSpinBorelSpace :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℝ) := ⟨rfl⟩

noncomputable local instance horizontalExceptionalChartPadicGSpinMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := borel _

noncomputable local instance horizontalExceptionalChartPadicGSpinBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := ⟨rfl⟩

/-! ## Unconditional local product identities -/

/-- The completed real square calculation gives the literal full horizontal
product-chart identity with coefficient two and no additional factor. -/
theorem realHorizontalProductSourceMeasure_split :
    Measure.map
        (Homeomorph.Set.prod
          (Rat.unitSquareIdentityChart ℝ).source
          V.realCliffordSpinCandidateIdentityChart.source)
        V.realCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure =
      rationalIdeleRealSquareModulus •
        (realUnitSquareIdentityChartAmbientSourceMeasure.prod
          V.realCliffordSpinCandidateIdentityChartSourceMeasure) :=
  V.realHorizontalProductSourceMeasure_split_of_squareChangeOfVariables
    realUnitSquareBranchChangeOfVariables

/-- The completed p-adic square calculation gives the literal full
horizontal product-chart identity at every finite place. -/
theorem padicHorizontalProductSourceMeasure_split
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (Homeomorph.Set.prod
          (Rat.unitSquareIdentityChart ℚ_[p]).source
          (V.padicCliffordSpinCandidateIdentityChart p).source)
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p) =
      rationalIdelePadicSquareModulus p •
        ((padicUnitSquareIdentityChartAmbientSourceMeasure p).prod
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p)) :=
  V.padicHorizontalProductSourceMeasure_split_of_squareChangeOfVariables p
    (padicUnitSquareBranchChangeOfVariables p)

/-! ## Finite exceptional chart products -/

/-- Product of the intrinsic p-adic horizontal identity-chart sources over a
finite exceptional set. -/
abbrev CliffordGeneralSpinHorizontalExceptionalChartSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ S}) →
    (V.padicCliffordGeneralSpinHorizontalProductIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).source

/-- Product of the corresponding scalar-square and Spin source coordinates.
-/
abbrev CliffordGeneralSpinHorizontalExceptionalChartSplitSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : {v // v ∈ S}) →
    (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source ×
      (V.padicCliffordSpinCandidateIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).source

/-- Componentwise scalar/Spin splitting on the finite exceptional chart
product. -/
def cliffordGeneralSpinHorizontalExceptionalChartSplit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalExceptionalChartSource S →
      V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource S :=
  fun g v =>
    Homeomorph.Set.prod
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source
      (V.padicCliffordSpinCandidateIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).source (g v)

theorem measurable_cliffordGeneralSpinHorizontalExceptionalChartSplit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (V.cliffordGeneralSpinHorizontalExceptionalChartSplit S) := by
  exact measurable_pi_lambda _ fun v =>
    (Homeomorph.Set.prod
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source
      (V.padicCliffordSpinCandidateIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).source).measurable.comp
      (measurable_pi_apply v)

/-- Product of the already fixed intrinsic horizontal source measures on the
finite exceptional chart. -/
def cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalExceptionalChartSource S) :=
  Measure.pi fun v : {v // v ∈ S} =>
    V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1

/-- Product of the scalar/Spin source measures carrying the literal local
square moduli. -/
def cliffordGeneralSpinHorizontalExceptionalChartSplitMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource S) :=
  Measure.pi fun v : {v // v ∈ S} =>
    rationalIdelePadicSquareModulus
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 •
      ((padicUnitSquareIdentityChartAmbientSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).prod
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1))

/-- The same finite scalar/Spin product before inserting the local square
moduli. -/
def cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalExceptionalChartSplitSource S) :=
  Measure.pi fun v : {v // v ∈ S} =>
    (padicUnitSquareIdentityChartAmbientSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).prod
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)

/-- The literal product of the p-adic square moduli on this finite chart. -/
def cliffordGeneralSpinHorizontalExceptionalChartSquareModulus
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0 :=
  ∏ v : {v // v ∈ S},
    rationalIdelePadicSquareModulus
      (Rat.HeightOneSpectrum.primesEquiv v.1).1

theorem cliffordGeneralSpinHorizontalExceptionalChartSquareModulus_eq
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    cliffordGeneralSpinHorizontalExceptionalChartSquareModulus S =
      rationalIdeleFiniteExceptionalSquareModulus S := by
  classical
  unfold cliffordGeneralSpinHorizontalExceptionalChartSquareModulus
    rationalIdeleFiniteExceptionalSquareModulus
  change (∏ v : {v // v ∈ S},
      rationalIdeleFinitePlaceSquareModulus v.1) =
    ∏ v ∈ S, rationalIdeleFinitePlaceSquareModulus v
  exact (Finset.prod_subtype S (fun _ => Iff.rfl)
    rationalIdeleFinitePlaceSquareModulus).symm

set_option backward.isDefEq.respectTransparency false in
/-- All local p-adic square coefficients combine into the one literal finite
exceptional modulus. -/
theorem cliffordGeneralSpinHorizontalExceptionalChartSplitMeasure_eq_smul
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalExceptionalChartSplitMeasure S =
      cliffordGeneralSpinHorizontalExceptionalChartSquareModulus S •
        V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure S := by
  let base := fun v : {v // v ∈ S} =>
    (padicUnitSquareIdentityChartAmbientSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).prod
      (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1)
  letI (v : {v // v ∈ S}) : SigmaFinite (base v) := by
    let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
    let squareChart := Rat.unitSquareIdentityChart ℚ_[p]
    let spinChart := V.padicCliffordSpinCandidateIdentityChart p
    letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) :=
      Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
    letI : SigmaFinite (padicUnitSquareIdentityChartAmbientSourceMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicUnitSquareIdentityChartAmbientSourceMeasure,
        map_comap_subtype_coe squareChart.open_source.measurableSet]
      infer_instance
    letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
      PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
        p n V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicCliffordSpinCandidateIdentityChartTargetMeasure,
        map_comap_subtype_coe spinChart.open_target.measurableSet]
      infer_instance
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
      rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
      exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
    infer_instance
  letI (v : {v // v ∈ S}) : SigmaFinite
      (rationalIdelePadicSquareModulus
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 • base v) := by
    infer_instance
  unfold cliffordGeneralSpinHorizontalExceptionalChartSplitMeasure
    cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure
    cliffordGeneralSpinHorizontalExceptionalChartSquareModulus
  change
    Measure.pi (fun v =>
      rationalIdelePadicSquareModulus
          (Rat.HeightOneSpectrum.primesEquiv v.1).1 • base v) =
      (∏ v : {v // v ∈ S},
        rationalIdelePadicSquareModulus
          (Rat.HeightOneSpectrum.primesEquiv v.1).1) • Measure.pi base
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi _ s]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.coe_finset_prod, Finset.prod_mul_distrib]

/-- Once the dyadic place occurs in the finite exceptional chart, its total
p-adic modulus cancels the real branch modulus exactly. -/
theorem real_mul_cliffordGeneralSpinHorizontalExceptionalChartSquareModulus_eq_one
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hS : rationalIdeleDyadicPlace ∈ S) :
    rationalIdeleRealSquareModulus *
        cliffordGeneralSpinHorizontalExceptionalChartSquareModulus S = 1 := by
  rw [cliffordGeneralSpinHorizontalExceptionalChartSquareModulus_eq]
  exact rationalIdeleReal_mul_finiteExceptionalSquareModulus_eq_one S hS

set_option backward.isDefEq.respectTransparency false in
/-- The finite exceptional product has the componentwise normalized
scalar/Spin disintegration. -/
theorem map_cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalExceptionalChartSplit S)
        (V.cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure S) =
      V.cliffordGeneralSpinHorizontalExceptionalChartSplitMeasure S := by
  let f := fun v : {v // v ∈ S} =>
    Homeomorph.Set.prod
      (Rat.unitSquareIdentityChart
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).source
      (V.padicCliffordSpinCandidateIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).source
  let μ := fun v : {v // v ∈ S} =>
    V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  letI (v : {v // v ∈ S}) : SigmaFinite ((μ v).map (f v)) := by
    let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
    let squareChart := Rat.unitSquareIdentityChart ℚ_[p]
    let spinChart := V.padicCliffordSpinCandidateIdentityChart p
    letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) :=
      Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
    letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
      PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
        p n V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite (padicUnitSquareIdentityChartTargetMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicUnitSquareIdentityChartTargetMeasure,
        map_comap_subtype_coe squareChart.open_target.measurableSet]
      infer_instance
    letI : SigmaFinite (padicUnitSquareIdentityChartSourceMeasure p) := by
      rw [padicUnitSquareIdentityChartSourceMeasure]
      exact squareChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [padicCliffordSpinCandidateIdentityChartTargetMeasure,
        map_comap_subtype_coe spinChart.open_target.measurableSet]
      infer_instance
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartSourceMeasure p) := by
      rw [padicCliffordSpinCandidateIdentityChartSourceMeasure]
      exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
    change SigmaFinite
      (Measure.map
        (Homeomorph.Set.prod squareChart.source spinChart.source)
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p))
    rw [V.map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_split p]
    infer_instance
  have hpi :
      (Measure.pi μ).map (fun g v => f v (g v)) =
        Measure.pi fun v => (μ v).map (f v) :=
    Measure.pi_map_pi fun v => (f v).measurable.aemeasurable
  simpa [cliffordGeneralSpinHorizontalExceptionalChartSplit,
    cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure,
    cliffordGeneralSpinHorizontalExceptionalChartSplitMeasure, f, μ,
    V.padicHorizontalProductSourceMeasure_split] using hpi

/-- The finite exceptional chart pushforward has one total coefficient: the
literal finite product of its p-adic square moduli. -/
theorem map_cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure_eq_smul
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalExceptionalChartSplit S)
        (V.cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure S) =
      cliffordGeneralSpinHorizontalExceptionalChartSquareModulus S •
        V.cliffordGeneralSpinHorizontalExceptionalChartAmbientSplitMeasure S := by
  rw [V.map_cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure S,
    V.cliffordGeneralSpinHorizontalExceptionalChartSplitMeasure_eq_smul S]

end RationalQuadraticSpaceMatrix
