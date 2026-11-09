import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCentralFiberSourceOverlapMeasure

/-!
# Finite exceptional products of presentation-chart overlap measures

For a finite set of rational places, the local transported and ambient
selected-chart measures already live on the same literal `GSpin(ℚ_p)` source
overlap.  This file forms their dependent finite products and combines the
placewise comparison formulas into the exact product of reciprocal local
presentation moduli.

No integral tail, finite-adelic presentation map, directed cylinder, or Haar
comparison scalar is used here.  In particular, the finite set is an explicit
parameter rather than a newly selected denominator support.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance finiteExceptionalOverlapDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteExceptionalOverlapPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The finite dependent product of the genuine common selected-chart group
sources at the displayed rational places. -/
abbrev FiniteExceptionalPadicCentralFiberSourceOverlap
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :=
  (v : {v // v ∈ S}) →
    P.transportedAmbientPadicCentralFiberSourceOverlap
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx

/-- Product of the transported-block selected-chart source measures at a
finite set of rational places. -/
def transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.FiniteExceptionalPadicCentralFiberSourceOverlap S hx) :=
  Measure.pi fun v ↦
    P.transportedPadicCentralFiberSourceOverlapProductMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx

/-- Product of the ambient selected-chart source measures on the same finite
dependent carrier. -/
def ambientFiniteExceptionalPadicCentralFiberSourceOverlapMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.FiniteExceptionalPadicCentralFiberSourceOverlap S hx) :=
  Measure.pi fun v ↦
    P.ambientPadicCentralFiberSourceOverlapProductMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx

set_option backward.isDefEq.respectTransparency false in
instance transportedPadicCentralFiberSourceOverlapProductMeasure_sigmaFinite
    (p : ℕ) [Fact (Nat.Prime p)]
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    SigmaFinite
      (P.transportedPadicCentralFiberSourceOverlapProductMeasure p hx) := by
  let target := P.transportedPadicCentralFiberTargetOverlap p hx
  let targetMeasure :=
    P.transportedPadicCentralFiberTargetOverlapProductMeasure p hx
  let productMeasure := P.transportedBlockPadicCentralFiberProductMeasure p hx
  letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) :=
    Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
  letI : SigmaFinite
      ((P.blockSpace hx).padicInvariantDifferentialGroupMeasure p) :=
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      p (m + 1) (P.blockSpace hx).pairingMatrix (P.blockSpace hx).form_symm
      (P.blockSpace hx).form_det_ne_zero
  letI : SigmaFinite
      ((P.blockSpace hx)
        |>.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p) := by
    unfold padicCliffordGeneralSpinHorizontalDifferentialProductMeasure
    infer_instance
  letI : SigmaFinite productMeasure := by
    unfold productMeasure transportedBlockPadicCentralFiberProductMeasure
    exact
      (P.blockToAmbientCentralFiberTargetContinuousMulEquiv hx ℚ_[p])
        |>.toMeasurableEquiv.sigmaFinite_map
  letI : SigmaFinite targetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [show Measure.map Subtype.val targetMeasure =
        productMeasure.restrict target by
      unfold targetMeasure target productMeasure
        transportedPadicCentralFiberTargetOverlapProductMeasure
      exact map_comap_subtype_coe
        (P.isOpen_transportedPadicCentralFiberTargetOverlap p hx).measurableSet
        productMeasure]
    infer_instance
  unfold transportedPadicCentralFiberSourceOverlapProductMeasure
  exact
    (P.transportedPadicCentralFiberSourceOverlapHomeomorphTarget p hx).symm
      |>.toMeasurableEquiv.sigmaFinite_map

set_option backward.isDefEq.respectTransparency false in
instance ambientPadicCentralFiberSourceOverlapProductMeasure_sigmaFinite
    (p : ℕ) [Fact (Nat.Prime p)]
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    SigmaFinite
      (P.ambientPadicCentralFiberSourceOverlapProductMeasure p hx) := by
  let target := P.ambientPadicCentralFiberTargetOverlap p hx
  let targetMeasure := P.ambientPadicCentralFiberTargetOverlapProductMeasure p hx
  let productMeasure :=
    V.padicCliffordGeneralSpinHorizontalDifferentialProductMeasure p
  letI : SigmaFinite (Measure.haar : Measure ℚ_[p]ˣ) :=
    Measure.IsHaarMeasure.sigmaFinite (Measure.haar : Measure ℚ_[p]ˣ)
  letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
    PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero
  letI : SigmaFinite productMeasure := by
    unfold productMeasure padicCliffordGeneralSpinHorizontalDifferentialProductMeasure
    infer_instance
  letI : SigmaFinite targetMeasure := by
    apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
    rw [show Measure.map Subtype.val targetMeasure =
        productMeasure.restrict target by
      unfold targetMeasure target productMeasure
        ambientPadicCentralFiberTargetOverlapProductMeasure
      exact map_comap_subtype_coe
        (P.isOpen_ambientPadicCentralFiberTargetOverlap p hx).measurableSet
        productMeasure]
    infer_instance
  unfold ambientPadicCentralFiberSourceOverlapProductMeasure
  exact
    (P.ambientPadicCentralFiberSourceOverlapHomeomorphTarget p hx).symm
      |>.toMeasurableEquiv.sigmaFinite_map

/-- The finite product of reciprocal p-adic norms of the single rational
presentation tangent determinant. -/
def finiteExceptionalPadicPresentationModulus
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hx : V.nativeRationalQuadraticForm x ≠ 0) : ℝ≥0 :=
  ∏ v : {v // v ∈ S},
    ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
        (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹

/-- On an arbitrary finite exceptional product, the transported-block and
ambient selected-chart source measures differ by exactly the product of the
reciprocal local norms of the rational presentation modulus. -/
theorem transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure_eq_smul
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure S hx =
      P.finiteExceptionalPadicPresentationModulus S hx •
        P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapMeasure S hx := by
  unfold transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure
    ambientFiniteExceptionalPadicCentralFiberSourceOverlapMeasure
    finiteExceptionalPadicPresentationModulus
  let transported := fun v : {v // v ∈ S} ↦
    P.transportedPadicCentralFiberSourceOverlapProductMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
  let ambient := fun v : {v // v ∈ S} ↦
    P.ambientPadicCentralFiberSourceOverlapProductMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1 hx
  let modulus := fun v : {v // v ∈ S} ↦
    ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
        (P.blockToAmbientSkewAdjointDetScalar hx)‖₊⁻¹
  have hlocal (v : {v // v ∈ S}) :
      transported v = modulus v • ambient v :=
    P.transportedPadicCentralFiberSourceOverlapProductMeasure_eq_smul
      (p := (Rat.HeightOneSpectrum.primesEquiv v.1).1) hx
  change Measure.pi transported = (∏ v, modulus v) • Measure.pi ambient
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [ENNReal.smul_def, smul_eq_mul]
  have hlocal_apply (v : {v // v ∈ S}) :
      transported v (s v) =
        (modulus v : ℝ≥0∞) * ambient v (s v) := by
    rw [hlocal, Measure.smul_apply]
    rfl
  simp_rw [hlocal_apply]
  rw [ENNReal.coe_finset_prod, Finset.prod_mul_distrib]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
