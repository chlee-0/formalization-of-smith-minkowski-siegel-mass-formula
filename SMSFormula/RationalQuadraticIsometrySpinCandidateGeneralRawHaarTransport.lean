import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralFiniteHaarTransport
import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralRealMeasureTransport

/-!
# Raw Spin Haar transport under an arbitrary rational isometry

The coherent finite Spin Haar comparison is combined with the independently
transported inverse-volume-product scale and the real tangent modulus.  The
raw correction cancels against the transported scale, while the rational
product formula cancels the remaining real and finite tangent moduli.  This
yields exact full-adelic raw Spin Haar transport.

Every intermediate scalar remains explicit until those two certified
cancellations.  No chart, lattice, quotient representative, normalization
axiom, or Tamagawa value is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

variable {m : ℕ}
variable (W Z : RationalQuadraticSpaceMatrix (m + 1))
variable (e : W.quadraticForm.IsometryEquiv Z.quadraticForm)

local instance generalRawHaarFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix (m + 1)) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance generalRawHaarFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix (m + 1)) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance generalRawHaarDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance generalRawHaarPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-! ## The full-adelic real--finite carrier square -/

/-- Product of the real and finite specializations of arbitrary-isometry
Spin transport. -/
abbrev rationalIsometryRealFiniteSpinCandidateContinuousMulEquiv :
    (W.RealCliffordSpinCandidateGroup ×
        W.FiniteAdelicCliffordSpinCandidateGroup) ≃ₜ*
      (Z.RealCliffordSpinCandidateGroup ×
        Z.FiniteAdelicCliffordSpinCandidateGroup) :=
  PositiveDefiniteIntegralLattice.prodContinuousMulEquiv
    (rationalIsometrySpinCandidateContinuousMulEquiv W Z e ℝ)
    (rationalIsometrySpinCandidateContinuousMulEquiv
      W Z e RationalFiniteAdele)

/-- Arbitrary-isometry Spin transport commutes literally with the fixed
real--finite splitting of the full-adelic carrier. -/
theorem rationalIsometryFullAdelicSpinCandidate_realFinite_commutes
    (z : W.FullAdelicCliffordSpinCandidateGroup) :
    Z.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalAdele z) =
      rationalIsometryRealFiniteSpinCandidateContinuousMulEquiv W Z e
        (W.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv z) := by
  apply Prod.ext
  · change Z.cliffordSpinCandidateGroupMap
        fullAdelicCliffordGeneralSpinRealAlgHom
          (rationalIsometrySpinCandidateMulEquiv W Z e RationalAdele z) =
      rationalIsometrySpinCandidateMulEquiv W Z e ℝ
        (W.cliffordSpinCandidateGroupMap
          fullAdelicCliffordGeneralSpinRealAlgHom z)
    exact (rationalIsometrySpinCandidateMulEquiv_naturality W Z e
      fullAdelicCliffordGeneralSpinRealAlgHom z).symm
  · change Z.cliffordSpinCandidateGroupMap
        fullAdelicCliffordGeneralSpinFiniteAlgHom
          (rationalIsometrySpinCandidateMulEquiv W Z e RationalAdele z) =
      rationalIsometrySpinCandidateMulEquiv W Z e RationalFiniteAdele
        (W.cliffordSpinCandidateGroupMap
          fullAdelicCliffordGeneralSpinFiniteAlgHom z)
    exact (rationalIsometrySpinCandidateMulEquiv_naturality W Z e
      fullAdelicCliffordGeneralSpinFiniteAlgHom z).symm

/-! ## The finite tangent modulus and the product formula -/

/-- On a support containing every nontrivial rational p-adic norm, the
exceptional tangent modulus is the inverse of the supported norm product. -/
theorem rationalIsometrySpinCandidateFiniteExceptionalModulus_coe_eq_supported_prod_inv
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hsupp : rationalPadicNormSupportPlaces
      (rationalIsometrySkewAdjointDetScalar W Z e) ⊆ S) :
    (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S : ℝ≥0∞) =
      ∏ q ∈ Rat.padicNormPrimeSupport
          (rationalIsometrySkewAdjointDetScalar W Z e),
        (Rat.padicNormENNRealAtPrime
          (rationalIsometrySkewAdjointDetScalar W Z e) q)⁻¹ := by
  let d := rationalIsometrySkewAdjointDetScalar W Z e
  let f : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0 := fun v ↦
    ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] d‖₊⁻¹
  have hd : d ≠ 0 := rationalIsometrySkewAdjointDetScalar_ne_zero W Z e
  have hf_out (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (hv : v ∉ rationalPadicNormSupportPlaces d) : f v = 1 := by
    have hp : Rat.HeightOneSpectrum.primesEquiv v ∉
        Rat.padicNormPrimeSupport d := by
      intro hp
      apply hv
      exact Finset.mem_map.mpr
        ⟨Rat.HeightOneSpectrum.primesEquiv v, hp,
          Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply v⟩
    have hnorm := Rat.nnnorm_ratCast_eq_one_of_not_mem_padicNormPrimeSupport
      hd (Rat.HeightOneSpectrum.primesEquiv v) hp
    simpa [f] using congrArg Inv.inv hnorm
  have hprod_places :
      ∏ v ∈ rationalPadicNormSupportPlaces d, f v = ∏ v ∈ S, f v :=
    Finset.prod_subset hsupp (fun v _ hv ↦ hf_out v hv)
  have hprod_primes :
      ∏ v ∈ rationalPadicNormSupportPlaces d, f v =
        ∏ q ∈ Rat.padicNormPrimeSupport d,
          (rationalPadicNormNNRealAtPrime d q)⁻¹ := by
    unfold rationalPadicNormSupportPlaces
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro q hq
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    have hpv : Rat.HeightOneSpectrum.primesEquiv (R := ℤ)
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm q) = q :=
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply q
    change
      (rationalPadicNormNNRealAtPrime d
        (Rat.HeightOneSpectrum.primesEquiv
          ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm q)))⁻¹ =
        (rationalPadicNormNNRealAtPrime d q)⁻¹
    exact congrArg
      (fun r ↦ (rationalPadicNormNNRealAtPrime d r)⁻¹) hpv
  have hnn :
      rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S =
        ∏ q ∈ Rat.padicNormPrimeSupport d,
          (rationalPadicNormNNRealAtPrime d q)⁻¹ := by
    unfold rationalIsometrySpinCandidateFiniteExceptionalModulus
    rw [← Finset.prod_subtype S (fun _ ↦ Iff.rfl) f]
    exact hprod_places.symm.trans hprod_primes
  rw [hnn, ENNReal.coe_finset_prod]
  apply Finset.prod_congr rfl
  intro q hq
  have hnorm : rationalPadicNormNNRealAtPrime d q ≠ 0 := by
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    rw [rationalPadicNormNNRealAtPrime, nnnorm_ne_zero_iff]
    exact (map_ne_zero (algebraMap ℚ ℚ_[q.1])).mpr hd
  rw [ENNReal.coe_inv hnorm]
  rfl

/-- The finite exceptional tangent modulus equals the archimedean absolute
value of the same rational tangent determinant. -/
theorem rationalIsometrySpinCandidateFiniteExceptionalModulus_coe_eq_ofReal_abs
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hsupp : rationalPadicNormSupportPlaces
      (rationalIsometrySkewAdjointDetScalar W Z e) ⊆ S) :
    (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S : ℝ≥0∞) =
      ENNReal.ofReal
        |((rationalIsometrySkewAdjointDetScalar W Z e : ℚ) : ℝ)| := by
  let d := rationalIsometrySkewAdjointDetScalar W Z e
  let A : ℝ≥0∞ := ENNReal.ofReal |((d : ℚ) : ℝ)|
  let N : ℝ≥0∞ :=
    ∏ q ∈ Rat.padicNormPrimeSupport d,
      Rat.padicNormENNRealAtPrime d q
  let Q : ℝ≥0∞ :=
    ∏ q ∈ Rat.padicNormPrimeSupport d,
      (Rat.padicNormENNRealAtPrime d q)⁻¹
  have hd : d ≠ 0 := rationalIsometrySkewAdjointDetScalar_ne_zero W Z e
  have hterm0 (q : {p : ℕ // Nat.Prime p}) :
      Rat.padicNormENNRealAtPrime d q ≠ 0 := by
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    rw [Rat.padicNormENNRealAtPrime, ENNReal.coe_ne_zero,
      nnnorm_ne_zero_iff]
    exact (map_ne_zero (algebraMap ℚ ℚ_[q.1])).mpr hd
  have htermTop (q : {p : ℕ // Nat.Prime p}) :
      Rat.padicNormENNRealAtPrime d q ≠ ⊤ := by
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    exact ENNReal.coe_ne_top
  have hN0 : N ≠ 0 := by
    dsimp only [N]
    exact Finset.prod_ne_zero_iff.mpr fun q _ ↦ hterm0 q
  have hNTop : N ≠ ⊤ := by
    dsimp only [N]
    exact ENNReal.prod_ne_top fun q _ ↦ htermTop q
  have hformula : A * N = 1 := by
    dsimp only [A, N, d]
    exact rationalIsometrySkewAdjointDetScalar_product_formula W Z e
  have hQN : Q * N = 1 := by
    dsimp only [Q, N]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro q hq
    exact ENNReal.inv_mul_cancel (hterm0 q) (htermTop q)
  rw [rationalIsometrySpinCandidateFiniteExceptionalModulus_coe_eq_supported_prod_inv
    W Z e hsupp]
  change Q = A
  apply (ENNReal.mul_right_inj hN0 hNTop).mp
  simpa only [mul_comm] using hQN.trans hformula.symm

/-! ## Coherent real--finite and full-adelic transport -/

/-- The coherent real--finite product measure transports by the real
reciprocal tangent modulus times the exact finite correction. -/
theorem map_rationalIsometryRealFiniteSpinCandidateCoherentGroupMeasure
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measure.map
        (rationalIsometryRealFiniteSpinCandidateContinuousMulEquiv W Z e)
        (W.realCliffordSpinCandidateChartGluedMeasure.prod
          W.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure) =
      ((((Real.toNNReal
          |((rationalIsometrySkewAdjointDetScalar W Z e : ℚ) : ℝ)|)⁻¹ :
            ℝ≥0) : ℝ≥0∞) *
          (e.spinCandidateRawRationalIsometryInverseVolumeCorrection S *
            (rationalIsometrySpinCandidateFiniteExceptionalModulus
              W Z e S : ℝ≥0∞))) •
        (Z.realCliffordSpinCandidateChartGluedMeasure.prod
          Z.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure) := by
  letI : IsLocallyFiniteMeasure
      W.realCliffordSpinCandidateChartGluedMeasure :=
    W.realCliffordSpinCandidateChartGluedMeasure_isLocallyFinite
  letI : SigmaFinite W.realCliffordSpinCandidateChartGluedMeasure :=
    sigmaFinite_of_locallyFinite
  letI : SFinite W.realCliffordSpinCandidateChartGluedMeasure := by
    infer_instance
  have hreal : Measurable
      (rationalIsometrySpinCandidateContinuousMulEquiv W Z e ℝ) :=
    (rationalIsometrySpinCandidateContinuousMulEquiv W Z e ℝ).measurable
  have hfinite : Measurable
      (rationalIsometrySpinCandidateContinuousMulEquiv
        W Z e RationalFiniteAdele) :=
    (rationalIsometrySpinCandidateContinuousMulEquiv
      W Z e RationalFiniteAdele).measurable
  change Measure.map
      (Prod.map
        (rationalIsometrySpinCandidateContinuousMulEquiv W Z e ℝ)
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalFiniteAdele))
      (W.realCliffordSpinCandidateChartGluedMeasure.prod
        W.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure) = _
  rw [← Measure.map_prod_map _ _ hreal hfinite,
    map_rationalIsometryRealCliffordSpinCandidateChartGluedMeasure W Z e,
    map_rationalIsometrySpinCandidateCoherentGroupMeasure
      W Z e hS hW hZ]
  let r : ℝ≥0∞ :=
    ((Real.toNNReal
      |((rationalIsometrySkewAdjointDetScalar W Z e : ℚ) : ℝ)|)⁻¹ : ℝ≥0)
  let c : ℝ≥0∞ :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection S *
      (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S : ℝ≥0∞)
  change
    (r • Z.realCliffordSpinCandidateChartGluedMeasure).prod
        (c • Z.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure) =
      (r * c) •
        (Z.realCliffordSpinCandidateChartGluedMeasure.prod
          Z.finiteAdelicCliffordSpinCandidateCoherentGroupMeasure)
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

/-- The coherent full-adelic Spin Haar pushforward retains the real modulus
and exact coherent finite scalar. -/
theorem map_rationalIsometryFullAdelicSpinCandidateCoherentGroupMeasure
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measure.map
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalAdele)
        W.fullAdelicCliffordSpinCandidateCoherentGroupMeasure =
      ((((Real.toNNReal
          |((rationalIsometrySkewAdjointDetScalar W Z e : ℚ) : ℝ)|)⁻¹ :
            ℝ≥0) : ℝ≥0∞) *
          (e.spinCandidateRawRationalIsometryInverseVolumeCorrection S *
            (rationalIsometrySpinCandidateFiniteExceptionalModulus
              W Z e S : ℝ≥0∞))) •
        Z.fullAdelicCliffordSpinCandidateCoherentGroupMeasure := by
  apply
    Z.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toHomeomorph
      |>.measurableEmbedding.map_injective
  have hfull : Measurable
      (rationalIsometrySpinCandidateContinuousMulEquiv
        W Z e RationalAdele) :=
    (rationalIsometrySpinCandidateContinuousMulEquiv
      W Z e RationalAdele).measurable
  have hsplit : Measurable
      Z.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toHomeomorph :=
    Z.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toHomeomorph.measurable
  rw [Measure.map_smul,
    Z.map_fullAdelicCliffordSpinCandidateCoherentGroupMeasure_realFinite]
  rw [Measure.map_map hsplit hfull]
  have hcommutes :
      Z.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toHomeomorph ∘
          rationalIsometrySpinCandidateContinuousMulEquiv W Z e RationalAdele =
        (rationalIsometryRealFiniteSpinCandidateContinuousMulEquiv
            W Z e).toHomeomorph ∘
          W.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toHomeomorph := by
    funext z
    exact rationalIsometryFullAdelicSpinCandidate_realFinite_commutes W Z e z
  rw [hcommutes]
  have hproduct : Measurable
      (rationalIsometryRealFiniteSpinCandidateContinuousMulEquiv
        W Z e).toHomeomorph :=
    (rationalIsometryRealFiniteSpinCandidateContinuousMulEquiv
      W Z e).toHomeomorph.measurable
  have hsourceSplit : Measurable
      W.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toHomeomorph :=
    W.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv.toHomeomorph.measurable
  rw [← Measure.map_map hproduct hsourceSplit]
  rw [W.map_fullAdelicCliffordSpinCandidateCoherentGroupMeasure_realFinite]
  exact map_rationalIsometryRealFiniteSpinCandidateCoherentGroupMeasure
    W Z e hS hW hZ

/-! ## Exact raw scalar cancellation -/

/-- The transported raw scale cancels the inverse-volume correction, while
the real reciprocal tangent modulus cancels the supported finite tangent
modulus by the rational product formula. -/
theorem transportedSpinCandidateRawScale_mul_fullRationalIsometryScalar
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (finiteScale : ℝ≥0) :
    (((finiteScale /
          e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S :
            ℝ≥0) : ℝ≥0∞) *
        ((((Real.toNNReal
            |((rationalIsometrySkewAdjointDetScalar W Z e : ℚ) : ℝ)|)⁻¹ :
              ℝ≥0) : ℝ≥0∞) *
          (e.spinCandidateRawRationalIsometryInverseVolumeCorrection S *
            (rationalIsometrySpinCandidateFiniteExceptionalModulus
              W Z e S : ℝ≥0∞)))) =
      (finiteScale : ℝ≥0∞) := by
  let correction :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection S
  let correctionNN :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S
  let a : ℝ≥0 := Real.toNNReal
    |((rationalIsometrySkewAdjointDetScalar W Z e : ℚ) : ℝ)|
  have hcorrectionNN0 : correctionNN ≠ 0 :=
    ne_of_gt
      (e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal_pos S)
  have hcorrection0 : correction ≠ 0 :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_zero S
  have hcorrectionTop : correction ≠ ⊤ :=
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection_ne_top S
  have hcoeCorrection : (correctionNN : ℝ≥0∞) = correction :=
    e.coe_spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S
  have hd : rationalIsometrySkewAdjointDetScalar W Z e ≠ 0 :=
    rationalIsometrySkewAdjointDetScalar_ne_zero W Z e
  have hdReal :
      ((rationalIsometrySkewAdjointDetScalar W Z e : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast hd
  have ha : a ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (abs_pos.mpr hdReal))
  have hcoeA : (a : ℝ≥0∞) =
      ENNReal.ofReal
        |((rationalIsometrySkewAdjointDetScalar W Z e : ℚ) : ℝ)| := by
    simp [a, ENNReal.ofReal]
  rw [rationalIsometrySpinCandidateFiniteExceptionalModulus_coe_eq_ofReal_abs
      W Z e hS.2.2.1,
    ← hcoeA]
  change
    (((finiteScale / correctionNN : ℝ≥0) : ℝ≥0∞) *
      (((a⁻¹ : ℝ≥0) : ℝ≥0∞) * (correction * (a : ℝ≥0∞)))) =
        (finiteScale : ℝ≥0∞)
  rw [ENNReal.coe_div hcorrectionNN0, ENNReal.coe_inv ha,
    hcoeCorrection]
  rw [ENNReal.div_eq_inv_mul]
  calc
    correction⁻¹ * (finiteScale : ℝ≥0∞) *
          ((a : ℝ≥0∞)⁻¹ * (correction * ↑a)) =
        (finiteScale : ℝ≥0∞) * (correction⁻¹ * correction) *
          ((a : ℝ≥0∞)⁻¹ * ↑a) := by
      ac_rfl
    _ = (finiteScale : ℝ≥0∞) := by
      rw [ENNReal.inv_mul_cancel hcorrection0 hcorrectionTop,
        ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr ha) ENNReal.coe_ne_top]
      simp

/-- Exact full-adelic raw Spin Haar transport under an arbitrary rational
isometry. -/
theorem map_rationalIsometryFullAdelicSpinCandidateRawDifferentialGroupMeasure
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (finiteScale : ℝ≥0) :
    Measure.map
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalAdele)
        (W.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
          (finiteScale /
            e.spinCandidateRawRationalIsometryInverseVolumeCorrectionNNReal S)) =
      Z.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
        finiteScale := by
  unfold fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
  rw [Measure.map_smul,
    map_rationalIsometryFullAdelicSpinCandidateCoherentGroupMeasure
      W Z e hS hW hZ,
    smul_smul,
    transportedSpinCandidateRawScale_mul_fullRationalIsometryScalar
      W Z e hS finiteScale]

end RationalQuadraticSpaceMatrix

end
