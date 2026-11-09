import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteAdelicCoherentWeightComparison
import SMSFormula.RationalQuadraticIsometryGeneralSpinRealHaarFactor

/-!
# Finite presentation Haar factor and the residual baseline ratio

The coherent overlap calculation determines the finite presentation Haar
scalar only after retaining the two baseline-relative restricted-product
weights.  This file solves that scalar equation exactly and combines its
local-norm part with the rational product formula.  The resulting full
real--finite scalar is the literal ratio of the block and ambient baseline
weights; no claim that this ratio is one is made here.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance finiteHaarFactorDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance finiteHaarFactorPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The exact residual ratio between the two independently fixed
baseline-relative coherent weights. -/
def finiteAdelicPresentationBaselineWeightRatio
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0∞ :=
  (P.blockSpace hx).cliffordGeneralSpinHorizontalRestrictedBlockWeight S *
    (V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S)⁻¹

/-- On a support containing every nontrivial rational p-adic norm, the
exceptional modulus is the inverse of the supported norm product. -/
theorem finiteExceptionalPadicPresentationModulus_coe_eq_supported_prod_inv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hsupp : rationalPadicNormSupportPlaces
      (P.blockToAmbientSkewAdjointDetScalar hx) ⊆ S) :
    (P.finiteExceptionalPadicPresentationModulus S hx : ℝ≥0∞) =
      ∏ q ∈ Rat.padicNormPrimeSupport
          (P.blockToAmbientSkewAdjointDetScalar hx),
        (Rat.padicNormENNRealAtPrime
          (P.blockToAmbientSkewAdjointDetScalar hx) q)⁻¹ := by
  let d := P.blockToAmbientSkewAdjointDetScalar hx
  let f : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0 := fun v ↦
    ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] d‖₊⁻¹
  have hd : d ≠ 0 := P.blockToAmbientSkewAdjointDetScalar_ne_zero hx
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
  have hnn : P.finiteExceptionalPadicPresentationModulus S hx =
      ∏ q ∈ Rat.padicNormPrimeSupport d,
        (rationalPadicNormNNRealAtPrime d q)⁻¹ := by
    unfold finiteExceptionalPadicPresentationModulus
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

/-- The finite exceptional modulus itself equals the archimedean absolute
value of the rational tangent determinant. -/
theorem finiteExceptionalPadicPresentationModulus_coe_eq_ofReal_abs
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hsupp : rationalPadicNormSupportPlaces
      (P.blockToAmbientSkewAdjointDetScalar hx) ⊆ S) :
    (P.finiteExceptionalPadicPresentationModulus S hx : ℝ≥0∞) =
      ENNReal.ofReal
        |((P.blockToAmbientSkewAdjointDetScalar hx : ℚ) : ℝ)| := by
  let d := P.blockToAmbientSkewAdjointDetScalar hx
  let A : ℝ≥0∞ := ENNReal.ofReal |((d : ℚ) : ℝ)|
  let N : ℝ≥0∞ :=
    ∏ q ∈ Rat.padicNormPrimeSupport d,
      Rat.padicNormENNRealAtPrime d q
  let Q : ℝ≥0∞ :=
    ∏ q ∈ Rat.padicNormPrimeSupport d,
      (Rat.padicNormENNRealAtPrime d q)⁻¹
  have hd : d ≠ 0 := P.blockToAmbientSkewAdjointDetScalar_ne_zero hx
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
    exact P.blockToAmbientSkewAdjointDetScalar_product_formula hx
  have hQN : Q * N = 1 := by
    dsimp only [Q, N]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro q hq
    exact ENNReal.inv_mul_cancel (hterm0 q) (htermTop q)
  rw [P.finiteExceptionalPadicPresentationModulus_coe_eq_supported_prod_inv
    hx hsupp]
  change Q = A
  apply (ENNReal.mul_right_inj hN0 hNTop).mp
  simpa only [mul_comm] using hQN.trans hformula.symm

/-- Solving the coherent cylinder equation evaluates the finite Haar scalar
as the local determinant modulus times the residual baseline-weight ratio. -/
theorem blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar_coe_eq
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    (P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) =
      P.finiteAdelicPresentationBaselineWeightRatio hx S *
        (P.finiteExceptionalPadicPresentationModulus S hx : ℝ≥0∞) := by
  let wB :=
    (P.blockSpace hx).cliffordGeneralSpinHorizontalRestrictedBlockWeight S
  let wA := V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S
  let q : ℝ≥0∞ := P.finiteExceptionalPadicPresentationModulus S hx
  let c : ℝ≥0∞ := P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx
  have hscalar : wB * q = c * wA :=
    P.coherentRestrictedBlockWeight_mul_modulus_eq_finiteHaarScalar_mul hx hS
  have hwA0 : wA ≠ 0 :=
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight_ne_zero S
  have hwATop : wA ≠ ⊤ :=
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight_ne_top S
  change c = (wB * wA⁻¹) * q
  calc
    c = (c * wA) * wA⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hwA0 hwATop, mul_one]
    _ = (wB * q) * wA⁻¹ := by rw [hscalar]
    _ = (wB * wA⁻¹) * q := by ac_rfl

/-- After the rational product formula cancels the real and local determinant
moduli, the complete presentation Haar scalar is exactly the residual ratio
of the two coherent baseline weights. -/
theorem blockToAmbientRealFiniteGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    ((P.blockToAmbientRealGeneralSpinHorizontalHaarScalar hx *
        P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0) : ℝ≥0∞) =
      P.finiteAdelicPresentationBaselineWeightRatio hx S := by
  let d := P.blockToAmbientSkewAdjointDetScalar hx
  let a : ℝ≥0 := Real.toNNReal |((d : ℚ) : ℝ)|
  let R : ℝ≥0∞ := P.finiteAdelicPresentationBaselineWeightRatio hx S
  have hd : d ≠ 0 := P.blockToAmbientSkewAdjointDetScalar_ne_zero hx
  have hdReal : ((d : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hd
  have ha : a ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (abs_pos.mpr hdReal))
  rw [ENNReal.coe_mul,
    P.blockToAmbientRealGeneralSpinHorizontalHaarScalar_eq hx,
    P.blockToAmbientFiniteAdelicGeneralSpinHorizontalHaarScalar_coe_eq hx hS,
    P.finiteExceptionalPadicPresentationModulus_coe_eq_ofReal_abs hx hS.2.2.1]
  change ↑(a⁻¹) * (R * ENNReal.ofReal |((d : ℚ) : ℝ)|) = R
  simp only [ENNReal.ofReal]
  rw [ENNReal.coe_inv ha]
  calc
    (↑a : ℝ≥0∞)⁻¹ * (R * ↑a) = ((↑a : ℝ≥0∞)⁻¹ * ↑a) * R := by
      ac_rfl
    _ = R := by
      rw [ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr ha) ENNReal.coe_ne_top,
        one_mul]

/-- The full-adelic Haar scalar equals the same exact residual
baseline-weight ratio. -/
theorem blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) =
      P.finiteAdelicPresentationBaselineWeightRatio hx S := by
  rw [P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_eq_mul_placewise hx]
  exact
    P.blockToAmbientRealFiniteGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio
      hx hS

/-- The residual baseline ratio is independent of the sufficiently large
finite presentation support used to compute it. -/
theorem finiteAdelicPresentationBaselineWeightRatio_eq_of_supports
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (hT : P.IsHorizontalIntegralTailPresentationSupport hx T) :
    P.finiteAdelicPresentationBaselineWeightRatio hx S =
      P.finiteAdelicPresentationBaselineWeightRatio hx T := by
  rw [← P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio
      hx hS,
    ← P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio
      hx hT]

/-- The residual baseline ratio is nonzero.  This records the positivity of
the already existing full-adelic Haar comparison scalar without asserting
that the ratio is one. -/
theorem finiteAdelicPresentationBaselineWeightRatio_ne_zero
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.finiteAdelicPresentationBaselineWeightRatio hx S ≠ 0 := by
  rw [← P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio
    hx hS]
  exact ENNReal.coe_ne_zero.mpr
    (ne_of_gt (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_pos hx))

/-- The residual baseline ratio is finite, so it can serve as a finite
normalization factor in quotient transport. -/
theorem finiteAdelicPresentationBaselineWeightRatio_ne_top
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.finiteAdelicPresentationBaselineWeightRatio hx S ≠ ⊤ := by
  rw [← P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio
    hx hS]
  exact ENNReal.coe_ne_top

/-- Exact full-adelic Haar transport with the support-independent residual
baseline ratio exposed as its scalar.  This is the scalar-covariant endpoint
available without assuming that the two mixed restricted-product baselines
coincide. -/
theorem map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_eq_weightRatio_smul
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        ((P.blockSpace hx)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
      P.finiteAdelicPresentationBaselineWeightRatio hx S •
        V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  rw [P.map_blockToAmbientFullAdelicGeneralSpinHorizontalGroupMeasure_eq_smul hx]
  change
    (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) •
        V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure = _
  rw [P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio
    hx hS]

/-- Literal presentation independence of the fixed full Haar normalization is
equivalent to triviality of the residual baseline-weight ratio. -/
theorem blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_eq_one_iff_weightRatio
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx = 1 ↔
      P.finiteAdelicPresentationBaselineWeightRatio hx S = 1 := by
  constructor
  · intro h
    have hcoe :=
      P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio
        hx hS
    rw [h] at hcoe
    exact hcoe.symm
  · intro h
    apply ENNReal.coe_injective
    rw [P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar_coe_eq_weightRatio
      hx hS, h]
    rfl

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
