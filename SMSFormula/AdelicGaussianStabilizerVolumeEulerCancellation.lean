import SMSFormula.AdelicGaussianPresentationVolumeDensity
import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteStabilizerVolumeRatio
import SMSFormula.EulerProductPartialRatioCancellation
import SMSFormula.RationalPadicPlaceNormProduct
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductConvergence

/-!
# The Euler product of the Riesz ratio cancels against the finite stabilizer volumes

For the ambient lattice `A` (rank `m + 1 ≥ 5`), a supplied presentation `P` whose lower space is the
supplied witness lattice `L_W`, and a supplied finite set `E` of primes outside which the
presentation is integral, the prime is odd, prime to `M`, good, and the rational scalars `c_P`, `r`
are units, the per-prime identity gives `vol_A(q) = vol_W(q) · δ_q(M)` off `E`.  With the limit of
partial volume ratios this yields

`(t_A / t_W) · ∏_{q ∈ E} δ_q(M) · ∏_{q ∈ E} vol_W(q) = ∏_{q ∈ E} vol_A(q) · ∏'_q δ_q(M)`,

so the Euler product `∏' δ_q(M)` of the orbit Riesz ratio is `t_A/t_W` times a finite product of
exceptional local factors.  Nothing is chosen: `P`, `L_W` and `E` are supplied.
-/

noncomputable section

open MeasureTheory Metric PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Filter
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

local instance vePadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance vePadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

variable {m : ℕ} [NeZero m] (A : PositiveDefiniteIntegralLattice (m + 1)) (LW : PositiveDefiniteIntegralLattice m)
  {x : Fin (m + 1) → ℚ}
variable (P : A.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
variable (hx : A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

theorem localResidueDensity_nonneg (M : ℤ) (hM0 : M ≠ 0) (q : {p : ℕ // Nat.Prime p}) :
    0 ≤ A.localResidueDensity M q.1 := by
  haveI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  obtain ⟨k, hk⟩ := (A.eventually_normalizedResidueCount_eq_localResidueDensity q.1 hM0).exists
  rw [← hk, normalizedResidueCount]
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)) (Nat.cast_nonneg _)

theorem nnnorm_algebraMap_eq_one_of_not_mem {c : ℚ} (hc : c ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : Rat.HeightOneSpectrum.primesEquiv v ∉ Rat.padicNormPrimeSupport c) :
    (‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] c‖₊ : ℝ≥0∞) = 1 := by
  have hv' : v ∉ rationalPadicNormSupportPlaces c := by
    intro h
    apply hv
    rw [rationalPadicNormSupportPlaces] at h
    obtain ⟨q, hq, hqv⟩ := Finset.mem_map.mp h
    have : q = Rat.HeightOneSpectrum.primesEquiv v := by
      rw [← hqv]; simp
    rwa [← this]
  have h := norm_algebraMap_eq_one_of_not_mem_rationalPadicNormSupportPlaces hc hv'
  have h' : ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] c‖₊ = 1 := by
    ext; simpa using h
  rw [h', ENNReal.coe_one]

set_option maxHeartbeats 1600000 in
/-- The per-prime factorization off the supplied exceptional set: `vol_A(q) = vol_W(q) · δ_q(M)`. -/
theorem stabilizerVolumeAtPrime_eq_mul_localResidueDensity (hm : 1 ≤ m)
    (hlow : P.lowerSpace = LW.rationalQuadraticSpaceMatrix)
    (M : ℤ) (hM : A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (q : {p : ℕ // Nat.Prime p})
    (hq : ¬ q.1 ∣ P.presentationDenominator hx ∧ q.1 ≠ 2 ∧ ¬ (q.1 : ℤ) ∣ M ∧
      q.1 ∉ P.lowerSpace.goodPlaceExceptionalPrimes
        (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∧
      q ∉ Rat.padicNormPrimeSupport (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx)
        A.rationalQuadraticSpaceMatrix (P.blockToAmbientIsometryEquiv hx)) ∧
      q ∉ Rat.padicNormPrimeSupport (P.lowerSpace.lastOrbitGaugeRatio
        (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ)) :
    A.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q =
      LW.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q *
        ENNReal.ofReal (A.localResidueDensity M q.1) := by
  obtain ⟨hqD, hq2, hqM, hqg, hqc, hqr⟩ := hq
  set v : IsDedekindDomain.HeightOneSpectrum ℤ := Rat.HeightOneSpectrum.primesEquiv.symm q with hvdef
  have hvq : Rat.HeightOneSpectrum.primesEquiv v = q := by rw [hvdef]; simp
  -- a covering block atlas
  have hbform : ∃ w, (P.blockSpace hx).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] w ≠ 0 := by
    refine ⟨lastCoordinateVector, ?_⟩
    have hsh := P.lowerSpace.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
      (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
    change (P.blockSpace hx).commutativeScalarExtensionQuadraticForm _ lastCoordinateVector =
      algebraMap ℚ _ _ at hsh
    rw [hsh]; exact (map_ne_zero _).mpr hx
  obtain ⟨point, hpoint, hcover⟩ := QuadraticMap.exists_padicSquareBranchAtlas_cover
    (Rat.HeightOneSpectrum.primesEquiv v).1 _ hbform
  have h := heightOneIntegralVolume_ambient_div_lower_eq_localResidueDensity A P hx hm M hM v
    (by rw [hvq]; exact hqD) (by rw [hvq]; exact hqg) (by rw [hvq]; exact hq2)
    (by rw [hvq]; exact hqM) Measure.addHaar point hpoint (fun _ ↦ Measure.addHaar) hcover
  rw [nnnorm_algebraMap_eq_one_of_not_mem (rationalIsometrySkewAdjointDetScalar_ne_zero _ _ _) v
      (by rw [hvq]; exact hqc),
    lastOrbitGaugeRatio_scalarExtension,
    nnnorm_algebraMap_eq_one_of_not_mem (lastOrbitGaugeRatio_ne_zero _ _ _ _) v
      (by rw [hvq]; exact hqr), one_mul, one_mul, hvq] at h
  rw [RationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume_eq_latticeAtPrime A v,
    hlow, RationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume_eq_latticeAtPrime
      LW v, hvq] at h
  have h2 := (ENNReal.eq_div_iff
    (LW.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_zero q)
    (LW.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_top q)).mp h.symm
  exact h2.symm

set_option maxHeartbeats 1600000 in
/-- The Euler product cancels (ambient rank at least four):
`(t_A/t_W) · ∏_E δ · ∏_E vol_W = ∏_E vol_A · ∏' δ` for every supplied
finite set `E` of primes outside which the presentation is integral, the prime is odd, prime to
`M`, good, and `c_P`, `r` are units. -/
theorem finiteStabilizerVolume_div_mul_prod_eq_prod_mul_tprod_of_three_le (hm : 3 ≤ m)
    (hlow : P.lowerSpace = LW.rationalQuadraticSpaceMatrix)
    {PA PL : ℝ} (hPA0 : 0 < PA) (hA : massLocalInverseProductTendsTo A PA)
    (hL : massLocalInverseProductTendsTo LW PL)
    (M : ℤ) (hM : A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (E : Finset {p : ℕ // Nat.Prime p})
    (hE : ∀ q ∉ E, ¬ q.1 ∣ P.presentationDenominator hx ∧ q.1 ≠ 2 ∧ ¬ (q.1 : ℤ) ∣ M ∧
      q.1 ∉ P.lowerSpace.goodPlaceExceptionalPrimes
        (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∧
      q ∉ Rat.padicNormPrimeSupport (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx)
        A.rationalQuadraticSpaceMatrix (P.blockToAmbientIsometryEquiv hx)) ∧
      q ∉ Rat.padicNormPrimeSupport (P.lowerSpace.lastOrbitGaugeRatio
        (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ)) :
    A.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume PA /
          LW.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume PL *
        ENNReal.ofReal (∏ q ∈ E, A.localResidueDensity M q.1) *
        ∏ q ∈ E, LW.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q =
      (∏ q ∈ E, A.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q) *
        ENNReal.ofReal (∏' q : {p : ℕ // Nat.Prime p}, A.localResidueDensity M q.1) := by
  have hM0 : M ≠ 0 := by
    rintro rfl; exact hx (by rw [hM]; simp)
  have hmult : Multipliable (fun q : {p : ℕ // Nat.Prime p} ↦ A.localResidueDensity M q.1) :=
    (A.multipliable_localResidueDensity_of_three_le hm hM0
      (A.isResidueBadBlock_residueBadBlock hM0)).1
  exact mul_prod_eq_prod_mul_tprod_of_partialRatio E
    (A.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_top)
    (LW.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_zero)
    (LW.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime_ne_top)
    (localResidueDensity_nonneg A M hM0) hmult
    (fun q hq ↦ stabilizerVolumeAtPrime_eq_mul_localResidueDensity A LW P hx (by omega) hlow M hM q
      (hE q hq))
    (tendsto_prod_stabilizerVolume_div_prod_stabilizerVolume A LW hPA0 hA hL)

set_option maxHeartbeats 1600000 in
/-- The rank-at-least-five form of the Euler cancellation. -/
theorem finiteStabilizerVolume_div_mul_prod_eq_prod_mul_tprod (hm : 4 ≤ m)
    (hlow : P.lowerSpace = LW.rationalQuadraticSpaceMatrix)
    {PA PL : ℝ} (hPA0 : 0 < PA) (hA : massLocalInverseProductTendsTo A PA)
    (hL : massLocalInverseProductTendsTo LW PL)
    (M : ℤ) (hM : A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (E : Finset {p : ℕ // Nat.Prime p})
    (hE : ∀ q ∉ E, ¬ q.1 ∣ P.presentationDenominator hx ∧ q.1 ≠ 2 ∧ ¬ (q.1 : ℤ) ∣ M ∧
      q.1 ∉ P.lowerSpace.goodPlaceExceptionalPrimes
        (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∧
      q ∉ Rat.padicNormPrimeSupport (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx)
        A.rationalQuadraticSpaceMatrix (P.blockToAmbientIsometryEquiv hx)) ∧
      q ∉ Rat.padicNormPrimeSupport (P.lowerSpace.lastOrbitGaugeRatio
        (A.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ)) :
    A.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume PA /
          LW.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume PL *
        ENNReal.ofReal (∏ q ∈ E, A.localResidueDensity M q.1) *
        ∏ q ∈ E, LW.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q =
      (∏ q ∈ E, A.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q) *
        ENNReal.ofReal (∏' q : {p : ℕ // Nat.Prime p}, A.localResidueDensity M q.1) :=
  finiteStabilizerVolume_div_mul_prod_eq_prod_mul_tprod_of_three_le A LW P hx (by omega) hlow hPA0 hA
    hL M hM E hE

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
