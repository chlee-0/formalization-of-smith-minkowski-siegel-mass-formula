import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorNormUnitValued
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductPrecursor
import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteStabilizerVolume
import SMSFormula.FiniteOrthogonalGroupGoodPrimeOddPositivity
import SMSFormula.FiniteOrthogonalGroupGoodPrimeEvenPositivity
import SMSFormula.RationalSpecialOrthogonalRawFullAdelicDifferentialNormalization

/-!
# Convergence of the raw Spin differential volume products

At every odd unimodular place outside the independent integral-lifting bad
set, the integral Spin and special-orthogonal differential volumes agree.
Consequently their reciprocal cutoff products differ eventually by one fixed
positive finite exceptional-place scalar.  This module combines that finite
comparison with the Euler-product convergence already proved for
the special-orthogonal lattice stabilizers.

For rank at least three this closes the positive-finite cutoff certificate
required by the raw Spin differential normalization.  It does not use or
assert condition (K), Ono's relative Tamagawa comparison, or `tau(Spin) = 1`.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped BigOperators ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option maxHeartbeats 600000

local instance : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-! ## The finite exceptional-place correction -/

/-- The special-orthogonal reciprocal-volume cutoff over the same height-one
places used by the Spin cutoff. -/
def cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct
    (V : RationalQuadraticSpaceMatrix n) (N : ℕ) : ℝ≥0∞ :=
  ∏ v ∈ cliffordSpinCandidateRationalHeightOnePlacesUpTo N,
    (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹

/-- The union of the three finite sets needed for the eventual comparison:
the admissible restricted-product set, the odd-unimodular range set, and the
integral-lifting set. -/
def cliffordSpinCandidateIntegralVolumeComparisonBadPlaces
    (V : RationalQuadraticSpaceMatrix n) :
    Finset (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  V.cliffordSpinCandidateAdmissibleBadPlaces ∪
    V.cliffordSpinCandidateOddUnimodularBadPlaces ∪
      V.cliffordSpinCandidateIntegralLiftingBadPlaces

/-- A natural-prime cutoff containing every comparison bad place. -/
def cliffordSpinCandidateIntegralVolumeComparisonBadPlacesCutoff
    (V : RationalQuadraticSpaceMatrix n) : ℕ :=
  (V.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces).sup fun v =>
    (Rat.HeightOneSpectrum.primesEquiv v).1

theorem cliffordSpinCandidateIntegralVolumeComparisonBadPlaces_subset_cutoff
    (V : RationalQuadraticSpaceMatrix n) :
    V.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces ⊆
      cliffordSpinCandidateRationalHeightOnePlacesUpTo
        V.cliffordSpinCandidateIntegralVolumeComparisonBadPlacesCutoff := by
  intro v hv
  rw [mem_cliffordSpinCandidateRationalHeightOnePlacesUpTo_iff]
  unfold cliffordSpinCandidateIntegralVolumeComparisonBadPlacesCutoff
  exact Finset.le_sup (f := fun w : IsDedekindDomain.HeightOneSpectrum ℤ =>
    (Rat.HeightOneSpectrum.primesEquiv w).1) hv

/-- The reciprocal Spin-volume contribution of comparison bad places which
are not already omitted by the admissible restricted product. -/
def cliffordSpinCandidateExceptionalIntegralInverseVolume
    (V : RationalQuadraticSpaceMatrix n) : ℝ≥0∞ :=
  ∏ v ∈ V.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces \
      V.cliffordSpinCandidateAdmissibleBadPlaces,
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹

/-- The reciprocal special-orthogonal volume of all comparison bad places. -/
def specialOrthogonalExceptionalIntegralInverseVolume
    (V : RationalQuadraticSpaceMatrix n) : ℝ≥0∞ :=
  ∏ v ∈ V.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces,
    (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹

/-- The fixed scalar converting the eventual special-orthogonal reciprocal
cutoff product into the Spin reciprocal cutoff product. -/
def specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection
    (V : RationalQuadraticSpaceMatrix n) : ℝ≥0∞ :=
  V.cliffordSpinCandidateExceptionalIntegralInverseVolume *
    (V.specialOrthogonalExceptionalIntegralInverseVolume)⁻¹

theorem cliffordSpinCandidateExceptionalIntegralInverseVolume_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.cliffordSpinCandidateExceptionalIntegralInverseVolume ≠ 0 := by
  unfold cliffordSpinCandidateExceptionalIntegralInverseVolume
  exact Finset.prod_ne_zero_iff.mpr fun v _ =>
    ENNReal.inv_ne_zero.mpr
      (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top v)

theorem cliffordSpinCandidateExceptionalIntegralInverseVolume_ne_top
    (V : RationalQuadraticSpaceMatrix n) :
    V.cliffordSpinCandidateExceptionalIntegralInverseVolume ≠ ⊤ := by
  unfold cliffordSpinCandidateExceptionalIntegralInverseVolume
  exact ENNReal.prod_ne_top fun v hv =>
    ENNReal.inv_ne_top.mpr
      (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero
        ∅ ⟨v, by
          simpa only [cliffordSpinCandidateAdmissibleExceptionalPlaces,
            Finset.empty_union] using (Finset.mem_sdiff.mp hv).2⟩)

theorem specialOrthogonalExceptionalIntegralInverseVolume_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.specialOrthogonalExceptionalIntegralInverseVolume ≠ 0 := by
  unfold specialOrthogonalExceptionalIntegralInverseVolume
  exact Finset.prod_ne_zero_iff.mpr fun v _ =>
    ENNReal.inv_ne_zero.mpr
      (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top v)

theorem specialOrthogonalExceptionalIntegralInverseVolume_ne_top
    (V : RationalQuadraticSpaceMatrix n) :
    V.specialOrthogonalExceptionalIntegralInverseVolume ≠ ⊤ := by
  unfold specialOrthogonalExceptionalIntegralInverseVolume
  exact ENNReal.prod_ne_top fun v _ =>
    ENNReal.inv_ne_top.mpr
      (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero v)

theorem specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection_ne_zero
    (V : RationalQuadraticSpaceMatrix n) :
    V.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection ≠ 0 := by
  exact mul_ne_zero
    V.cliffordSpinCandidateExceptionalIntegralInverseVolume_ne_zero
    (ENNReal.inv_ne_zero.mpr
      V.specialOrthogonalExceptionalIntegralInverseVolume_ne_top)

theorem specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection_ne_top
    (V : RationalQuadraticSpaceMatrix n) :
    V.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    V.cliffordSpinCandidateExceptionalIntegralInverseVolume_ne_top
    (ENNReal.inv_ne_top.mpr
      V.specialOrthogonalExceptionalIntegralInverseVolume_ne_zero)

/-! ## Comparison with the lattice special-orthogonal product -/

/-- The height-one special-orthogonal integral volume is the lattice
differential stabilizer volume at the corresponding rational prime. -/
theorem heightOnePadicSpecialOrthogonalIntegralVolume_eq_latticeAtPrime
    (L : PositiveDefiniteIntegralLattice n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume
        v =
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime
        (Rat.HeightOneSpectrum.primesEquiv v) := by
  rw [← padicInvariantDifferentialIntegralVolumeAtPrime_eq_lattice]
  unfold heightOnePadicSpecialOrthogonalIntegralVolume
    padicInvariantDifferentialIntegralVolumeAtPrime
  rw [L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSubgroup_eq_comap]

/-- The height-one reciprocal cutoff is exactly the already convergent
lattice special-orthogonal reciprocal cutoff. -/
theorem
    cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct_eq_lattice
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ) :
    L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct
        N =
      L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct
        N := by
  classical
  have prod_inv (S : Finset {p : ℕ // Nat.Prime p})
      (f : {p : ℕ // Nat.Prime p} → ℝ≥0∞)
      (h0 : ∀ q, f q ≠ 0) (htop : ∀ q, f q ≠ ⊤) :
      (∏ q ∈ S, (f q)⁻¹) = (∏ q ∈ S, f q)⁻¹ := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert q S hqS ih =>
        simp only [Finset.prod_insert hqS, ih]
        rw [ENNReal.mul_inv (Or.inl (h0 q)) (Or.inl (htop q))]
  unfold cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct
    cliffordSpinCandidateRationalHeightOnePlacesUpTo
    localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct
  rw [Finset.prod_map]
  simp only [Equiv.toEmbedding_apply]
  calc
    (∏ q ∈ rationalPrimesUpTo N,
        (L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume
          (Rat.HeightOneSpectrum.primesEquiv.symm q))⁻¹) =
        (∏ q ∈ rationalPrimesUpTo N,
          L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume
            (Rat.HeightOneSpectrum.primesEquiv.symm q))⁻¹ :=
      prod_inv (rationalPrimesUpTo N)
        (fun q =>
          L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume
            (Rat.HeightOneSpectrum.primesEquiv.symm q))
        (fun q =>
          L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero
            (Rat.HeightOneSpectrum.primesEquiv.symm q))
        (fun q =>
          L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top
            (Rat.HeightOneSpectrum.primesEquiv.symm q))
    _ = (∏ q ∈ rationalPrimesUpTo N,
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q)⁻¹ := by
      congr 1
      apply Finset.prod_congr rfl
      intro q _
      rw [heightOnePadicSpecialOrthogonalIntegralVolume_eq_latticeAtPrime L]
      exact congrArg
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime
        (Equiv.apply_symm_apply Rat.HeightOneSpectrum.primesEquiv q)

/-- Beyond the finite comparison cutoff, the Spin reciprocal product is the
fixed correction times the special-orthogonal reciprocal product. -/
theorem
    cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_correction_mul_specialOrthogonal_of_cutoff_le
    (L : PositiveDefiniteIntegralLattice (r + 2)) {N : ℕ}
    (hN :
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlacesCutoff ≤
        N) :
    L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralInverseVolumePartialProduct
        N =
      L.rationalQuadraticSpaceMatrix.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection *
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct
          N := by
  classical
  let V := L.rationalQuadraticSpaceMatrix
  let places := cliffordSpinCandidateRationalHeightOnePlacesUpTo N
  let admissible := V.cliffordSpinCandidateAdmissibleBadPlaces
  let exceptional := V.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces
  have hExceptional : exceptional ⊆ places := by
    exact Finset.Subset.trans
      V.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces_subset_cutoff
      (fun v hv =>
        (mem_cliffordSpinCandidateRationalHeightOnePlacesUpTo_iff N v).2
          (le_trans
            ((mem_cliffordSpinCandidateRationalHeightOnePlacesUpTo_iff
              V.cliffordSpinCandidateIntegralVolumeComparisonBadPlacesCutoff
              v).1 hv) hN))
  have hAdmissible : admissible ⊆ exceptional := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hspinSet :
      places \ admissible =
        (exceptional \ admissible) ∪ (places \ exceptional) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hvPlaces, hvAdmissible⟩
      by_cases hvExceptional : v ∈ exceptional
      · exact Or.inl ⟨hvExceptional, hvAdmissible⟩
      · exact Or.inr ⟨hvPlaces, hvExceptional⟩
    · rintro (⟨hvExceptional, hvAdmissible⟩ | ⟨hvPlaces, hvExceptional⟩)
      · exact ⟨hExceptional hvExceptional, hvAdmissible⟩
      · exact ⟨hvPlaces, fun hvAdmissible =>
          hvExceptional (hAdmissible hvAdmissible)⟩
  have hsoSet : places = exceptional ∪ (places \ exceptional) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hvPlaces
      by_cases hvExceptional : v ∈ exceptional
      · exact Or.inl hvExceptional
      · exact Or.inr ⟨hvPlaces, hvExceptional⟩
    · rintro (hvExceptional | ⟨hvPlaces, _⟩)
      · exact hExceptional hvExceptional
      · exact hvPlaces
  have hdisjSpin :
      Disjoint (exceptional \ admissible) (places \ exceptional) := by
    exact Finset.disjoint_left.mpr fun v hvEA hvPE =>
      (Finset.mem_sdiff.mp hvPE).2 (Finset.mem_sdiff.mp hvEA).1
  have hdisjSO : Disjoint exceptional (places \ exceptional) := by
    exact Finset.disjoint_left.mpr fun v hvE hvPE =>
      (Finset.mem_sdiff.mp hvPE).2 hvE
  have htail :
      (∏ v ∈ places \ exceptional,
          (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) =
        ∏ v ∈ places \ exceptional,
          (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ := by
    apply Finset.prod_congr rfl
    intro v hv
    have hvExceptional := (Finset.mem_sdiff.mp hv).2
    have hvAdmissible : v ∉ admissible := fun h =>
      hvExceptional (hAdmissible h)
    have hvRange :
        v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces := by
      intro h
      exact hvExceptional
        (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hvLift : v ∉ V.cliffordSpinCandidateIntegralLiftingBadPlaces := by
      intro h
      exact hvExceptional (Finset.mem_union_right _ h)
    rw [L.heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_not_mem_badPlaces
      ∅ ⟨v, by
        simpa only [cliffordSpinCandidateAdmissibleExceptionalPlaces,
          Finset.empty_union] using hvAdmissible⟩ hvRange hvLift]
  have hspin :
      V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N =
        V.cliffordSpinCandidateExceptionalIntegralInverseVolume *
          (∏ v ∈ places \ exceptional,
            (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹) := by
    unfold cliffordSpinCandidateIntegralInverseVolumePartialProduct
      cliffordSpinCandidateExceptionalIntegralInverseVolume
    change (∏ v ∈ places \ admissible,
        (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume v)⁻¹) = _
    rw [hspinSet, Finset.prod_union hdisjSpin, htail]
  have hso :
      V.cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct
          N =
        V.specialOrthogonalExceptionalIntegralInverseVolume *
          (∏ v ∈ places \ exceptional,
            (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹) := by
    unfold
      cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct
      specialOrthogonalExceptionalIntegralInverseVolume
    change (∏ v ∈ places,
      (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹) = _
    conv_lhs => rw [hsoSet, Finset.prod_union hdisjSO]
  rw [hspin, hso]
  unfold specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection
  have hcancel :
      (V.specialOrthogonalExceptionalIntegralInverseVolume)⁻¹ *
          V.specialOrthogonalExceptionalIntegralInverseVolume = 1 :=
    ENNReal.inv_mul_cancel
      V.specialOrthogonalExceptionalIntegralInverseVolume_ne_zero
      V.specialOrthogonalExceptionalIntegralInverseVolume_ne_top
  calc
    V.cliffordSpinCandidateExceptionalIntegralInverseVolume *
        ∏ v ∈ places \ exceptional,
          (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ =
      V.cliffordSpinCandidateExceptionalIntegralInverseVolume * 1 *
        ∏ v ∈ places \ exceptional,
          (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ := by
        rw [mul_one]
    _ = V.cliffordSpinCandidateExceptionalIntegralInverseVolume *
        (V.specialOrthogonalExceptionalIntegralInverseVolume)⁻¹ *
          (V.specialOrthogonalExceptionalIntegralInverseVolume *
            ∏ v ∈ places \ exceptional,
              (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹) := by
      rw [← hcancel]
      ac_rfl

/-! ## Positive-finite convergence certificates -/

/-- Any positive real Schulze--Pillot inverse-product limit supplies the raw
Spin differential cutoff certificate. -/
theorem
    exists_cliffordSpinCandidateRawDifferentialVolumeProductCertificate_of_massLocalInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice (r + 2)) {P : ℝ} (hPpos : 0 < P)
    (hP : massLocalInverseProductTendsTo L P) :
    ∃ finiteScale : ℝ≥0,
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
        finiteScale := by
  let V := L.rationalQuadraticSpaceMatrix
  let correction :=
    V.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection
  let soLimit :=
    L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P
  let spinLimit := correction * soLimit
  haveI : NeZero (r + 2) := ⟨by omega⟩
  have hSO :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo_finiteStabilizerInverseVolume_of_massLocalInverseProductTendsTo
      hP
  have hSOHeight :
      Filter.Tendsto
        (fun N : ℕ =>
          V.cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct
            N)
        Filter.atTop (nhds soLimit) := by
    refine Filter.Tendsto.congr' ?_ hSO
    filter_upwards with N
    exact
      (cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct_eq_lattice
        L N).symm
  have hCorrectionTop : correction ≠ ⊤ :=
    V.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection_ne_top
  have hScaled :
      Filter.Tendsto
        (fun N : ℕ => correction *
          V.cliffordSpinCandidateSpecialOrthogonalIntegralInverseVolumePartialProduct
            N)
        Filter.atTop (nhds spinLimit) :=
    ENNReal.Tendsto.const_mul hSOHeight (Or.inr hCorrectionTop)
  have hSpin :
      Filter.Tendsto
        (fun N : ℕ =>
          V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)
        Filter.atTop (nhds spinLimit) := by
    refine Filter.Tendsto.congr' ?_ hScaled
    filter_upwards [Filter.eventually_ge_atTop
      V.cliffordSpinCandidateIntegralVolumeComparisonBadPlacesCutoff]
      with N hN
    exact
      (cliffordSpinCandidateIntegralInverseVolumePartialProduct_eq_correction_mul_specialOrthogonal_of_cutoff_le
        L hN).symm
  have hSpinLimitZero : spinLimit ≠ 0 :=
    mul_ne_zero
      V.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection_ne_zero
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_zero
        hPpos)
  have hSpinLimitTop : spinLimit ≠ ⊤ :=
    ENNReal.mul_ne_top
      V.specialOrthogonalToCliffordSpinCandidateInverseVolumeCorrection_ne_top
      (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_top
        P)
  let finiteScale : ℝ≥0 := (spinLimit⁻¹).toNNReal
  refine ⟨finiteScale, ?_⟩
  have hscalePos : 0 < finiteScale := by
    dsimp [finiteScale]
    exact ENNReal.toNNReal_pos
      (ENNReal.inv_ne_zero.mpr hSpinLimitTop)
      (ENNReal.inv_ne_top.mpr hSpinLimitZero)
  have hscaleInv : (finiteScale : ℝ≥0∞)⁻¹ = spinLimit := by
    dsimp [finiteScale]
    rw [ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hSpinLimitZero), inv_inv]
  exact
    { finiteScale_pos := hscalePos
      inverseVolumeProduct_tendsto := by
        unfold CliffordSpinCandidateIntegralInverseVolumeProductTendsTo
        simpa only [hscaleInv] using hSpin }

/-! ## Direct products and rank-at-least-three endpoints -/

/-- At every cutoff, the direct volume product is the reciprocal of the
reciprocal-volume product. -/
theorem cliffordSpinCandidateIntegralVolumePartialProduct_eq_inv_inverseVolumePartialProduct
    (V : RationalQuadraticSpaceMatrix n) (N : ℕ) :
    V.cliffordSpinCandidateIntegralVolumePartialProduct N =
      (V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)⁻¹ := by
  classical
  unfold cliffordSpinCandidateIntegralVolumePartialProduct
    cliffordSpinCandidateIntegralInverseVolumePartialProduct
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro v hv
  exact ENNReal.mul_inv_cancel
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_zero
      ∅ ⟨v, by
        simpa only [cliffordSpinCandidateAdmissibleExceptionalPlaces,
          Finset.empty_union] using (Finset.mem_sdiff.mp hv).2⟩)
    (V.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume_ne_top v)

namespace CliffordSpinCandidateRawDifferentialVolumeProductCertificate

/-- A reciprocal cutoff certificate also gives convergence of the direct
volume cutoffs to the named positive finite scale. -/
theorem volumeProduct_tendsto
    {V : RationalQuadraticSpaceMatrix n} {finiteScale : ℝ≥0}
    (C : V.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
      finiteScale) :
    Filter.Tendsto
      (fun N : ℕ => V.cliffordSpinCandidateIntegralVolumePartialProduct N)
      Filter.atTop (nhds (finiteScale : ℝ≥0∞)) := by
  have hInverse := C.inverseVolumeProduct_tendsto
  unfold CliffordSpinCandidateIntegralInverseVolumeProductTendsTo at hInverse
  have hInverseInv :
      Filter.Tendsto
        (fun N : ℕ =>
          (V.cliffordSpinCandidateIntegralInverseVolumePartialProduct N)⁻¹)
        Filter.atTop (nhds (finiteScale : ℝ≥0∞)) := by
    simpa only [inv_inv] using hInverse.inv
  refine Filter.Tendsto.congr' ?_ hInverseInv
  filter_upwards with N
  rw [V.cliffordSpinCandidateIntegralVolumePartialProduct_eq_inv_inverseVolumePartialProduct]

end CliffordSpinCandidateRawDifferentialVolumeProductCertificate

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- In every rank at least three, the odd/even Euler products
supply a strictly positive real Schulze--Pillot inverse-product limit. -/
theorem exists_pos_massLocalInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) (hn3 : 3 ≤ n) :
    ∃ P : ℝ, 0 < P ∧ massLocalInverseProductTendsTo L P := by
  classical
  let N := (massBadPrimeSet L).sup fun p => p.1
  have hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N := by
    intro p hp
    rw [mem_rationalPrimesUpTo_iff]
    change p.1 ≤ (massBadPrimeSet L).sup (fun q => q.1)
    exact Finset.le_sup hp
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n
  · have hr1 : 1 < r := by omega
    let P := massPartialPrimeInverseProduct L N *
      ((Finset.Icc 1 (r - 1)).prod
          (fun j => goodPrimeEulerCoreZetaTailFactor N j) *
        goodPrimeEvenDirichletTailFactorOfCharacter L N r)
    refine ⟨P, ?_, ?_⟩
    · exact evenRankOrdinaryMassProductExpression_pos L N r hr1 hr
    · exact
        massLocalInverseProductTendsTo_of_goodPrimeEvenDirichletEulerProduct_one_lt
          L hB hr1 hr
  · have hr1 : 0 < r + 1 := by omega
    have hnOdd : n = 2 * (r + 1) - 1 := by omega
    let P := massPartialPrimeInverseProduct L N *
      (Finset.Icc 1 ((r + 1) - 1)).prod
        (fun j => goodPrimeEulerCoreZetaTailFactor N j)
    refine ⟨P, ?_, ?_⟩
    · exact oddRankOrdinaryMassProductExpression_pos L N (r + 1)
    · exact
        massLocalInverseProductTendsTo_of_goodPrimeOddZetaEulerProduct
          L hB hr1 hnOdd

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

/-- For every syntactic rank `r + 3`, the raw Spin direct and reciprocal
cutoff products have a positive finite certificate. -/
theorem
    exists_cliffordSpinCandidateRawDifferentialVolumeProductCertificate
    (L : PositiveDefiniteIntegralLattice (r + 3)) :
    ∃ finiteScale : ℝ≥0,
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawDifferentialVolumeProductCertificate
        finiteScale := by
  obtain ⟨P, hPpos, hP⟩ :=
    L.exists_pos_massLocalInverseProductTendsTo
      (by omega)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exists_cliffordSpinCandidateRawDifferentialVolumeProductCertificate_of_massLocalInverseProductTendsTo
      (r := r + 1) L hPpos hP)

/-- The cutoff certificate gives a finite scale for which the raw
measurable-Weil datum satisfies the raw normalization predicate.  The quotient
carrier is the simultaneous scaling of the coherent datum. -/
theorem
    exists_fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_isRawWithScale
    (L : PositiveDefiniteIntegralLattice (r + 3)) :
    ∃ finiteScale : ℝ≥0,
      L.rationalQuadraticSpaceMatrix.IsRawCliffordSpinCandidateDifferentialMeasurableWeilDataWithScale
        finiteScale
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData
          finiteScale) := by
  obtain ⟨finiteScale, C⟩ :=
    exists_cliffordSpinCandidateRawDifferentialVolumeProductCertificate
      L
  exact ⟨finiteScale,
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateRawDifferentialMeasurableWeilData_isRawWithScale
      finiteScale C⟩

end RationalQuadraticSpaceMatrix
