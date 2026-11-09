import SMSFormula.AdelicGaussianShellWeightGoodPlaceTerm
import SMSFormula.AdelicGaussianOneShellWeightLocal
import SMSFormula.AdelicGaussianShellWeightRationalIdentity
import SMSFormula.PadicQuadraticLatticeGlueDensityGeneral
import SMSFormula.PadicCoordinateVectorHaar
import SMSFormula.RationalQuadraticIsometryGeneralSpinPadicCayleyTransport

/-!
# The bad-place scale at every horizontal bad place

For the supplied presentation, `E_p = toLin'(E)` pushes the unit-cube Haar to `‖det E‖_p⁻¹` times the
unit-cube Haar (`Padic.map_vectorHaar_matrix`).  By the glue isometry transport,
`glue_B(E_p⁻¹ ℤ_p^N) = ‖det E‖_p⁻¹ · glue_V(ℤ_p^N)`, and `ν(ℤ_p) · glue_V(ℤ_p^N) = δ_p(a)` at every prime
(`latticeGlue_toReal_mul_eq_localResidueDensity_of_ne_zero`).  Hence at every `v ∈ B`

`D_v = ‖r‖_v · ‖det E‖_v⁻¹ · δ_v(a)`,  so  `num_v = ‖q_a‖_v · D_v = δ_v(a) = den_v`

(using `‖r q_a‖_v = ‖det E‖_v`).  Off the primes of `D_P`, `‖det E‖_p = 1`.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Metric
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation

variable {m : ℕ} {V : RationalQuadraticSpaceMatrix (m + 1)} {x : Fin (m + 1) → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

local instance dgPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance dgPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- `E_p` is the matrix action of the rational block-to-ambient matrix. -/
theorem blockToAmbientPadicContinuousLinearEquiv_eq_toLin' (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact p.Prime] :
    (P.blockToAmbientPadicContinuousLinearEquiv hx p : (Fin (m + 1) → ℚ_[p]) → (Fin (m + 1) → ℚ_[p])) =
      Matrix.toLin' ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p])) := by
  funext y
  rw [blockToAmbientPadicContinuousLinearEquiv_apply, blockToAmbientBaseChangeIsometryEquiv_padic_eq_mulVec,
    Matrix.toLin'_apply]

/-- The unit-cube Haar under the presentation: `map E_p unitHaar = ‖det E‖_p⁻¹ • unitHaar`. -/
theorem map_blockToAmbientPadic_unitHaar (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact p.Prime] :
    (Padic.unitHaar p (Fin (m + 1))).map (P.blockToAmbientPadicContinuousLinearEquiv hx p) =
      ((‖algebraMap ℚ ℚ_[p] (P.blockToAmbientRationalMatrix hx).det‖₊⁻¹ : ℝ≥0) : ℝ≥0∞) •
        Padic.unitHaar p (Fin (m + 1)) := by
  have hmd : ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p])).det =
      algebraMap ℚ ℚ_[p] (P.blockToAmbientRationalMatrix hx).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hdet : ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p])).det ≠ 0 := by
    rw [hmd]
    exact (map_ne_zero _).mpr (P.blockToAmbientRationalMatrix_det_ne_zero hx)
  have h := Padic.map_vectorHaar_matrix p Measure.addHaar (Padic.unitHaar p (Fin (m + 1)))
    ((P.blockToAmbientRationalMatrix hx).map (algebraMap ℚ ℚ_[p])) hdet
  rw [P.blockToAmbientPadicContinuousLinearEquiv_eq_toLin' hx p, h, hmd]
  rfl

/-- Off the primes of `D_P`, `‖det E‖_p = 1`. -/
theorem norm_algebraMap_det_blockToAmbient_eq_one (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ P.presentationDenominator hx) :
    ‖algebraMap ℚ ℚ_[p] (P.blockToAmbientRationalMatrix hx).det‖ = 1 := by
  have hdetle : ∀ (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ), (∀ i j, ¬ p ∣ (A i j).den) →
      ‖algebraMap ℚ ℚ_[p] A.det‖ ≤ 1 := by
    intro A hA
    have hmem := PadicInt.map_ratMatrix_mem_subring A hA
    let A' : Matrix (Fin (m + 1)) (Fin (m + 1)) (PadicInt.subring p) :=
      fun i j ↦ ⟨A.map (algebraMap ℚ ℚ_[p]) i j, hmem i j⟩
    have hA' : A'.map (PadicInt.subring p).subtype = A.map (algebraMap ℚ ℚ_[p]) := by
      ext i j; rfl
    have hdet := RingHom.map_det (PadicInt.subring p).subtype A'
    rw [RingHom.mapMatrix_apply, hA', ← RingHom.mapMatrix_apply (algebraMap ℚ ℚ_[p]),
      ← RingHom.map_det] at hdet
    rw [← hdet]
    exact (A'.det).2
  have h1 := hdetle _ (P.not_dvd_den_blockToAmbientRationalMatrix_of_not_dvd hx hp)
  have h2 := hdetle _ (P.not_dvd_den_ambientToBlockRationalMatrix_of_not_dvd hx hp)
  have hprod : (P.blockToAmbientRationalMatrix hx).det * (P.ambientToBlockRationalMatrix hx).det = 1 := by
    rw [← Matrix.det_mul, P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx,
      Matrix.det_one]
  have hn := congrArg (fun c : ℚ ↦ ‖algebraMap ℚ ℚ_[p] c‖) hprod
  simp only [map_mul, norm_mul, map_one, norm_one] at hn
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  have : ‖algebraMap ℚ ℚ_[p] (P.blockToAmbientRationalMatrix hx).det‖ *
      ‖algebraMap ℚ ℚ_[p] (P.ambientToBlockRationalMatrix hx).det‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
  linarith

end RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum

local instance dgbPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance dgbPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance dgbDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

variable {m : ℕ} (L : PositiveDefiniteIntegralLattice (m + 1)) {x : Fin (m + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance dgbPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option maxHeartbeats 1600000 in
/-- The bad-place scale at every place: `D_v = ‖r‖_v · ‖det E‖_v⁻¹ · δ_v(a)`. -/
theorem badPlaceScale_eq_gauge_mul_inv_det_mul_localResidueDensity
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (D : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞) (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hD : ∀ (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v).1])
      (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
        ℚ_[(primesEquiv v).1]) (point₁ i) ≠ 0),
      {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) w ≠ 0} ⊆
        ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
          ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasRegion (primesEquiv v).1 point₁ hpoint₁ i →
      D v = (‖P.lowerSpace.lastOrbitGaugeRatio
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
          ℚ_[(primesEquiv v).1]‖₊ : ℝ≥0∞) *
        ((Measure.addHaar : Measure ℚ_[(primesEquiv v).1]) (Metric.closedBall 0 1) *
          ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
            ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasGlue (primesEquiv v).1 point₁ hpoint₁
            (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v).1 (Fin (m + 1)))
            (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1])
            (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) ⁻¹'
              Metric.closedBall 0 1)))) :
    D v = Rat.padicNormENNRealAtPrime (P.lowerSpace.lastOrbitGaugeRatio
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ) (primesEquiv v) *
      (Rat.padicNormENNRealAtPrime (P.blockToAmbientRationalMatrix hx).det (primesEquiv v))⁻¹ *
      ENNReal.ofReal (L.localResidueDensity M (primesEquiv v).1) := by
  set p := (Rat.HeightOneSpectrum.primesEquiv v).1
  haveI : Fact (Nat.Prime p) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hM0 : M ≠ 0 := by
    rintro rfl; exact hx (by rw [hM]; simp)
  have hvalue : ((((M : ℤ) : ℤ_[p]) : ℚ_[p])) ≠ 0 := by
    rw [padicIntCast_intCast_eq_algebraMap]
    exact (map_ne_zero _).mpr (by exact_mod_cast hM0)
  -- block atlas
  have hbform : ∃ w, (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] w ≠ 0 := by
    refine ⟨lastCoordinateVector, ?_⟩
    have hsh := P.lowerSpace.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p]
    change (P.blockSpace hx).commutativeScalarExtensionQuadraticForm _ lastCoordinateVector =
      algebraMap ℚ _ _ at hsh
    rw [hsh]; exact (map_ne_zero _).mpr hx
  obtain ⟨point, hpoint, hcover⟩ := QuadraticMap.exists_padicSquareBranchAtlas_cover p _ hbform
  -- lattice atlas
  have hform : ∃ w, ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
      (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w ≠ 0 := by
    refine ⟨P.blockToAmbientPadicContinuousLinearEquiv hx p lastCoordinateVector, ?_⟩
    rw [latticeGram_blockToAmbient L P hx p]
    obtain ⟨w, hw⟩ := hbform
    have hsh := P.lowerSpace.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p]
    change (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] lastCoordinateVector =
      algebraMap ℚ ℚ_[p] _ at hsh
    rw [hsh]; exact (map_ne_zero _).mpr hx
  obtain ⟨point₂, hpoint₂, hcover₂⟩ := QuadraticMap.exists_padicSquareBranchAtlas_cover p _ hform
  set E := P.blockToAmbientPadicContinuousLinearEquiv hx p
  have hmap := P.map_blockToAmbientPadic_unitHaar hx p
  have hTc : IsCompact (E ⁻¹' Metric.closedBall (0 : Fin (m + 1) → ℚ_[p]) 1) :=
    E.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall 0 1)
  have hTo : IsOpen (E ⁻¹' Metric.closedBall (0 : Fin (m + 1) → ℚ_[p]) 1) :=
    (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero).preimage E.continuous
  have htr := QuadraticMap.padicSquareBranchAtlasGlue_linearIsometry p _ _ E
    (latticeGram_blockToAmbient L P hx p) point hpoint (fun _ ↦ Measure.addHaar) hcover
    point₂ hpoint₂ (fun _ ↦ Measure.addHaar) hcover₂ Measure.addHaar _ _ hmap hvalue hTc hTo
  rw [Set.image_preimage_eq _ E.surjective] at htr
  have hdens := PositiveDefiniteIntegralLattice.latticeGlue_toReal_mul_eq_localResidueDensity_of_ne_zero L p hM0
    point₂ hpoint₂ (fun _ ↦ Measure.addHaar) hcover₂ Measure.addHaar
  have hgt := padicSquareBranchAtlasGlue_integral_ne_top
    ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]))
    point₂ hpoint₂ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar p (Fin (m + 1)))
    hcover₂ hvalue
  have hνt : (Measure.addHaar : Measure ℚ_[p]) (Metric.closedBall 0 1) ≠ ⊤ :=
    (isCompact_closedBall 0 1).measure_lt_top.ne
  have e1 : (Subtype.val ⁻¹' Metric.closedBall 0 1 :
      Set {w // ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' w = (((M : ℤ) : ℤ_[p]) : ℚ_[p])}) =
      {y | ‖y.1‖ ≤ 1} := by
    ext w
    change dist (w : Fin (m + 1) → ℚ_[p]) (0 : Fin (m + 1) → ℚ_[p]) ≤ 1 ↔
      ‖(w : Fin (m + 1) → ℚ_[p])‖ ≤ 1
    rw [dist_zero_right]
  have hglue : (Measure.addHaar : Measure ℚ_[p]) (Metric.closedBall 0 1) *
      (((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap').padicSquareBranchAtlasGlue
        p point₂ hpoint₂ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar p (Fin (m + 1)))
        (((M : ℤ) : ℤ_[p]) : ℚ_[p]) (Subtype.val ⁻¹' Metric.closedBall 0 1) =
      ENNReal.ofReal (L.localResidueDensity M p) := by
    rw [e1, ← hdens, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hgt,
      ENNReal.ofReal_toReal hνt, mul_comm]
  have hdet0 : (‖algebraMap ℚ ℚ_[p] (P.blockToAmbientRationalMatrix hx).det‖₊ : ℝ≥0) ≠ 0 := by
    rw [nnnorm_ne_zero_iff]
    exact (map_ne_zero _).mpr (P.blockToAmbientRationalMatrix_det_ne_zero hx)
  rw [hD point hpoint hcover, htr, lastOrbitGaugeRatio_scalarExtension, ← hglue]
  simp only [Rat.padicNormENNRealAtPrime]
  rw [ENNReal.coe_inv hdet0]
  ring

/-- At every horizontal bad place the local shell-weight ratio is one: `num_v = den_v` for `v ∈ B`. -/
theorem localNumerator_eq_localDenominator_of_mem_badPlaces
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (D : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞) (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvB : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)
    (hD : ∀ (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v).1])
      (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
        ℚ_[(primesEquiv v).1]) (point₁ i) ≠ 0),
      {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) w ≠ 0} ⊆
        ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
          ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasRegion (primesEquiv v).1 point₁ hpoint₁ i →
      D v = (‖P.lowerSpace.lastOrbitGaugeRatio
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
          ℚ_[(primesEquiv v).1]‖₊ : ℝ≥0∞) *
        ((Measure.addHaar : Measure ℚ_[(primesEquiv v).1]) (Metric.closedBall 0 1) *
          ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
            ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasGlue (primesEquiv v).1 point₁ hpoint₁
            (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v).1 (Fin (m + 1)))
            (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1])
            (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) ⁻¹'
              Metric.closedBall 0 1)))) :
    Rat.padicNormENNRealAtPrime (P.rationalShellFactor hx) (primesEquiv v) *
        (if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then D v
          else P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v) =
      (if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then 1
          else (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v) *
        ENNReal.ofReal (L.localResidueDensity M (primesEquiv v).1) := by
  rw [if_pos hvB, if_pos hvB, one_mul,
    badPlaceScale_eq_gauge_mul_inv_det_mul_localResidueDensity L P hx M hM D v hD]
  have hn := Rat.padicNormENNRealAtPrime_eq_of_abs_eq
    (P.abs_lastOrbitGaugeRatio_mul_rationalShellFactor hx) (primesEquiv v)
  have hmul : Rat.padicNormENNRealAtPrime (P.lowerSpace.lastOrbitGaugeRatio
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ *
        P.rationalShellFactor hx) (primesEquiv v) =
      Rat.padicNormENNRealAtPrime (P.lowerSpace.lastOrbitGaugeRatio
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ) (primesEquiv v) *
        Rat.padicNormENNRealAtPrime (P.rationalShellFactor hx) (primesEquiv v) := by
    simp only [Rat.padicNormENNRealAtPrime, map_mul, nnnorm_mul, ENNReal.coe_mul]
  have hE0 : Rat.padicNormENNRealAtPrime (P.blockToAmbientRationalMatrix hx).det (primesEquiv v) ≠ 0 := by
    simp only [Rat.padicNormENNRealAtPrime, ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero, map_eq_zero]
    exact P.blockToAmbientRationalMatrix_det_ne_zero hx
  have hEt : Rat.padicNormENNRealAtPrime (P.blockToAmbientRationalMatrix hx).det (primesEquiv v) ≠ ⊤ := by
    simp only [Rat.padicNormENNRealAtPrime]; exact ENNReal.coe_ne_top
  calc Rat.padicNormENNRealAtPrime (P.rationalShellFactor hx) (primesEquiv v) *
        (Rat.padicNormENNRealAtPrime (P.lowerSpace.lastOrbitGaugeRatio
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ) (primesEquiv v) *
        (Rat.padicNormENNRealAtPrime (P.blockToAmbientRationalMatrix hx).det (primesEquiv v))⁻¹ *
        ENNReal.ofReal (L.localResidueDensity M (primesEquiv v).1)) =
      (Rat.padicNormENNRealAtPrime (P.blockToAmbientRationalMatrix hx).det (primesEquiv v) *
        (Rat.padicNormENNRealAtPrime (P.blockToAmbientRationalMatrix hx).det (primesEquiv v))⁻¹) *
        ENNReal.ofReal (L.localResidueDensity M (primesEquiv v).1) := by
        rw [← hn, hmul]; ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hE0 hEt, one_mul]

/-- The shell-weight constant is one: from the localized identity on `T`, if every place of `T` off
`B` is fully good (in particular `p ∤ D_P`) and `D` is the bad-place scale on `B`, then
`Θ_a · τ_V = τ_W · d_Φ(a)`. -/
theorem theta_mul_eq_of_localized (hm : 2 ≤ m)
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (D : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞)
    {T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hoff : ∀ v ∈ T, v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx →
      v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ∧
      v ∉ P.lowerSpace.cliffordSpinCandidateOddUnimodularBadPlaces ∧
      (Rat.HeightOneSpectrum.primesEquiv v).1 ∉
        P.lowerSpace.goodPlaceExceptionalPrimes
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∧
      ¬ (Rat.HeightOneSpectrum.primesEquiv v).1 ∣ P.presentationDenominator hx ∧
      (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ 2 ∧
      ¬ ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℤ) ∣ M)
    (hD : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (_ : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx), D v ≠ 0 ∧ D v ≠ ⊤ ∧
      ∀ (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v).1])
        (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
          ℚ_[(primesEquiv v).1]) (point₁ i) ≠ 0),
        {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) w ≠ 0} ⊆
          ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
            ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasRegion (primesEquiv v).1 point₁ hpoint₁ i →
        D v = (‖P.lowerSpace.lastOrbitGaugeRatio
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
          ℚ_[(primesEquiv v).1]‖₊ : ℝ≥0∞) *
        ((Measure.addHaar : Measure ℚ_[(primesEquiv v).1]) (Metric.closedBall 0 1) *
          ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
            ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasGlue (primesEquiv v).1 point₁ hpoint₁
            (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v).1 (Fin (m + 1)))
            (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1])
            (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) ⁻¹'
              Metric.closedBall 0 1))))
    {Θ τV τW d : ℝ≥0∞}
    (h : Θ * τV * ∏ v ∈ T, ((if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then 1
          else (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v) *
          ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1)) = τW * d * ∏ v ∈ T, (Rat.padicNormENNRealAtPrime (P.rationalShellFactor hx)
            (Rat.HeightOneSpectrum.primesEquiv v) *
          (if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
              (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then D v
            else P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v))) :
    Θ * τV = τW * d := by
  have hnum : ∀ v ∈ T, (Rat.padicNormENNRealAtPrime (P.rationalShellFactor hx)
            (Rat.HeightOneSpectrum.primesEquiv v) *
          (if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
              (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then D v
            else P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v)) = ((if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then 1
          else (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v) *
          ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1)) := by
    intro v hv
    by_cases hvB : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
    · exact localNumerator_eq_localDenominator_of_mem_badPlaces L P hx M hM D v hvB (hD v hvB).2.2
    · obtain ⟨h2, h3, h4, h5, h6, h7⟩ := hoff v hv hvB
      rw [localNumerator_eq_padicNorm_mul_localDenominator L P hx hm M hM D v hvB h2 h3 h4 h5 h6 h7,
        Rat.padicNormENNRealAtPrime_eq_of_abs_eq
          (P.abs_lastOrbitGaugeRatio_mul_rationalShellFactor hx) (primesEquiv v)]
      have h1 := P.norm_algebraMap_det_blockToAmbient_eq_one hx (primesEquiv v).1 h5
      have h1' : Rat.padicNormENNRealAtPrime (P.blockToAmbientRationalMatrix hx).det
          (primesEquiv v) = 1 := by
        simp only [Rat.padicNormENNRealAtPrime]
        rw [show (‖algebraMap ℚ ℚ_[(primesEquiv v).1] (P.blockToAmbientRationalMatrix hx).det‖₊ : ℝ≥0∞)
            = 1 from by
          rw [ENNReal.coe_eq_one]; exact NNReal.eq (by simpa using h1)]
      rw [h1', one_mul]
  have hden : ∀ v ∈ T, ((if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then 1
          else (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v) *
          ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1)) ≠ 0 ∧ ((if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then 1
          else (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v) *
          ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1)) ≠ ⊤ := by
    intro v hv
    by_cases hvB : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
    · rw [if_pos hvB, one_mul]
      refine ⟨fun hδ ↦ (hD v hvB).1 ?_, ENNReal.ofReal_ne_top⟩
      rw [badPlaceScale_eq_gauge_mul_inv_det_mul_localResidueDensity L P hx M hM D v (hD v hvB).2.2,
        hδ, mul_zero]
    · obtain ⟨h2, h3, h4, h5, h6, h7⟩ := hoff v hv hvB
      have hs := lowerBaselineScale_eq_gauge_mul_localResidueDensity_mul_block L P hx hm M hM v
        hvB h2 h3 h4 h5 h6 h7
      rw [if_neg hvB]
      refine ⟨mul_ne_zero ((P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale_ne_zero v) ?_,
        ENNReal.mul_ne_top ((P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale_ne_top v)
          ENNReal.ofReal_ne_top⟩
      intro hδ
      have := P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale_ne_zero v
      rw [hs, hδ, mul_zero, zero_mul] at this
      exact this rfl
  rw [Finset.prod_congr rfl hnum] at h
  have h0 : ∏ v ∈ T, ((if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then 1
          else (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v) *
          ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v hv ↦ (hden v hv).1
  have ht : ∏ v ∈ T, ((if v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx then 1
          else (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v) *
          ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1)) ≠ ⊤ := ENNReal.prod_ne_top fun v hv ↦ (hden v hv).2
  exact (ENNReal.mul_left_inj h0 ht).mp h

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
