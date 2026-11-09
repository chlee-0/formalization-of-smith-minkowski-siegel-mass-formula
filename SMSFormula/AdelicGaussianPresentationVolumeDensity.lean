import SMSFormula.AdelicGaussianPresentationUnitGlue
import SMSFormula.AdelicGaussianPresentationIntegralVolume
import SMSFormula.AdelicGaussianLocalRatioBadPlace
import SMSFormula.QuadraticPadicSquareBranchAtlasGlueScalar

/-!
# The per-prime volume ratio is the local density

At a prime `q` with `q ∤ D_P`, `q` odd, `q ∤ M` and outside the good-place exceptional set,
the ambient-over-lower integral volume ratio of the supplied presentation is

`vol_A(SO_A(ℤ_q)) / vol_W(SO_W(ℤ_q)) = ‖c_P‖_q · (‖r‖_q · δ_q(M))`,

where `δ_q(M)` is the ambient lattice's local residue density (the Euler factor of the orbit
Riesz ratio), `c_P` the tangent determinant of the presentation and `r` the orbit gauge.
The chain is: good-place ledger (block form) → block glue = lattice glue of the integral points
(unit-cube Haar preserved by the integral presentation) → lattice glue · ν(ℤ_q) = δ_q(M) (old
level-one count).  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Metric PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

local instance vdPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance vdPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The glue mass of the integral points is finite (no representative needed). -/
theorem padicSquareBranchAtlasGlue_integral_ne_top {N : ℕ} {p : ℕ} [Fact p.Prime]
    (G : Matrix (Fin N) (Fin N) ℚ_[p]) (point : ℕ → Fin N → ℚ_[p])
    (hpoint : ∀ i, G.toQuadraticMap' (point i) ≠ 0)
    (tH : ∀ i, Measure ((G.toQuadraticMap').anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin N → ℚ_[p]))
    [νv.IsAddHaarMeasure]
    (hcover : {w | G.toQuadraticMap' w ≠ 0} ⊆
      ⋃ i, (G.toQuadraticMap').padicSquareBranchAtlasRegion p point hpoint i)
    {value : ℚ_[p]} (hv0 : value ≠ 0) :
    (G.toQuadraticMap').padicSquareBranchAtlasGlue p point hpoint tH νs νv value
        {x | ‖x.val‖ ≤ 1} ≠ ⊤ := by
  obtain ⟨B₀, hB₀o, hMB₀, hB₀⟩ :=
    (G.toQuadraticMap').exists_isOpen_padicSquareBranchAtlasGlue_integralPoints_mul p
      point hpoint tH νs νv hcover value hv0
  set B := B₀ ∩ ball value 1
  have hBo : IsOpen B := hB₀o.inter isOpen_ball
  have hB := hB₀ B Set.inter_subset_left hBo.measurableSet
  have hνB0 : νs B ≠ 0 := hBo.measure_ne_zero νs ⟨value, hMB₀, mem_ball_self one_pos⟩
  have hball : {vector : Fin N → ℚ_[p] | ‖vector‖ ≤ 1} = closedBall 0 1 := by
    ext w; simp [mem_closedBall, dist_zero_right]
  have hLt : νv ({vector : Fin N → ℚ_[p] | ‖vector‖ ≤ 1} ∩ G.toQuadraticMap' ⁻¹' B) ≠ ⊤ := by
    refine ((measure_mono Set.inter_subset_left).trans_lt ?_).ne
    rw [hball]
    exact (isCompact_closedBall 0 1).measure_lt_top
  exact fun ht ↦ hLt (by rw [hB, ht, ENNReal.top_mul hνB0])

variable {m : ℕ} (L : PositiveDefiniteIntegralLattice (m + 1)) {x : Fin (m + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m)
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance vdPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The per-prime volume ratio is the local density at a good odd prime off `D_P · M`. -/
theorem heightOneIntegralVolume_ambient_div_lower_eq_localResidueDensity (hm : 1 ≤ m)
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hp : ¬ (Rat.HeightOneSpectrum.primesEquiv v).1 ∣ P.presentationDenominator hx)
    (hgood : (Rat.HeightOneSpectrum.primesEquiv v).1 ∉
      P.lowerSpace.goodPlaceExceptionalPrimes
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)
    (hp2 : (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ 2)
    (hpM : ¬ ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℤ) ∣ M)
    (ν : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) [ν.IsAddHaarMeasure]
    (point : ℕ → Fin (m + 1) → ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hpoint : ∀ i, (P.blockSpace hx).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (point i) ≠ 0)
    (tH : ∀ i, Measure (((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (P.blockSpace hx).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] y ≠ 0} ⊆
      ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).padicSquareBranchAtlasRegion
          (Rat.HeightOneSpectrum.primesEquiv v).1 point hpoint i) :
    L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume v /
        P.lowerSpace.heightOnePadicSpecialOrthogonalIntegralVolume v =
      (‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx) L.rationalQuadraticSpaceMatrix
            (P.blockToAmbientIsometryEquiv hx))‖₊ : ℝ≥0∞) *
        ((‖P.lowerSpace.lastOrbitGaugeRatio
              (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]‖₊ : ℝ≥0∞) *
          ENNReal.ofReal (L.localResidueDensity M (Rat.HeightOneSpectrum.primesEquiv v).1)) := by
  set p := (Rat.HeightOneSpectrum.primesEquiv v).1
  haveI : Fact (Nat.Prime p) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hM0 : M ≠ 0 := by
    rintro rfl; exact hx (by rw [hM]; simp)
  rw [P.heightOnePadicSpecialOrthogonalIntegralVolume_ambient_div_lower_eq hx hm v hp hgood ν point
    hpoint tH hcover, mul_assoc (‖P.lowerSpace.lastOrbitGaugeRatio _ hx _‖₊ : ℝ≥0∞)]
  congr 2
  -- the lattice atlas
  set G := (L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])
  have hvalue : algebraMap ℚ ℚ_[p] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) ≠ 0 :=
    (map_ne_zero _).mpr hx
  have hform : ∃ w, G.toQuadraticMap' w ≠ 0 := by
    refine ⟨P.blockToAmbientPadicContinuousLinearEquiv hx p lastCoordinateVector, ?_⟩
    rw [latticeGram_blockToAmbient L P hx p]
    have hsh := P.lowerSpace.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[p]
    change (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[p] lastCoordinateVector =
      algebraMap ℚ ℚ_[p] _ at hsh
    rw [hsh]; exact hvalue
  obtain ⟨point₂, hpoint₂, hcover₂⟩ := QuadraticMap.exists_padicSquareBranchAtlas_cover p
    (G.toQuadraticMap') hform
  have hbl := blockGlue_integralPoints_eq_latticeGlue L P hx p hp point hpoint tH hcover point₂
    hpoint₂ (fun _ ↦ Measure.addHaar) hcover₂ ν hvalue
  have e1 : ({y | ‖y.1‖ ≤ 1} : Set {w // (P.blockSpace hx).commutativeScalarExtensionQuadraticForm
      ℚ_[p] w = algebraMap ℚ ℚ_[p] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)}) =
      Subtype.val ⁻¹' closedBall 0 1 := by
    ext w; simp [mem_closedBall, dist_zero_right]
  rw [e1, hbl]
  have key : ∀ value : ℚ_[p], (hv : value ≠ 0) → value = (((M : ℤ) : ℤ_[p]) : ℚ_[p]) →
      ν (closedBall 0 1) * (G.toQuadraticMap').padicSquareBranchAtlasGlue p point₂ hpoint₂
        (fun _ ↦ Measure.addHaar) ν (Padic.unitHaar p (Fin (m + 1))) value
          (Subtype.val ⁻¹' closedBall 0 1) =
        ENNReal.ofReal (L.localResidueDensity M p) := by
    rintro value hv rfl
    have e2 : (Subtype.val ⁻¹' closedBall 0 1 : Set {w // G.toQuadraticMap' w =
        (((M : ℤ) : ℤ_[p]) : ℚ_[p])}) = {y | ‖y.1‖ ≤ 1} := by
      ext w
      change dist (w : Fin (m + 1) → ℚ_[p]) (0 : Fin (m + 1) → ℚ_[p]) ≤ 1 ↔
        ‖(w : Fin (m + 1) → ℚ_[p])‖ ≤ 1
      rw [dist_zero_right]
    have hdens := latticeGlue_toReal_mul_eq_localResidueDensity L p hp2 hM0 hpM point₂ hpoint₂
      (fun _ ↦ Measure.addHaar) hcover₂ ν
    have hgt := padicSquareBranchAtlasGlue_integral_ne_top G point₂ hpoint₂
      (fun _ ↦ Measure.addHaar) ν (Padic.unitHaar p (Fin (m + 1))) hcover₂ hv
    have hνt : ν (closedBall 0 1) ≠ ⊤ := (isCompact_closedBall 0 1).measure_lt_top.ne
    rw [e2, ← hdens, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hgt,
      ENNReal.ofReal_toReal hνt, mul_comm]
  exact key _ hvalue ((congrArg (algebraMap ℚ ℚ_[p]) hM).trans
    (padicIntCast_intCast_eq_algebraMap p M).symm)

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
