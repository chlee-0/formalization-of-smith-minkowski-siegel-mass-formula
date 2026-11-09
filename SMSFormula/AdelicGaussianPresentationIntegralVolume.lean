import SMSFormula.RationalQuadraticIsometryPadicIntegralVolume
import SMSFormula.AdelicGaussianResidueRestrictedOrbitCarrying
import SMSFormula.QuadraticPadicCayleyGoodPlaceHeightOne

/-!
# Ambient and block integral volumes through the presentation

For a supplied anisotropic complement presentation `P` of an ambient rational quadratic space `V`
of rank `m + 1`, the block-to-ambient isometry `E_P : W ⊕ ⟨a⟩ → V` has matrix and inverse
`p`-integral at every prime `p ∤ D_P` (`D_P` the product of all denominators).  There the
integral special-orthogonal volumes satisfy

`vol_V(SO_V(ℤ_p)) = ‖c_P‖_p · vol_{W⊕⟨a⟩}(SO_{W⊕⟨a⟩}(ℤ_p))`,

with `c_P` the rational tangent determinant of `E_P`.  This connects the ambient lattice's
local volumes with the block form, where the good-place ledger evaluates
`vol_{W⊕⟨a⟩}/vol_W = |r|_p · ν(ℤ_p) · δ_p(a)`.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice Matrix
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation

variable {m : ℕ} {V : RationalQuadraticSpaceMatrix (m + 1)} {x : Fin (m + 1) → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)
variable (hx : V.nativeRationalQuadraticForm x ≠ 0)

local instance apivPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

theorem not_dvd_den_blockToAmbientRationalMatrix_of_not_dvd {p : ℕ}
    (hp : ¬ p ∣ P.presentationDenominator hx) (i j : Fin (m + 1)) :
    ¬ p ∣ (P.blockToAmbientRationalMatrix hx i j).den := fun h ↦ hp
  (h.trans ((Finset.dvd_prod_of_mem (fun j ↦ (P.blockToAmbientRationalMatrix hx i j).den)
    (Finset.mem_univ j)).trans ((Finset.dvd_prod_of_mem
      (fun i ↦ ∏ j, (P.blockToAmbientRationalMatrix hx i j).den) (Finset.mem_univ i)).trans
        (dvd_mul_right _ _))))

theorem not_dvd_den_ambientToBlockRationalMatrix_of_not_dvd {p : ℕ}
    (hp : ¬ p ∣ P.presentationDenominator hx) (i j : Fin (m + 1)) :
    ¬ p ∣ (P.ambientToBlockRationalMatrix hx i j).den := fun h ↦ hp
  (h.trans ((Finset.dvd_prod_of_mem (fun j ↦ (P.ambientToBlockRationalMatrix hx i j).den)
    (Finset.mem_univ j)).trans ((Finset.dvd_prod_of_mem
      (fun i ↦ ∏ j, (P.ambientToBlockRationalMatrix hx i j).den) (Finset.mem_univ i)).trans
        (dvd_mul_left _ _))))

/-- Ambient versus block integral volumes off the primes of `D_P`. -/
theorem heightOnePadicSpecialOrthogonalIntegralVolume_ambient_eq_block
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hp : ¬ (Rat.HeightOneSpectrum.primesEquiv v).1 ∣ P.presentationDenominator hx) :
    V.heightOnePadicSpecialOrthogonalIntegralVolume v =
      (‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx) V
            (P.blockToAmbientIsometryEquiv hx))‖₊ : ℝ≥0∞) *
        (P.blockSpace hx).heightOnePadicSpecialOrthogonalIntegralVolume v :=
  heightOnePadicSpecialOrthogonalIntegralVolume_eq_of_rationalIsometry (P.blockSpace hx) V
    (P.blockToAmbientIsometryEquiv hx) v
    (fun i j ↦ PadicInt.map_ratMatrix_mem_subring _
      (P.not_dvd_den_blockToAmbientRationalMatrix_of_not_dvd hx hp) i j)
    (fun i j ↦ PadicInt.map_ratMatrix_mem_subring _
      (P.not_dvd_den_ambientToBlockRationalMatrix_of_not_dvd hx hp) i j)

local instance apivPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance apivPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The ambient-over-lower local volume ratio at a good prime off `D_P`:
`vol_V(SO_V(ℤ_p)) / vol_W(SO_W(ℤ_p)) = ‖c_P‖_p · (‖r‖_p · ν(ℤ_p)) · glue_a(X_a(ℤ_p))`, the last two
factors being the good-place ledger of the block form `W ⊕ ⟨a⟩`. -/
theorem heightOnePadicSpecialOrthogonalIntegralVolume_ambient_div_lower_eq (hm : 1 ≤ m)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hp : ¬ (Rat.HeightOneSpectrum.primesEquiv v).1 ∣ P.presentationDenominator hx)
    (hgood : (Rat.HeightOneSpectrum.primesEquiv v).1 ∉
      P.lowerSpace.goodPlaceExceptionalPrimes (V.nativeRationalQuadraticForm x) hx)
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
    V.heightOnePadicSpecialOrthogonalIntegralVolume v /
        P.lowerSpace.heightOnePadicSpecialOrthogonalIntegralVolume v =
      (‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (rationalIsometrySkewAdjointDetScalar (P.blockSpace hx) V
            (P.blockToAmbientIsometryEquiv hx))‖₊ : ℝ≥0∞) *
        (((‖P.lowerSpace.lastOrbitGaugeRatio (V.nativeRationalQuadraticForm x) hx
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]‖₊ : ℝ≥0∞) * ν (Metric.closedBall 0 1)) *
          ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).padicSquareBranchAtlasGlue
            (Rat.HeightOneSpectrum.primesEquiv v).1 point hpoint tH ν
            (Padic.unitHaar (Rat.HeightOneSpectrum.primesEquiv v).1 (Fin (m + 1)))
            (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
              (V.nativeRationalQuadraticForm x)) {y | ‖y.1‖ ≤ 1}) := by
  rw [P.heightOnePadicSpecialOrthogonalIntegralVolume_ambient_eq_block hx v hp, mul_div_assoc]
  congr 1
  exact P.lowerSpace.heightOneIntegralVolume_div_eq_ledger_of_notMem
    (V.nativeRationalQuadraticForm x) hx hm v hgood ν point hpoint tH hcover

end RationalQuadraticSpaceMatrix.AnisotropicComplementPresentation
