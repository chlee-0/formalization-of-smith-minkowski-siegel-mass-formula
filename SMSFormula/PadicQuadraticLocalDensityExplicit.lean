import SMSFormula.PadicQuadraticLocalDensityResidueCount
import SMSFormula.RationalCliffordGeneralSpinHorizontalBaselineLedger

/-! The explicit good-place local density. For `p` odd, a symmetric Gram matrix
`F` over `ℤ_p` with unit determinant, a unit value `a` and supplied Haars
`ν` on `ℚ_p`, `ν_vec` on `ℚ_p^N`, the normalized local density

`δ_p(a) = λ(X_a(ℤ_p)) · ν(ℤ_p) / ν_vec(ℤ_p^N)`

(real-valued, `λ` the atlas-glued fiber measure) is

* `N = 2m + 1`: `δ_p(a) = 1 + χ((-1)^m det F̄ · ā) / p^m`;
* `N = 2m + 2`: `δ_p(a) = 1 − χ((-1)^{m+1} det F̄) / p^{m+1}`.

At primes outside the `goodPlaceExceptionalPrimes` of `W ⊕ ⟨a⟩` the
symmetric rational Gram matrix has an integral lift with unit determinant, so
the formula applies to the scalar-extension form with the repository unit
Haar `Padic.unitHaar` (mass one on `ℤ_p^N`). Nothing is chosen: the lift is the
matrix itself, and the atlas and `ν` are supplied. -/
noncomputable section
open MeasureTheory Set Metric Matrix Finset
open scoped ENNReal

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

local instance ldePadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance ldePadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

local instance ldeFactPrimePowOne : Fact (p ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩

theorem measure_closedBall_one_toReal_pos {N : ℕ} (ν : Measure (Fin N → ℚ_[p]))
    [ν.IsAddHaarMeasure] : 0 < (ν (closedBall 0 1)).toReal := by
  refine ENNReal.toReal_pos ?_ (isCompact_closedBall 0 1).measure_lt_top.ne
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).measure_ne_zero ν
    ⟨0, mem_closedBall_self zero_le_one⟩

theorem scalar_measure_closedBall_one_toReal_pos (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure] :
    0 < (ν (closedBall 0 1)).toReal := by
  refine ENNReal.toReal_pos ?_ (isCompact_closedBall 0 1).measure_lt_top.ne
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).measure_ne_zero ν
    ⟨0, mem_closedBall_self zero_le_one⟩

/-- Real-valued level one: `δ_p(a) = #R_1 / p^n` in dimension `n + 1`, for any
form `Q` equal to that of `F` and any value `t` equal to `a`. -/
theorem localDensity_toReal_eq_card_div (hp : p ≠ 2) {n : ℕ}
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p])
    (Q : QuadraticForm ℚ_[p] (Fin (n + 1) → ℚ_[p]))
    (hQ : Q = (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap')
    (a : ℤ_[p]) (ha : ‖(a : ℚ_[p])‖ = 1) (t : ℚ_[p]) (ht : t = a)
    (point : ℕ → Fin (n + 1) → ℚ_[p]) (hpoint : ∀ i, Q (point i) ≠ 0)
    (tH : ∀ i, Measure (Q.anisotropicOrthogonal (point i))) [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin (n + 1) → ℚ_[p]))
    [νv.IsAddHaarMeasure]
    (hcover : {v | Q v ≠ 0} ⊆ ⋃ i, Q.padicSquareBranchAtlasRegion p point hpoint i) :
    (Q.padicSquareBranchAtlasGlue p point hpoint tH νs νv t {x | ‖x.1‖ ≤ 1}).toReal *
        (νs (closedBall 0 1)).toReal / (νv (closedBall 0 1)).toReal =
      ((univ.filter (fun r : Fin (n + 1) → ZMod (p ^ 1) ↦
        r ⬝ᵥ (F.map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card : ℝ) / (p : ℝ) ^ n := by
  subst hQ
  subst ht
  have h := congrArg ENNReal.toReal
    (card_levelOne_eq_localDensity hp F a ha point hpoint tH νs νv hcover)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at h
  have hV := measure_closedBall_one_toReal_pos νv
  have hp0 : (0 : ℝ) < (p : ℝ) ^ n := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) n
  rw [div_eq_div_iff hV.ne' hp0.ne']
  linarith

/-- Odd rank `N = 2m + 1`: `δ_p(a) = 1 + χ((-1)^m det F̄ · ā) / p^m`. -/
theorem localDensity_toReal_odd (hp : p ≠ 2) (m : ℕ)
    (F : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ_[p]) (hF : F.IsSymm)
    (hdet : ‖((F.det : ℤ_[p]) : ℚ_[p])‖ = 1)
    (Q : QuadraticForm ℚ_[p] (Fin (2 * m + 1) → ℚ_[p]))
    (hQ : Q = (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap')
    (a : ℤ_[p]) (ha : ‖(a : ℚ_[p])‖ = 1) (t : ℚ_[p]) (ht : t = a)
    (point : ℕ → Fin (2 * m + 1) → ℚ_[p]) (hpoint : ∀ i, Q (point i) ≠ 0)
    (tH : ∀ i, Measure (Q.anisotropicOrthogonal (point i))) [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin (2 * m + 1) → ℚ_[p]))
    [νv.IsAddHaarMeasure]
    (hcover : {v | Q v ≠ 0} ⊆ ⋃ i, Q.padicSquareBranchAtlasRegion p point hpoint i) :
    (Q.padicSquareBranchAtlasGlue p point hpoint tH νs νv t {x | ‖x.1‖ ≤ 1}).toReal *
        (νs (closedBall 0 1)).toReal / (νv (closedBall 0 1)).toReal =
      1 + (quadraticChar (ZMod (p ^ 1)) ((-1) ^ m * toZModPow 1 F.det * toZModPow 1 a) : ℝ) /
        (p : ℝ) ^ m := by
  rw [localDensity_toReal_eq_card_div hp F Q hQ a ha t ht point hpoint tH νs νv hcover]
  have hc := card_levelOne_odd hp m F hF hdet a
  rw [show ((univ.filter (fun r : Fin (2 * m + 1) → ZMod (p ^ 1) ↦
      r ⬝ᵥ (F.map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card : ℝ) =
      (((univ.filter (fun r : Fin (2 * m + 1) → ZMod (p ^ 1) ↦
      r ⬝ᵥ (F.map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card : ℤ) : ℝ) from rfl, hc]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  push_cast
  field_simp
  ring

/-- Even rank `N = 2m + 2`: `δ_p(a) = 1 − χ((-1)^{m+1} det F̄) / p^{m+1}`. -/
theorem localDensity_toReal_even (hp : p ≠ 2) (m : ℕ)
    (F : Matrix (Fin (2 * m + 1 + 1)) (Fin (2 * m + 1 + 1)) ℤ_[p]) (hF : F.IsSymm)
    (hdet : ‖((F.det : ℤ_[p]) : ℚ_[p])‖ = 1)
    (Q : QuadraticForm ℚ_[p] (Fin (2 * m + 1 + 1) → ℚ_[p]))
    (hQ : Q = (F.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap')
    (a : ℤ_[p]) (ha : ‖(a : ℚ_[p])‖ = 1) (t : ℚ_[p]) (ht : t = a)
    (point : ℕ → Fin (2 * m + 1 + 1) → ℚ_[p]) (hpoint : ∀ i, Q (point i) ≠ 0)
    (tH : ∀ i, Measure (Q.anisotropicOrthogonal (point i))) [∀ i, (tH i).IsAddHaarMeasure]
    (νs : Measure ℚ_[p]) [νs.IsAddHaarMeasure] (νv : Measure (Fin (2 * m + 1 + 1) → ℚ_[p]))
    [νv.IsAddHaarMeasure]
    (hcover : {v | Q v ≠ 0} ⊆ ⋃ i, Q.padicSquareBranchAtlasRegion p point hpoint i) :
    (Q.padicSquareBranchAtlasGlue p point hpoint tH νs νv t {x | ‖x.1‖ ≤ 1}).toReal *
        (νs (closedBall 0 1)).toReal / (νv (closedBall 0 1)).toReal =
      1 - (quadraticChar (ZMod (p ^ 1)) ((-1) ^ (m + 1) * toZModPow 1 F.det) : ℝ) /
        (p : ℝ) ^ (m + 1) := by
  rw [localDensity_toReal_eq_card_div hp F Q hQ a ha t ht point hpoint tH νs νv hcover]
  have hc := card_levelOne_even hp m F hF hdet a ha
  rw [show ((univ.filter (fun r : Fin (2 * m + 1 + 1) → ZMod (p ^ 1) ↦
      r ⬝ᵥ (F.map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card : ℝ) =
      (((univ.filter (fun r : Fin (2 * m + 1 + 1) → ZMod (p ^ 1) ↦
      r ⬝ᵥ (F.map (toZModPow 1)) *ᵥ r = toZModPow 1 a)).card : ℤ) : ℝ) from rfl, hc]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  push_cast
  field_simp
  ring

end PadicInt

namespace RationalQuadraticSpaceMatrix

local instance ldeGoodPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] :=
  borel _
local instance ldeGoodPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

section GoodPlace

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
variable (p : ℕ) [Fact p.Prime] (hp : p ∉ W.goodPlaceExceptionalPrimes a ha)

/-- The Gram matrix of `W ⊕ ⟨a⟩`, viewed over `ℤ_p` at a good prime. -/
def goodPlaceIntegralGram : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p] :=
  fun i j ↦ ⟨(W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]) i j,
    (W.goodPlace_of_notMem_exceptionalPrimes a ha p hp).2.1 i j⟩

/-- The value `a`, viewed in `ℤ_p` at a good prime. -/
def goodPlaceIntegralValue : ℤ_[p] :=
  ⟨algebraMap ℚ ℚ_[p] a, (W.goodPlace_of_notMem_exceptionalPrimes a ha p hp).2.2.2.le⟩

theorem map_goodPlaceIntegralGram :
    (W.goodPlaceIntegralGram a ha p hp).map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) =
      (W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]) := by
  ext i j
  rfl

theorem goodPlaceIntegralGram_isSymm : (W.goodPlaceIntegralGram a ha p hp).IsSymm :=
  Matrix.IsSymm.ext fun i j ↦ Subtype.ext
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionFormMatrix_isSymm ℚ_[p]).apply i j)

theorem norm_det_goodPlaceIntegralGram :
    ‖(((W.goodPlaceIntegralGram a ha p hp).det : ℤ_[p]) : ℚ_[p])‖ = 1 := by
  have h : (((W.goodPlaceIntegralGram a ha p hp).det : ℤ_[p]) : ℚ_[p]) =
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])).det := by
    rw [← map_goodPlaceIntegralGram,
      show (((W.goodPlaceIntegralGram a ha p hp).det : ℤ_[p]) : ℚ_[p]) =
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) (W.goodPlaceIntegralGram a ha p hp).det from rfl,
      RingHom.map_det, RingHom.mapMatrix_apply]
  rw [h]
  exact (W.goodPlace_of_notMem_exceptionalPrimes a ha p hp).2.2.1

theorem norm_goodPlaceIntegralValue :
    ‖((W.goodPlaceIntegralValue a ha p hp : ℤ_[p]) : ℚ_[p])‖ = 1 :=
  (W.goodPlace_of_notMem_exceptionalPrimes a ha p hp).2.2.2

theorem commutativeScalarExtensionQuadraticForm_eq_goodPlaceIntegralGram :
    (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] =
      ((W.goodPlaceIntegralGram a ha p hp).map
        (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])).toQuadraticMap' := by
  rw [map_goodPlaceIntegralGram]
  rfl

end GoodPlace

local instance ldeGoodPadicFactPrimePowOne (p : ℕ) [Fact p.Prime] : Fact (p ^ 1).Prime :=
  ⟨by rw [pow_one]; exact Fact.out⟩

/-- Explicit good-place density, odd rank `2m + 1`: outside the exceptional
primes, with the repository unit Haar on `ℚ_p^{2m+1}` and a supplied `ν`,
`λ(X_a(ℤ_p)) ν(ℤ_p) = 1 + χ((-1)^m det F̄ · ā) / p^m`. -/
theorem goodPlace_localDensity_toReal_odd {m : ℕ} (W : RationalQuadraticSpaceMatrix (2 * m))
    (a : ℚ) (ha : a ≠ 0) (p : ℕ) [Fact p.Prime] (hp : p ∉ W.goodPlaceExceptionalPrimes a ha)
    (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure] (point : ℕ → Fin (2 * m + 1) → ℚ_[p])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[p] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[p]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[p] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[p]).padicSquareBranchAtlasRegion p point hpoint i) :
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
          ℚ_[p]).padicSquareBranchAtlasGlue p point hpoint tH ν
          (Padic.unitHaar p (Fin (2 * m + 1))) (algebraMap ℚ ℚ_[p] a) {y | ‖y.1‖ ≤ 1}).toReal *
        (ν (closedBall 0 1)).toReal =
      1 + (quadraticChar (ZMod (p ^ 1)) ((-1) ^ m *
          PadicInt.toZModPow 1 (W.goodPlaceIntegralGram a ha p hp).det *
          PadicInt.toZModPow 1 (W.goodPlaceIntegralValue a ha p hp)) : ℝ) / (p : ℝ) ^ m := by
  have h := PadicInt.localDensity_toReal_odd
    (W.goodPlace_of_notMem_exceptionalPrimes a ha p hp).1 m
    (W.goodPlaceIntegralGram a ha p hp) (W.goodPlaceIntegralGram_isSymm a ha p hp)
    (W.norm_det_goodPlaceIntegralGram a ha p hp) _
    (W.commutativeScalarExtensionQuadraticForm_eq_goodPlaceIntegralGram a ha p hp)
    (W.goodPlaceIntegralValue a ha p hp) (W.norm_goodPlaceIntegralValue a ha p hp) _ rfl
    point hpoint tH ν (Padic.unitHaar p (Fin (2 * m + 1))) hcover
  rwa [Padic.unitHaar_unitCube, ENNReal.toReal_one, div_one] at h

/-- Explicit good-place density, even rank `2m + 2`:
`λ(X_a(ℤ_p)) ν(ℤ_p) = 1 − χ((-1)^{m+1} det F̄) / p^{m+1}`. -/
theorem goodPlace_localDensity_toReal_even {m : ℕ} (W : RationalQuadraticSpaceMatrix (2 * m + 1))
    (a : ℚ) (ha : a ≠ 0) (p : ℕ) [Fact p.Prime] (hp : p ∉ W.goodPlaceExceptionalPrimes a ha)
    (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure] (point : ℕ → Fin (2 * m + 1 + 1) → ℚ_[p])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[p] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[p]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[p] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[p]).padicSquareBranchAtlasRegion p point hpoint i) :
    (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
          ℚ_[p]).padicSquareBranchAtlasGlue p point hpoint tH ν
          (Padic.unitHaar p (Fin (2 * m + 1 + 1))) (algebraMap ℚ ℚ_[p] a) {y | ‖y.1‖ ≤ 1}).toReal *
        (ν (closedBall 0 1)).toReal =
      1 - (quadraticChar (ZMod (p ^ 1)) ((-1) ^ (m + 1) *
          PadicInt.toZModPow 1 (W.goodPlaceIntegralGram a ha p hp).det) : ℝ) /
        (p : ℝ) ^ (m + 1) := by
  have h := PadicInt.localDensity_toReal_even
    (W.goodPlace_of_notMem_exceptionalPrimes a ha p hp).1 m
    (W.goodPlaceIntegralGram a ha p hp) (W.goodPlaceIntegralGram_isSymm a ha p hp)
    (W.norm_det_goodPlaceIntegralGram a ha p hp) _
    (W.commutativeScalarExtensionQuadraticForm_eq_goodPlaceIntegralGram a ha p hp)
    (W.goodPlaceIntegralValue a ha p hp) (W.norm_goodPlaceIntegralValue a ha p hp) _ rfl
    point hpoint tH ν (Padic.unitHaar p (Fin (2 * m + 1 + 1))) hcover
  rwa [Padic.unitHaar_unitCube, ENNReal.toReal_one, div_one] at h

local instance ldeGoodPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The explicit value multiplier, odd rank: at a good place `v` outside both
original baselines, the odd-unimodular bad sets and the exceptional primes,
`u_v = |r|_v · (1 + χ((-1)^m det F̄ · ā) / p^m)`. -/
theorem lastExtensionValueMultiplier_toReal_odd {m : ℕ} (W : RationalQuadraticSpaceMatrix (2 * m))
    (a : ℚ) (ha : a ≠ 0) (hn : 2 ≤ 2 * m) (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvExt : v ∉ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hvW : v ∉ W.cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hvOddExt : v ∉ (W.nonisotropicLastExtension a ha).cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvOddW : v ∉ W.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hp : (Rat.HeightOneSpectrum.primesEquiv v).1 ∉ W.goodPlaceExceptionalPrimes a ha)
    (ν : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) [ν.IsAddHaarMeasure]
    (point : ℕ → Fin (2 * m + 1) → ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).padicSquareBranchAtlasRegion
          (Rat.HeightOneSpectrum.primesEquiv v).1 point hpoint i) :
    (W.lastExtensionValueMultiplier a ha v).toReal =
      ‖W.lastOrbitGaugeRatio a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]‖ *
        (1 + (quadraticChar (ZMod ((Rat.HeightOneSpectrum.primesEquiv v).1 ^ 1)) ((-1) ^ m *
          PadicInt.toZModPow 1 (W.goodPlaceIntegralGram a ha _ hp).det *
          PadicInt.toZModPow 1 (W.goodPlaceIntegralValue a ha _ hp)) : ℝ) /
          ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℝ) ^ m) := by
  rw [W.lastExtensionValueMultiplier_eq_ledger_of_notMem a ha hn v hvExt hvW hvOddExt hvOddW hp ν
    point hpoint tH hcover, ← W.goodPlace_localDensity_toReal_odd a ha _ hp ν point hpoint tH hcover]
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, coe_nnnorm]
  ring

/-- The explicit value multiplier, even rank:
`u_v = |r|_v · (1 − χ((-1)^{m+1} det F̄) / p^{m+1})`. -/
theorem lastExtensionValueMultiplier_toReal_even {m : ℕ}
    (W : RationalQuadraticSpaceMatrix (2 * m + 1))
    (a : ℚ) (ha : a ≠ 0) (hn : 2 ≤ 2 * m + 1) (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvExt : v ∉ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hvW : v ∉ W.cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hvOddExt : v ∉ (W.nonisotropicLastExtension a ha).cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvOddW : v ∉ W.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hp : (Rat.HeightOneSpectrum.primesEquiv v).1 ∉ W.goodPlaceExceptionalPrimes a ha)
    (ν : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) [ν.IsAddHaarMeasure]
    (point : ℕ → Fin (2 * m + 1 + 1) → ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).padicSquareBranchAtlasRegion
          (Rat.HeightOneSpectrum.primesEquiv v).1 point hpoint i) :
    (W.lastExtensionValueMultiplier a ha v).toReal =
      ‖W.lastOrbitGaugeRatio a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]‖ *
        (1 - (quadraticChar (ZMod ((Rat.HeightOneSpectrum.primesEquiv v).1 ^ 1)) ((-1) ^ (m + 1) *
          PadicInt.toZModPow 1 (W.goodPlaceIntegralGram a ha _ hp).det) : ℝ) /
          ((Rat.HeightOneSpectrum.primesEquiv v).1 : ℝ) ^ (m + 1)) := by
  rw [W.lastExtensionValueMultiplier_eq_ledger_of_notMem a ha hn v hvExt hvW hvOddExt hvOddW hp ν
    point hpoint tH hcover, ← W.goodPlace_localDensity_toReal_even a ha _ hp ν point hpoint tH hcover]
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, coe_nnnorm]
  ring

end RationalQuadraticSpaceMatrix
