import SMSFormula.RationalCliffordGeneralSpinHorizontalGoodPlaceLedger
import SMSFormula.RationalCliffordGeneralSpinHorizontalRestrictedPrincipalBlockCoherence

/-! The good-place ledger in the baseline weights. The horizontal baseline
of `V` is `B_V = cliffordGeneralSpinHorizontalIntegralBadPlaces`, and the
block weight `w_V(S) = cliffordGeneralSpinHorizontalRestrictedBlockWeight V S`
is the product over the new places `S \ B_V` of the inverse integral GSpin
volumes. With the per-place scale `s_V(v) = 1` on `B_V` and `v^G_{V,v}⁻¹` off it:

* `w_V(S) = ∏_{v ∈ S} s_V(v)`;
* `u_v := s_W(v) / s_V(v)` gives `∏_{v ∈ S} u_v = w_W(S) / w_V(S)`;
* at every place outside both baselines, the odd-unimodular bad sets and
  the explicit exceptional primes, `u_v = κ_v · d_v(a)` with
  `κ_v = |r| ν(ℤ_p)` and `d_v(a) = λ(X_a(ℤ_p))`.

The baselines are the original ones; no new baseline or normalization is
chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace RationalQuadraticSpaceMatrix

local instance baselineLedgerPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance baselineLedgerDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

section Scale

variable {m : ℕ} (V : RationalQuadraticSpaceMatrix m)

/-- The baseline scale `s_V(v)`: one on the original baseline, the inverse
integral GSpin volume elsewhere. -/
def cliffordGeneralSpinHorizontalBaselineScale (v : IsDedekindDomain.HeightOneSpectrum ℤ) : ℝ≥0∞ :=
  if v ∈ V.cliffordGeneralSpinHorizontalIntegralBadPlaces then 1
  else (V.padicCliffordGeneralSpinHorizontalIntegralVolume v)⁻¹

theorem cliffordGeneralSpinHorizontalBaselineScale_ne_top (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.cliffordGeneralSpinHorizontalBaselineScale v ≠ ∞ := by
  unfold cliffordGeneralSpinHorizontalBaselineScale
  split_ifs with hv
  · exact ENNReal.one_ne_top
  · exact ENNReal.inv_ne_top.mpr (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_zero ∅
      ⟨v, by simpa using hv⟩)

theorem cliffordGeneralSpinHorizontalBaselineScale_ne_zero (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.cliffordGeneralSpinHorizontalBaselineScale v ≠ 0 := by
  unfold cliffordGeneralSpinHorizontalBaselineScale
  split_ifs
  · exact one_ne_zero
  · exact ENNReal.inv_ne_zero.mpr (V.padicCliffordGeneralSpinHorizontalIntegralVolume_ne_top v)

/-- The block weight is the product of baseline scales. -/
theorem cliffordGeneralSpinHorizontalRestrictedBlockWeight_eq_prod_scale
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight S =
      ∏ v ∈ S, V.cliffordGeneralSpinHorizontalBaselineScale v := by
  unfold cliffordGeneralSpinHorizontalRestrictedBlockWeight
  change ∏ v ∈ V.cliffordGeneralSpinHorizontalExceptionalPlaces S \
      V.cliffordGeneralSpinHorizontalExceptionalPlaces ∅,
      (V.padicCliffordGeneralSpinHorizontalIntegralVolume v)⁻¹ = _
  have hset : V.cliffordGeneralSpinHorizontalExceptionalPlaces S \
      V.cliffordGeneralSpinHorizontalExceptionalPlaces ∅ =
      S.filter (fun v ↦ v ∉ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
    ext v
    simp only [cliffordGeneralSpinHorizontalExceptionalPlaces, Finset.mem_sdiff, Finset.mem_union,
      Finset.empty_union, Finset.mem_filter]
    tauto
  rw [hset, Finset.prod_filter]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  unfold cliffordGeneralSpinHorizontalBaselineScale
  split_ifs <;> simp_all

end Scale

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- The value multiplier `u_v = s_W(v) / s_V(v)` for `V = W ⊕ ⟨a⟩`. -/
def lastExtensionValueMultiplier (v : IsDedekindDomain.HeightOneSpectrum ℤ) : ℝ≥0∞ :=
  W.cliffordGeneralSpinHorizontalBaselineScale v /
    (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v

/-- Block product: `∏_{v ∈ S} u_v = w_W(S) / w_V(S)`. -/
theorem prod_lastExtensionValueMultiplier (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ∏ v ∈ S, W.lastExtensionValueMultiplier a ha v =
      W.cliffordGeneralSpinHorizontalRestrictedBlockWeight S /
        (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalRestrictedBlockWeight S := by
  rw [cliffordGeneralSpinHorizontalRestrictedBlockWeight_eq_prod_scale,
    cliffordGeneralSpinHorizontalRestrictedBlockWeight_eq_prod_scale]
  simp only [lastExtensionValueMultiplier, div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
  intro i _ j _ _
  exact Or.inr ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale_ne_top j)

section Ledger

local instance baselineLedgerPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] :=
  borel _
local instance baselineLedgerPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- Good-place ledger in baseline weights: outside both original
baselines, the odd-unimodular bad sets and the exceptional primes,
`u_v = κ_v · d_v(a)` with `κ_v = |r| ν(ℤ_p)` and `d_v(a) = λ(X_a(ℤ_p))`. -/
theorem lastExtensionValueMultiplier_eq_ledger_of_notMem (hn : 2 ≤ n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvExt : v ∉ (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hvW : v ∉ W.cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hvOddExt : v ∉ (W.nonisotropicLastExtension a ha).cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvOddW : v ∉ W.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hp : (Rat.HeightOneSpectrum.primesEquiv v).1 ∉ W.goodPlaceExceptionalPrimes a ha)
    (ν : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) [ν.IsAddHaarMeasure]
    (point : ℕ → Fin (n+1) → ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
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
    W.lastExtensionValueMultiplier a ha v =
      ((‖W.lastOrbitGaugeRatio a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]‖₊ : ℝ≥0∞) *
          ν (closedBall 0 1)) *
        ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]).padicSquareBranchAtlasGlue
          (Rat.HeightOneSpectrum.primesEquiv v).1 point hpoint tH ν
          (Padic.unitHaar (Rat.HeightOneSpectrum.primesEquiv v).1 (Fin (n+1)))
          (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] a) {y | ‖y.1‖ ≤ 1} := by
  rw [← W.gspinHorizontalIntegralVolume_div_eq_ledger_of_notMem a ha hn v hvExt hvW hvOddExt hvOddW
    hp ν point hpoint tH hcover]
  unfold lastExtensionValueMultiplier cliffordGeneralSpinHorizontalBaselineScale
  rw [if_neg hvW, if_neg hvExt, div_eq_mul_inv, inv_inv, mul_comm, ← div_eq_mul_inv]

end Ledger

end RationalQuadraticSpaceMatrix
