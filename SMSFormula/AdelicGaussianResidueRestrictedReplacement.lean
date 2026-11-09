import SMSFormula.AdelicGaussianResidueRestrictedUnit
import SMSFormula.AdelicValueDensityLocalProduct
import SMSFormula.RationalAdeleFiniteLocalReplacementAssembly

/-!
# The replacement lemma for the orbit test

The residue-restricted Gaussian unit is a product test: its real factor is the normalized
Gaussian `exp(2πb a_∞) e^{-πb Q(x_∞)}` and its finite factor is the residue-restricted
indicator.  The local product of value densities therefore gives

`d_Φ(w) = d_∞(Φ_∞)(w_∞) · d_fin(1_{U_R})(w_f)`.

At an adele `a` whose finite part is the rational integer `M`, the replacement lemma applies
to the finite factor for supplied local restriction data `(P, e, R_p)` with the CRT product `R`:

`d(Φ_∞ ⊗ 1_{U_R})(a) = (∏_P gR_p / ∏_P gF_p) · d(Φ_∞ ⊗ 1_Zhat)(a)`,

and, through the Riesz evaluation of carried fiber sets,

`σ({x ∈ X_a : x_f ∈ U_R}) = (∏_P gR_p / ∏_P gF_p) · σ({x ∈ X_a : x_f integral})`.

The finiteness of the numerator follows from the local count identity itself.  The real factor
is common to both sides and is never evaluated; no Euler product, orbit index or normalization
is used.  Nothing is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix MeasureTheory Filter
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The real factor of the orbit test: `exp(2πb a_∞) e^{-πb Q(y)}`, read in `ℂ`. -/
def gaussianOrbitTestRealFactor (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele) :
    (Fin n → ℝ) → ℂ :=
  fun y ↦ ((Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) *
    realShiftedGaussian L b 0 y : ℝ) : ℂ)

/-- The orbit test is a product test: its value density is the real local density of the real
factor times the finite local density of the residue-restricted indicator. -/
theorem complexValueFourierDensity_gaussianResidueRestrictedUnit (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (a : RationalAdele) (N₀ : ℕ) [NeZero N₀] (R : Set (Fin n → ZMod N₀)) (w : RationalAdele) :
    L.rationalQuadraticSpaceMatrix.complexValueFourierDensity
        (fun x ↦ ((gaussianResidueRestrictedUnit L b a N₀ R).val x : ℂ)) w =
      L.rationalQuadraticSpaceMatrix.realLocalValueDensity (gaussianOrbitTestRealFactor L b a)
          (rationalAdeleRealScalar w) *
        L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity
          (residueRestrictedIndicator n N₀ R) w.2 := by
  have hf : (fun x ↦ ((gaussianResidueRestrictedUnit L b a N₀ R).val x : ℂ)) =
      fun x ↦ gaussianOrbitTestRealFactor L b a (rationalAdeleVectorRealPart n x) *
        residueRestrictedIndicator n N₀ R (rationalAdeleVectorFinitePart n x) := by
    funext x
    change ((Real.exp (Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) *
        (realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x) *
          realResidueRestrictedIndicator n N₀ R (rationalAdeleVectorFinitePart n x)) : ℝ) : ℂ) = _
    rw [← coe_realResidueRestrictedIndicator N₀ R]
    simp only [gaussianOrbitTestRealFactor]
    push_cast
    ring
  rw [hf]
  exact complexValueFourierDensity_productTest _ _ _ w

/-- A local count identity with eventually nonzero full counts forces a finite restricted mass. -/
theorem ne_top_of_eventually_count_mul_eq {f F : ℕ → ℕ} {gF gR : ℝ≥0∞} (hgFt : gF ≠ ⊤)
    (hloc : ∀ᶠ v : ℕ in atTop, (f v : ℝ≥0∞) * gF = (F v : ℝ≥0∞) * gR)
    (hFne : ∀ᶠ v : ℕ in atTop, F v ≠ 0) : gR ≠ ⊤ := by
  obtain ⟨v, hv, hF⟩ := (hloc.and hFne).exists
  intro htop
  have hlt : (f v : ℝ≥0∞) * gF ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hgFt
  rw [hv, htop, ENNReal.mul_top (by exact_mod_cast hF)] at hlt
  exact hlt rfl

/-- The replacement lemma for the orbit test: at an adele with rational-integer finite part `M`,
`d(Φ_∞ ⊗ 1_{U_R})(a) = (∏_P gR_p / ∏_P gF_p) · d(Φ_∞ ⊗ 1_Zhat)(a)` for the CRT product `R`. -/
theorem realValueDensity_gaussianResidueRestrictedUnit_localRestriction (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) (b : ℝ) (a : RationalAdele) (M : ℤ)
    (ha : a.2 = algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ))
    (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞)
    (hgF0 : ∀ p ∈ P, gF p ≠ 0) (hgFt : ∀ p ∈ P, gF p ≠ ⊤)
    (hloc : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop,
      (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p)
    (hFne : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0) :
    haveI : NeZero (localRestrictionLevel P e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
    L.rationalQuadraticSpaceMatrix.realValueDensity
        (gaussianResidueRestrictedUnit L b a (localRestrictionLevel P e)
          (localRestrictionSet P e R)).val a =
      ((∏ p ∈ P, gR p) / ∏ p ∈ P, gF p).toReal *
        L.rationalQuadraticSpaceMatrix.realValueDensity
          (gaussianResidueRestrictedUnit L b a (localRestrictionLevel P e) Set.univ).val a := by
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  change (L.rationalQuadraticSpaceMatrix.complexValueFourierDensity _ a).re =
    _ * (L.rationalQuadraticSpaceMatrix.complexValueFourierDensity _ a).re
  rw [complexValueFourierDensity_gaussianResidueRestrictedUnit,
    complexValueFourierDensity_gaussianResidueRestrictedUnit, ha,
    L.finiteLocalValueDensity_localRestriction_eq_mul hn M P e R hP gF gR hgF0 hgFt hloc hFne,
    residueRestrictedIndicator_univ, ← Complex.re_ofReal_mul]
  congr 1
  ring

/-- With the full residue set, the carried fiber set is the integral part of the fiber. -/
theorem fiberResidueRestrictedSet_univ (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) (N₀ : ℕ)
    [NeZero N₀] : fiberResidueRestrictedSet L a N₀ Set.univ = fiberDividedCarrier L a 1 := by
  ext x
  simp only [fiberResidueRestrictedSet, fiberDividedCarrier, Set.mem_setOf_eq,
    realResidueRestrictedIndicator, residueRestrictedIndicator, Set.mem_univ, if_true]
  by_cases hx : rationalAdeleVectorFinitePart n x.val ∈ integralFiniteAdeleVectors n
  · rw [dif_pos hx]
    simpa [standardDividedLattice] using hx
  · rw [dif_neg hx]
    simpa [standardDividedLattice] using hx

/-- The σ-mass of the carried fiber set through the replacement lemma:
`σ({x ∈ X_a : x_f ∈ U_R}) = (∏_P gR_p / ∏_P gF_p) · σ({x ∈ X_a : x_f integral})`. -/
theorem gaussianFiberMeasure_fiberResidueRestrictedSet_localRestriction (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) {b : ℝ} (hb : 0 < b) (a : RationalAdele) (M : ℤ)
    (ha : a.2 = algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ))
    (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞)
    (hgF0 : ∀ p ∈ P, gF p ≠ 0) (hgFt : ∀ p ∈ P, gF p ≠ ⊤)
    (hloc : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop,
      (L.restrictedResidueCount M P e R (p ^ v) : ℝ≥0∞) * gF p =
        (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p)
    (hFne : ∀ p ∈ P, ∀ᶠ v : ℕ in atTop, L.fullResidueCount M (p ^ v) ≠ 0) :
    haveI : NeZero (localRestrictionLevel P e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
    gaussianFiberMeasure L hn hb a
        (fiberResidueRestrictedSet L a (localRestrictionLevel P e) (localRestrictionSet P e R)) =
      ((∏ p ∈ P, gR p) / ∏ p ∈ P, gF p) * gaussianFiberMeasure L hn hb a (fiberDividedCarrier L a 1) := by
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  have hgRt : ∀ p ∈ P, gR p ≠ ⊤ := fun p hp ↦ ne_top_of_eventually_count_mul_eq (hgFt p hp)
    (hloc p hp) (hFne p hp)
  have hratio : (∏ p ∈ P, gR p) / ∏ p ∈ P, gF p ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.prod_ne_top hgRt) (Finset.prod_ne_zero_iff.2 hgF0)
  rw [← fiberResidueRestrictedSet_univ L a (localRestrictionLevel P e),
    gaussianFiberMeasure_fiberResidueRestrictedSet, gaussianFiberMeasure_fiberResidueRestrictedSet,
    realValueDensity_gaussianResidueRestrictedUnit_localRestriction L hn b a M ha P e R hP gF gR
      hgF0 hgFt hloc hFne, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hratio]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
