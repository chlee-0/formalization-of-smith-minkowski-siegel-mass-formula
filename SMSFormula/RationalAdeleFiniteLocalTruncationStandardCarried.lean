import SMSFormula.AdelicGeneratorL1
import SMSFormula.RationalAdeleFiniteLocalTruncationGeneral

/-!
# Congruence-tube limits for every standard-carried periodic finite test

For a lattice `L` of rank above four and a finite test `g` that is standard-carried at a
nonzero scale `c` and standard-periodic at a nonzero level `d` (the `(c,d)` class), the
bound `lintegral_norm_finiteFactor_generalCarrier_lt_top` makes the finite Bruhat coefficient
of `g` integrable.  With the integrability of `g` itself, the congruence-tube limit applies:

```text
d_fin(g)(b) = lim_k k! · ∫ g(x) · 1_Zhat((Q(x) - b)/k!) dx,
```

and two such tests with eventually proportional tube masses have proportional finite densities.
This discharges the admissibility hypotheses of the finite-place replacement lemma for every `(c,d)`
test, in particular for indicators of residue-defined subsets of `Zhat^n`.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix RationalQuadraticSpaceMatrix
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

/-- The finite Bruhat coefficient of a `(c,d)` test is integrable above rank four. -/
theorem integrable_finiteLocalBruhatCoefficient_of_standardCarried (L : PositiveDefiniteIntegralLattice n)
    (hn : 4 < n) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0) {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c g) (hperiodic : IsStandardPeriodic d g) :
    Integrable (L.rationalQuadraticSpaceMatrix.finiteLocalBruhatCoefficient g)
      rationalFiniteAdeleAddHaarMeasure := by
  have hgmeas : Measurable g := measurable_of_standardCarried hc hd hcarried hperiodic
  have heq : L.rationalQuadraticSpaceMatrix.finiteLocalBruhatCoefficient g =
      fun t ↦ ∫ x, g x * complexFiniteChar
        (t * dotQuadratic (integralModelMatrix L.pairingMatrix) x)
        ∂(rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
    funext fun t ↦ integral_finiteFactor_eq L t g
  rw [heq]
  exact ⟨(stronglyMeasurable_finiteFactor hgmeas _).aestronglyMeasurable,
    (hasFiniteIntegral_iff_norm _).2
      (lintegral_norm_finiteFactor_generalCarrier_lt_top L hn hc hd hcarried hperiodic)⟩

/-- The congruence-tube limit for every `(c,d)` test above rank four. -/
theorem tendsto_natScaleTruncated_finiteLocalValueDensity_of_standardCarried
    (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c g) (hperiodic : IsStandardPeriodic d g) (b : ℚ) :
    Tendsto (fun k : ℕ =>
        ((Nat.factorial k : ℕ) : ℂ) * ∫ x : Fin n → RationalFiniteAdele,
          g x * rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele b))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n)
      atTop (𝓝 (L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity g
        (algebraMap ℚ RationalFiniteAdele b))) :=
  L.rationalQuadraticSpaceMatrix.tendsto_natScaleTruncated_finiteLocalValueDensity
    (integrable_of_standardCarried hc hd hcarried hperiodic)
    (integrable_finiteLocalBruhatCoefficient_of_standardCarried L hn hc hd hcarried hperiodic) b

/-- Tube ratio ⇒ density ratio for two `(c,d)` tests above rank four. -/
theorem finiteLocalValueDensity_eq_mul_of_eventually_tube_eq_of_standardCarried
    (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {c d c' d' : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    (hc' : c' ≠ 0) (hd' : d' ≠ 0) {g g' : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c g) (hperiodic : IsStandardPeriodic d g)
    (hcarried' : IsStandardCarried c' g') (hperiodic' : IsStandardPeriodic d' g')
    (b : ℚ) (κ : ℂ)
    (h : ∀ᶠ k : ℕ in atTop,
      (∫ x : Fin n → RationalFiniteAdele,
          g x * rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele b))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
        κ * ∫ x : Fin n → RationalFiniteAdele,
          g' x * rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((Nat.factorial k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele b))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) :
    L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity g (algebraMap ℚ RationalFiniteAdele b) =
      κ * L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity g'
        (algebraMap ℚ RationalFiniteAdele b) :=
  L.rationalQuadraticSpaceMatrix.finiteLocalValueDensity_eq_mul_of_eventually_tube_eq
    (integrable_of_standardCarried hc hd hcarried hperiodic)
    (integrable_finiteLocalBruhatCoefficient_of_standardCarried L hn hc hd hcarried hperiodic)
    (integrable_of_standardCarried hc' hd' hcarried' hperiodic')
    (integrable_finiteLocalBruhatCoefficient_of_standardCarried L hn hc' hd' hcarried' hperiodic')
    b κ h

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
