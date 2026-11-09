import SMSFormula.CompactOrbitAveraging
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The three pieces assembled

Positivity, the averaging identity and propagation are proved separately. This file composes them
into one theorem.

The chain. (a) The orbit of a base point is stable under the compact group, so the restriction of an
invariant measure to it is invariant and the averaging identity applies. (b) Hence for every bounded
test the two restricted integrals satisfy the cross-multiplied comparison on the orbit, both masses
kept. (c) If that comparison holds for every compactly supported continuous test, regular
uniqueness upgrades it from integrals to measures on the orbit, and the propagation step spreads it to
the whole space: `nu(U) * mu = mu(U) * nu`.

A remark on the composition.  Step (c) needs the restricted measures to be regular, which holds only
because the orbit has finite measure -- `restrict_of_measure_ne_top`.  So compactness of the orbit is
used twice and for different reasons: once for finiteness of the mass in the pinning, and again here
for regularity of the restriction.

Scope: the conclusion is the cross-multiplied comparison, not equality of the measures -- the
scalar is only a ratio and the numerical identity `Lambda(1_U) = mu_nat(U)` is not proved here.
Nothing is adelic; no compact open subgroup is constructed; and the per-test hypotheses of (b) are
supplied, not derived from a concrete family.
-/

namespace SMSFormula.CompactOrbit

open MeasureTheory Set Pointwise CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal

/-! ## The orbit is stable -/

/-- The orbit of a base point is stable under the acting compact group, which is what lets the
averaging identity be applied to a restriction. -/
theorem preimage_smul_orbit {K X : Type*} [Group K] [MulAction K X] (x₀ : X) (k : K) :
    (fun x : X ↦ k • x) ⁻¹' (Set.range fun l : K ↦ l • x₀) = Set.range fun l : K ↦ l • x₀ := by
  ext x
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨k⁻¹ * l, ?_⟩
    show (k⁻¹ * l) • x₀ = x
    rw [mul_smul]
    show k⁻¹ • ((fun l : K ↦ l • x₀) l) = x
    rw [hl]
    show k⁻¹ • (k • x) = x
    rw [inv_smul_smul]
  · rintro ⟨l, rfl⟩
    refine ⟨k * l, ?_⟩
    show (k * l) • x₀ = k • (l • x₀)
    rw [mul_smul]

/-! ## The comparison on the orbit, one test at a time -/

/-- The cross-multiplied comparison on the orbit.  Both measures give the same average, so their
restricted integrals differ exactly by the two masses.  Finiteness of the orbit is what makes the
restrictions finite measures; stability is what makes them invariant. -/
theorem measure_mul_setIntegral_eq {K X : Type*} [Group K] [MeasurableSpace K] [MeasurableMul K]
    [MeasurableSpace X] [MulAction K X] [MeasurableConstSMul K X] (haar : Measure K)
    [IsProbabilityMeasure haar] [haar.IsMulLeftInvariant] (μ nu : Measure X)
    [SMulInvariantMeasure K X μ] [SMulInvariantMeasure K X nu] (x₀ : X)
    (hUm : MeasurableSet (Set.range fun l : K ↦ l • x₀))
    (hμtop : μ (Set.range fun l : K ↦ l • x₀) ≠ ⊤)
    (hnutop : nu (Set.range fun l : K ↦ l • x₀) ≠ ⊤) {f : X → ℝ}
    (hjoint : Measurable fun p : K × X ↦ f (p.1⁻¹ • p.2)) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    nu.real (Set.range fun l : K ↦ l • x₀) * (∫ x in Set.range fun l : K ↦ l • x₀, f x ∂μ) =
      μ.real (Set.range fun l : K ↦ l • x₀) *
        (∫ x in Set.range fun l : K ↦ l • x₀, f x ∂nu) := by
  set U : Set X := Set.range fun l : K ↦ l • x₀ with hUdef
  haveI : IsFiniteMeasure (μ.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμtop.lt_top⟩
  haveI : IsFiniteMeasure (nu.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hnutop.lt_top⟩
  haveI : SMulInvariantMeasure K X (μ.restrict U) :=
    smulInvariantMeasure_restrict μ hUm fun k ↦ preimage_smul_orbit x₀ k
  haveI : SMulInvariantMeasure K X (nu.restrict U) :=
    smulInvariantMeasure_restrict nu hUm fun k ↦ preimage_smul_orbit x₀ k
  have hae : ∀ eta : Measure X, ∀ᵐ x ∂(eta.restrict U),
      (∫ k, f (k⁻¹ • x) ∂haar) = ∫ k, f (k⁻¹ • x₀) ∂haar := by
    intro eta
    filter_upwards [ae_restrict_mem hUm] with x hx
    obtain ⟨k₀, rfl⟩ := hx
    exact average_const_on_orbit haar f x₀ k₀
  have hmain := measure_mul_integral_eq haar (μ.restrict U) (nu.restrict U) hjoint hC
    (hae μ) (hae nu)
  have hmassμ : (μ.restrict U).real Set.univ = μ.real U := by
    simp [Measure.real]
  have hmassnu : (nu.restrict U).real Set.univ = nu.real U := by
    simp [Measure.real]
  rwa [hmassμ, hmassnu] at hmain

/-! ## From the orbit to the whole space -/

/-- A scaled invariant measure is invariant, as an instance, so the propagation step can be applied
to the cross-multiplied pair without normalising anything. -/
theorem smulInvariantMeasure_smul {G X : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
    (nu : Measure X) [SMulInvariantMeasure G X nu] (c : ℝ≥0∞) :
    SMulInvariantMeasure G X (c • nu) :=
  ⟨fun g s _ ↦ by simp [Measure.smul_apply, measure_preimage_smul]⟩

/-- The assembled comparison.  From the cross-multiplied comparison on one nonempty open orbit,
holding for every compactly supported continuous test, regular uniqueness upgrades integrals to
measures there and propagation spreads it to the whole space.

Both uses of the orbit's finite measure are visible here: it makes the restrictions finite, and it is
exactly what `restrict_of_measure_ne_top` consumes to make them regular. -/
theorem smul_measure_eq_of_setIntegral_eq {G X : Type*} [Group G] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MulAction G X] [ContinuousConstSMul G X] (μ nu : Measure X)
    [μ.Regular] [nu.Regular] [SMulInvariantMeasure G X μ] [SMulInvariantMeasure G X nu]
    (htrans : IsTransitiveAction G X) {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (hμtop : μ U ≠ ⊤) (hnutop : nu U ≠ ⊤)
    (h : ∀ f : C_c(X, ℝ), nu.real U * (∫ x in U, (f : X → ℝ) x ∂μ) =
      μ.real U * (∫ x in U, (f : X → ℝ) x ∂nu)) :
    (nu U) • μ = (μ U) • nu := by
  haveI : (μ.restrict U).Regular := Measure.Regular.restrict_of_measure_ne_top hμtop
  haveI : (nu.restrict U).Regular := Measure.Regular.restrict_of_measure_ne_top hnutop
  haveI : ((nu U) • μ.restrict U).Regular := Measure.Regular.smul hnutop
  haveI : ((μ U) • nu.restrict U).Regular := Measure.Regular.smul hμtop
  haveI : SMulInvariantMeasure G X ((nu U) • μ) := smulInvariantMeasure_smul μ _
  have hlocal : ((nu U) • μ).restrict U = ((μ U) • nu).restrict U := by
    rw [Measure.restrict_smul, Measure.restrict_smul]
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
    rw [integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul]
    exact h f
  exact eq_smul_of_restrict_eq ((nu U) • μ) nu htrans hU hUne hlocal

end SMSFormula.CompactOrbit
