import SMSFormula.CompactOrbitAssembly

/-!
# The per-test hypotheses follow from continuity

The assembled comparison carries two hypotheses per test -- a uniform bound and joint measurability
of `(k,x) |-> f(k^-1 . x)`.  Both follow from continuity, and this
file derives them, leaving the comparison with only structural hypotheses.

The bound is not an extra assumption on the test: a continuous function of compact support is bounded,
which mathlib records by coercing `C_c` into the bounded continuous functions.  The joint
measurability is likewise free: `(k,x) |-> f(k^-1 . x)` is a composition of inversion, the action and
`f`, all continuous, and a continuous map into a Borel space is measurable.  Second countability is
what makes the product Borel structure agree with the Borel structure of the product, so it is
needed here.

Consequence.  The comparison on a compact open orbit reads with no analytic hypothesis on the
test at all: for every compactly supported continuous test the cross-multiplied identity holds, and
feeding the whole family to the assembly gives `nu(U) * mu = mu(U) * nu` on the whole space from
structural data only -- a compact open orbit, invariance under the auxiliary compact group, and
transitivity, invariance and regularity for the acting group.

Scope: nothing here is adelic.  No compact open subgroup of the acting group is
constructed, the shell's structural hypotheses are not verified, and the identity
`Lambda(1_U) = mu_nat(U)` is not proved -- the conclusion remains cross-multiplied, so the scalar is
still only a ratio.
-/

namespace SMSFormula.CompactOrbit

open MeasureTheory Set Pointwise CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal

/-! ## Both per-test hypotheses come from continuity -/

/-- The joint map is continuous: `(k,x) |-> f(k^-1 . x)` composes inversion, the action and `f`. -/
theorem continuous_inv_smul_comp {K X : Type*} [Group K] [TopologicalSpace K] [ContinuousInv K]
    [TopologicalSpace X] [MulAction K X] [ContinuousSMul K X] {f : X → ℝ} (hf : Continuous f) :
    Continuous fun p : K × X ↦ f (p.1⁻¹ • p.2) :=
  hf.comp ((continuous_inv.comp continuous_fst).smul continuous_snd)

/-- Hence it is measurable.  Second countability is what makes the product Borel structure the Borel
structure of the product, so it is genuinely used. -/
theorem measurable_inv_smul_comp {K X : Type*} [Group K] [TopologicalSpace K] [ContinuousInv K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [MulAction K X]
    [ContinuousSMul K X] {f : X → ℝ} (hf : Continuous f) :
    Measurable fun p : K × X ↦ f (p.1⁻¹ • p.2) :=
  (continuous_inv_smul_comp hf).measurable

/-- A compactly supported continuous test is bounded, with the bound named -- mathlib's own coercion
into the bounded continuous functions. -/
theorem abs_le_norm_toBoundedContinuousFunction {X : Type*} [TopologicalSpace X] (f : C_c(X, ℝ))
    (x : X) : |f x| ≤ ‖f.toBoundedContinuousFunction‖ := by
  rw [← Real.norm_eq_abs]
  exact BoundedContinuousFunction.norm_coe_le_norm f.toBoundedContinuousFunction x

/-! ## The comparison with no analytic hypothesis on the test -/

/-- The orbit comparison for every compactly supported continuous test, with the two per-test
hypotheses derived rather than supplied. -/
theorem measure_mul_setIntegral_eq_of_continuous {K X : Type*} [Group K] [TopologicalSpace K]
    [ContinuousInv K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    [MeasurableMul K] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [MulAction K X] [ContinuousSMul K X] [MeasurableConstSMul K X]
    (haar : Measure K) [IsProbabilityMeasure haar] [haar.IsMulLeftInvariant] (μ nu : Measure X)
    [SMulInvariantMeasure K X μ] [SMulInvariantMeasure K X nu] (x₀ : X)
    (hUm : MeasurableSet (Set.range fun l : K ↦ l • x₀))
    (hμtop : μ (Set.range fun l : K ↦ l • x₀) ≠ ⊤)
    (hnutop : nu (Set.range fun l : K ↦ l • x₀) ≠ ⊤) (f : C_c(X, ℝ)) :
    nu.real (Set.range fun l : K ↦ l • x₀) *
        (∫ x in Set.range fun l : K ↦ l • x₀, (f : X → ℝ) x ∂μ) =
      μ.real (Set.range fun l : K ↦ l • x₀) *
        (∫ x in Set.range fun l : K ↦ l • x₀, (f : X → ℝ) x ∂nu) :=
  measure_mul_setIntegral_eq haar μ nu x₀ hUm hμtop hnutop
    (measurable_inv_smul_comp (f : C(X, ℝ)).continuous)
    (abs_le_norm_toBoundedContinuousFunction f)

/-- The comparison from structural data alone.  With the orbit compact and open, the auxiliary
compact group leaving both measures invariant, and the acting group transitive with both measures
invariant and regular, the cross-multiplied comparison holds on the whole space.  No analytic
hypothesis on any test survives. -/
theorem smul_measure_eq_of_compactOpen_orbit {G K X : Type*} [Group G] [Group K]
    [TopologicalSpace K] [ContinuousInv K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] [MeasurableMul K] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MulAction G X]
    [ContinuousConstSMul G X] [MulAction K X] [ContinuousSMul K X] [MeasurableConstSMul K X]
    (haar : Measure K) [IsProbabilityMeasure haar] [haar.IsMulLeftInvariant] (μ nu : Measure X)
    [μ.Regular] [nu.Regular] [SMulInvariantMeasure G X μ] [SMulInvariantMeasure G X nu]
    [SMulInvariantMeasure K X μ] [SMulInvariantMeasure K X nu]
    (htrans : IsTransitiveAction G X) (x₀ : X)
    (hUo : IsOpen (Set.range fun l : K ↦ l • x₀))
    (hUc : IsCompact (Set.range fun l : K ↦ l • x₀)) :
    (nu (Set.range fun l : K ↦ l • x₀)) • μ = (μ (Set.range fun l : K ↦ l • x₀)) • nu := by
  have hUm : MeasurableSet (Set.range fun l : K ↦ l • x₀) := hUo.measurableSet
  have hμtop : μ (Set.range fun l : K ↦ l • x₀) ≠ ⊤ := hUc.measure_lt_top.ne
  have hnutop : nu (Set.range fun l : K ↦ l • x₀) ≠ ⊤ := hUc.measure_lt_top.ne
  refine smul_measure_eq_of_setIntegral_eq μ nu htrans hUo ⟨x₀, ⟨1, one_smul K x₀⟩⟩ hμtop hnutop
    fun f ↦ ?_
  exact measure_mul_setIntegral_eq_of_continuous haar μ nu x₀ hUm hμtop hnutop f

end SMSFormula.CompactOrbit
