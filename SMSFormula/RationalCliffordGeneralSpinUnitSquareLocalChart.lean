import SMSFormula.RationalCliffordGeneralSpinFieldCentralFiber
import SMSFormula.RationalCliffordSpinCandidatePlacewiseChartMeasurePrecursor
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Local square charts for the horizontal general-Spin factor

The scalar part of the crossed map is the literal square map on field units.
For every proper nontrivially normed rational field, Mathlib's power-map
covering theorem makes this square map a local homeomorphism.  We choose its
identity chart and then take products with the existing real and p-adic
Spin-to-`SO` identity charts.

These are genuine local horizontal parameter charts.  They do not identify
the product parameter source with an open subset of intrinsic `GSpin`, and
they assign no Haar or differential scale.
-/

noncomputable section

open Topology

namespace Rat

variable (K : Type*) [NontriviallyNormedField K] [ProperSpace K] [Algebra ℚ K]

/-- The square homomorphism on the unit group of a local rational field. -/
def unitSquareMonoidHom : Kˣ →* Kˣ :=
  powMonoidHom 2

/-- The unit-square map is a covering map over every proper local rational
field. -/
theorem unitSquareMonoidHom_isCoveringMap :
    IsCoveringMap (unitSquareMonoidHom K) := by
  have htwo : (2 : K) ≠ 0 := by
    intro h
    have hq : (2 : ℚ) = 0 := by
      apply (algebraMap ℚ K).injective
      simpa using h
    norm_num at hq
  let e := unitsHomeomorphNeZero (G₀ := K)
  let f : {z : K // z ≠ 0} → {z : K // z ≠ 0} :=
    fun z => ⟨z.1 ^ 2, pow_ne_zero 2 z.2⟩
  have hf : IsCoveringMap f := by
    simpa [f] using isCoveringMap_npow 2 htwo
  have h := (hf.comp_homeomorph e).homeomorph_comp e.symm
  have hfun : e.symm ∘ f ∘ e = unitSquareMonoidHom K := by
    funext z
    apply e.injective
    change e (e.symm (f (e z))) = e (unitSquareMonoidHom K z)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rfl
  rw [hfun] at h
  exact h

/-- The unit-square map is a local homeomorphism. -/
theorem unitSquareMonoidHom_isLocalHomeomorph :
    IsLocalHomeomorph (unitSquareMonoidHom K) :=
  (unitSquareMonoidHom_isCoveringMap K).isLocalHomeomorph

/-- A chosen identity-centered chart for the unit-square covering map. -/
noncomputable def unitSquareIdentityChart :
    OpenPartialHomeomorph Kˣ Kˣ :=
  Classical.choose (unitSquareMonoidHom_isLocalHomeomorph K (1 : Kˣ))

@[simp]
theorem one_mem_unitSquareIdentityChart_source :
    (1 : Kˣ) ∈ (unitSquareIdentityChart K).source :=
  (Classical.choose_spec
    (unitSquareMonoidHom_isLocalHomeomorph K (1 : Kˣ))).1

/-- The chosen chart has the literal square map as its global underlying
function. -/
theorem unitSquareIdentityChart_coe :
    (unitSquareMonoidHom K : Kˣ → Kˣ) = unitSquareIdentityChart K :=
  (Classical.choose_spec
    (unitSquareMonoidHom_isLocalHomeomorph K (1 : Kˣ))).2

@[simp]
theorem unitSquareIdentityChart_apply (z : Kˣ) :
    unitSquareIdentityChart K z = z ^ 2 := by
  rw [← congrFun (unitSquareIdentityChart_coe K) z]
  rfl

/-- The identity chart cannot also contain the other point of the square-map
fiber over one. -/
theorem neg_one_not_mem_unitSquareIdentityChart_source :
    (-1 : Kˣ) ∉ (unitSquareIdentityChart K).source := by
  intro hneg
  have hone := one_mem_unitSquareIdentityChart_source K
  have hsquare : unitSquareIdentityChart K (1 : Kˣ) =
      unitSquareIdentityChart K (-1 : Kˣ) := by
    simp
  have hunit : (1 : Kˣ) = -1 :=
    (unitSquareIdentityChart K).injOn hone hneg hsquare
  have hval : (1 : K) = -1 := congrArg Units.val hunit
  have hq : (1 : ℚ) = -1 := by
    apply (algebraMap ℚ K).injective
    simpa using hval
  norm_num at hq

end Rat

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The real local horizontal parameter chart: scalar square together with
the existing Spin-to-`SO` chart. -/
noncomputable def realCliffordGeneralSpinHorizontalProductIdentityChart :
    OpenPartialHomeomorph
      (ℝˣ × V.RealCliffordSpinCandidateGroup)
      (ℝˣ × V.RealSpecialOrthogonalGroup) :=
  (Rat.unitSquareIdentityChart ℝ).prod
    V.realCliffordSpinCandidateIdentityChart

@[simp]
theorem one_mem_realCliffordGeneralSpinHorizontalProductIdentityChart_source :
    ((1, 1) : ℝˣ × V.RealCliffordSpinCandidateGroup) ∈
      V.realCliffordGeneralSpinHorizontalProductIdentityChart.source := by
  exact ⟨Rat.one_mem_unitSquareIdentityChart_source ℝ,
    V.one_mem_realCliffordSpinCandidateIdentityChart_source⟩

/-- Pointwise value of the real horizontal product chart. -/
@[simp]
theorem realCliffordGeneralSpinHorizontalProductIdentityChart_apply
    (x : ℝˣ × V.RealCliffordSpinCandidateGroup) :
    V.realCliffordGeneralSpinHorizontalProductIdentityChart x =
      (x.1 ^ 2, V.realCliffordSpinCandidateToSpecialOrthogonalHom x.2) := by
  rw [realCliffordGeneralSpinHorizontalProductIdentityChart,
    OpenPartialHomeomorph.prod_apply]
  apply Prod.ext
  · exact Rat.unitSquareIdentityChart_apply ℝ x.1
  · exact congrFun V.realCliffordSpinCandidateIdentityChart_coe.symm x.2

/-- The p-adic local horizontal parameter chart. -/
noncomputable def padicCliffordGeneralSpinHorizontalProductIdentityChart
    (p : ℕ) [Fact (Nat.Prime p)] :
    OpenPartialHomeomorph
      (ℚ_[p]ˣ × V.PadicCliffordSpinCandidateGroup p)
      (ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  (Rat.unitSquareIdentityChart ℚ_[p]).prod
    (V.padicCliffordSpinCandidateIdentityChart p)

@[simp]
theorem one_mem_padicCliffordGeneralSpinHorizontalProductIdentityChart_source
    (p : ℕ) [Fact (Nat.Prime p)] :
    ((1, 1) : ℚ_[p]ˣ × V.PadicCliffordSpinCandidateGroup p) ∈
      (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).source := by
  exact ⟨Rat.one_mem_unitSquareIdentityChart_source ℚ_[p],
    V.one_mem_padicCliffordSpinCandidateIdentityChart_source p⟩

/-- Pointwise value of the p-adic horizontal product chart. -/
@[simp]
theorem padicCliffordGeneralSpinHorizontalProductIdentityChart_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (x : ℚ_[p]ˣ × V.PadicCliffordSpinCandidateGroup p) :
    V.padicCliffordGeneralSpinHorizontalProductIdentityChart p x =
      (x.1 ^ 2,
        V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] x.2) := by
  rw [padicCliffordGeneralSpinHorizontalProductIdentityChart,
    OpenPartialHomeomorph.prod_apply]
  apply Prod.ext
  · exact Rat.unitSquareIdentityChart_apply ℚ_[p] x.1
  · exact congrFun (V.padicCliffordSpinCandidateIdentityChart_coe p).symm x.2

end RationalQuadraticSpaceMatrix
