import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular

/-!
# The Riesz layer of the coarea system

The fiber system of the coarea construction is built by Riesz: at each value the test-to-density map
is a positive linear functional on compactly supported continuous functions, so it is integration
against a regular measure, and the invariance already proved for the functional must transfer to
that measure.

This file proves the transfer, abstractly.

* A regular measure whose compactly supported integrals are unchanged by a homeomorphism is
  invariant under it. The proof is the regular uniqueness theorem: two regular measures agreeing
  on every `C_c` test are equal, and the pushforward of a regular measure along a homeomorphism is
  regular.
* Hence for a Riesz measure: if the functional is invariant under precomposition with a
  homeomorphism, so is the measure it represents.
* And the converse direction of the representation: a regular measure representing the functional
  is the Riesz measure (regular uniqueness from `C_c` tests).

Two further pieces of the construction side are proved in the last section.  Support by
regularity: a functional killing every nonnegative test supported inside an open set gives that set
measure zero -- inner regularity reduces to compact subsets, and a Urysohn function squeezed between
a compact set and a compact closed neighbourhood inside the open set converts vanishing of the
functional into the measure bound.  And the local bound: a functional bounded by a constant on tests
with values in the unit interval has a measure of at most that total mass, which is the
measure-level form of a bound `|d_f(a)| <= ‖f‖_inf d_eta(a)`.

The scalar is not determined by invariance, and that is recorded here as a theorem: if a regular
measure is invariant then so is every nonnegative multiple of it.  So
invariance, and uniqueness up to it, never determine the normalisation, so the
`a`-independence of the fiber scalar does not follow from them.

Scope: this is the representation and invariance layer only.  Nothing here constructs the
value-density functional, verifies its positivity, identifies its support with a shell, compares it
with the orbital measure, or evaluates anything.  A homeomorphism is assumed, not derived
from a continuous bijection.
-/

namespace SMSFormula.Coarea

open MeasureTheory CompactlySupported CompactlySupportedContinuousMap Set

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X]

/-- Regular uniqueness, applied to a homeomorphism: a regular measure whose compactly supported
integrals are unchanged by a homeomorphism is invariant under it. -/
theorem map_eq_self_of_integral_comp_eq {μ : Measure X} [μ.Regular] (T : X ≃ₜ X)
    (h : ∀ f : C_c(X, ℝ), ∫ x, f (T x) ∂μ = ∫ x, f x ∂μ) :
    Measure.map T μ = μ := by
  haveI : (Measure.map T μ).Regular := Measure.Regular.map T
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
  have hmap : ∫ x, f x ∂(Measure.map T μ) = ∫ x, f (T x) ∂μ :=
    integral_map T.continuous.aemeasurable f.continuous.aestronglyMeasurable
  rw [hmap]
  exact h f

/-- The transfer: if the functional is invariant under precomposition with a homeomorphism, then so
is the measure representing it. -/
theorem map_rieszMeasure_eq_of_invariant (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) (T : X ≃ₜ X)
    (hΛ : ∀ f : C_c(X, ℝ), Λ (f.comp (Homeomorph.toCocompactMap T)) = Λ f) :
    Measure.map T (RealRMK.rieszMeasure Λ) = RealRMK.rieszMeasure Λ := by
  refine map_eq_self_of_integral_comp_eq T fun f ↦ ?_
  have hcomp : ∫ x, (f.comp (Homeomorph.toCocompactMap T)) x ∂(RealRMK.rieszMeasure Λ) =
      Λ (f.comp (Homeomorph.toCocompactMap T)) :=
    RealRMK.integral_rieszMeasure Λ _
  calc ∫ x, f (T x) ∂(RealRMK.rieszMeasure Λ)
      = Λ (f.comp (Homeomorph.toCocompactMap T)) := hcomp
    _ = Λ f := hΛ f
    _ = ∫ x, f x ∂(RealRMK.rieszMeasure Λ) := (RealRMK.integral_rieszMeasure Λ f).symm

/-- Regular uniqueness from `C_c` tests: a regular measure representing the functional is the Riesz
measure.  Nothing beyond the values on compactly supported tests is used. -/
theorem eq_rieszMeasure_of_integral_eq (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) {μ : Measure X} [μ.Regular]
    (h : ∀ f : C_c(X, ℝ), ∫ x, f x ∂μ = Λ f) :
    μ = RealRMK.rieszMeasure Λ :=
  Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ by
    rw [h f, RealRMK.integral_rieszMeasure]

omit [T2Space X] [BorelSpace X] [LocallyCompactSpace X] in
/-- The scalar is not determined by invariance.  Every nonnegative multiple of an invariant measure
is invariant, so invariance -- and uniqueness up to it -- can never determine the normalisation. -/
theorem map_smul_eq_smul_of_map_eq {μ : Measure X} (T : X ≃ₜ X) (h : Measure.map T μ = μ)
    (c : ENNReal) : Measure.map T (c • μ) = c • μ := by
  rw [Measure.map_smul, h]


section Support

variable [RegularSpace X]

/-- Support by regularity: if the functional kills every nonnegative test supported inside an open
set, the measure gives that set measure zero.  This is the step the route calls "support in `X_a` by
regularity": inner regularity reduces to compact subsets, and a Urysohn function squeezed between a
compact set and a compact closed neighbourhood inside the open set converts the functional's
vanishing into the measure bound. -/
theorem rieszMeasure_eq_zero_of_forall_eq_zero (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) {U : Set X} (hU : IsOpen U)
    (h : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) → tsupport (f : X → ℝ) ⊆ U → Λ f = 0) :
    RealRMK.rieszMeasure Λ U = 0 := by
  refine le_antisymm ?_ zero_le
  rw [hU.measure_eq_iSup_isCompact]
  refine iSup_le fun K ↦ iSup_le fun hKU ↦ iSup_le fun hK ↦ ?_
  obtain ⟨L, hLc, hLcl, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨f, hf1, hf0, hfsupp, hfmem⟩ :=
    exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hKL)
  have hsub : Function.support (f : X → ℝ) ⊆ interior L := by
    intro x hx
    by_contra hxL
    exact hx (hf0 hxL)
  have htsupp : tsupport (f : X → ℝ) ⊆ U := by
    refine (closure_mono hsub).trans ?_
    exact (hLcl.closure_subset_iff.2 interior_subset).trans hLU
  have hbound := RealRMK.rieszMeasure_le_of_eq_one Λ (f := ⟨f, hfsupp⟩)
    (fun x ↦ (hfmem x).1) hK (fun x hx ↦ hf1 hx)
  rw [h ⟨f, hfsupp⟩ (fun x ↦ (hfmem x).1) htsupp] at hbound
  simpa using hbound

/-- The local bound gives a finite measure: if the functional is bounded by a constant on every test
with values in the unit interval, the whole measure has mass at most that constant.  This is the
measure-level consequence of the route's `|d_f(a)| <= ‖f‖_inf d_eta(a)`. -/
theorem rieszMeasure_univ_le (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) {C : ℝ}
    (h : ∀ f : C_c(X, ℝ), (∀ x, (f : X → ℝ) x ∈ Set.Icc (0 : ℝ) 1) → Λ f ≤ C) :
    RealRMK.rieszMeasure Λ Set.univ ≤ ENNReal.ofReal C := by
  rw [isOpen_univ.measure_eq_iSup_isCompact]
  refine iSup_le fun K ↦ iSup_le fun _ ↦ iSup_le fun hK ↦ ?_
  obtain ⟨f, hf1, _, hfsupp, hfmem⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  refine le_trans (RealRMK.rieszMeasure_le_of_eq_one Λ (f := ⟨f, hfsupp⟩)
    (fun x ↦ (hfmem x).1) hK (fun x hx ↦ hf1 hx)) ?_
  exact ENNReal.ofReal_le_ofReal (h ⟨f, hfsupp⟩ hfmem)


/-- The positivity witness is exactly nonvanishing.  The measure is zero precisely when the
functional kills every nonnegative test.  One direction is the support statement at the whole space;
the other is that the measure represents the functional. -/
theorem rieszMeasure_eq_zero_iff (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) :
    RealRMK.rieszMeasure Λ = 0 ↔ ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) → Λ f = 0 := by
  constructor
  · intro h f _
    rw [← RealRMK.integral_rieszMeasure Λ f, h]
    simp
  · intro h
    have huniv : RealRMK.rieszMeasure Λ Set.univ = 0 :=
      rieszMeasure_eq_zero_of_forall_eq_zero Λ isOpen_univ fun f hf _ ↦ h f hf
    exact Measure.measure_univ_eq_zero.mp huniv

/-- The witness form: the fiber measure is nonzero exactly when some nonnegative test has nonzero
value.  So the route's positivity witness is not merely sufficient -- it is necessary, and it cannot
be circumvented. -/
theorem rieszMeasure_ne_zero_iff (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) :
    RealRMK.rieszMeasure Λ ≠ 0 ↔ ∃ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) ∧ Λ f ≠ 0 := by
  rw [ne_eq, rieszMeasure_eq_zero_iff]
  push_neg
  rfl

end Support

end SMSFormula.Coarea
