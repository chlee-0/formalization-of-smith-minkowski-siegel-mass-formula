import SMSFormula.AdelicGaussianFiberEulerRatio

/-!
# Fiber Euler ratios from an invariant fiber measure (rank-free)

`IsFiberEulerRatio L P hx b M ρ` depends on the supplied presentation `P` through `M_native`.
The natural rank-free source is a presentation-free measure: let `σ` be any regular
`SO(𝔸)`-invariant measure on the value fiber `X_a` (`a = Q(x)`, `M = Q(x) ∈ ℤ`) whose carried fiber
sets obey the local-restriction law and whose integral carrier has the Euler mass
`σ(X_a ∩ {x_f integral}) = ofReal(Re d_∞(a_∞) · ∏'_p δ_p(M))`.  Then for every supplied
presentation the raw orbit ratio `σ(U)/M_native(U)` is a fiber Euler ratio
(`isFiberEulerRatio_of_measure`): the orbital comparison (transitivity of `SO(𝔸)` on the fiber,
compact open subgroups) gives `σ = (σ(U)/M_native(U)) · M_native`.

In lattice rank at least five `σ = gaussianFiberMeasure` is such a measure (its two laws are the
replacement lemma and the integral-carrier Euler product).  No rank bound, no
normalization and no presentation is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix MeasureTheory
open SMSFormula.CompactOrbit
open scoped ENNReal

local instance fermT2Infinite : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space
local instance fermT2Finite : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
local instance fermT2Adele : T2Space RationalAdele :=
  show T2Space (RationalInfiniteAdele × RationalFiniteAdele) from inferInstance

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

/-- A fiber Euler ratio from any invariant fiber measure with the two laws.  The laws are stated
on `σ` alone, so they do not see the presentation `P`; the conclusion holds for every `P`. -/
theorem isFiberEulerRatio_of_measure (hn : 1 ≤ n) (b : ℝ)
    (σ : Measure (adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))) [σ.Regular]
    [SMulInvariantMeasure L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup
      (adelicValueFiber L (algebraMap ℚ RationalAdele
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))) σ]
    (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
    (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
    (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
    (M : ℤ)
    (hloc : ∀ (Pr : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p)))
      (hPr : ∀ p ∈ Pr, p.Prime ∧ 1 ≤ e p) (gF gR : ℕ → ℝ≥0∞),
      (∀ p ∈ Pr, gF p ≠ 0) → (∀ p ∈ Pr, gF p ≠ ⊤) →
      (∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop,
        (L.restrictedResidueCount M Pr e R (p ^ v) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) →
      (∀ p ∈ Pr, ∀ᶠ v : ℕ in Filter.atTop, L.fullResidueCount M (p ^ v) ≠ 0) →
      haveI : NeZero (localRestrictionLevel Pr e) :=
        ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hPr p hp).1⟩
      σ (fiberResidueRestrictedSet L (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))
          (localRestrictionLevel Pr e) (localRestrictionSet Pr e R)) =
        ((∏ p ∈ Pr, gR p) / ∏ p ∈ Pr, gF p) *
          σ (fiberDividedCarrier L (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) 1))
    (hcar : σ (fiberDividedCarrier L (algebraMap ℚ RationalAdele
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) 1) =
      ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
          (gaussianOrbitTestRealFactor L b (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
          (rationalAdeleRealScalar (algebraMap ℚ RationalAdele
            (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))).re *
        ∏' p : Nat.Primes, L.localResidueDensity M p)) :
    IsFiberEulerRatio L P hx b M
      (σ ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) /
        nativeShellMeasureOnValueFiber L P hx
          ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))) := by
  letI := smulInvariantMeasure_nativeShellMeasureOnValueFiber L P hx (by omega : 2 ≤ n + 1)
  letI := secondCountableTopology_fiberActingGroup L
  letI := sigmaCompactSpace_fiberActingGroup L
  have hσ := eq_smul_of_compactOpen_subgroup σ (nativeShellMeasureOnValueFiber L P hx)
    (isTransitiveAction_nativeValueFiber L P hx) x₀ K hc ho (nativeShellMeasureOnValueFiber_ne_zero L P hx)
  have key : ∀ A, (σ ((fun g ↦ g • x₀) ''
        (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)) /
        nativeShellMeasureOnValueFiber L P hx
          ((fun g ↦ g • x₀) '' (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))) *
        nativeShellMeasureOnValueFiber L P hx A = σ A := fun A ↦ by
    conv_rhs => rw [hσ]
    rfl
  refine ⟨fun Pr e R hPr gF gR hgF0 hgFt hloc' hFne ↦ ?_, ?_⟩
  · rw [key, key]
    exact hloc Pr e R hPr gF gR hgF0 hgFt hloc' hFne
  · rw [key]
    exact hcar

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
