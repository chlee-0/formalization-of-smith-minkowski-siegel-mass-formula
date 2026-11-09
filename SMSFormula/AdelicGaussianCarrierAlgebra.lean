import SMSFormula.AdelicGaussianCarrierFunctional
import SMSFormula.ShellExtensionPositivity
import SMSFormula.CompactOpenExhaustionDetermining
import SMSFormula.RationalAdeleFourierCharacterSeparation

/-!
# Fixed-width algebra on the compact fiber piece

The ambient core is only a linear space. Its trace image is an algebra:
on the fiber the fixed-width product identity applies, retaining the
polar factor two, while products of finite factors retain a carrier and a
common period of the factors. No ambient product-closure claim is made.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}

theorem realShiftedGaussian_mul_of_value (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (u v : Fin n → ℝ) {x : Fin n → RationalAdele} {a : RationalAdele}
    (hx : L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a) :
    realShiftedGaussian L b u (rationalAdeleVectorRealPart n x) *
        realShiftedGaussian L b v (rationalAdeleVectorRealPart n x) =
      Real.exp (-(Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) +
        Real.pi * b * QuadraticMap.polar L.polarQuadraticForm u v) *
        realShiftedGaussian L b (u + v) (rationalAdeleVectorRealPart n x) := by
  simp only [realShiftedGaussian_eq]
  exact SMSFormula.ShellFixedWidth.quadraticShiftedGaussian_mul_of_shell
    L.polarQuadraticForm L.continuous_polarQuadraticForm (Real.pi * b)
    (ContinuousMap.id _) u v (polarQuadraticForm_realPart_of_value L hx)

/-- Every product of two core traces is another core trace at the same width. -/
theorem exists_realGaussianCore_mul_trace (L : PositiveDefiniteIntegralLattice n) (b : ℝ)
    (a : RationalAdele) (c : ℕ) {f g : (Fin n → RationalAdele) → ℝ}
    (hf : f ∈ realGaussianCore L b) (hg : g ∈ realGaussianCore L b) :
    ∃ h : realGaussianCore L b, ∀ x : adelicFiberCarrier L a c,
      h.val x.val = f x.val * g x.val := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, e, d, f, he, hd, hfc, hfp, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨v, e', d', g, he', hd', hgc, hgp, rfl⟩ := hg
      have hcar : IsStandardCarried e (fun y ↦ ((f y * g y : ℝ) : ℂ)) := by
        intro y hy
        simp [Complex.ofReal_eq_zero.mp (hfc y hy)]
      have hper : IsStandardPeriodic (d * d') (fun y ↦ ((f y * g y : ℝ) : ℂ)) := by
        intro y z hz
        dsimp only
        rw [Complex.ofReal_injective ((hfp.mono (dvd_mul_right d d')) y z hz),
          Complex.ofReal_injective ((hgp.mono (dvd_mul_left d' d)) y z hz)]
      let h : realGaussianCore L b := ⟨fun x ↦
        realShiftedGaussian L b (u + v) (rationalAdeleVectorRealPart n x) *
          (f (rationalAdeleVectorFinitePart n x) * g (rationalAdeleVectorFinitePart n x)),
        Submodule.subset_span ⟨u + v, e, d * d', _, he, mul_ne_zero hd hd', hcar, hper, rfl⟩⟩
      refine ⟨Real.exp (-(Real.pi * b * (2 * rationalInfiniteAdeleContinuousAddEquivReal a.1)) +
        Real.pi * b * QuadraticMap.polar L.polarQuadraticForm u v) • h, fun x ↦ ?_⟩
      change _ * (realShiftedGaussian L b (u + v) _ * (_ * _)) = _
      have hmul := realShiftedGaussian_mul_of_value L b u v x.property.1
      calc
        _ = (realShiftedGaussian L b u (rationalAdeleVectorRealPart n x.val) *
          realShiftedGaussian L b v (rationalAdeleVectorRealPart n x.val)) *
          (f (rationalAdeleVectorFinitePart n x.val) * g (rationalAdeleVectorFinitePart n x.val)) := by
            rw [hmul]; ring
        _ = _ := by ring
    | zero => exact ⟨0, fun x ↦ by simp⟩
    | add g₁ g₂ _ _ h₁ h₂ =>
      obtain ⟨h₁, hh₁⟩ := h₁
      obtain ⟨h₂, hh₂⟩ := h₂
      exact ⟨h₁ + h₂, fun x ↦ by simp only [Submodule.coe_add, Pi.add_apply]; rw [hh₁, hh₂]; ring⟩
    | smul r g _ h =>
      obtain ⟨h, hh⟩ := h
      exact ⟨r • h, fun x ↦ by change r * _ = _ * (r * _); rw [hh]; ring⟩
  | zero => exact ⟨0, fun x ↦ by simp⟩
  | add f₁ f₂ _ _ h₁ h₂ =>
    obtain ⟨h₁, hh₁⟩ := h₁
    obtain ⟨h₂, hh₂⟩ := h₂
    exact ⟨h₁ + h₂, fun x ↦ by simp only [Submodule.coe_add, Pi.add_apply]; rw [hh₁, hh₂]; ring⟩
  | smul r f _ h =>
    obtain ⟨h, hh⟩ := h
    exact ⟨r • h, fun x ↦ by change r * _ = (r * _) * _; rw [hh]; ring⟩

/-- The actual image, not an unrelated model algebra. -/
def gaussianCarrierTraceAlgebra (L : PositiveDefiniteIntegralLattice n) (b : ℝ) (a : RationalAdele)
    {c : ℕ} (hc : c ≠ 0) : Subalgebra ℝ C(adelicFiberCarrier L a c, ℝ) :=
  (gaussianCarrierTrace L b a c).range.toSubalgebra
    (by
      refine ⟨gaussianCarrierUnit L b a hc, ?_⟩
      ext x
      exact gaussianCarrierUnit_on L b a hc x.property)
    (by
      rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
      obtain ⟨h, hh⟩ := exists_realGaussianCore_mul_trace L b a c f.property g.property
      exact ⟨h, ContinuousMap.ext hh⟩)

@[simp] theorem gaussianCarrierTraceAlgebra_toSubmodule (L : PositiveDefiniteIntegralLattice n)
    (b : ℝ) (a : RationalAdele) {c : ℕ} (hc : c ≠ 0) :
    (gaussianCarrierTraceAlgebra L b a hc).toSubmodule = (gaussianCarrierTrace L b a c).range := rfl


/-- The finite test family separates points of each divided carrier.
The character is the existing Fourier character; a component of a modulation
supplies a real test, with its period supplied by the existing denominator theorem. -/
theorem exists_real_standard_test_separating {c : ℕ}
    {x y : Fin n → RationalFiniteAdele} (hx : x ∈ standardDividedLattice n c)
    (hy : y ∈ standardDividedLattice n c) (hxy : x ≠ y) :
    ∃ (g : (Fin n → RationalFiniteAdele) → ℝ) (d : ℕ), d ≠ 0 ∧
      IsStandardCarried c (fun z ↦ (g z : ℂ)) ∧
      IsStandardPeriodic d (fun z ↦ (g z : ℂ)) ∧ g x ≠ g y := by
  classical
  have hsep : ∃ v : Fin n → RationalFiniteAdele,
      rationalFiniteAdeleFourierChar (dotProduct x v) ≠
        rationalFiniteAdeleFourierChar (dotProduct y v) := by
    by_contra! h
    apply hxy
    funext i
    apply sub_eq_zero.mp
    apply rationalFiniteAdele_eq_zero_of_fourierChar_mul_eq_one
    intro t
    have ht := h (Pi.single i t)
    simp only [dotProduct_single] at ht
    rw [mul_comm, sub_mul, AddChar.map_sub_eq_div, ht, div_self']
  obtain ⟨v, hv⟩ := hsep
  obtain ⟨d, hd, hvd⟩ := exists_natScale_mem_standardDividedLattice n v
  let I : (Fin n → RationalFiniteAdele) → ℂ :=
    fun z ↦ Complex.ofReal ((standardDividedLattice n c).indicator (fun _ ↦ (1 : ℝ)) z)
  let F := standardModulation v I
  have hcar : IsStandardCarried c F := (dividedIndicator_standard c).1.modulation v
  have hper : IsStandardPeriodic d F := by
    simpa using (dividedIndicator_standard c).2.modulation hvd
  have hF : F x ≠ F y := by
    have hFx : F x = (rationalFiniteAdeleFourierChar (dotProduct x v) : ℂ) := by
      simp [F, I, standardModulation, hx]
    have hFy : F y = (rationalFiniteAdeleFourierChar (dotProduct y v) : ℂ) := by
      simp [F, I, standardModulation, hy]
    rw [hFx, hFy]
    exact fun h ↦ hv (Subtype.ext h)
  obtain ⟨p, hp0, hp⟩ : ∃ p : ℂ → ℝ, p 0 = 0 ∧ p (F x) ≠ p (F y) := by
    by_cases hre : (F x).re = (F y).re
    · exact ⟨Complex.im, rfl, fun him ↦ hF (Complex.ext hre him)⟩
    · exact ⟨Complex.re, rfl, hre⟩
  refine ⟨fun z ↦ p (F z), d, hd, ?_, ?_, hp⟩
  · intro z hz
    dsimp only
    rw [hcar z hz, hp0, Complex.ofReal_zero]
  · intro z w hw
    dsimp only
    rw [hper z w hw]

/-- Separation on the literal fiber piece, using both coordinate projections.
The real projection alone is not claimed to be injective. -/
theorem gaussianCarrierTraceAlgebra_separatesPoints (L : PositiveDefiniteIntegralLattice n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) {c : ℕ} (hc : c ≠ 0) :
    (gaussianCarrierTraceAlgebra L b a hc).SeparatesPoints := by
  classical
  intro x y hxy
  by_cases hr : rationalAdeleVectorRealPart n x.val = rationalAdeleVectorRealPart n y.val
  · have hs : rationalAdeleVectorFinitePart n x.val ≠ rationalAdeleVectorFinitePart n y.val := by
      intro hs
      apply hxy
      apply Subtype.ext
      exact (rationalAdeleVectorRealFiniteEquiv n).injective (Prod.ext hr hs)
    obtain ⟨g, d, hd, hcar, hper, hg⟩ :=
      exists_real_standard_test_separating x.property.2 y.property.2 hs
    let f : realGaussianCore L b := ⟨fun z ↦
      realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n z) *
        g (rationalAdeleVectorFinitePart n z),
      Submodule.subset_span ⟨0, c, d, g, hc, hd, hcar, hper, rfl⟩⟩
    refine ⟨_, ⟨gaussianCarrierTrace L b a c f, ⟨f, rfl⟩, rfl⟩, ?_⟩
    change realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n x.val) * _ ≠
      realShiftedGaussian L b 0 (rationalAdeleVectorRealPart n y.val) * _
    rw [hr]
    exact fun h ↦ hg (mul_left_cancel₀ (realShiftedGaussian_pos L b 0 _).ne' h)
  · let u := rationalAdeleVectorRealPart n x.val
    let g : (Fin n → RationalFiniteAdele) → ℝ :=
      (standardDividedLattice n c).indicator (fun _ ↦ 1)
    let f : realGaussianCore L b := ⟨fun z ↦
      realShiftedGaussian L b u (rationalAdeleVectorRealPart n z) *
        g (rationalAdeleVectorFinitePart n z),
      Submodule.subset_span ⟨u, c, 1, g, hc, one_ne_zero,
        (dividedIndicator_standard c).1, (dividedIndicator_standard c).2, rfl⟩⟩
    refine ⟨_, ⟨gaussianCarrierTrace L b a c f, ⟨f, rfl⟩, rfl⟩, ?_⟩
    change realShiftedGaussian L b u (rationalAdeleVectorRealPart n x.val) * _ ≠
      realShiftedGaussian L b u (rationalAdeleVectorRealPart n y.val) * _
    simp only [g, Set.indicator_of_mem x.property.2, Set.indicator_of_mem y.property.2, mul_one,
      realShiftedGaussian_eq]
    have hself : SMSFormula.ShiftedGaussian.quadraticShiftedGaussian
        L.polarQuadraticForm L.continuous_polarQuadraticForm (Real.pi * b)
        (ContinuousMap.id _) u (rationalAdeleVectorRealPart n x.val) = 1 := by
      simp [SMSFormula.ShiftedGaussian.quadraticShiftedGaussian_apply, u]
    rw [hself]
    exact ne_of_gt (SMSFormula.ShiftedGaussian.quadraticShiftedGaussian_lt_one
      L.polarQuadraticForm L.continuous_polarQuadraticForm L.posDef_polarQuadraticForm
      (mul_pos Real.pi_pos hb) (ContinuousMap.id _) (Ne.symm hr))

/-- Stone--Weierstrass on the actual compact piece discharges density of the
actual image, without substituting a product model. -/
theorem dense_gaussianCarrierTrace (L : PositiveDefiniteIntegralLattice n) {b : ℝ} (hb : 0 < b)
    (a : RationalAdele) (c : ℕ) [NeZero c] :
    Dense ((gaussianCarrierTrace L b a c).range : Set C(adelicFiberCarrier L a c, ℝ)) :=
  SMSFormula.ShellLocalBound.dense_of_separatesPoints (gaussianCarrierTraceAlgebra L b a (NeZero.ne c))
    (gaussianCarrierTraceAlgebra_separatesPoints L hb a (NeZero.ne c))

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
