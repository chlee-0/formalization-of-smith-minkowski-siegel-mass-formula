import SMSFormula.AdelicGaussianRankFourDensityPositivity
import SMSFormula.AdelicGaussianFiberInvariance
import SMSFormula.RationalSpecialOrthogonalFullAdelicRealFiniteCarrier
import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeSummability
import SMSFormula.RationalAdeleArchimedeanGaussianRepresentation

/-!
# `SO(𝔸)`-invariance of the rank-four density

For `h ∈ SO(V)(𝔸)` with real and finite components `h_∞`, `h_f`
(`fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv`):
* `h · (x_∞, x_f) = (h_∞ x_∞, h_f x_f)` (`mulVec_join`);
* the finite quadratic value is `h_f`-invariant;
* the finite coordinate Haar is `h_f`-invariant on integrable tests
  (`integral_comp_finiteComponent`): pair with the `SO(ℝ)`-invariant polar Gaussian on the real
  factor, use the full-adelic Haar invariance and the product split, and cancel the nonzero
  Gaussian integral;
* the real orbit average absorbs `h_∞` (`realOrbitAverage_comp_mulVec`).
Hence every finite tube mass of `φ_{f∘h}` equals that of `φ_f`, and the rank-four density is
`SO(𝔸)`-invariant (`rankFourTracePositiveDensity_isSpecialOrthogonalInvariant`).  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

section Components

variable (V : RationalQuadraticSpaceMatrix n) (h : V.FullAdelicSpecialOrthogonalGroup)

/-- The real component of a full-adelic special orthogonal matrix. -/
def fullAdelicRealComponent : V.RealSpecialOrthogonalGroup :=
  (V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).1

/-- The finite component matrix. -/
def fullAdelicFiniteComponentMatrix : Matrix (Fin n) (Fin n) RationalFiniteAdele :=
  h.1.1.1.map (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)

theorem fullAdelicRealComponent_matrix :
    ((fullAdelicRealComponent V h).1.1.1 : Matrix (Fin n) (Fin n) ℝ) =
      h.1.1.1.map (rationalInfiniteAdeleRingEquivReal.toRingHom.comp
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)) := by
  unfold fullAdelicRealComponent
  rw [fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_apply_real_matrix, Matrix.map_map]
  rfl

theorem rationalAdeleVectorRealPart_mulVec (x : Fin n → RationalAdele) :
    rationalAdeleVectorRealPart n (h.1.1.1 *ᵥ x) =
      ((fullAdelicRealComponent V h).1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ
        rationalAdeleVectorRealPart n x := by
  rw [fullAdelicRealComponent_matrix]
  funext i
  exact RingHom.map_mulVec (rationalInfiniteAdeleRingEquivReal.toRingHom.comp
    (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)) h.1.1.1 x i

theorem rationalAdeleVectorFinitePart_mulVec (x : Fin n → RationalAdele) :
    rationalAdeleVectorFinitePart n (h.1.1.1 *ᵥ x) =
      fullAdelicFiniteComponentMatrix V h *ᵥ rationalAdeleVectorFinitePart n x := by
  funext i
  exact RingHom.map_mulVec (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) h.1.1.1 x i

theorem join_eq_of_parts (x : Fin n → RationalAdele) :
    rationalAdeleVectorJoin n (rationalAdeleVectorRealPart n x) (rationalAdeleVectorFinitePart n x) =
      x := by
  apply (rationalAdeleVectorRealFiniteEquiv n).injective
  rw [rationalAdeleVectorRealFiniteEquiv_join, rationalAdeleVectorRealFiniteEquiv_apply]

/-- `h · (x_∞, x_f) = (h_∞ x_∞, h_f x_f)`. -/
theorem mulVec_join (xr : Fin n → ℝ) (xf : Fin n → RationalFiniteAdele) :
    h.1.1.1 *ᵥ rationalAdeleVectorJoin n xr xf =
      rationalAdeleVectorJoin n (((fullAdelicRealComponent V h).1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ xr)
        (fullAdelicFiniteComponentMatrix V h *ᵥ xf) := by
  rw [← join_eq_of_parts (h.1.1.1 *ᵥ rationalAdeleVectorJoin n xr xf),
    rationalAdeleVectorRealPart_mulVec, rationalAdeleVectorFinitePart_mulVec,
    rationalAdeleVectorRealPart_join, rationalAdeleVectorFinitePart_join]

theorem finiteAdelicQuadraticFormValue_finiteComponent (xf : Fin n → RationalFiniteAdele) :
    V.finiteAdelicQuadraticFormValue (fullAdelicFiniteComponentMatrix V h *ᵥ xf) =
      V.finiteAdelicQuadraticFormValue xf := by
  have hq := congrArg Prod.snd
    (V.fullAdelicQuadraticFormValue_specialOrthogonal h (rationalAdeleVectorJoin n 0 xf))
  simp only [rationalAdeleVectorFinitePart_fullAdelicQuadraticFormValue] at hq
  rwa [rationalAdeleVectorFinitePart_mulVec, rationalAdeleVectorFinitePart_join] at hq

end Components

/-- `∫ G(x_∞) H(x_f)` over the full adeles is the product of the integrals. -/
theorem integral_realPart_mul_finitePart (G : (Fin n → ℝ) → ℂ) (H : (Fin n → RationalFiniteAdele) → ℂ) :
    ∫ x, G (rationalAdeleVectorRealPart n x) * H (rationalAdeleVectorFinitePart n x)
        ∂rationalAdeleCoordinateAddHaarMeasure n =
      (∫ y, G y) * ∫ w, H w ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
  letI : SigmaFinite (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
    rw [rationalFiniteAdeleCoordinateAddHaarMeasure]
    infer_instance
  have hp := measurePreserving_rationalAdeleVectorRealFiniteSplit n
  rw [← integral_prod_mul, ← hp.integral_comp (rationalAdeleVectorRealFiniteEquiv n).measurableEmbedding]
  rfl

/-- The finite Haar is invariant under the finite component, on integrable tests. -/
theorem integral_comp_finiteComponent (L : PositiveDefiniteIntegralLattice n)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (ψ : (Fin n → RationalFiniteAdele) → ℂ) :
    ∫ w, ψ (fullAdelicFiniteComponentMatrix _ h *ᵥ w) ∂rationalFiniteAdeleCoordinateAddHaarMeasure n =
      ∫ w, ψ w ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
  set ζ : (Fin n → ℝ) → ℂ := polarRealGaussian L (1 : ℂ) with hζ
  have hζ0 : (∫ y, ζ y) ≠ 0 := by
    rw [hζ, integral_polarRealGaussian (by simp) L]
    rw [Complex.one_cpow, div_one, one_pow, mul_one]
    refine inv_ne_zero ?_
    exact_mod_cast L.polarRealDeterminantScale_pos.ne'
  have hp : MeasurePreserving (fullAdelicMatrixUnitMeasurableEquiv h.1.1)
      (rationalAdeleCoordinateAddHaarMeasure n) (rationalAdeleCoordinateAddHaarMeasure n) :=
    L.rationalQuadraticSpaceMatrix.measurePreserving_fullAdelicSpecialOrthogonal_mulVec h
  have hi := hp.integral_comp' (fun x ↦ ζ (rationalAdeleVectorRealPart n x) *
    ψ (rationalAdeleVectorFinitePart n x))
  change (∫ x, ζ (rationalAdeleVectorRealPart n (h.1.1.1 *ᵥ x)) *
      ψ (rationalAdeleVectorFinitePart n (h.1.1.1 *ᵥ x)) ∂_) = _ at hi
  simp_rw [rationalAdeleVectorRealPart_mulVec, rationalAdeleVectorFinitePart_mulVec] at hi
  have hG : ∀ y, ζ (((fullAdelicRealComponent _ h).1.1.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) = ζ y :=
    fun y ↦ polarRealGaussian_realSpecialOrthogonal L 1 (fullAdelicRealComponent _ h) y
  simp_rw [hG] at hi
  rw [integral_realPart_mul_finitePart (G := ζ)
      (H := fun w ↦ ψ (fullAdelicFiniteComponentMatrix _ h *ᵥ w)),
    integral_realPart_mul_finitePart (G := ζ) (H := ψ)] at hi
  exact mul_left_cancel₀ hζ0 hi

/-- The finite section average of `f ∘ h` is that of `f` at `h_f x_f`. -/
theorem finiteSectionAverage_comp_specialOrthogonal (L : PositiveDefiniteIntegralLattice n) (x₀ : Fin n → ℝ)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (f : (Fin n → RationalAdele) → ℝ) (xf : Fin n → RationalFiniteAdele) :
    finiteSectionAverage L x₀ (fun x ↦ f (h.1.1.1 *ᵥ x)) xf =
      finiteSectionAverage L x₀ f (fullAdelicFiniteComponentMatrix _ h *ᵥ xf) := by
  unfold finiteSectionAverage
  simp_rw [mulVec_join]
  exact L.rationalQuadraticSpaceMatrix.realOrbitAverage_comp_mulVec x₀ (fullAdelicRealComponent _ h)
    (fun xr ↦ f (rationalAdeleVectorJoin n xr (fullAdelicFiniteComponentMatrix _ h *ᵥ xf)))

/-- Every finite tube mass is `SO(𝔸)`-invariant. -/
theorem finiteTubeMass_finiteSectionAverage_comp_specialOrthogonal (L : PositiveDefiniteIntegralLattice n)
    (x₀ : Fin n → ℝ) (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
    (f : (Fin n → RationalAdele) → ℝ) (w : ℕ) (M : ℤ) :
    L.finiteTubeMass (fun xf ↦ (finiteSectionAverage L x₀ (fun x ↦ f (h.1.1.1 *ᵥ x)) xf : ℂ)) w M =
      L.finiteTubeMass (fun xf ↦ (finiteSectionAverage L x₀ f xf : ℂ)) w M := by
  unfold finiteTubeMass
  congr 1
  set ψ : (Fin n → RationalFiniteAdele) → ℂ := fun y ↦ (finiteSectionAverage L x₀ f y : ℂ) *
    rationalFiniteAdeleIntegralIndicator (algebraMap ℚ RationalFiniteAdele ((w : ℚ))⁻¹ *
      (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue y -
        algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ))) with hψ
  have hfun : (fun xf ↦ (finiteSectionAverage L x₀ (fun x ↦ f (h.1.1.1 *ᵥ x)) xf : ℂ) *
      rationalFiniteAdeleIntegralIndicator (algebraMap ℚ RationalFiniteAdele ((w : ℚ))⁻¹ *
        (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue xf -
          algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))) =
      fun xf ↦ ψ (fullAdelicFiniteComponentMatrix _ h *ᵥ xf) := by
    funext xf
    rw [finiteSectionAverage_comp_specialOrthogonal, hψ]
    simp only
    rw [finiteAdelicQuadraticFormValue_finiteComponent]
  rw [hfun]
  exact integral_comp_finiteComponent L h ψ

/-- The rank-four density is `SO(𝔸)`-invariant. -/
theorem rankFourDensityLinearMap_comp_specialOrthogonal (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n)
    {M : ℤ} (hM : M ≠ 0) {b : ℝ} (hb : 0 ≤ b) (x₀ : Fin (n + 1) → ℝ) (cInf : ℝ)
    (h : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) (f : realGaussianCore L b) :
    rankFourDensityLinearMap L hn hM hb x₀ cInf ⟨fun x ↦ f.val (h.1.1.1.mulVec x),
      mem_realGaussianCore_comp_specialOrthogonal L b h f.property⟩ =
      rankFourDensityLinearMap L hn hM hb x₀ cInf f := by
  rw [rankFourDensityLinearMap_apply, rankFourDensityLinearMap_apply]
  unfold rankFourFiniteDensity
  simp_rw [finiteTubeMass_finiteSectionAverage_comp_specialOrthogonal]

theorem rankFourTracePositiveDensity_isSpecialOrthogonalInvariant (L : PositiveDefiniteIntegralLattice (n + 1))
    (hn : 3 ≤ n) {M : ℤ} (hM : M ≠ 0) {b : ℝ} (hb : 0 ≤ b) (x₀ : Fin (n + 1) → ℝ)
    (hx₀ : L.rationalQuadraticSpaceMatrix.realQuadraticFormValue x₀ = ((M : ℤ) : ℝ))
    {cInf : ℝ} (hc : 0 ≤ cInf) (a : RationalAdele) (ha : a = algebraMap ℚ RationalAdele ((M : ℤ) : ℚ)) :
    (rankFourTracePositiveDensity L hn hM hb x₀ hx₀ hc a ha).IsSpecialOrthogonalInvariant :=
  fun h f ↦ rankFourDensityLinearMap_comp_specialOrthogonal L hn hM hb x₀ cInf h f

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
