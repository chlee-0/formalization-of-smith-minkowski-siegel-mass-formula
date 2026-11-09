import SMSFormula.AdelicGaussianCarrierExtension
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!
# Gluing the actual value-density functional on the literal fiber

Every compact support lies in one divided carrier. The positive compact-piece
extensions agree whenever the same test is supported in two carriers, by passing
to their product. We select the unique scalar they specify, not an ambient test
extension or a fiber representative. This gives a positive functional on all
compactly supported continuous tests of the literal adelic fiber.
-/

noncomputable section
open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix CompactlySupported

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
variable {n : ℕ}

/-- A transparent name for the literal value fiber, with its subtype topology. -/
abbrev adelicValueFiber (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) :=
  {x : Fin n → RationalAdele // L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue x = a}

/-- Compact sets need only one of the old divided carriers. -/
theorem exists_dividedCarrier_of_isCompact {K : Set (Fin n → RationalFiniteAdele)}
    (hK : IsCompact K) : ∃ c : ℕ, c ≠ 0 ∧ K ⊆ standardDividedLattice n c := by
  let I := {c : ℕ // c ≠ 0}
  haveI : Nonempty I := ⟨⟨1, one_ne_zero⟩⟩
  obtain ⟨c, hc⟩ := hK.elim_directed_cover (fun c : I ↦ standardDividedLattice n c.val)
    (fun c ↦ isOpen_standardDividedLattice n c.val) (by
      intro x _
      obtain ⟨c, hc, hx⟩ := exists_natScale_mem_standardDividedLattice n x
      exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩, hx⟩) (by
      intro c d
      exact ⟨⟨c.val * d.val, mul_ne_zero c.property d.property⟩,
        dividedCarrier_subset_of_dvd (dvd_mul_right _ _),
        dividedCarrier_subset_of_dvd (dvd_mul_left _ _)⟩)
  exact ⟨c.val, c.property, hc⟩

/-- Literal inclusion of a compact carrier piece into the whole literal fiber. -/
def gaussianCarrierToFiber (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) (c : ℕ) :
    C(adelicFiberCarrier L a c, adelicValueFiber L a) :=
  subsetInclusionMap _ _ (fun _ hx ↦ hx.1)

theorem gaussianCarrierToFiber_val (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) (c : ℕ)
    (x : adelicFiberCarrier L a c) : (gaussianCarrierToFiber L a c x).val = x.val :=
  subsetInclusionMap_val _ _ _ x

/-- Restriction, with no chosen extension off the fiber or off the piece. -/
def fiberCarrierRestriction (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) (c : ℕ) :
    C(adelicValueFiber L a, ℝ) →ₗ[ℝ] C(adelicFiberCarrier L a c, ℝ) where
  toFun f := f.comp (gaussianCarrierToFiber L a c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A test vanishes off the indicated finite carrier, on the literal fiber. -/
def FiberCarried (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele) (c : ℕ)
    (f : adelicValueFiber L a → ℝ) : Prop :=
  ∀ x, rationalAdeleVectorFinitePart n x.val ∉ standardDividedLattice n c → f x = 0

theorem FiberCarried.mono {L : PositiveDefiniteIntegralLattice n} {a : RationalAdele} {c d : ℕ}
    {f : adelicValueFiber L a → ℝ} (hf : FiberCarried L a c f) (hcd : c ∣ d) :
    FiberCarried L a d f :=
  fun x hx ↦ hf x (fun h ↦ hx (dividedCarrier_subset_of_dvd hcd h))

/-- Compact support, not a global concentration assumption, supplies the carrier. -/
theorem exists_fiberCarried (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    (f : C_c(adelicValueFiber L a, ℝ)) : ∃ c : ℕ, c ≠ 0 ∧ FiberCarried L a c f := by
  have hS : Continuous (fun x : adelicValueFiber L a ↦ rationalAdeleVectorFinitePart n x.val) := by
    exact (show Continuous (rationalAdeleVectorFinitePart n) by
      unfold rationalAdeleVectorFinitePart; fun_prop).comp continuous_subtype_val
  obtain ⟨c, hc, hK⟩ := exists_dividedCarrier_of_isCompact (f.hasCompactSupport.image hS)
  refine ⟨c, hc, fun x hx ↦ ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  exact fun h ↦ hx (hK ⟨x, h, rfl⟩)

theorem fiberCarrierRestriction_restrict (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    {c d : ℕ} (hcd : c ∣ d) (f : C(adelicValueFiber L a, ℝ)) :
    (fiberCarrierRestriction L a d f).comp (gaussianCarrierInclusion L a hcd) =
      fiberCarrierRestriction L a c f := by
  apply ContinuousMap.ext
  intro x
  apply congrArg f
  apply Subtype.ext
  change (gaussianCarrierToFiber L a d (gaussianCarrierInclusion L a hcd x)).val =
    (gaussianCarrierToFiber L a c x).val
  rw [gaussianCarrierToFiber_val, gaussianCarrierToFiber_val, gaussianCarrierInclusion_val]

theorem fiberCarrierRestriction_mul_indicator (L : PositiveDefiniteIntegralLattice n) (a : RationalAdele)
    {c : ℕ} (hc : c ≠ 0) (d : ℕ) (f : C(adelicValueFiber L a, ℝ))
    (hf : FiberCarried L a c f) :
    fiberCarrierRestriction L a d f * gaussianCarrierIndicator L a hc d =
      fiberCarrierRestriction L a d f := by
  apply ContinuousMap.ext
  intro x
  change f (gaussianCarrierToFiber L a d x) *
    (standardDividedLattice n c).indicator (fun _ ↦ (1 : ℝ))
      (rationalAdeleVectorFinitePart n x.val) = f (gaussianCarrierToFiber L a d x)
  by_cases hx : rationalAdeleVectorFinitePart n x.val ∈ standardDividedLattice n c
  · rw [Set.indicator_of_mem hx, mul_one]
  · have hz := hf (gaussianCarrierToFiber L a d x) (by
      simpa only [gaussianCarrierToFiber_val] using hx)
    rw [hz, zero_mul]

/-- No change of functional value when a supporting carrier is enlarged. -/
theorem gaussianCarrierExtension_of_fiberCarried (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) {c d : ℕ} [NeZero c] [NeZero d]
    (hcd : c ∣ d) (f : C(adelicValueFiber L a, ℝ)) (hf : FiberCarried L a c f) :
    gaussianCarrierExtension L hn hb a d (fiberCarrierRestriction L a d f) =
      gaussianCarrierExtension L hn hb a c (fiberCarrierRestriction L a c f) := by
  have h := gaussianCarrierExtension_compatible L hn hb a hcd (fiberCarrierRestriction L a d f)
  rw [fiberCarrierRestriction_mul_indicator L a (NeZero.ne c) d f hf,
    fiberCarrierRestriction_restrict] at h
  exact h

/-- Any two supporting carriers give the same scalar. No nesting required. -/
theorem gaussianCarrierExtension_independent (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) {c d : ℕ} [NeZero c] [NeZero d]
    (f : C(adelicValueFiber L a, ℝ)) (hc : FiberCarried L a c f) (hd : FiberCarried L a d f) :
    gaussianCarrierExtension L hn hb a c (fiberCarrierRestriction L a c f) =
      gaussianCarrierExtension L hn hb a d (fiberCarrierRestriction L a d f) := by
  exact (gaussianCarrierExtension_of_fiberCarried L hn hb a (dvd_mul_right c d) f hc).symm.trans
    (gaussianCarrierExtension_of_fiberCarried L hn hb a (dvd_mul_left d c) f hd)

private theorem existsUnique_fiberValue (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n)
    {b : ℝ} (hb : 0 < b) (a : RationalAdele) (f : C_c(adelicValueFiber L a, ℝ)) :
    ∃! r : ℝ, ∀ (c : ℕ) (hc : c ≠ 0), FiberCarried L a c f →
      r = @gaussianCarrierExtension n L hn b hb a c ⟨hc⟩ (fiberCarrierRestriction L a c f.toContinuousMap) := by
  obtain ⟨c, hc, hf⟩ := exists_fiberCarried L a f
  letI : NeZero c := ⟨hc⟩
  refine ⟨gaussianCarrierExtension L hn hb a c (fiberCarrierRestriction L a c f.toContinuousMap), ?_, ?_⟩
  · intro d hd hfd
    letI : NeZero d := ⟨hd⟩
    exact gaussianCarrierExtension_independent L hn hb a f.toContinuousMap hf hfd
  · intro r hr
    exact hr c hc hf

/-- The unique scalar specified by all supporting carriers. No carrier is selected. -/
def gaussianFiberValue (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {b : ℝ} (hb : 0 < b)
    (a : RationalAdele) (f : C_c(adelicValueFiber L a, ℝ)) : ℝ :=
  (existsUnique_fiberValue L hn hb a f).exists.choose

theorem gaussianFiberValue_eq (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {b : ℝ} (hb : 0 < b)
    (a : RationalAdele) (f : C_c(adelicValueFiber L a, ℝ)) (c : ℕ) [NeZero c]
    (hf : FiberCarried L a c f) :
    gaussianFiberValue L hn hb a f =
      gaussianCarrierExtension L hn hb a c (fiberCarrierRestriction L a c f.toContinuousMap) :=
  (existsUnique_fiberValue L hn hb a f).exists.choose_spec c (NeZero.ne c) hf

theorem gaussianFiberValue_add (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {b : ℝ} (hb : 0 < b)
    (a : RationalAdele) (f g : C_c(adelicValueFiber L a, ℝ)) :
    gaussianFiberValue L hn hb a (f + g) = gaussianFiberValue L hn hb a f + gaussianFiberValue L hn hb a g := by
  obtain ⟨c, hc, hf⟩ := exists_fiberCarried L a f
  obtain ⟨d, hd, hg⟩ := exists_fiberCarried L a g
  letI : NeZero (c*d) := ⟨mul_ne_zero hc hd⟩
  have hf' := hf.mono (dvd_mul_right c d)
  have hg' := hg.mono (dvd_mul_left d c)
  have hsum : FiberCarried L a (c*d) (f+g) := fun x hx ↦ by
    change f x + g x = 0
    rw [hf' x hx, hg' x hx, add_zero]
  rw [gaussianFiberValue_eq L hn hb a (f+g) (c*d) hsum,
    gaussianFiberValue_eq L hn hb a f (c*d) hf', gaussianFiberValue_eq L hn hb a g (c*d) hg']
  change gaussianCarrierExtension L hn hb a (c*d)
    (fiberCarrierRestriction L a (c*d) (f.toContinuousMap + g.toContinuousMap)) = _
  rw [map_add, map_add]

theorem gaussianFiberValue_smul (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {b : ℝ} (hb : 0 < b)
    (a : RationalAdele) (r : ℝ) (f : C_c(adelicValueFiber L a, ℝ)) :
    gaussianFiberValue L hn hb a (r • f) = r * gaussianFiberValue L hn hb a f := by
  obtain ⟨c, hc, hf⟩ := exists_fiberCarried L a f
  letI : NeZero c := ⟨hc⟩
  have hsmul : FiberCarried L a c (r • f) := fun x hx ↦ by
    change r * f x = 0
    rw [hf x hx, mul_zero]
  rw [gaussianFiberValue_eq L hn hb a (r • f) c hsmul, gaussianFiberValue_eq L hn hb a f c hf]
  change gaussianCarrierExtension L hn hb a c (fiberCarrierRestriction L a c (r • f.toContinuousMap)) = _
  rw [map_smul, map_smul, smul_eq_mul]

/-- The actual glued functional on all compactly supported continuous fiber tests. -/
def gaussianFiberFunctional (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {b : ℝ} (hb : 0 < b)
    (a : RationalAdele) : C_c(adelicValueFiber L a, ℝ) →ₚ[ℝ] ℝ where
  toFun := gaussianFiberValue L hn hb a
  map_add' := gaussianFiberValue_add L hn hb a
  map_smul' := gaussianFiberValue_smul L hn hb a
  monotone' := by
    intro f g hfg
    obtain ⟨c, hc, hf⟩ := exists_fiberCarried L a f
    obtain ⟨d, hd, hg⟩ := exists_fiberCarried L a g
    letI : NeZero (c*d) := ⟨mul_ne_zero hc hd⟩
    rw [gaussianFiberValue_eq L hn hb a f (c*d) (hf.mono (dvd_mul_right c d)),
      gaussianFiberValue_eq L hn hb a g (c*d) (hg.mono (dvd_mul_left d c))]
    have h := gaussianCarrierExtension_nonneg L hn hb a (c*d)
      (fiberCarrierRestriction L a (c*d) g.toContinuousMap -
        fiberCarrierRestriction L a (c*d) f.toContinuousMap)
      (fun x ↦ sub_nonneg.mpr (hfg (gaussianCarrierToFiber L a (c*d) x)))
    rw [map_sub] at h
    exact sub_nonneg.mp h

theorem gaussianFiberFunctional_eq (L : PositiveDefiniteIntegralLattice n) (hn : 4 < n) {b : ℝ} (hb : 0 < b)
    (a : RationalAdele) (f : C_c(adelicValueFiber L a, ℝ)) (c : ℕ) [NeZero c]
    (hf : FiberCarried L a c f) :
    gaussianFiberFunctional L hn hb a f =
      gaussianCarrierExtension L hn hb a c (fiberCarrierRestriction L a c f.toContinuousMap) :=
  gaussianFiberValue_eq L hn hb a f c hf

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
