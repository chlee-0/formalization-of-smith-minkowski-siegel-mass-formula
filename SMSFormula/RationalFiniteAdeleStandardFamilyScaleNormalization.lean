import SMSFormula.RationalFiniteAdeleStandardFamilyCovariance
import SMSFormula.RationalFiniteAdeleIntegralLatticeFiniteQuotient

/-!
# Scale normalization of the standard compact family

The remaining half of the compliant Poisson route is the spanning statement over
the literal finite quotient.  This file removes the first of the two scales from
that problem: every member with scales `(c, d)`, `c` nonzero, is the `c`-scaling
pullback of a member with scales `(1, c * d)`, and the correspondence is an exact
mutual inverse.

So the spanning question only ever has to be settled for tests carried by the
standard lattice itself and periodic modulo one dilate of it, which is exactly
the setting of the existing `addQuotientPeriodicLift` quotient machinery.

Only the existing rational scaling of finite-adelic coordinates is used.  No
representative, section, quotient construction, subgroup, cutoff, conductor,
chart, Haar normalization or new additive character is introduced, and no Haar
measure is rescaled: this file makes no measure-theoretic statement at all.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## The scaling pullback -/

/-- Pull a finite test back along the `c`-scaling: `x` goes to `f (x / c)`. -/
def standardScalePullback (c : ℕ) (f : (Fin n → RationalFiniteAdele) → ℂ) :
    (Fin n → RationalFiniteAdele) → ℂ :=
  fun x => f (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ x)

/-- Push a finite test forward along the `c`-scaling: `x` goes to `f (c * x)`. -/
def standardScalePushforward (c : ℕ) (f : (Fin n → RationalFiniteAdele) → ℂ) :
    (Fin n → RationalFiniteAdele) → ℂ :=
  fun x => f (c • x)

theorem rationalFiniteAdeleCoordinateScale_inv_nsmul {c : ℕ} (hc : c ≠ 0)
    (x : Fin n → RationalFiniteAdele) :
    rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ (c • x) = x := by
  have hq : ((c : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  rw [← rationalFiniteAdeleCoordinateScale_natCast,
    rationalFiniteAdeleCoordinateScale_trans, inv_mul_cancel₀ hq,
    rationalFiniteAdeleCoordinateScale_one]

theorem rationalFiniteAdeleCoordinateScale_inv_mul_nsmul {c d : ℕ} (hc : c ≠ 0)
    (x : Fin n → RationalFiniteAdele) :
    rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ ((c * d) • x) = d • x := by
  have hq : ((c : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  rw [← rationalFiniteAdeleCoordinateScale_natCast,
    rationalFiniteAdeleCoordinateScale_trans,
    ← rationalFiniteAdeleCoordinateScale_natCast]
  congr 1
  push_cast
  field_simp

/-! ## Exact mutual inverses -/

@[simp]
theorem standardScalePushforward_standardScalePullback {c : ℕ} (hc : c ≠ 0)
    (f : (Fin n → RationalFiniteAdele) → ℂ) :
    standardScalePushforward c (standardScalePullback c f) = f := by
  funext x
  show f (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ (c • x)) = f x
  rw [rationalFiniteAdeleCoordinateScale_inv_nsmul hc]

@[simp]
theorem standardScalePullback_standardScalePushforward {c : ℕ} (hc : c ≠ 0)
    (f : (Fin n → RationalFiniteAdele) → ℂ) :
    standardScalePullback c (standardScalePushforward c f) = f := by
  have hq : ((c : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  funext x
  show f (c • rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ x) = f x
  rw [← rationalFiniteAdeleCoordinateScale_natCast,
    rationalFiniteAdeleCoordinateScale_trans, mul_inv_cancel₀ hq,
    rationalFiniteAdeleCoordinateScale_one]

/-! ## The scales transform exactly -/

/-- Pulling back by `c` normalizes the carrier scale to one. -/
theorem IsStandardCarried.scalePullback {c : ℕ} (hc : c ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardCarried c f) :
    IsStandardCarried 1 (standardScalePullback c f) := by
  intro x hx
  refine hf _ fun hmem => hx ?_
  show (1 : ℕ) • x ∈ integralFiniteAdeleVectors n
  rw [one_smul]
  have hval : c • rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ x = x := by
    have hq : ((c : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
    rw [← rationalFiniteAdeleCoordinateScale_natCast,
      rationalFiniteAdeleCoordinateScale_trans, mul_inv_cancel₀ hq,
      rationalFiniteAdeleCoordinateScale_one]
  have hmem' : c • rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ x ∈
    integralFiniteAdeleVectors n := hmem
  rwa [hval] at hmem'

/-- Pulling back by `c` multiplies the period scale by `c`. -/
theorem IsStandardPeriodic.scalePullback {c d : ℕ} (hc : c ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardPeriodic d f) :
    IsStandardPeriodic (c * d) (standardScalePullback c f) := by
  intro x u hu
  show f (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ (x + (c * d) • u)) =
    f (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ x)
  have hsplit : rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ (x + (c * d) • u) =
      rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ x + d • u := by
    rw [← rationalFiniteAdeleCoordinateScale_inv_mul_nsmul (c := c) (d := d) hc u]
    funext i
    simp [rationalFiniteAdeleCoordinateScale, mul_add]
  rw [hsplit]
  exact hf _ u hu

private theorem carried_precomp_of_preimage
    {A B : Type*} (S : Set A) (T : Set B) (g : B → A) (f : A → ℂ)
    (hmap : ∀ x, g x ∈ S → x ∈ T)
    (hf : ∀ y, y ∉ S → f y = 0) :
    ∀ x, x ∉ T → f (g x) = 0 :=
  fun x hx => hf (g x) (fun hmem => hx (hmap x hmem))

private theorem standardDividedLattice_one_eq_integral :
    standardDividedLattice n 1 = integralFiniteAdeleVectors n := by
  ext x
  change (1 : ℕ) • x ∈ integralFiniteAdeleVectors n ↔
    x ∈ integralFiniteAdeleVectors n
  rw [one_smul]

set_option backward.isDefEq.respectTransparency false in
/-- Pushing forward by `c` restores the carrier scale. -/
theorem IsStandardCarried.scalePushforward {c : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardCarried 1 f) :
    IsStandardCarried c (standardScalePushforward c f) := by
  have hf0 : ∀ y, y ∉ integralFiniteAdeleVectors n → f y = 0 := by
    simpa only [IsStandardCarried, standardDividedLattice_one_eq_integral] using hf
  exact carried_precomp_of_preimage
    (integralFiniteAdeleVectors n) (standardDividedLattice n c)
    (fun x => c • x) f (fun _ hmem => hmem) hf0

/-- Pushing forward by `c` divides the period scale by `c`. -/
theorem IsStandardPeriodic.scalePushforward {c d : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardPeriodic (c * d) f) :
    IsStandardPeriodic d (standardScalePushforward c f) := by
  intro x u hu
  show f (c • (x + d • u)) = f (c • x)
  rw [smul_add, ← mul_nsmul' u c d]
  exact hf (c • x) u hu

/-! ## Normalization of the spanning problem -/

/-- Scale normalization: for nonzero `c`, the family at scales `(c, d)` is
carried isomorphically onto the family at scales `(1, c * d)` by the existing
rational scaling, with the two directions exact mutual inverses.  The spanning
question therefore only has to be settled at carrier scale one. -/
theorem standardScalePullback_normalizes {c d : ℕ} (hc : c ≠ 0)
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    IsStandardCarried 1 (standardScalePullback c f) ∧
      IsStandardPeriodic (c * d) (standardScalePullback c f) ∧
      standardScalePushforward c (standardScalePullback c f) = f :=
  ⟨hcarried.scalePullback hc, hperiodic.scalePullback hc,
    standardScalePushforward_standardScalePullback hc f⟩

theorem standardScalePushforward_normalizes {c d : ℕ} (hc : c ≠ 0)
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried 1 g) (hperiodic : IsStandardPeriodic (c * d) g) :
    IsStandardCarried c (standardScalePushforward c g) ∧
      IsStandardPeriodic d (standardScalePushforward c g) ∧
      standardScalePullback c (standardScalePushforward c g) = g :=
  ⟨hcarried.scalePushforward, hperiodic.scalePushforward,
    standardScalePullback_standardScalePushforward hc g⟩

/-! ## Handing the normalized problem to the existing quotient machinery -/

/-- A scale-one family member restricts to the integral coordinate subtype as a
function periodic modulo the `N`-dilation range.  This is exactly the
hypothesis the existing section-free quotient machinery consumes. -/
theorem isStandardPeriodic_integralRestriction {N : ℕ}
    {g : (Fin n → RationalFiniteAdele) → ℂ} (hg : IsStandardPeriodic N g)
    (x z : Fin n → IntegralFiniteAdele)
    (hz : z ∈ (integralFiniteAdeleCoordinateNatDilation n N).range) :
    g (fun i => (((x + z) i : IntegralFiniteAdele) : RationalFiniteAdele)) =
      g (fun i => ((x i : IntegralFiniteAdele) : RationalFiniteAdele)) := by
  obtain ⟨y, rfl⟩ := hz
  have hya : (fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) ∈
      integralFiniteAdeleVectors n := fun i => (y i).property
  have harg :
      (fun i => (((x + integralFiniteAdeleCoordinateNatDilation n N y) i :
        IntegralFiniteAdele) : RationalFiniteAdele)) =
      (fun i => ((x i : IntegralFiniteAdele) : RationalFiniteAdele)) +
        N • (fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) := rfl
  rw [harg]
  exact hg _ _ hya

/-- The section-free descent of a scale-one family member to the literal finite
quotient `Zhat^n / N * Zhat^n`.  It is built by the quotient eliminator through
the existing `addQuotientPeriodicLift`, so it stores no residue representative
and no section. -/
noncomputable def standardFamilyQuotientLift {N : ℕ}
    (g : (Fin n → RationalFiniteAdele) → ℂ) (hg : IsStandardPeriodic N g) :
    ((Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range) → ℂ :=
  addQuotientPeriodicLift (integralFiniteAdeleCoordinateNatDilation n N).range
    (fun x => g (fun i => ((x i : IntegralFiniteAdele) : RationalFiniteAdele)))
    (isStandardPeriodic_integralRestriction hg)

@[simp]
theorem standardFamilyQuotientLift_coe {N : ℕ}
    (g : (Fin n → RationalFiniteAdele) → ℂ) (hg : IsStandardPeriodic N g)
    (x : Fin n → IntegralFiniteAdele) :
    standardFamilyQuotientLift g hg (x : (Fin n → IntegralFiniteAdele) ⧸
        (integralFiniteAdeleCoordinateNatDilation n N).range) =
      g (fun i => ((x i : IntegralFiniteAdele) : RationalFiniteAdele)) :=
  rfl

/-- On the standard lattice a scale-one family member is its quotient descent.
This is the descent half of the spanning statement. -/
theorem standardScaleOne_eq_quotientLift_of_mem {N : ℕ}
    {g : (Fin n → RationalFiniteAdele) → ℂ} (hg : IsStandardPeriodic N g)
    {x : Fin n → RationalFiniteAdele} (hx : x ∈ integralFiniteAdeleVectors n) :
    g x =
      standardFamilyQuotientLift g hg
        ((fun i => (⟨x i, hx i⟩ : IntegralFiniteAdele)) :
          (Fin n → IntegralFiniteAdele) ⧸
            (integralFiniteAdeleCoordinateNatDilation n N).range) :=
  rfl

/-- Off the standard lattice a scale-one family member vanishes. -/
theorem standardScaleOne_eq_zero_of_not_mem
    {g : (Fin n → RationalFiniteAdele) → ℂ} (hcarried : IsStandardCarried 1 g)
    {x : Fin n → RationalFiniteAdele} (hx : x ∉ integralFiniteAdeleVectors n) :
    g x = 0 := by
  refine hcarried x ?_
  intro hmem
  exact hx (by simpa using hmem)

end RationalQuadraticSpaceMatrix
