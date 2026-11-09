import SMSFormula.RationalFiniteAdeleStandardFamilyScaleNormalization

/-!
# The spanning statement for the standard compact family

This completes the remaining half of the compliant Poisson route.  A scale-one
family member was already known to descend to the literal finite quotient
`Zhat^n / N * Zhat^n`.  Here it is written as the finite sum of its descent
values against coset indicators, and the indicators themselves are defined
without choosing a residue representative: the indicator of a class is the
indicator of the literal image of that class under the existing coordinate
inclusion.

The finite-index and `Fintype` instances for the coordinate dilation range are
the existing ones.  No representative, section, new subgroup, cutoff, conductor,
chart, Haar normalization or additive character is introduced, and this file
makes no measure-theoretic statement.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-! ## Coset sets without representatives -/

/-- The literal image in ambient finite-adelic vectors of a class of the
`N`-dilated standard lattice.  The class is used directly; no representative is
chosen. -/
def standardCosetSet (n N : ℕ)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range) :
    Set (Fin n → RationalFiniteAdele) :=
  (fun (y : Fin n → IntegralFiniteAdele) (i : Fin n) =>
    ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) ''
      {y | (y : (Fin n → IntegralFiniteAdele) ⧸
        (integralFiniteAdeleCoordinateNatDilation n N).range) = alpha}

theorem mem_standardCosetSet_imp_integral {N : ℕ}
    {alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range}
    {x : Fin n → RationalFiniteAdele} (hx : x ∈ standardCosetSet n N alpha) :
    x ∈ integralFiniteAdeleVectors n := by
  obtain ⟨y, -, rfl⟩ := hx
  exact fun i => (y i).property

theorem mem_standardCosetSet_iff_of_mem {N : ℕ}
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range)
    {x : Fin n → RationalFiniteAdele} (hx : x ∈ integralFiniteAdeleVectors n) :
    x ∈ standardCosetSet n N alpha ↔
      (((fun i => (⟨x i, hx i⟩ : IntegralFiniteAdele)) :
        Fin n → IntegralFiniteAdele) :
        (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range) = alpha := by
  constructor
  · rintro ⟨y, hy, hcoe⟩
    have hyx : y = fun i => (⟨x i, hx i⟩ : IntegralFiniteAdele) := by
      funext i
      apply Subtype.ext
      exact congrFun hcoe i
    rwa [hyx] at hy
  · intro hclass
    exact ⟨fun i => (⟨x i, hx i⟩ : IntegralFiniteAdele), hclass, rfl⟩

/-- The indicator of a class, built from the class alone. -/
def standardCosetIndicator (n N : ℕ)
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range) :
    (Fin n → RationalFiniteAdele) → ℂ :=
  (standardCosetSet n N alpha).indicator 1

theorem standardCosetIndicator_of_not_integral {N : ℕ}
    (alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range)
    {x : Fin n → RationalFiniteAdele} (hx : x ∉ integralFiniteAdeleVectors n) :
    standardCosetIndicator n N alpha x = 0 :=
  Set.indicator_of_notMem (fun hmem => hx (mem_standardCosetSet_imp_integral hmem)) _

theorem standardCosetIndicator_self {N : ℕ}
    {x : Fin n → RationalFiniteAdele} (hx : x ∈ integralFiniteAdeleVectors n) :
    standardCosetIndicator n N
        (((fun i => (⟨x i, hx i⟩ : IntegralFiniteAdele)) :
          Fin n → IntegralFiniteAdele) :
          (Fin n → IntegralFiniteAdele) ⧸
            (integralFiniteAdeleCoordinateNatDilation n N).range) x = 1 :=
  Set.indicator_of_mem ((mem_standardCosetSet_iff_of_mem _ hx).mpr rfl) _

theorem standardCosetIndicator_of_ne {N : ℕ}
    {alpha : (Fin n → IntegralFiniteAdele) ⧸
      (integralFiniteAdeleCoordinateNatDilation n N).range}
    {x : Fin n → RationalFiniteAdele} (hx : x ∈ integralFiniteAdeleVectors n)
    (hne : alpha ≠
      (((fun i => (⟨x i, hx i⟩ : IntegralFiniteAdele)) :
        Fin n → IntegralFiniteAdele) :
        (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range)) :
    standardCosetIndicator n N alpha x = 0 := by
  refine Set.indicator_of_notMem (fun hmem => ?_) _
  exact hne ((mem_standardCosetSet_iff_of_mem alpha hx).mp hmem).symm

/-! ## The finite-sum spanning statement -/

/-- Spanning, at carrier scale one: a family member is the finite sum over the
literal quotient of its descent values against coset indicators.  No residue
representative is chosen anywhere. -/
theorem standardScaleOne_eq_sum_cosetIndicator {N : ℕ} [NeZero N]
    {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried 1 g) (hperiodic : IsStandardPeriodic N g) :
    g = fun x => ∑ alpha, standardFamilyQuotientLift g hperiodic alpha *
      standardCosetIndicator n N alpha x := by
  funext x
  by_cases hx : x ∈ integralFiniteAdeleVectors n
  · rw [Finset.sum_eq_single
      (((fun i => (⟨x i, hx i⟩ : IntegralFiniteAdele)) :
        Fin n → IntegralFiniteAdele) :
        (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range)]
    · rw [standardCosetIndicator_self hx, mul_one,
        standardFamilyQuotientLift_coe]
    · intro alpha _ hne
      rw [standardCosetIndicator_of_ne hx hne, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [standardScaleOne_eq_zero_of_not_mem hcarried hx]
    symm
    apply Finset.sum_eq_zero
    intro alpha _
    rw [standardCosetIndicator_of_not_integral alpha hx, mul_zero]

/-- Spanning at general scales: after the existing `c`-scaling normalization,
every family member with nonzero scales is a finite combination of coset
indicators over the literal quotient at level `c * d`. -/
theorem standardScalePullback_eq_sum_cosetIndicator {c d : ℕ} (hc : c ≠ 0)
    [NeZero (c * d)]
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f) :
    standardScalePullback c f =
      fun x => ∑ alpha, standardFamilyQuotientLift (standardScalePullback c f)
        (hperiodic.scalePullback hc) alpha *
        standardCosetIndicator n (c * d) alpha x :=
  standardScaleOne_eq_sum_cosetIndicator (hcarried.scalePullback hc)
    (hperiodic.scalePullback hc)

/-! ## Coset indicators are literal translates -/

/-- The indicator of the `N`-dilated standard lattice. -/
def standardDilatedIndicator (n N : ℕ) : (Fin n → RationalFiniteAdele) → ℂ :=
  (standardDilatedLattice n N).indicator 1

/-- Membership in the class image is exactly membership of the difference in the
dilated lattice, for every member `y` of the class.  Nothing is chosen: the
statement quantifies over all members. -/
theorem mem_standardCosetSet_iff_sub_mem (n N : ℕ)
    (y : Fin n → IntegralFiniteAdele) (x : Fin n → RationalFiniteAdele) :
    x ∈ standardCosetSet n N
        ((y : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range)) ↔
      x - (fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) ∈
        standardDilatedLattice n N := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hsub : z - y ∈ (integralFiniteAdeleCoordinateNatDilation n N).range :=
      QuotientAddGroup.eq_iff_sub_mem.mp hz
    obtain ⟨w, hw⟩ := hsub
    refine ⟨fun i => ((w i : IntegralFiniteAdele) : RationalFiniteAdele),
      fun i => (w i).property, ?_⟩
    funext i
    have hwi : (integralFiniteAdeleCoordinateNatDilation n N w) i = (z - y) i :=
      congrFun hw i
    have hval := congrArg (fun t : IntegralFiniteAdele => (t : RationalFiniteAdele)) hwi
    simpa [integralFiniteAdeleCoordinateNatDilation] using hval
  · rintro ⟨u, hu, hxu⟩
    refine ⟨y + integralFiniteAdeleCoordinateNatDilation n N
      (fun i => (⟨u i, hu i⟩ : IntegralFiniteAdele)), ?_, ?_⟩
    · refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      simp
    · funext i
      have hxi : (N : ℕ) • u i =
          x i - ((y i : IntegralFiniteAdele) : RationalFiniteAdele) := congrFun hxu i
      show (((y + integralFiniteAdeleCoordinateNatDilation n N
        (fun i => (⟨u i, hu i⟩ : IntegralFiniteAdele))) i :
          IntegralFiniteAdele) : RationalFiniteAdele) = x i
      show ((y i : IntegralFiniteAdele) : RationalFiniteAdele) +
        (N : ℕ) • u i = x i
      rw [hxi]
      ring

/-- Each coset indicator is a literal translate of the dilated-lattice
indicator, for every member of the class.  Combined with the already closed
translation covariance this makes the actual finite Fourier transform of every
piece of the spanning decomposition explicit. -/
theorem standardCosetIndicator_eq_translate (n N : ℕ)
    (y : Fin n → IntegralFiniteAdele) :
    standardCosetIndicator n N
        ((y : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range)) =
      fun x => standardDilatedIndicator n N
        (x - fun i => ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) := by
  funext x
  by_cases hx : x ∈ standardCosetSet n N
      ((y : (Fin n → IntegralFiniteAdele) ⧸
        (integralFiniteAdeleCoordinateNatDilation n N).range))
  · rw [standardCosetIndicator, Set.indicator_of_mem hx,
      standardDilatedIndicator,
      Set.indicator_of_mem ((mem_standardCosetSet_iff_sub_mem n N y x).mp hx)]
    rfl
  · rw [standardCosetIndicator, Set.indicator_of_notMem hx,
      standardDilatedIndicator,
      Set.indicator_of_notMem
        (fun hmem => hx ((mem_standardCosetSet_iff_sub_mem n N y x).mpr hmem))]

end RationalQuadraticSpaceMatrix
