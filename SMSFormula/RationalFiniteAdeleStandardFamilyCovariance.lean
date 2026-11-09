import SMSFormula.RationalFiniteAdeleStandardCompactFamily

/-!
# Translation and modulation covariance of the standard compact family

Poisson summation on the enlarged orbit needs a general family member related
to the standard indicator.  Two routes exist: decompose the periodic finite
weight over residue representatives, or use the covariance of the actual finite Fourier
transform under translation and modulation, which needs no representative,
section, coset decomposition or new structure at all.  This file develops the
second route.

For `v` in the `c'`-divided standard lattice the two operations are the literal
translation `f (· + v)` and the literal modulation by the existing finite
additive character at frequency `v`.  Both keep the family with explicit scales,

```text
translation : (c, d) |-> (c * c', d)
modulation  : (c, d) |-> (c, d * c')
```

and the actual finite Fourier transform interchanges them: translation becomes a
character factor, modulation becomes a frequency shift.

No residue representative, quotient section, coset decomposition, new subgroup,
cutoff, conductor, chart, Haar normalization or new additive character is
introduced.  No Poisson identity or theta transformation is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix
open scoped BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

attribute [local instance]
  rationalFiniteAdeleCoordinateAddHaarMeasure_isAddLeftInvariant''

/-! ## Translation -/

/-- Translation keeps the carrier condition, multiplying the scale by the
scale of the translation vector. -/
theorem IsStandardCarried.translate {c c' : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardCarried c f)
    {v : Fin n → RationalFiniteAdele} (hv : v ∈ standardDividedLattice n c') :
    IsStandardCarried (c * c') (fun x => f (x + v)) := by
  intro x hx
  refine hf (x + v) fun hmem => hx ?_
  intro i
  have hsplit : ((c * c') • x) i =
      c' • ((c • (x + v)) i) - c • ((c' • v) i) := by
    simp only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, Nat.cast_mul]
    ring
  rw [hsplit]
  exact integralFiniteAdeleSubring.sub_mem
    (integralFiniteAdeleSubring.nsmul_mem (hmem i) c')
    (integralFiniteAdeleSubring.nsmul_mem (hv i) c)

/-- Translation keeps the period scale unchanged. -/
theorem IsStandardPeriodic.translate {d : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardPeriodic d f)
    (v : Fin n → RationalFiniteAdele) :
    IsStandardPeriodic d (fun x => f (x + v)) := by
  intro x u hu
  show f (x + d • u + v) = f (x + v)
  rw [add_right_comm]
  exact hf (x + v) u hu

/-! ## Modulation -/

/-- Modulation of a finite test by the existing additive character at a fixed
finite-adelic frequency. -/
def standardModulation (v : Fin n → RationalFiniteAdele)
    (f : (Fin n → RationalFiniteAdele) → ℂ) :
    (Fin n → RationalFiniteAdele) → ℂ :=
  fun x => (rationalFiniteAdeleFourierChar (dotProduct x v) : ℂ) * f x

/-- Modulation keeps the carrier scale unchanged. -/
theorem IsStandardCarried.modulation {c : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardCarried c f)
    (v : Fin n → RationalFiniteAdele) :
    IsStandardCarried c (standardModulation v f) := by
  intro x hx
  show (rationalFiniteAdeleFourierChar (dotProduct x v) : ℂ) * f x = 0
  rw [hf x hx, mul_zero]

/-- Modulation keeps the period condition, multiplying the period scale by the
scale of the modulation frequency. -/
theorem IsStandardPeriodic.modulation {d c' : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ} (hf : IsStandardPeriodic d f)
    {v : Fin n → RationalFiniteAdele} (hv : v ∈ standardDividedLattice n c') :
    IsStandardPeriodic (d * c') (standardModulation v f) := by
  intro x u hu
  have hfx : f (x + (d * c') • u) = f x :=
    (hf.mono ⟨c', rfl⟩) x u hu
  have hchar : rationalFiniteAdeleFourierChar (dotProduct ((d * c') • u) v) = 1 := by
    have hmem : dotProduct ((d * c') • u) v ∈ integralFiniteAdeleSubring := by
      have hrw : dotProduct ((d * c') • u) v = d • dotProduct u (c' • v) := by
        rw [dotProduct_nsmul_comm, nsmul_dotProduct_eq, nsmul_dotProduct_eq]
        push_cast
        ring
      rw [hrw]
      refine integralFiniteAdeleSubring.nsmul_mem ?_ d
      rw [dotProduct]
      exact Subring.sum_mem integralFiniteAdeleSubring fun i _ =>
        integralFiniteAdeleSubring.mul_mem (hu i) (hv i)
    exact rationalFiniteAdeleFourierChar_eq_one_of_mem_integral _ hmem
  show (rationalFiniteAdeleFourierChar (dotProduct (x + (d * c') • u) v) : ℂ) *
    f (x + (d * c') • u) = _
  rw [hfx, add_dotProduct, AddChar.map_add_eq_mul, hchar, mul_one]
  rfl

/-! ## The Fourier transform interchanges the two -/

/-- Translating the test multiplies its actual finite Fourier transform by the
existing character at the translation vector.  Only Haar translation invariance
is used; no measure is rescaled. -/
theorem standardFiniteFourier_translate
    (f : (Fin n → RationalFiniteAdele) → ℂ) (v w : Fin n → RationalFiniteAdele) :
    standardFiniteFourier (fun x => f (x + v)) w =
      (rationalFiniteAdeleFourierChar (dotProduct v w) : ℂ) *
        standardFiniteFourier f w := by
  have hshift := integral_add_right_eq_self
    (μ := rationalFiniteAdeleCoordinateAddHaarMeasure n)
    (fun x => (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) * f x) v
  calc
    standardFiniteFourier (fun x => f (x + v)) w =
        ∫ x, (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) * f (x + v)
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := rfl
    _ = ∫ x, (rationalFiniteAdeleFourierChar (dotProduct v w) : ℂ) *
          ((rationalFiniteAdeleFourierChar (-(dotProduct (x + v) w)) : ℂ) * f (x + v))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
        refine integral_congr_ae ?_
        filter_upwards with x
        have hsplit : rationalFiniteAdeleFourierChar (-(dotProduct x w)) =
            rationalFiniteAdeleFourierChar (dotProduct v w) *
              rationalFiniteAdeleFourierChar (-(dotProduct (x + v) w)) := by
          rw [← AddChar.map_add_eq_mul, add_dotProduct]
          congr 1
          ring
        rw [hsplit, Circle.coe_mul, mul_assoc]
    _ = (rationalFiniteAdeleFourierChar (dotProduct v w) : ℂ) *
          ∫ x, (rationalFiniteAdeleFourierChar (-(dotProduct (x + v) w)) : ℂ) * f (x + v)
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := integral_const_mul _ _
    _ = (rationalFiniteAdeleFourierChar (dotProduct v w) : ℂ) *
          standardFiniteFourier f w := by
        rw [hshift]
        rfl

/-- Modulating the test shifts the frequency of its actual finite Fourier
transform.  This is a pointwise identity of integrands. -/
theorem standardFiniteFourier_modulation
    (f : (Fin n → RationalFiniteAdele) → ℂ) (v w : Fin n → RationalFiniteAdele) :
    standardFiniteFourier (standardModulation v f) w =
      standardFiniteFourier f (w - v) := by
  refine integral_congr_ae ?_
  filter_upwards with x
  show (rationalFiniteAdeleFourierChar (-(dotProduct x w)) : ℂ) *
      ((rationalFiniteAdeleFourierChar (dotProduct x v) : ℂ) * f x) =
    (rationalFiniteAdeleFourierChar (-(dotProduct x (w - v))) : ℂ) * f x
  have hsplit : rationalFiniteAdeleFourierChar (-(dotProduct x (w - v))) =
      rationalFiniteAdeleFourierChar (-(dotProduct x w)) *
        rationalFiniteAdeleFourierChar (dotProduct x v) := by
    rw [← AddChar.map_add_eq_mul, dotProduct_sub]
    congr 1
    ring
  rw [hsplit, Circle.coe_mul, mul_assoc]

/-! ## Both operations keep the family -/

theorem isStandardCarried_isStandardPeriodic_translate {c c' d : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f)
    {v : Fin n → RationalFiniteAdele} (hv : v ∈ standardDividedLattice n c') :
    IsStandardCarried (c * c') (fun x => f (x + v)) ∧
      IsStandardPeriodic d (fun x => f (x + v)) :=
  ⟨hcarried.translate hv, hperiodic.translate v⟩

theorem isStandardCarried_isStandardPeriodic_modulation {c c' d : ℕ}
    {f : (Fin n → RationalFiniteAdele) → ℂ}
    (hcarried : IsStandardCarried c f) (hperiodic : IsStandardPeriodic d f)
    {v : Fin n → RationalFiniteAdele} (hv : v ∈ standardDividedLattice n c') :
    IsStandardCarried c (standardModulation v f) ∧
      IsStandardPeriodic (d * c') (standardModulation v f) :=
  ⟨hcarried.modulation v, hperiodic.modulation hv⟩

/-! ## The interchange, and the explicit translated standard indicator -/

/-- Translation on the test side is exactly modulation on the frequency side.
This is the representative-free replacement for a coset decomposition. -/
theorem standardFiniteFourier_translate_eq_modulation
    (f : (Fin n → RationalFiniteAdele) → ℂ) (v : Fin n → RationalFiniteAdele) :
    standardFiniteFourier (fun x => f (x + v)) =
      standardModulation v (standardFiniteFourier f) := by
  funext w
  rw [standardFiniteFourier_translate, standardModulation, dotProduct_comm]

/-- Modulation on the test side is exactly translation on the frequency side. -/
theorem standardFiniteFourier_modulation_eq_translate
    (f : (Fin n → RationalFiniteAdele) → ℂ) (v : Fin n → RationalFiniteAdele) :
    standardFiniteFourier (standardModulation v f) =
      fun w => standardFiniteFourier f (w - v) := by
  funext w
  exact standardFiniteFourier_modulation f v w

/-- The actual finite Fourier transform of a translate of the standard lattice
indicator is explicit: the existing character at the translation vector times
the same indicator.  This is the building block any decomposition would use,
obtained here with no representative. -/
theorem standardFiniteFourier_translate_integralIndicator
    (v w : Fin n → RationalFiniteAdele) :
    standardFiniteFourier
        (fun x => rationalFiniteAdeleVectorIntegralIndicator (x + v)) w =
      (rationalFiniteAdeleFourierChar (dotProduct v w) : ℂ) *
        rationalFiniteAdeleVectorIntegralIndicator w := by
  rw [standardFiniteFourier_translate, standardFiniteFourier_eq_fourierIntegral,
    rationalFiniteAdeleCoordinate_fourierIntegral_integralIndicator]

end RationalQuadraticSpaceMatrix
