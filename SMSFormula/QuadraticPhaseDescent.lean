import SMSFormula.CosetAverageIntegral

/-!
# The quadratic phase descends, and the local integral becomes the finite sum

`CosetAverageIntegral` turns a bound on a normalized finite sum into a bound on a local integral,
but only for an integrand already presented as a function on the quotient.  This file supplies the
missing unit: the quadratic phase is such a function, once the character kills the polarization
discrepancy at the chosen level.

The polarization is the whole mechanism.  Writing `b = a + h` with `h` in the subgroup,
`Q b = Q a + B a h + Q h`, so the phase moves by `psi (B a h + Q h)` and by nothing else.  If that
factor is one the phase is constant on cosets, hence a function on the quotient -- produced by
`Quotient.lift`, so no representative is chosen.  Composing with the coset-average identity, the
local integral of the quadratic phase is the normalized finite sum.

The level condition has a usable sufficient form: if every member of the subgroup is `c` times an
element, bilinearity in the second slot and the square law make the discrepancy `c` times something,
so a character killing `c`-multiples kills it.  That is where a conductor would enter.

Negative scope.  The polarization, the level and the character are all hypotheses: no quadratic form
is constructed, no valuation appears, and nothing is `p`-adic.  Nothing is evaluated -- this makes
the bridge applicable, and the bridge itself was already recorded as evaluating nothing.
-/

namespace SMSFormula.QuadraticPhaseDescent

open MeasureTheory SMSFormula.CosetAverage

variable {G : Type*} [AddCommGroup G] {R : Type*} [AddCommGroup R]

/-! ## Descending a coset-constant function -/

/-- A function constant on cosets as a function on the quotient, by `Quotient.lift` -- so no
representative is chosen anywhere. -/
def descend (f : G → ℂ) (K : AddSubgroup G) (hf : ∀ a b : G, -a + b ∈ K → f a = f b) :
    G ⧸ K → ℂ :=
  Quotient.lift f fun a b hab ↦ hf a b (QuotientAddGroup.leftRel_apply.mp hab)

@[simp]
theorem descend_mk (f : G → ℂ) (K : AddSubgroup G) (hf : ∀ a b : G, -a + b ∈ K → f a = f b)
    (x : G) : descend f K hf (QuotientAddGroup.mk x) = f x := rfl

/-! ## The phase is coset constant -/

/-- The polarization forces the discrepancy to vanish at the zero shift, so the level condition is
automatically satisfiable -- the trivial subgroup always works. -/
theorem polarization_zero (Q : G → R) (B : G → G → R)
    (hpol : ∀ x h, Q (x + h) = Q x + B x h + Q h) (x : G) : B x 0 + Q 0 = 0 := by
  have h := hpol x 0
  rw [add_zero] at h
  have h' : Q x + (B x 0 + Q 0) = Q x + 0 := by
    rw [add_zero, ← add_assoc]
    exact h.symm
  exact (add_right_injective (Q x)) h'

/-- The phase is constant on cosets as soon as the character kills the polarization discrepancy.
The discrepancy is the entire content: `Q (a + h) - Q a = B a h + Q h`. -/
theorem phase_coset_const {Q : G → R} {B : G → G → R}
    (hpol : ∀ x h, Q (x + h) = Q x + B x h + Q h) (psi : AddChar R ℂ) {K : AddSubgroup G}
    (hlevel : ∀ x : G, ∀ h ∈ K, psi (B x h + Q h) = 1) :
    ∀ a b : G, -a + b ∈ K → psi (Q a) = psi (Q b) := by
  intro a b hab
  have hb : b = a + (-a + b) := by abel
  rw [hb, hpol, add_assoc, AddChar.map_add_eq_mul, hlevel a _ hab, mul_one]

/-- Hence the phase is a function on the quotient. -/
noncomputable def phaseQuotient {Q : G → R} {B : G → G → R}
    (hpol : ∀ x h, Q (x + h) = Q x + B x h + Q h) (psi : AddChar R ℂ) {K : AddSubgroup G}
    (hlevel : ∀ x : G, ∀ h ∈ K, psi (B x h + Q h) = 1) : G ⧸ K → ℂ :=
  descend (fun x ↦ psi (Q x)) K (phase_coset_const hpol psi hlevel)

@[simp]
theorem phaseQuotient_mk {Q : G → R} {B : G → G → R}
    (hpol : ∀ x h, Q (x + h) = Q x + B x h + Q h) (psi : AddChar R ℂ) {K : AddSubgroup G}
    (hlevel : ∀ x : G, ∀ h ∈ K, psi (B x h + Q h) = 1) (x : G) :
    phaseQuotient hpol psi hlevel (QuotientAddGroup.mk x) = psi (Q x) := rfl

/-! ## A usable sufficient form of the level condition -/

/-- The level condition from a scale: if every member of the subgroup is `c` times an element, then
bilinearity in the second slot and the square law make the discrepancy `c` times something, so a
character killing `c`-multiples kills it.  This is where a conductor enters. -/
theorem level_of_scale {Q : G → R} {B : G → G → R} (psi : AddChar R ℂ) (c : ℤ)
    (hB : ∀ x u, B x (c • u) = c • B x u) (hQ : ∀ u, Q (c • u) = c • (c • Q u))
    (hkill : ∀ r : R, psi (c • r) = 1) {K : AddSubgroup G}
    (hK : ∀ h ∈ K, ∃ u : G, h = c • u) :
    ∀ x : G, ∀ h ∈ K, psi (B x h + Q h) = 1 := by
  intro x h hh
  obtain ⟨u, rfl⟩ := hK h hh
  rw [hB, hQ, ← smul_add]
  exact hkill _

/-- The same criterion at a natural scale, which is the shape the repository's own level subgroup
has (its members are `m` times an element, with `m` a natural). -/
theorem level_of_natScale {Q : G → R} {B : G → G → R} (psi : AddChar R ℂ) (c : ℕ)
    (hB : ∀ x u, B x (c • u) = c • B x u) (hQ : ∀ u, Q (c • u) = c • (c • Q u))
    (hkill : ∀ r : R, psi (c • r) = 1) {K : AddSubgroup G}
    (hK : ∀ h ∈ K, ∃ u : G, h = c • u) :
    ∀ x : G, ∀ h ∈ K, psi (B x h + Q h) = 1 := by
  intro x h hh
  obtain ⟨u, rfl⟩ := hK h hh
  rw [hB, hQ, ← smul_add]
  exact hkill _

/-! ## The payoff -/

/-- The local integral of the quadratic phase is the normalized finite sum -- the bridge made to
bite.  A bound on the sum over the quotient is a bound on the integral. -/
theorem integral_phase_eq_average [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G)
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] {Q : G → R} {B : G → G → R}
    (hpol : ∀ x h, Q (x + h) = Q x + B x h + Q h) (psi : AddChar R ℂ) {K : AddSubgroup G}
    (hlevel : ∀ x : G, ∀ h ∈ K, psi (B x h + Q h) = 1) [Fintype (G ⧸ K)]
    (hfib : ∀ q : G ⧸ K, MeasurableSet (QuotientAddGroup.mk ⁻¹' {q} : Set G)) :
    ∫ x, psi (Q x) ∂μ =
      ((Fintype.card (G ⧸ K) : ℝ))⁻¹ • ∑ q : G ⧸ K, phaseQuotient hpol psi hlevel q :=
  integral_comp_mk_eq_average μ hfib (phaseQuotient hpol psi hlevel)

/-- And in the form the conductor bounds are stated in: the modulus of the local integral is the
modulus of the normalized sum over the quotient. -/
theorem norm_integral_phase [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G)
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] {Q : G → R} {B : G → G → R}
    (hpol : ∀ x h, Q (x + h) = Q x + B x h + Q h) (psi : AddChar R ℂ) {K : AddSubgroup G}
    (hlevel : ∀ x : G, ∀ h ∈ K, psi (B x h + Q h) = 1) [Fintype (G ⧸ K)]
    (hfib : ∀ q : G ⧸ K, MeasurableSet (QuotientAddGroup.mk ⁻¹' {q} : Set G)) :
    ‖∫ x, psi (Q x) ∂μ‖ =
      ((Fintype.card (G ⧸ K) : ℝ))⁻¹ * ‖∑ q : G ⧸ K, phaseQuotient hpol psi hlevel q‖ :=
  norm_integral_comp_mk μ hfib (phaseQuotient hpol psi hlevel)

end SMSFormula.QuadraticPhaseDescent
