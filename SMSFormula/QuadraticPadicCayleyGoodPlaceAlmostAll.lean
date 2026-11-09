import SMSFormula.QuadraticPadicCayleyIntegralOrbit

/-! Good places from rational data. For the rational Gram matrix `F` of
`W ⊕ ⟨a⟩` (nonzero determinant) and `a ≠ 0` there is a finite set of primes
outside of which `p` is odd, the mapped matrix `F` is `p`-integral, `det F` and
`a` are `p`-adic units. The set is explicit: `2`, the prime factors of the
denominators of the entries of `F`, and of the numerators and denominators of
`det F` and `a`. Consequently, at every prime outside it, the orbit of `x_old`
under the integral subgroup is `X_a(ℤ_p)` (for `n ≥ 1`). No representative,
chart or normalization is chosen. -/
noncomputable section
open Matrix PositiveDefiniteIntegralLattice Set QuadraticMap

namespace RationalQuadraticSpaceMatrix

/-- A rational number whose denominator is prime to `p` is a `p`-adic integer. -/
theorem padic_norm_ratCast_le_one {p : ℕ} [Fact p.Prime] {q : ℚ} (h : ¬ p ∣ q.den) :
    ‖(q : ℚ_[p])‖ ≤ 1 :=
  Padic.norm_rat_le_one h

/-- A rational number whose numerator and denominator are prime to `p` is a
`p`-adic unit. -/
theorem padic_norm_ratCast_eq_one {p : ℕ} [Fact p.Prime] {q : ℚ} (hnum : ¬ p ∣ q.num.natAbs)
    (hden : ¬ p ∣ q.den) : ‖(q : ℚ_[p])‖ = 1 := by
  have hnum' : ‖(q.num : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one _) (not_lt.mp fun h ↦
      hnum (Int.natCast_dvd.mp (Padic.norm_intCast_lt_one_iff.mp h)))
  have hden' : ‖(q.den : ℚ_[p])‖ = 1 :=
    le_antisymm (by simpa using Padic.norm_int_le_one (p := p) (q.den : ℤ)) (not_lt.mp fun h ↦
      hden (Padic.norm_natCast_lt_one_iff.mp h))
  rw [← Rat.num_div_den q]
  push_cast
  rw [norm_div, hnum', hden', div_one]

theorem not_dvd_of_notMem_primeFactors {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (h : p ∉ m.primeFactors) : ¬ p ∣ m :=
  fun hd ↦ h (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, hm⟩)

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- The explicit finite set of bad primes of `W ⊕ ⟨a⟩`. -/
def goodPlaceExceptionalPrimes : Finset ℕ :=
  {2} ∪ Finset.univ.biUnion (fun ij : Fin (n+1) × Fin (n+1) ↦
      ((W.nonisotropicLastExtension a ha).pairingMatrix ij.1 ij.2).den.primeFactors) ∪
    (W.nonisotropicLastExtension a ha).pairingMatrix.det.num.natAbs.primeFactors ∪
    (W.nonisotropicLastExtension a ha).pairingMatrix.det.den.primeFactors ∪
    a.num.natAbs.primeFactors ∪ a.den.primeFactors

/-- Good places at almost all primes. -/
theorem goodPlace_of_notMem_exceptionalPrimes (p : ℕ) [Fact p.Prime]
    (hp : p ∉ W.goodPlaceExceptionalPrimes a ha) :
    p ≠ 2 ∧
      (∀ i j, ‖((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) i j‖ ≤ 1) ∧
      ‖((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])).det‖ = 1 ∧
      ‖(algebraMap ℚ ℚ_[p] a)‖ = 1 := by
  set F := (W.nonisotropicLastExtension a ha).pairingMatrix with hF
  unfold goodPlaceExceptionalPrimes at hp
  rw [← hF] at hp
  simp only [Finset.mem_union, not_or] at hp
  obtain ⟨⟨⟨⟨⟨h2, hent⟩, hdnum⟩, hdden⟩, hanum⟩, haden⟩ := hp
  have hd : F.det ≠ 0 := (W.nonisotropicLastExtension a ha).form_det_ne_zero
  refine ⟨fun h ↦ h2 (by simp [h]), fun i j ↦ ?_, ?_, ?_⟩
  · rw [Matrix.map_apply, eq_ratCast]
    refine padic_norm_ratCast_le_one (not_dvd_of_notMem_primeFactors (Rat.den_nz _) ?_)
    intro hmem
    exact hent (Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, hmem⟩)
  · rw [show F.map (algebraMap ℚ ℚ_[p]) = (algebraMap ℚ ℚ_[p]).mapMatrix F from rfl,
      ← RingHom.map_det, eq_ratCast]
    exact padic_norm_ratCast_eq_one
      (not_dvd_of_notMem_primeFactors (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hd)) hdnum)
      (not_dvd_of_notMem_primeFactors (Rat.den_nz _) hdden)
  · rw [eq_ratCast]
    exact padic_norm_ratCast_eq_one
      (not_dvd_of_notMem_primeFactors (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr ha)) hanum)
      (not_dvd_of_notMem_primeFactors (Rat.den_nz _) haden)

/-- At every prime outside the explicit finite exceptional set, the integral
subgroup is compact open and its orbit of `x_old` is `X_a(ℤ_p)`. -/
theorem range_smul_lastFiberBasePoint_padicIntegral_of_notMem (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime]
    (hp : p ∉ W.goodPlaceExceptionalPrimes a ha) :
    range (fun γ : padicIntegralSpecialSubgroup
        ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦
        γ • W.lastFiberBasePoint p a ha) =
      {y | ‖y.1‖ ≤ 1} := by
  obtain ⟨h2, hint, hdet, ha1⟩ := W.goodPlace_of_notMem_exceptionalPrimes a ha p hp
  exact W.range_smul_lastFiberBasePoint_padicIntegral p a ha h2 hn hint hdet ha1

end RationalQuadraticSpaceMatrix
