import SMSFormula.RationalAdeleFiniteLocalResidueCount

/-!
# The level-`m` residue count is multiplicative over coprime levels

The finite local factor is the limit of the normalized level-`m` residue counts.  Nothing
so far factored that data over primes -- every statement was careful to say that a limit of
normalized counts is not an Euler product.  This file derives the first genuine step of such
a factorization, with no product assumed anywhere.

The reduced quadratic form commutes with every ring homomorphism between residue rings,
because it is a polynomial expression with integer-cast coefficients.  Applying this to the
two components of the existing Chinese remainder isomorphism
`ZMod (m1 * m2) ~ ZMod m1 x ZMod m2` turns the solution set at a composite coprime level
into the literal product of the two solution sets, so

```text
#{z mod m1 m2 : Q(z) = M}  =  #{z mod m1 : Q(z) = M} * #{z mod m2 : Q(z) = M},
```

and consequently the congruence measure `m^{-n} #{...}` is multiplicative as well.

Negative scope: this is coprime multiplicativity of one count, not an Euler product for the
singular series: no limit is taken here, no prime-power local density is defined, and the
infinite product over all primes is not formed.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The reduced quadratic form commutes with every residue-ring homomorphism. -/
theorem zmodQuadForm_map (L : PositiveDefiniteIntegralLattice n) {m₁ m₂ : ℕ} (f : ZMod m₁ →+* ZMod m₂)
    (z : Fin n → ZMod m₁) :
    f (L.zmodQuadForm m₁ z) = L.zmodQuadForm m₂ (fun i => f (z i)) := by
  simp only [zmodQuadForm, map_sum, map_mul, map_intCast]

/-- The existing Chinese remainder isomorphism, applied coordinatewise. -/
def residueCoordinateCRT {m₁ m₂ : ℕ} (h : Nat.Coprime m₁ m₂) :
    (Fin n → ZMod (m₁ * m₂)) ≃ (Fin n → ZMod m₁) × (Fin n → ZMod m₂) :=
  (Equiv.piCongrRight fun _ : Fin n => (ZMod.chineseRemainder h).toEquiv).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

theorem residueCoordinateCRT_apply {m₁ m₂ : ℕ} (h : Nat.Coprime m₁ m₂)
    (z : Fin n → ZMod (m₁ * m₂)) :
    residueCoordinateCRT (n := n) h z =
      (fun i => (ZMod.chineseRemainder h (z i)).1,
        fun i => (ZMod.chineseRemainder h (z i)).2) := rfl

/-- The solution set at a composite coprime level is the literal product of the two
solution sets. -/
def residueSolutionCRTEquiv (L : PositiveDefiniteIntegralLattice n) {m₁ m₂ : ℕ} (h : Nat.Coprime m₁ m₂)
    (M : ℤ) :
    {z : Fin n → ZMod (m₁ * m₂) //
        L.zmodQuadForm (m₁ * m₂) z = ((M : ℤ) : ZMod (m₁ * m₂))} ≃
      {z : Fin n → ZMod m₁ // L.zmodQuadForm m₁ z = ((M : ℤ) : ZMod m₁)} ×
        {z : Fin n → ZMod m₂ // L.zmodQuadForm m₂ z = ((M : ℤ) : ZMod m₂)} := by
  have hf : ∀ z : Fin n → ZMod (m₁ * m₂),
      (L.zmodQuadForm (m₁ * m₂) z = ((M : ℤ) : ZMod (m₁ * m₂))) ↔
        (L.zmodQuadForm m₁ (residueCoordinateCRT (n := n) h z).1 =
            ((M : ℤ) : ZMod m₁) ∧
          L.zmodQuadForm m₂ (residueCoordinateCRT (n := n) h z).2 =
            ((M : ℤ) : ZMod m₂)) := by
    intro z
    set e := ZMod.chineseRemainder h with he
    set f₁ : ZMod (m₁ * m₂) →+* ZMod m₁ :=
      (RingHom.fst (ZMod m₁) (ZMod m₂)).comp (e : ZMod (m₁ * m₂) →+* ZMod m₁ × ZMod m₂)
      with hf₁
    set f₂ : ZMod (m₁ * m₂) →+* ZMod m₂ :=
      (RingHom.snd (ZMod m₁) (ZMod m₂)).comp (e : ZMod (m₁ * m₂) →+* ZMod m₁ × ZMod m₂)
      with hf₂
    have h1 : L.zmodQuadForm m₁ (residueCoordinateCRT (n := n) h z).1 =
        f₁ (L.zmodQuadForm (m₁ * m₂) z) := by
      rw [L.zmodQuadForm_map f₁ z]
      rfl
    have h2 : L.zmodQuadForm m₂ (residueCoordinateCRT (n := n) h z).2 =
        f₂ (L.zmodQuadForm (m₁ * m₂) z) := by
      rw [L.zmodQuadForm_map f₂ z]
      rfl
    rw [h1, h2]
    constructor
    · intro hz
      rw [hz]
      exact ⟨by simp [hf₁], by simp [hf₂]⟩
    · rintro ⟨ha, hb⟩
      have hcast : e (((M : ℤ) : ZMod (m₁ * m₂))) =
          (((M : ℤ) : ZMod m₁), ((M : ℤ) : ZMod m₂)) := by
        rw [map_intCast]
        rfl
      have hpair : e (L.zmodQuadForm (m₁ * m₂) z) = e (((M : ℤ) : ZMod (m₁ * m₂))) := by
        rw [hcast]
        exact Prod.ext ha hb
      exact e.injective hpair
  exact (Equiv.subtypeEquiv (residueCoordinateCRT (n := n) h) hf).trans
    (Equiv.subtypeProdEquivProd)

/-- The residue count is multiplicative over coprime levels. -/
theorem card_residueSet_mul_of_coprime (L : PositiveDefiniteIntegralLattice n) {m₁ m₂ : ℕ}
    (h : Nat.Coprime m₁ m₂) (M : ℤ) :
    Nat.card {z : Fin n → ZMod (m₁ * m₂) //
        L.zmodQuadForm (m₁ * m₂) z = ((M : ℤ) : ZMod (m₁ * m₂))} =
      Nat.card {z : Fin n → ZMod m₁ // L.zmodQuadForm m₁ z = ((M : ℤ) : ZMod m₁)} *
        Nat.card {z : Fin n → ZMod m₂ //
          L.zmodQuadForm m₂ z = ((M : ℤ) : ZMod m₂)} := by
  rw [Nat.card_congr (L.residueSolutionCRTEquiv h M), Nat.card_prod]

/-- Hence the congruence measure is multiplicative over coprime levels. -/
theorem congruenceMeasure_mul_of_coprime (L : PositiveDefiniteIntegralLattice n) {m₁ m₂ : ℕ}
    (h : Nat.Coprime m₁ m₂) (M : ℤ) :
    (((m₁ * m₂ : ℕ) : ℝ) ^ n)⁻¹ *
        (Nat.card {z : Fin n → ZMod (m₁ * m₂) //
          L.zmodQuadForm (m₁ * m₂) z = ((M : ℤ) : ZMod (m₁ * m₂))} : ℝ) =
      ((((m₁ : ℕ) : ℝ) ^ n)⁻¹ *
          (Nat.card {z : Fin n → ZMod m₁ //
            L.zmodQuadForm m₁ z = ((M : ℤ) : ZMod m₁)} : ℝ)) *
        ((((m₂ : ℕ) : ℝ) ^ n)⁻¹ *
          (Nat.card {z : Fin n → ZMod m₂ //
            L.zmodQuadForm m₂ z = ((M : ℤ) : ZMod m₂)} : ℝ)) := by
  rw [L.card_residueSet_mul_of_coprime h M]
  push_cast
  rw [mul_pow]
  rw [mul_inv]
  ring

/-- At level one the residue cube is a single point. -/
theorem card_residueSet_one (L : PositiveDefiniteIntegralLattice n) (M : ℤ) :
    Nat.card {z : Fin n → ZMod 1 // L.zmodQuadForm 1 z = ((M : ℤ) : ZMod 1)} = 1 := by
  haveI : Unique {z : Fin n → ZMod 1 // L.zmodQuadForm 1 z = ((M : ℤ) : ZMod 1)} := by
    refine ⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩⟩, fun a => ?_⟩
    exact Subtype.ext (Subsingleton.elim _ _)
  simp

/-- The residue count factors over the prime powers of the level.  This is the Euler
structure of the local data, derived from coprime multiplicativity and never assumed. -/
theorem card_residueSet_eq_prod_factorization (L : PositiveDefiniteIntegralLattice n) (M : ℤ) {m : ℕ}
    (hm : m ≠ 0) :
    Nat.card {z : Fin n → ZMod m // L.zmodQuadForm m z = ((M : ℤ) : ZMod m)} =
      m.factorization.prod fun p k =>
        Nat.card {z : Fin n → ZMod (p ^ k) //
          L.zmodQuadForm (p ^ k) z = ((M : ℤ) : ZMod (p ^ k))} :=
  Nat.multiplicative_factorization
    (fun j => Nat.card {z : Fin n → ZMod j // L.zmodQuadForm j z = ((M : ℤ) : ZMod j)})
    (fun _ _ hxy => L.card_residueSet_mul_of_coprime hxy M)
    (L.card_residueSet_one M) hm

end PositiveDefiniteIntegralLattice
