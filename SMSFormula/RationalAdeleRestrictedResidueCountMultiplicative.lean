import SMSFormula.RationalAdeleResidueCountMultiplicative

/-!
# Restricted residue counts factor over the prime powers of the level

Fix supplied local restriction data: a finite set `P` of primes, exponents `e p ≥ 1`, and residue
sets `R p ⊆ (ZMod p^{e p})^n`.  At a level `j` a residue vector `z` is admissible when, for every
`p ∈ P` with `p^{e p} ∣ j`, its reduction modulo `p^{e p}` lies in `R p`.  The restricted count

`f(j) = #{z mod j : Q(z) = M, z admissible}`

is multiplicative over coprime levels (coordinatewise Chinese remainder theorem; a prime power
dividing a product of coprime levels divides exactly one of them, and every reduction map between
residue rings is the unique ring homomorphism).  Hence it factors over the prime powers of every
level, and at primes outside `P` it agrees with the full count.  Consequently

`f(m) · ∏_{p∈P} F(p^{v_p m}) = F(m) · ∏_{p∈P} f(p^{v_p m})`,

with `F` the full count: the ratio of restricted to full counts is a finite product of local
ratios at the primes of `P`.  The data `P, e, R` are supplied; nothing is chosen.
-/

noncomputable section

open Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Admissibility of a residue vector at level `j` for the supplied local restriction data. -/
def IsLocallyAdmissible (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (j : ℕ) (z : Fin n → ZMod j) : Prop :=
  ∀ p ∈ P, ∀ h : p ^ e p ∣ j, (fun i ↦ ZMod.castHom h (ZMod (p ^ e p)) (z i)) ∈ R p

/-- The restricted residue count at level `j`. -/
def restrictedResidueCount (L : PositiveDefiniteIntegralLattice n) (M : ℤ) (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (j : ℕ) : ℕ :=
  Nat.card {z : Fin n → ZMod j //
    L.zmodQuadForm j z = ((M : ℤ) : ZMod j) ∧ IsLocallyAdmissible P e R j z}

/-- The full residue count at level `j`. -/
def fullResidueCount (L : PositiveDefiniteIntegralLattice n) (M : ℤ) (j : ℕ) : ℕ :=
  Nat.card {z : Fin n → ZMod j // L.zmodQuadForm j z = ((M : ℤ) : ZMod j)}

/-- A prime power dividing a product of coprime numbers divides one of them. -/
theorem primePow_dvd_or_of_dvd_mul_of_coprime {p e j₁ j₂ : ℕ} (hp : p.Prime)
    (h : Nat.Coprime j₁ j₂) (hd : p ^ e ∣ j₁ * j₂) : p ^ e ∣ j₁ ∨ p ^ e ∣ j₂ := by
  rcases Nat.eq_zero_or_pos e with he | he
  · left
    rw [he, pow_zero]
    exact one_dvd _
  · exact (Nat.Coprime.isPrimePow_dvd_mul h (hp.isPrimePow.pow he.ne')).1 hd

/-- Admissibility splits under the Chinese remainder map. -/
theorem isLocallyAdmissible_mul_iff (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime)
    {j₁ j₂ : ℕ} (h : Nat.Coprime j₁ j₂) (z : Fin n → ZMod (j₁ * j₂)) :
    IsLocallyAdmissible P e R (j₁ * j₂) z ↔
      IsLocallyAdmissible P e R j₁ (residueCoordinateCRT (n := n) h z).1 ∧
        IsLocallyAdmissible P e R j₂ (residueCoordinateCRT (n := n) h z).2 := by
  have hfst : ∀ (p : ℕ) (h₁ : p ^ e p ∣ j₁) (i : Fin n),
      ZMod.castHom h₁ (ZMod (p ^ e p)) ((residueCoordinateCRT (n := n) h z).1 i) =
        ZMod.castHom (h₁.trans (dvd_mul_right j₁ j₂)) (ZMod (p ^ e p)) (z i) := by
    intro p h₁ i
    rw [residueCoordinateCRT_apply]
    change ((ZMod.castHom h₁ (ZMod (p ^ e p))).comp
      ((RingHom.fst (ZMod j₁) (ZMod j₂)).comp
        (ZMod.chineseRemainder h : ZMod (j₁ * j₂) →+* ZMod j₁ × ZMod j₂))) (z i) = _
    congr 1
    exact Subsingleton.elim _ _
  have hsnd : ∀ (p : ℕ) (h₂ : p ^ e p ∣ j₂) (i : Fin n),
      ZMod.castHom h₂ (ZMod (p ^ e p)) ((residueCoordinateCRT (n := n) h z).2 i) =
        ZMod.castHom (h₂.trans (dvd_mul_left j₂ j₁)) (ZMod (p ^ e p)) (z i) := by
    intro p h₂ i
    rw [residueCoordinateCRT_apply]
    change ((ZMod.castHom h₂ (ZMod (p ^ e p))).comp
      ((RingHom.snd (ZMod j₁) (ZMod j₂)).comp
        (ZMod.chineseRemainder h : ZMod (j₁ * j₂) →+* ZMod j₁ × ZMod j₂))) (z i) = _
    congr 1
    exact Subsingleton.elim _ _
  constructor
  · intro hz
    refine ⟨fun p hp h₁ ↦ ?_, fun p hp h₂ ↦ ?_⟩
    · have := hz p hp (h₁.trans (dvd_mul_right j₁ j₂))
      simpa only [hfst p h₁] using this
    · have := hz p hp (h₂.trans (dvd_mul_left j₂ j₁))
      simpa only [hsnd p h₂] using this
  · rintro ⟨hz₁, hz₂⟩ p hp hd
    rcases primePow_dvd_or_of_dvd_mul_of_coprime (hP p hp) h hd with h₁ | h₂
    · have := hz₁ p hp h₁
      simpa only [hfst p h₁] using this
    · have := hz₂ p hp h₂
      simpa only [hsnd p h₂] using this

/-- The restricted count is multiplicative over coprime levels. -/
theorem restrictedResidueCount_mul_of_coprime (L : PositiveDefiniteIntegralLattice n) (M : ℤ) (P : Finset ℕ)
    (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime)
    {j₁ j₂ : ℕ} (h : Nat.Coprime j₁ j₂) :
    L.restrictedResidueCount M P e R (j₁ * j₂) =
      L.restrictedResidueCount M P e R j₁ * L.restrictedResidueCount M P e R j₂ := by
  unfold restrictedResidueCount
  have hf : ∀ z : Fin n → ZMod (j₁ * j₂),
      (L.zmodQuadForm (j₁ * j₂) z = ((M : ℤ) : ZMod (j₁ * j₂)) ∧
          IsLocallyAdmissible P e R (j₁ * j₂) z) ↔
        ((L.zmodQuadForm j₁ (residueCoordinateCRT (n := n) h z).1 = ((M : ℤ) : ZMod j₁) ∧
            IsLocallyAdmissible P e R j₁ (residueCoordinateCRT (n := n) h z).1) ∧
          (L.zmodQuadForm j₂ (residueCoordinateCRT (n := n) h z).2 = ((M : ℤ) : ZMod j₂) ∧
            IsLocallyAdmissible P e R j₂ (residueCoordinateCRT (n := n) h z).2)) := by
    intro z
    have hQz : L.zmodQuadForm (j₁ * j₂) z = ((M : ℤ) : ZMod (j₁ * j₂)) ↔
        (L.zmodQuadForm j₁ (residueCoordinateCRT (n := n) h z).1 = ((M : ℤ) : ZMod j₁) ∧
          L.zmodQuadForm j₂ (residueCoordinateCRT (n := n) h z).2 = ((M : ℤ) : ZMod j₂)) := by
      constructor
      · intro hz
        exact ⟨(L.residueSolutionCRTEquiv h M ⟨z, hz⟩).1.2,
          (L.residueSolutionCRTEquiv h M ⟨z, hz⟩).2.2⟩
      · intro hz
        have := ((L.residueSolutionCRTEquiv h M).symm
          (⟨_, hz.1⟩, ⟨_, hz.2⟩)).2
        have hz' : ((L.residueSolutionCRTEquiv h M).symm (⟨_, hz.1⟩, ⟨_, hz.2⟩)).1 = z := by
          apply (residueCoordinateCRT (n := n) h).injective
          have := congrArg (fun w ↦ ((w.1.1, w.2.1) : (Fin n → ZMod j₁) × (Fin n → ZMod j₂)))
            ((L.residueSolutionCRTEquiv h M).apply_symm_apply (⟨_, hz.1⟩, ⟨_, hz.2⟩))
          exact this
        rwa [hz'] at this
    rw [hQz, isLocallyAdmissible_mul_iff P e R hP h z]
    tauto
  rw [Nat.card_congr ((Equiv.subtypeEquiv
      (q := fun c : (Fin n → ZMod j₁) × (Fin n → ZMod j₂) ↦
        (L.zmodQuadForm j₁ c.1 = ((M : ℤ) : ZMod j₁) ∧ IsLocallyAdmissible P e R j₁ c.1) ∧
          (L.zmodQuadForm j₂ c.2 = ((M : ℤ) : ZMod j₂) ∧ IsLocallyAdmissible P e R j₂ c.2))
      (residueCoordinateCRT (n := n) h) hf).trans
    (Equiv.subtypeProdEquivProd
      (p := fun w : Fin n → ZMod j₁ ↦
        L.zmodQuadForm j₁ w = ((M : ℤ) : ZMod j₁) ∧ IsLocallyAdmissible P e R j₁ w)
      (q := fun w : Fin n → ZMod j₂ ↦
        L.zmodQuadForm j₂ w = ((M : ℤ) : ZMod j₂) ∧ IsLocallyAdmissible P e R j₂ w))),
    Nat.card_prod]

theorem restrictedResidueCount_one (L : PositiveDefiniteIntegralLattice n) (M : ℤ) (P : Finset ℕ) (e : ℕ → ℕ)
    (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) :
    L.restrictedResidueCount M P e R 1 = 1 := by
  have hadm : ∀ z : Fin n → ZMod 1, IsLocallyAdmissible P e R 1 z := by
    intro z p hp hd
    exfalso
    have hle := Nat.le_of_dvd one_pos hd
    have : 2 ≤ p ^ e p :=
      (hP p hp).1.two_le.trans (Nat.le_self_pow (by have := (hP p hp).2; omega) p)
    omega
  unfold restrictedResidueCount
  calc _ = Nat.card {z : Fin n → ZMod 1 // L.zmodQuadForm 1 z = ((M : ℤ) : ZMod 1)} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun z ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, hadm z⟩⟩)
    _ = 1 := L.card_residueSet_one M

/-- The restricted count factors over the prime powers of the level. -/
theorem restrictedResidueCount_eq_prod_factorization (L : PositiveDefiniteIntegralLattice n) (M : ℤ)
    (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) {m : ℕ} (hm : m ≠ 0) :
    L.restrictedResidueCount M P e R m =
      m.factorization.prod fun p k ↦ L.restrictedResidueCount M P e R (p ^ k) :=
  Nat.multiplicative_factorization (L.restrictedResidueCount M P e R)
    (fun _ _ hxy ↦ L.restrictedResidueCount_mul_of_coprime M P e R (fun p hp ↦ (hP p hp).1) hxy)
    (L.restrictedResidueCount_one M P e R hP) hm

/-- At a prime power `q^k` of a prime `q ∉ P` the restricted count is the full count. -/
theorem restrictedResidueCount_primePow_of_notMem (L : PositiveDefiniteIntegralLattice n) (M : ℤ)
    (P : Finset ℕ) (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p)))
    (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p) {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) (k : ℕ) :
    L.restrictedResidueCount M P e R (q ^ k) = L.fullResidueCount M (q ^ k) := by
  have hadm : ∀ z : Fin n → ZMod (q ^ k), IsLocallyAdmissible P e R (q ^ k) z := by
    intro z p hp hd
    exfalso
    have hpq : p ∣ q ^ k := (dvd_pow_self p (by have := (hP p hp).2; omega)).trans hd
    have := (Nat.prime_dvd_prime_iff_eq (hP p hp).1 hq).1 ((hP p hp).1.dvd_of_dvd_pow hpq)
    exact hqP (this ▸ hp)
  unfold restrictedResidueCount fullResidueCount
  exact Nat.card_congr (Equiv.subtypeEquivRight fun z ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, hadm z⟩⟩)

/-- The ratio of restricted to full counts is a finite product of local ratios:
`f(m) · ∏_{p∈P} F(p^{v_p m}) = F(m) · ∏_{p∈P} f(p^{v_p m})`. -/
theorem restrictedResidueCount_mul_prod_eq (L : PositiveDefiniteIntegralLattice n) (M : ℤ) (P : Finset ℕ)
    (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p)
    {m : ℕ} (hm : m ≠ 0) :
    L.restrictedResidueCount M P e R m *
        ∏ p ∈ P, L.fullResidueCount M (p ^ m.factorization p) =
      L.fullResidueCount M m *
        ∏ p ∈ P, L.restrictedResidueCount M P e R (p ^ m.factorization p) := by
  classical
  set f := L.restrictedResidueCount M P e R with hfdef
  set F := L.fullResidueCount M with hFdef
  have hF1 : F 1 = 1 := L.card_residueSet_one M
  have hf1 : f 1 = 1 := L.restrictedResidueCount_one M P e R hP
  have hfm : f m = ∏ q ∈ m.primeFactors, f (q ^ m.factorization q) := by
    rw [hfdef, L.restrictedResidueCount_eq_prod_factorization M P e R hP hm, Finsupp.prod,
      Nat.support_factorization]
  have hFm : F m = ∏ q ∈ m.primeFactors, F (q ^ m.factorization q) := by
    rw [hFdef, fullResidueCount, L.card_residueSet_eq_prod_factorization M hm, Finsupp.prod,
      Nat.support_factorization]
    rfl
  -- local products over `P` only see the primes of `m`
  have hPf : ∀ g : ℕ → ℕ, g 1 = 1 →
      ∏ p ∈ P, g (p ^ m.factorization p) =
        ∏ q ∈ m.primeFactors.filter (· ∈ P), g (q ^ m.factorization q) := by
    intro g hg
    symm
    rw [Finset.filter_mem_eq_inter]
    refine Finset.prod_subset Finset.inter_subset_right fun q hqP hq ↦ ?_
    have : q ∉ m.primeFactors := fun h ↦ hq (Finset.mem_inter.2 ⟨h, hqP⟩)
    rw [Nat.factorization_eq_zero_of_not_dvd (fun hd ↦ this (Nat.mem_primeFactors.2
      ⟨(hP q hqP).1, hd, hm⟩)), pow_zero, hg]
  have hout : ∏ q ∈ m.primeFactors.filter (· ∉ P), f (q ^ m.factorization q) =
      ∏ q ∈ m.primeFactors.filter (· ∉ P), F (q ^ m.factorization q) :=
    Finset.prod_congr rfl fun q hq ↦ by
      obtain ⟨hqm, hqP⟩ := Finset.mem_filter.1 hq
      exact L.restrictedResidueCount_primePow_of_notMem M P e R hP
        (Nat.prime_of_mem_primeFactors hqm) hqP _
  rw [hPf F hF1, hPf f hf1, hfm, hFm, ← Finset.prod_filter_mul_prod_filter_not m.primeFactors
      (· ∈ P) (f := fun q ↦ f (q ^ m.factorization q)),
    ← Finset.prod_filter_mul_prod_filter_not m.primeFactors (· ∈ P)
      (f := fun q ↦ F (q ^ m.factorization q)), hout]
  ring

end PositiveDefiniteIntegralLattice
