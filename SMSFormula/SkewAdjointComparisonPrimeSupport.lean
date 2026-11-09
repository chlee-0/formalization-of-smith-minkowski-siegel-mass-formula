import SMSFormula.SkewAdjointPadicElementaryBasis

/-!
# Prime support of the skew-adjoint basis comparison

The determinant comparing the arbitrary rational skew-adjoint basis
with the form-adapted elementary basis is a nonzero rational number.  This
file packages the finite set of primes dividing its numerator or denominator
and proves that the determinant has valuation zero, hence p-adic norm one,
outside that set.

This support is deliberately separate from the Schulze--Pillot bad-prime set.
No integral coordinate lattice or measure is compared here.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {n : ℕ}

/-- Prime subtypes occurring in the prime factorization of a natural number. -/
private def primeDivisorSubtypeFinset (m : ℕ) :
    Finset {p : ℕ // Nat.Prime p} :=
  (m.primeFactors.attach).map
    ⟨fun p => ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩, by
      intro p q hpq
      exact Subtype.ext
        (show p.1 = q.1 from
          congrArg (fun r : {p : ℕ // Nat.Prime p} => r.1) hpq)⟩

private theorem mem_primeDivisorSubtypeFinset_iff
    {m : ℕ} (hm : m ≠ 0) (q : {p : ℕ // Nat.Prime p}) :
    q ∈ primeDivisorSubtypeFinset m ↔ q.1 ∣ m := by
  simp only [primeDivisorSubtypeFinset, Finset.mem_map, Finset.mem_attach]
  constructor
  · rintro ⟨r, _hr, hrq⟩
    have hrdvd : r.1 ∣ m :=
      (Nat.mem_primeFactors.mp r.2).2.1
    have hrval : r.1 = q.1 :=
      congrArg (fun s : {p : ℕ // Nat.Prime p} => s.1) hrq
    simpa [hrval] using hrdvd
  · intro hq
    exact
      ⟨⟨q.1, Nat.mem_primeFactors.mpr ⟨q.2, hq, hm⟩⟩,
        trivial, Subtype.ext rfl⟩

/-- The finite set of rational primes dividing the numerator or denominator
of the fixed/form-adapted skew-adjoint basis comparison determinant. -/
def skewAdjointFixedFormElementaryDetPrimeSupport
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Finset {p : ℕ // Nat.Prime p} :=
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  primeDivisorSubtypeFinset c.num.natAbs ∪
    primeDivisorSubtypeFinset c.den

/-- Membership in the comparison support is literal divisibility of the
rational determinant's numerator or denominator. -/
theorem mem_skewAdjointFixedFormElementaryDetPrimeSupport_iff
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (q : {p : ℕ // Nat.Prime p}) :
    q ∈ skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet ↔
      q.1 ∣
          (skewAdjointFixedFormElementaryDetScalar F hF hdet).num.natAbs ∨
        q.1 ∣
          (skewAdjointFixedFormElementaryDetScalar F hF hdet).den := by
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  have hc : c ≠ 0 :=
    skewAdjointFixedFormElementaryDetScalar_ne_zero F hF hdet
  have hnum : c.num.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact Rat.num_ne_zero.mpr hc
  have hden : c.den ≠ 0 := c.den_nz
  change
    q ∈ primeDivisorSubtypeFinset c.num.natAbs ∪
        primeDivisorSubtypeFinset c.den ↔
      q.1 ∣ c.num.natAbs ∨ q.1 ∣ c.den
  rw [Finset.mem_union,
    mem_primeDivisorSubtypeFinset_iff hnum,
    mem_primeDivisorSubtypeFinset_iff hden]

/-- Away from the comparison support, the rational basis-change determinant
has p-adic valuation zero. -/
theorem padicValRat_skewAdjointFixedFormElementaryDetScalar_eq_zero_of_not_mem
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    padicValRat q.1
      (skewAdjointFixedFormElementaryDetScalar F hF hdet) = 0 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  have hsupp : ¬(q.1 ∣ c.num.natAbs ∨ q.1 ∣ c.den) := by
    intro h
    exact hq
      ((mem_skewAdjointFixedFormElementaryDetPrimeSupport_iff
        F hF hdet q).mpr h)
  have hnum : ¬q.1 ∣ c.num.natAbs := fun h => hsupp (Or.inl h)
  have hden : ¬q.1 ∣ c.den := fun h => hsupp (Or.inr h)
  rw [padicValRat_def, padicValInt,
    ← Nat.factorization_def _ (Fact.out : Nat.Prime q.1),
    ← Nat.factorization_def _ (Fact.out : Nat.Prime q.1),
    Nat.factorization_eq_zero_of_not_dvd hnum,
    Nat.factorization_eq_zero_of_not_dvd hden]
  norm_num

/-- Away from the comparison support, the scalar-extended basis comparison
determinant has p-adic `NNReal` norm one. -/
theorem nnnorm_skewAdjointFixedFormElementaryDetScalar_eq_one_of_not_mem
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) (q : {p : ℕ // Nat.Prime p})
    (hq : q ∉ skewAdjointFixedFormElementaryDetPrimeSupport F hF hdet) :
    letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
    ‖algebraMap ℚ ℚ_[q.1]
        (skewAdjointFixedFormElementaryDetScalar F hF hdet)‖₊ = 1 := by
  letI : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let c := skewAdjointFixedFormElementaryDetScalar F hF hdet
  have hc : c ≠ 0 :=
    skewAdjointFixedFormElementaryDetScalar_ne_zero F hF hdet
  have hcp : (c : ℚ_[q.1]) ≠ 0 := by
    exact_mod_cast hc
  have hval : padicValRat q.1 c = 0 :=
    padicValRat_skewAdjointFixedFormElementaryDetScalar_eq_zero_of_not_mem
      F hF hdet q hq
  apply NNReal.eq
  change ‖(c : ℚ_[q.1])‖ = (1 : ℝ)
  rw [Padic.norm_eq_zpow_neg_valuation hcp,
    Padic.valuation_ratCast, hval]
  norm_num

end Matrix
