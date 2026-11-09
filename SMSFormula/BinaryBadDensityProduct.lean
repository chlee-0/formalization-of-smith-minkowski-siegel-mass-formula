import SMSFormula.BinaryLocalDensityFormula

/-!
# The original finite binary bad-density product

The local formula is assembled over the original bad-prime set. Prime
factorization separates the actual norm indices from discriminant and
conductor factors. The quantitative genus equality remains an open target.
-/

noncomputable section

namespace BinaryNormIdeal

/-- Recover a nonzero integer's magnitude over any prime set containing
its support. Additional primes contribute exponent zero. -/
theorem primeSet_prod_valuation (m : ℕ) (hm : m≠0)
    (S : Finset {p : ℕ // p.Prime})
    (hs : ∀ p : {p : ℕ // p.Prime}, p.val∣m → p∈S) :
    (∏ p ∈ S, (p.val : ℝ)^(padicValNat p.val m))=(m : ℝ) := by
  let N := S.image Subtype.val
  have hn : m.primeFactors⊆N := by
    intro p hp
    have hh := Nat.mem_primeFactors.mp hp
    exact Finset.mem_image.mpr ⟨⟨p,hh.1⟩,hs ⟨p,hh.1⟩ hh.2.1,rfl⟩
  have he : (∏ p ∈ N, p^(m.factorization p))=m := by
    rw [← Finset.prod_subset hn (by
      intro p _ hp
      have hz : m.factorization p=0 := Finsupp.notMem_support_iff.mp hp
      rw [hz,pow_zero])]
    have hh := Nat.prod_factorization_pow_eq_self hm
    rw [Nat.prod_factorization_eq_prod_primeFactors] at hh
    exact hh
  have hmap : (∏ p ∈ N, (p : ℝ)^(m.factorization p))=
      ∏ p ∈ S, (p.val : ℝ)^(m.factorization p.val) :=
    Finset.prod_image Subtype.val_injective.injOn
  have hv : (∏ p ∈ S, (p.val : ℝ)^(padicValNat p.val m))=
      ∏ p ∈ S, (p.val : ℝ)^(m.factorization p.val) := by
    apply Finset.prod_congr rfl
    intro p _
    rw [Nat.factorization_def m p.prop]
  rw [hv,← hmap]
  exact_mod_cast he

/-- The exact real half-valuation product is the positive square root,
including a unit magnitude and additional primes. -/
theorem primeSet_prod_half_valuation (m : ℕ) (hm : m≠0)
    (S : Finset {p : ℕ // p.Prime})
    (hs : ∀ p : {p : ℕ // p.Prime}, p.val∣m → p∈S) :
    (∏ p ∈ S, (p.val : ℝ)^((padicValNat p.val m : ℝ)/2))=Real.sqrt (m : ℝ) := by
  calc
    _=∏ p ∈ S, ((p.val : ℝ)^(padicValNat p.val m))^((1 : ℝ)/2) := by
      apply Finset.prod_congr rfl
      intro p _
      rw [div_eq_mul_inv,Real.rpow_mul (by positivity),Real.rpow_natCast]
      norm_num
    _=(∏ p ∈ S, (p.val : ℝ)^(padicValNat p.val m))^((1 : ℝ)/2) :=
      Real.finsetProd_rpow _ _ (by intro p _; positivity) _
    _=Real.sqrt (m : ℝ) := by
      rw [primeSet_prod_valuation m hm S hs,Real.sqrt_eq_rpow]

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- Every primitive discriminant prime belongs to the original bad set. -/
theorem binary_mem_bad_of_dvd_primitive (K : PositiveDefiniteIntegralLattice 2)
    (p : {p : ℕ // p.Prime}) (hp : p.val∣K.binaryPrimitiveDiscriminant.natAbs) :
    p∈massBadPrimeSet K := by
  have he : K.polarDeterminant=-((K.binaryContent : ℤ)^2*K.binaryPrimitiveDiscriminant) := by
    rw [K.polarDeterminant_eq_two_pow_mul_pairingDeterminant,
      K.binaryContent_sq_mul_binaryPrimitiveDiscriminant]
    norm_num
  have ha : K.polarDeterminant.natAbs=K.binaryContent^2*K.binaryPrimitiveDiscriminant.natAbs := by
    rw [he,Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
  apply (mem_massBadPrimeSet_iff K p).mpr
  right
  rw [ha]
  exact hp.trans (dvd_mul_left _ _)

/-- Every actual conductor prime is an original bad prime, on the same field. -/
theorem binary_mem_bad_of_dvd_orderIndex (K : PositiveDefiniteIntegralLattice 2)
    (p : {p : ℕ // p.Prime}) (hp : p.val∣K.binaryOrderIndex) :
    p∈massBadPrimeSet K := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  apply K.binary_mem_bad_of_dvd_primitive
  have he := congrArg Int.natAbs K.binaryPrimitiveDiscriminant_eq_orderIndex_sq_mul_fieldDiscr
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at he
  rw [he]
  exact (hp.trans (dvd_pow_self _ (by decide : (2 : ℕ)≠0))).trans (dvd_mul_right _ _)

/-- The literal product of original local norm-quotient cardinalities. -/
def binaryLocalNormIndexProduct (K : PositiveDefiniteIntegralLattice 2) : ℕ :=
  ∏ p ∈ massBadPrimeSet K,
    (letI : Fact p.val.Prime := ⟨p.prop⟩
     Nat.card (OrderUnitNormQuotient ℤ_[p.val] K.binaryPrimitiveDiscriminant))

theorem binaryLocalNormIndexProduct_pos (K : PositiveDefiniteIntegralLattice 2) :
    0<K.binaryLocalNormIndexProduct := by
  apply Finset.prod_pos
  intro p _
  letI : Fact p.val.Prime := ⟨p.prop⟩
  exact card_orderUnitNormQuotient_pos p.val K.binaryPrimitiveDiscriminant

/-- Half-valuations over the original Bad set recover sqrt(abs(D)). -/
theorem binary_bad_half_valuation_product (K : PositiveDefiniteIntegralLattice 2) :
    (∏ p ∈ massBadPrimeSet K,
      (p.val : ℝ)^((padicValNat p.val K.binaryPrimitiveDiscriminant.natAbs : ℝ)/2))=
      Real.sqrt |(K.binaryPrimitiveDiscriminant : ℝ)| := by
  rw [primeSet_prod_half_valuation _
    (Int.natAbs_ne_zero.mpr (ne_of_lt K.binaryPrimitiveDiscriminant_neg)) _
    K.binary_mem_bad_of_dvd_primitive]
  have he : (K.binaryPrimitiveDiscriminant.natAbs : ℝ)=|(K.binaryPrimitiveDiscriminant : ℝ)| := by
    rw [Nat.cast_natAbs,Int.cast_abs]
  rw [he]

/-- The dyadic inverse-density coefficient occurs exactly once in original Bad. -/
theorem binary_bad_dyadic_coefficient_product (K : PositiveDefiniteIntegralLattice 2) :
    (∏ p ∈ massBadPrimeSet K, if p.val=2 then (1/4 : ℝ) else 1)=1/4 := by
  have htwo : (⟨2,Nat.prime_two⟩ : {p : ℕ // p.Prime})∈massBadPrimeSet K :=
    (mem_massBadPrimeSet_iff K _).mpr (Or.inl rfl)
  rw [Finset.prod_eq_single_of_mem ⟨2,Nat.prime_two⟩ htwo (by
    intro p _ hp
    have hv : p.val≠2 := fun h=>hp (Subtype.ext h)
    simp only [if_neg hv])]
  norm_num

/-- The conductor terms over the bad prime set are exactly the conductor
Euler product of the same field. -/
theorem binary_bad_conductor_product (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    (∏ p ∈ massBadPrimeSet K, if p.val∣K.binaryOrderIndex then K.binaryFieldEulerFactor p else 1)=
      ∏ p ∈ K.binaryOrderIndex.primeFactors,
        (1-(conductorPrimeSign (NumberField.discr
          (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℝ)/(p : ℝ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  let N := (massBadPrimeSet K).image Subtype.val
  let f : ℕ → ℝ := fun p=>1-(conductorPrimeSign (NumberField.discr
    (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℝ)/(p : ℝ)
  have hn : N.filter (fun p=>p∣K.binaryOrderIndex)=K.binaryOrderIndex.primeFactors := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_image,N]
    constructor
    · rintro ⟨⟨q,hq,rfl⟩,hp⟩
      exact Nat.mem_primeFactors.mpr ⟨q.prop,hp,ne_of_gt K.binaryOrderIndex_pos⟩
    · intro hp
      have hh := Nat.mem_primeFactors.mp hp
      exact ⟨⟨⟨p,hh.1⟩,K.binary_mem_bad_of_dvd_orderIndex ⟨p,hh.1⟩ hh.2.1,rfl⟩,hh.2.1⟩
  have hmap : (∏ p ∈ N, if p∣K.binaryOrderIndex then f p else 1)=
      ∏ p ∈ massBadPrimeSet K, if p.val∣K.binaryOrderIndex then f p.val else 1 :=
    Finset.prod_image Subtype.val_injective.injOn
  change (∏ p ∈ massBadPrimeSet K, if p.val∣K.binaryOrderIndex then f p.val else 1)=
    ∏ p ∈ K.binaryOrderIndex.primeFactors,f p
  rw [← hmap,← Finset.prod_filter,hn]

/-- Exact finite simplification of the bad-density product.
Every bad prime and every local norm index is kept. -/
theorem binaryBadDensityCorrection_eq_sqrt_div_normIndexProduct (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    K.binaryBadDensityCorrection=
      Real.sqrt |(K.binaryPrimitiveDiscriminant : ℝ)| *
        (∏ p ∈ K.binaryOrderIndex.primeFactors,
          (1-(conductorPrimeSign (NumberField.discr
            (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℝ)/(p : ℝ)))/
        (4*(K.binaryLocalNormIndexProduct : ℝ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  rw [K.binaryBadDensityCorrection_eq_normIndex_product]
  simp only [Finset.prod_mul_distrib]
  rw [K.binary_bad_dyadic_coefficient_product,K.binary_bad_half_valuation_product,
    K.binary_bad_conductor_product]
  have he : (∏ p ∈ massBadPrimeSet K,
      (letI : Fact p.val.Prime := ⟨p.prop⟩
       (Nat.card (OrderUnitNormQuotient ℤ_[p.val] K.binaryPrimitiveDiscriminant) : ℝ)⁻¹))=
      (K.binaryLocalNormIndexProduct : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    congr 1
    rw [binaryLocalNormIndexProduct,Nat.cast_prod]
  rw [he]
  ring

/-- The binary mass formula, with the same `K` and the same positive `P`, is
equivalent to the quantitative genus equality on the norm quotients and two-torsion.
This equivalence does not prove that cardinality equality. -/
theorem binaryMassFormula_iff_normIndexProduct_eq_twoTorsion (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    (∃ P : ℝ, 0<P ∧ massLocalInverseProductTendsTo K P ∧
      ((ordinaryGenusMass K : ℚ) : ℝ)=archimedeanMassFactor 2*P) ↔
      K.binaryLocalNormIndexProduct=2*Nat.card
        (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
          ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  have he := K.binaryMassFormula_iff_finite_badDensity_identity
  dsimp only at he
  rw [he]
  have hB : (K.binaryLocalNormIndexProduct : ℝ)≠0 := by
    exact_mod_cast ne_of_gt K.binaryLocalNormIndexProduct_pos
  have hc : Real.sqrt |(K.binaryPrimitiveDiscriminant : ℝ)| *
      (∏ p ∈ K.binaryOrderIndex.primeFactors,
        (1-(conductorPrimeSign (NumberField.discr
          (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℝ)/(p : ℝ)))=
      K.binaryBadDensityCorrection*(4*(K.binaryLocalNormIndexProduct : ℝ)) := by
    rw [K.binaryBadDensityCorrection_eq_sqrt_div_normIndexProduct,
      div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hB)]
  rw [hc]
  constructor
  · intro h
    have hx := mul_left_cancel₀ K.binaryBadDensityCorrection_pos.ne'
      ((mul_comm _ _).trans h)
    have hz : (K.binaryLocalNormIndexProduct : ℝ)=
        ((2*Nat.card (powMonoidHom 2 :
          ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
          ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hz
  · intro h
    have hr : (K.binaryLocalNormIndexProduct : ℝ)=2*(Nat.card (powMonoidHom 2 :
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker : ℝ) := by
      exact_mod_cast h
    rw [hr]
    ring

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.primeSet_prod_valuation
#assert_standard_axioms BinaryNormIdeal.primeSet_prod_half_valuation
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_mem_bad_of_dvd_primitive
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_mem_bad_of_dvd_orderIndex
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalNormIndexProduct
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalNormIndexProduct_pos
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_bad_half_valuation_product
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_bad_dyadic_coefficient_product
#assert_standard_axioms PositiveDefiniteIntegralLattice.binary_bad_conductor_product
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadDensityCorrection_eq_sqrt_div_normIndexProduct
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryMassFormula_iff_normIndexProduct_eq_twoTorsion
