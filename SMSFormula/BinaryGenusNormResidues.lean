import SMSFormula.BinaryGenusNormImage
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Whole original norm tuples from one scalar progression

Scalar congruences preserve the original order-unit norm classes. CRT gives
one positive coprime progression for every tuple on original Bad. Dirichlet
gives arbitrarily large prime scalar representatives of that whole tuple.
No field splitting, Picard-class realization or image index is asserted.
-/

noncomputable section

namespace BinaryNormIdeal

/-- Equal scalar residues give equal original order-unit norm classes. -/
theorem orderUnitNormQuotientMap_eq_of_residue_eq (p : ℕ) [Fact p.Prime]
    (D : ℤ) (u v : ℤ_[p]ˣ)
    (h : normResidueUnits p u=normResidueUnits p v) :
    orderUnitNormQuotientMap ℤ_[p] D u=orderUnitNormQuotientMap ℤ_[p] D v := by
  have hk : u/v ∈ (normResidueUnits p).ker := by
    change normResidueUnits p (u/v)=1
    rw [map_div,h]
    exact div_self' (normResidueUnits p v)
  have hn := normResidueUnits_ker_le p D hk
  have he : orderUnitNormQuotientMap ℤ_[p] D (u/v)=1 :=
    (QuotientGroup.eq_one_iff _).mpr hn
  exact div_eq_one.mp ((map_div (orderUnitNormQuotientMap ℤ_[p] D) u v).symm.trans he)

theorem normResidueModulus_eq_prime_pow (p : ℕ) :
    normResidueModulus p=p^(if p=2 then 3 else 1) := by
  by_cases hp : p=2 <;> simp [normResidueModulus,hp]

/-- Distinct prime coordinates have coprime scalar residue moduli. -/
theorem normResidueModulus_coprime (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p≠q) : (normResidueModulus p).Coprime (normResidueModulus q) := by
  rw [normResidueModulus_eq_prime_pow,normResidueModulus_eq_prime_pow]
  exact Nat.coprime_pow_primes _ _ (Fact.out : p.Prime) (Fact.out : q.Prime) hpq

theorem prime_dvd_normResidueModulus (p : ℕ) [Fact p.Prime] :
    p∣normResidueModulus p := by
  by_cases hp : p=2 <;> simp [normResidueModulus,hp]

/-- A scalar natural number with unit residue is an actual p-adic unit. -/
theorem isUnit_padic_natCast_of_normResidue (p : ℕ) [Fact p.Prime] (a : ℕ)
    (ha : IsUnit (a : ZMod (normResidueModulus p))) : IsUnit (a : ℤ_[p]) := by
  have hc := (ZMod.isUnit_iff_coprime a (normResidueModulus p)).mp ha
  have hn : (a : ZMod p)≠0 := by
    intro hz
    have hpa := (ZMod.natCast_eq_zero_iff a p).mp hz
    have hd := Nat.dvd_gcd hpa (prime_dvd_normResidueModulus p)
    rw [hc.gcd_eq_one] at hd
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hd)
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  intro hz
  apply hn
  calc
    (a : ZMod p)=PadicInt.toZMod (a : ℤ_[p]) := (map_natCast _ a).symm
    _=0 := by
      change PadicInt.residueField (IsLocalRing.residue ℤ_[p] (a : ℤ_[p]))=0
      rw [hz,map_zero]

/-- Transport an original norm class to the literal natural scalar b.
This uses scalar-unit lifting, never finite norm-one lifting. -/
theorem exists_natCast_unit_normClass_of_modEq (p : ℕ) [Fact p.Prime]
    (D : ℤ) (a b : ℕ) (u : ℤ_[p]ˣ)
    (ha : (a : ZMod (normResidueModulus p))=(normResidueUnits p u).val)
    (hb : b ≡ a [MOD normResidueModulus p]) :
    ∃ v : ℤ_[p]ˣ, (v : ℤ_[p])=(b : ℤ_[p]) ∧
      orderUnitNormQuotientMap ℤ_[p] D v=orderUnitNormQuotientMap ℤ_[p] D u := by
  have he : (b : ZMod (normResidueModulus p))=(normResidueUnits p u).val :=
    ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hb).trans ha
  have hu := isUnit_padic_natCast_of_normResidue p b (he ▸ (normResidueUnits p u).isUnit)
  refine ⟨hu.unit,hu.unit_spec,?_⟩
  apply orderUnitNormQuotientMap_eq_of_residue_eq
  apply Units.ext
  change normResidueHom p (hu.unit : ℤ_[p])=(normResidueUnits p u).val
  rw [hu.unit_spec,map_natCast]
  exact he

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The CRT modulus retains every original Bad prime: eight at two,
and p at each odd coordinate. -/
def binaryBadNormResidueModulus (K : PositiveDefiniteIntegralLattice 2) : ℕ :=
  ∏ p ∈ massBadPrimeSet K, normResidueModulus p.val

theorem binaryBadNormResidueModulus_pos (K : PositiveDefiniteIntegralLattice 2) :
    0<K.binaryBadNormResidueModulus := by
  apply Finset.prod_pos
  intro p _
  letI : Fact p.val.Prime := ⟨p.prop⟩
  exact Nat.pos_of_ne_zero (NeZero.ne _)

theorem normResidueModulus_dvd_binaryBadNormResidueModulus
    (K : PositiveDefiniteIntegralLattice 2) (p : ↥(massBadPrimeSet K)) :
    normResidueModulus p.val.val∣K.binaryBadNormResidueModulus :=
  Finset.dvd_prod_of_mem _ p.prop

theorem prime_dvd_binaryBadNormResidueModulus
    (K : PositiveDefiniteIntegralLattice 2) (p : ↥(massBadPrimeSet K)) :
    p.val.val∣K.binaryBadNormResidueModulus := by
  letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
  exact (prime_dvd_normResidueModulus p.val.val).trans
    (K.normResidueModulus_dvd_binaryBadNormResidueModulus p)

/-- Every whole original tuple has one positive coprime scalar progression.
Every natural member has the requested actual local norm class at every
original Bad coordinate. No Picard-image condition is assumed or concluded. -/
theorem exists_progression_binaryBadNormProduct (K : PositiveDefiniteIntegralLattice 2)
    (x : K.BinaryBadNormProduct) :
    ∃ a : ℕ, 0<a ∧ a.Coprime K.binaryBadNormResidueModulus ∧
      ∀ b : ℕ, b ≡ a [MOD K.binaryBadNormResidueModulus] →
        ∀ p : ↥(massBadPrimeSet K),
          letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
          ∃ v : ℤ_[p.val.val]ˣ, (v : ℤ_[p.val.val])=(b : ℤ_[p.val.val]) ∧
            orderUnitNormQuotientMap ℤ_[p.val.val] K.binaryPrimitiveDiscriminant v=x p := by
  classical
  let u := fun p : ↥(massBadPrimeSet K) =>
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    Classical.choose (QuotientGroup.mk'_surjective
      (orderUnitNormSubgroup ℤ_[p.val.val] K.binaryPrimitiveDiscriminant) (x p))
  have hu (p : ↥(massBadPrimeSet K)) :
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      orderUnitNormQuotientMap ℤ_[p.val.val] K.binaryPrimitiveDiscriminant (u p)=x p := by
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    exact Classical.choose_spec (QuotientGroup.mk'_surjective
      (orderUnitNormSubgroup ℤ_[p.val.val] K.binaryPrimitiveDiscriminant) (x p))
  let m (p : ↥(massBadPrimeSet K)) := normResidueModulus p.val.val
  let r (p : ↥(massBadPrimeSet K)) : ℕ :=
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    (normResidueUnits p.val.val (u p)).val.val
  have hnz (p : ↥(massBadPrimeSet K)) (_ : p∈Finset.univ) : m p≠0 := by
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    exact NeZero.ne _
  have hcop : Set.Pairwise (↑(Finset.univ : Finset ↥(massBadPrimeSet K)))
      (Function.onFun Nat.Coprime m) := by
    intro p _ q _ hpq
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    letI : Fact q.val.val.Prime := ⟨q.val.prop⟩
    apply normResidueModulus_coprime
    intro he
    apply hpq
    exact Subtype.ext (Subtype.ext he)
  let w := Nat.chineseRemainderOfFinset r m Finset.univ hnz hcop
  let a := w.val+K.binaryBadNormResidueModulus
  have hres (p : ↥(massBadPrimeSet K)) :
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      (a : ZMod (m p))=(normResidueUnits p.val.val (u p)).val := by
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    have hd : m p∣K.binaryBadNormResidueModulus :=
      K.normResidueModulus_dvd_binaryBadNormResidueModulus p
    have he : a ≡ r p [MOD m p] := by
      calc
        a % m p=w.val % m p := by
          rw [show a=w.val+K.binaryBadNormResidueModulus from rfl,
            Nat.add_mod,Nat.mod_eq_zero_of_dvd hd,add_zero,Nat.mod_mod]
        _=r p % m p := w.property p (Finset.mem_univ p)
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr he).trans
      (ZMod.natCast_zmod_val _)
  refine ⟨a,Nat.add_pos_right _ K.binaryBadNormResidueModulus_pos,?_,?_⟩
  · apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    letI : Fact p.val.Prime := ⟨p.prop⟩
    apply (ZMod.isUnit_iff_coprime a _).mp
    rw [hres ⟨p,hp⟩]
    exact (normResidueUnits p.val (u ⟨p,hp⟩)).isUnit
  · intro b hb p
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    obtain ⟨v,hv,hq⟩ := exists_natCast_unit_normClass_of_modEq p.val.val
      K.binaryPrimitiveDiscriminant a b (u p) (hres p)
      (hb.of_dvd (K.normResidueModulus_dvd_binaryBadNormResidueModulus p))
    exact ⟨v,hv,hq.trans (hu p)⟩

/-- Dirichlet supplies arbitrarily large prime SCALARS for every original
tuple. Such a prime is outside original Bad. Splitting and membership in
the actual Picard image remain separate reciprocity/prime-form tasks. -/
theorem exists_prime_scalar_binaryBadNormProduct (K : PositiveDefiniteIntegralLattice 2)
    (x : K.BinaryBadNormProduct) (N : ℕ) :
    ∃ l : ℕ, ∃ hl : l.Prime, N<l ∧
      (⟨l,hl⟩ : {p : ℕ // p.Prime})∉massBadPrimeSet K ∧
      ∀ p : ↥(massBadPrimeSet K),
        letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
        ∃ v : ℤ_[p.val.val]ˣ, (v : ℤ_[p.val.val])=(l : ℤ_[p.val.val]) ∧
          orderUnitNormQuotientMap ℤ_[p.val.val] K.binaryPrimitiveDiscriminant v=x p := by
  obtain ⟨a,_,ha,hclasses⟩ := K.exists_progression_binaryBadNormProduct x
  obtain ⟨l,hl,hprime,hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max N K.binaryBadNormResidueModulus) K.binaryBadNormResidueModulus_pos.ne' ha
  refine ⟨l,hprime,lt_of_le_of_lt (le_max_left _ _) hl,?_,hclasses l hmod⟩
  intro hmem
  have hd := K.prime_dvd_binaryBadNormResidueModulus ⟨⟨l,hprime⟩,hmem⟩
  have hle := Nat.le_of_dvd K.binaryBadNormResidueModulus_pos hd
  exact (not_lt_of_ge hle) (lt_of_le_of_lt (le_max_right _ _) hl)

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.orderUnitNormQuotientMap_eq_of_residue_eq
#assert_standard_axioms BinaryNormIdeal.normResidueModulus_eq_prime_pow
#assert_standard_axioms BinaryNormIdeal.normResidueModulus_coprime
#assert_standard_axioms BinaryNormIdeal.prime_dvd_normResidueModulus
#assert_standard_axioms BinaryNormIdeal.isUnit_padic_natCast_of_normResidue
#assert_standard_axioms BinaryNormIdeal.exists_natCast_unit_normClass_of_modEq
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadNormResidueModulus
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadNormResidueModulus_pos
#assert_standard_axioms PositiveDefiniteIntegralLattice.normResidueModulus_dvd_binaryBadNormResidueModulus
#assert_standard_axioms PositiveDefiniteIntegralLattice.prime_dvd_binaryBadNormResidueModulus
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_progression_binaryBadNormProduct
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_prime_scalar_binaryBadNormProduct
