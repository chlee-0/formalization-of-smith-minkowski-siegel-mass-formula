import SMSFormula.BinaryGenusNormResidues

/-!
# Split prime forms in the original binary Picard image

A split odd prime gives primitive coefficients with the order
discriminant. Reconstruction keeps the original content and integral F.
Its represented leading unit binds the whole original local norm tuple
to the Picard image. The product character and reciprocity are treated
separately; no index-two or mass theorem is asserted here.
-/

noncomputable section

namespace BinaryNormIdeal

/-- A split odd prime has an integral root of the canonical order norm
polynomial. This is on the original order, without maximality assumptions. -/
theorem exists_prime_dvd_discriminantOrder_norm (D : ℤ)
    (hD : D%4=0 ∨ D%4=1) (l : ℕ) [Fact l.Prime] (hl : l≠2)
    (hs : conductorPrimeSign D l=1) :
    ∃ t : ℤ, (l : ℤ)∣(⟨t,1⟩ : DiscriminantOrder D).norm := by
  let r := D%2
  let c := (r^2-D)/4
  have hcanon : r^2-4*c=D := by
    simpa only [mul_one] using discriminantOrder_coefficients D hD
  have hleg : legendreSym l (r^2+4*(-c))=1 := by
    have he : r^2+4*(-c)=D := by linear_combination hcanon
    rw [he]
    simpa only [conductorPrimeSign_eq,if_neg hl] using hs
  have hcount := card_quadraticRoots_odd l hl (-c) r
  rw [hleg] at hcount
  have hpos : 0<Nat.card {z : ZMod l // z*z+(r : ZMod l)*z-(-c : ℤ)=0} := by
    exact_mod_cast (show (0 : ℤ)<Nat.card {z : ZMod l // z*z+(r : ZMod l)*z-(-c : ℤ)=0} by omega)
  let z := Classical.choice (Nat.card_pos_iff.mp hpos).1
  let t : ℤ := z.val.val
  have ht : (t : ZMod l)=z.val := by
    simpa only [t,Int.cast_natCast] using ZMod.natCast_zmod_val z.val
  refine ⟨t,(ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp ?_⟩
  have hn : (⟨t,1⟩ : DiscriminantOrder D).norm=t*t+r*t+c := by
    rw [QuadraticAlgebra.norm_def]
    ring
  rw [hn]
  push_cast
  rw [ht]
  simpa only [Int.cast_neg,sub_neg_eq_add] using z.prop

/-- The prime-leading coefficients are primitive; a common prime divisor
would divide the original discriminant, contradicting split sign one. -/
theorem prime_coefficients_gcd_eq_one (D B C : ℤ) (l : ℕ) [Fact l.Prime]
    (hl : l≠2) (hs : conductorPrimeSign D l=1)
    (hD : B^2-4*(l : ℤ)*C=D) : Int.gcd (l : ℤ) (Int.gcd B C : ℤ)=1 := by
  have hnot : ¬(l : ℤ)∣D := by
    intro hd
    have hz := (legendreSym.eq_zero_iff l D).mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd D l).mpr hd)
    have he : legendreSym l D=1 := by
      simpa only [conductorPrimeSign_eq,if_neg hl] using hs
    omega
  have hdiv : Int.gcd (l : ℤ) (Int.gcd B C : ℤ)∣l := by
    exact_mod_cast Int.gcd_dvd_left (l : ℤ) (Int.gcd B C : ℤ)
  rcases (Nat.dvd_prime (Fact.out : l.Prime)).mp hdiv with h | h
  · exact h
  · exfalso
    apply hnot
    have hdB : (l : ℤ)∣B := by
      have hh := (Int.gcd_dvd_right (l : ℤ) (Int.gcd B C : ℤ)).trans (Int.gcd_dvd_left B C)
      rw [h] at hh
      exact hh
    rw [← hD]
    exact dvd_sub (dvd_pow hdB (by decide : (2 : ℕ)≠0))
      (dvd_mul_of_dvd_left (dvd_mul_left (l : ℤ) 4) C)

/-- Primitive original-order coefficients with prime leading term. -/
theorem exists_primitive_prime_coefficients (D : ℤ)
    (hD : D%4=0 ∨ D%4=1) (l : ℕ) [Fact l.Prime] (hl : l≠2)
    (hs : conductorPrimeSign D l=1) :
    ∃ B C : ℤ, B^2-4*(l : ℤ)*C=D ∧
      Int.gcd (l : ℤ) (Int.gcd B C : ℤ)=1 := by
  obtain ⟨t,ht⟩ := exists_prime_dvd_discriminantOrder_norm D hD l hl hs
  let r := D%2
  let c := (r^2-D)/4
  have he := normalized_discriminant 1 r c (l : ℤ) t ht
  have hc := discriminantOrder_coefficients D hD
  have hdisc : (r+2*t)^2-4*(l : ℤ)*((⟨t,1⟩ : DiscriminantOrder D).norm/(l : ℤ))=D :=
    he.trans hc
  exact ⟨_,_,hdisc,prime_coefficients_gcd_eq_one D _ _ l hl hs hdisc⟩

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- A split good prime produces an actual lattice at K's original content
and discriminant, with the literal prime-leading polynomial over every
commutative scalar ring. Original parity is discharged internally. -/
theorem exists_binaryPrimeForm (K : PositiveDefiniteIntegralLattice 2)
    (l : {p : ℕ // p.Prime}) (hl : l∉massBadPrimeSet K)
    (hs : conductorPrimeSign K.binaryPrimitiveDiscriminant l.val=1) :
    ∃ (B C : ℤ) (L : PositiveDefiniteIntegralLattice 2),
      L.binaryContent=K.binaryContent ∧
      L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant ∧
      B^2-4*(l.val : ℤ)*C=K.binaryPrimitiveDiscriminant ∧
      ∀ (R : Type*) [CommRing R] (v : Fin 2 → R),
        L.binaryPrimitivePolynomialOver R v=
          (l.val : R)*(v 0)^2+(B : R)*v 0*v 1+(C : R)*(v 1)^2 := by
  letI : Fact l.val.Prime := ⟨l.prop⟩
  obtain ⟨B,C,hD,hprim⟩ := exists_primitive_prime_coefficients
    K.binaryPrimitiveDiscriminant K.binaryPrimitiveDiscriminant_mod_four l.val
    (not_mem_massBadPrimeSet_ne_two K hl) hs
  have hpos : (0 : ℤ)<l.val := by exact_mod_cast l.prop.pos
  have hneg : B^2-4*(l.val : ℤ)*C<0 := hD ▸ K.binaryPrimitiveDiscriminant_neg
  have heven := K.binary_scaled_mixed_even_of_discriminant (l.val : ℤ) B C hD
  let L := binaryLatticeOfCoefficients K.binaryContent K.binaryContent_pos
    (l.val : ℤ) B C hpos hneg heven
  have hc := binaryLatticeOfCoefficients_coefficients K.binaryContent K.binaryContent_pos
    (l.val : ℤ) B C hpos hneg heven hprim
  refine ⟨B,C,L,binaryLatticeOfCoefficients_content _ _ _ _ _ _ _ _ hprim,
    (binaryLatticeOfCoefficients_discriminant _ _ _ _ _ _ _ _ hprim).trans hD,hD,?_⟩
  intro R _ v
  rw [binaryPrimitivePolynomialOver_apply,hc.1,hc.2.1,hc.2.2]
  simp only [Int.cast_natCast]

/-- The primitive-order sign is the same field sign at every original
good prime. The native conductor support proves the missing index is a unit. -/
theorem binaryPrimitivePrimeSign_eq_fieldSign_of_good (K : PositiveDefiniteIntegralLattice 2)
    (l : {p : ℕ // p.Prime}) (hl : l∉massBadPrimeSet K) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    conductorPrimeSign K.binaryPrimitiveDiscriminant l.val=
      conductorPrimeSign (NumberField.discr
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) l.val := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  letI : Fact l.val.Prime := ⟨l.prop⟩
  have hnot : ¬l.val∣K.binaryOrderIndex := fun h => hl (K.binary_mem_bad_of_dvd_orderIndex l h)
  rw [K.binaryPrimitivePrimeSign_eq_masked_fieldSign,if_neg hnot]

/-- If a whole original tuple has a scalar representative at a same-field
split good prime, its actual prime-form class maps to that tuple. This is a
reverse-image bridge; the character condition forcing splitting remains open. -/
theorem mem_binaryBadLocalNormImage_of_field_split_prime (K : PositiveDefiniteIntegralLattice 2)
    (x : K.BinaryBadNormProduct) (l : {p : ℕ // p.Prime})
    (hl : l∉massBadPrimeSet K)
    (hs : letI := K.binaryDiscriminantOrder_isDomain
      letI := K.binaryFractionNumberField
      conductorPrimeSign (NumberField.discr
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) l.val=1)
    (hx : ∀ p : ↥(massBadPrimeSet K),
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      ∃ u : ℤ_[p.val.val]ˣ, (u : ℤ_[p.val.val])=(l.val : ℤ_[p.val.val]) ∧
        orderUnitNormQuotientMap ℤ_[p.val.val] K.binaryPrimitiveDiscriminant u=x p) :
    letI := K.binaryDiscriminantOrder_isDomain
    x∈K.binaryBadLocalNormImage := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  have hs' := (K.binaryPrimitivePrimeSign_eq_fieldSign_of_good l hl).trans hs
  obtain ⟨B,C,L,hg,hD,_,hpoly⟩ := K.exists_binaryPrimeForm l hl hs'
  change ∃ xi, K.binaryBadLocalNormHom xi=x
  refine ⟨L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD,?_⟩
  funext p
  letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
  obtain ⟨u,hu,hq⟩ := hx p
  have hv : L.binaryPrimitivePolynomialOver ℤ_[p.val.val] ![1,0]=(u : ℤ_[p.val.val]) := by
    rw [hpoly]
    simpa using hu.symm
  exact (K.binaryBadLocalNormHom_apply L hg hD p ![1,0] u hv).trans hq

/-- Every whole tuple has a positive coprime scalar progression such that
Any sufficiently large same-field split prime in it realizes the tuple in
the actual Picard image. The character condition yielding such a split prime
is not supplied by this conditional bridge. -/
theorem exists_progression_binaryBadLocalNormImage_of_fieldSign
    (K : PositiveDefiniteIntegralLattice 2) (x : K.BinaryBadNormProduct) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    ∃ a : ℕ, 0<a ∧ a.Coprime K.binaryBadNormResidueModulus ∧
      ∀ l : {p : ℕ // p.Prime}, K.binaryBadNormResidueModulus<l.val →
        l.val ≡ a [MOD K.binaryBadNormResidueModulus] →
        conductorPrimeSign (NumberField.discr
          (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) l.val=1 →
        x∈K.binaryBadLocalNormImage := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  obtain ⟨a,ha,hcop,hclasses⟩ := K.exists_progression_binaryBadNormProduct x
  refine ⟨a,ha,hcop,?_⟩
  intro l hlarge hmod hs
  have hgood : l∉massBadPrimeSet K := by
    intro hmem
    have hd := K.prime_dvd_binaryBadNormResidueModulus ⟨l,hmem⟩
    exact (not_lt_of_ge (Nat.le_of_dvd K.binaryBadNormResidueModulus_pos hd)) hlarge
  exact K.mem_binaryBadLocalNormImage_of_field_split_prime x l hgood hs
    (hclasses l.val hmod)

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.exists_prime_dvd_discriminantOrder_norm
#assert_standard_axioms BinaryNormIdeal.prime_coefficients_gcd_eq_one
#assert_standard_axioms BinaryNormIdeal.exists_primitive_prime_coefficients
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryPrimeForm
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPrimitivePrimeSign_eq_fieldSign_of_good
#assert_standard_axioms PositiveDefiniteIntegralLattice.mem_binaryBadLocalNormImage_of_field_split_prime
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_progression_binaryBadLocalNormImage_of_fieldSign
