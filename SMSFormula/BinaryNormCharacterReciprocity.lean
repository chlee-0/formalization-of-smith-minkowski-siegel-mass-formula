import SMSFormula.BinaryRepresentedJacobi

/-!
# Reciprocity on the actual original Picard map

Every original class has one positive represented value coprime to original
Bad. The same scalar evaluates every original coordinate. Its Jacobi sign
is one, including for nonprimitive vectors and composite represented values.
-/

noncomputable section
namespace PositiveDefiniteIntegralLattice
open BinaryNormIdeal

/-- The whole original tuple character equals the discriminant Jacobi sign
at any odd natural scalar carrying that tuple, not merely prime scalars. -/
theorem binaryNormProductCharacter_scalar_eq_jacobi (K : PositiveDefiniteIntegralLattice 2)
    (x : K.BinaryBadNormProduct) (A : ℕ) (hodd : Odd A)
    (hx : ∀ p : ↥(massBadPrimeSet K),
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      ∃ u : ℤ_[p.val.val]ˣ, (u : ℤ_[p.val.val])=(A : ℤ_[p.val.val]) ∧
        orderUnitNormQuotientMap ℤ_[p.val.val] K.binaryPrimitiveDiscriminant u=x p) :
    (K.binaryNormProductCharacter x : ℤ)=jacobiSym K.binaryPrimitiveDiscriminant A := by
  rw [K.binaryNormProductCharacter_scalar x A hx,K.binaryBad_odd_prime_product_eq_jacobi,
    ← jacobiSym_eq_signed_oddPart _ K.binaryPrimitiveDiscriminant_neg A hodd]

/-- Global reciprocity on the class map, with content, order-unit norms and all
bad coordinates kept. -/
theorem binaryBadLocalNormImage_le_normCharacter_ker (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryBadLocalNormImage ≤
      MonoidHom.ker (G := K.BinaryBadNormProduct) K.binaryNormProductCharacter := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  rintro x ⟨xi,rfl⟩
  obtain ⟨L,hg,hD,hclass⟩ := K.exists_lattice_of_binaryIdealClass xi
  obtain ⟨v,hpos,havoid⟩ := L.exists_pos_binaryPrimitivePolynomial_avoiding (massBadPrimeSet K)
  let A : ℕ := (L.binaryPrimitivePolynomial v).natAbs
  have hAcast : (A : ℤ)=L.binaryPrimitivePolynomial v := by
    dsimp [A]
    rw [Int.natCast_natAbs,abs_of_pos hpos]
  have hA : 0<A := Int.natAbs_pos.mpr (ne_of_gt hpos)
  have hnot2 : ¬(2 : ℤ)∣L.binaryPrimitivePolynomial v :=
    havoid ⟨2,Nat.prime_two⟩ ((mem_massBadPrimeSet_iff K _).mpr (Or.inl rfl))
  have hodd : Odd A := (Int.not_even_iff_odd.mp (by
    intro he
    exact hnot2 (even_iff_two_dvd.mp he))).natAbs
  have hcop : K.binaryPrimitiveDiscriminant.gcd A=1 := by
    have hc : K.binaryPrimitiveDiscriminant.natAbs.Coprime A := by
      apply Nat.coprime_of_dvd'
      intro p hp hpD hpA
      exact False.elim ((havoid ⟨p,hp⟩ (K.binary_mem_bad_of_dvd_primitive ⟨p,hp⟩ hpD))
        (Int.natCast_dvd.mpr hpA))
    exact hc.gcd_eq_one
  have hj : jacobiSym K.binaryPrimitiveDiscriminant A=1 := by
    rw [← hD]
    exact jacobi_discriminant_represented_eq_one
      (L.pairingMatrix 0 0/(L.binaryContent : ℤ))
      ((2*L.pairingMatrix 0 1)/(L.binaryContent : ℤ))
      (L.pairingMatrix 1 1/(L.binaryContent : ℤ)) A hA hodd (v 0) (v 1)
      (by simpa only [binaryPrimitivePolynomial_apply] using hAcast.symm)
      (by change L.binaryPrimitiveDiscriminant.gcd A=1; rw [hD]; exact hcop)
  have hx : ∀ p : ↥(massBadPrimeSet K),
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      ∃ u : ℤ_[p.val.val]ˣ, (u : ℤ_[p.val.val])=(A : ℤ_[p.val.val]) ∧
        orderUnitNormQuotientMap ℤ_[p.val.val] K.binaryPrimitiveDiscriminant u=
          K.binaryBadLocalNormHom xi p := by
    intro p
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    have hu : IsUnit (L.binaryPrimitivePolynomial v : ℤ_[p.val.val]) := by
      by_contra hn
      rw [PadicInt.not_isUnit_iff,PadicInt.norm_intCast_lt_one_iff] at hn
      exact havoid p.val p.prop hn
    refine ⟨hu.unit,?_,?_⟩
    · rw [hu.unit_spec]
      exact_mod_cast hAcast.symm
    · have hv : L.binaryPrimitivePolynomialOver ℤ_[p.val.val]
          (fun i => (v i : ℤ_[p.val.val]))=(hu.unit : ℤ_[p.val.val]) := by
        rw [L.binaryPrimitivePolynomialOver_intCast,hu.unit_spec]
      have he := K.binaryBadLocalNormHom_apply L hg hD p
        (fun i => (v i : ℤ_[p.val.val])) hu.unit hv
      rw [hclass] at he
      exact he.symm
  change K.binaryNormProductCharacter (K.binaryBadLocalNormHom xi)=1
  apply Units.ext
  change (K.binaryNormProductCharacter (K.binaryBadLocalNormHom xi) : ℤ)=1
  rw [K.binaryNormProductCharacter_scalar_eq_jacobi _ A hodd hx,hj]

/-- Exact image/kernel equality on the original finite product. -/
theorem binaryBadLocalNormImage_eq_normCharacter_ker (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryBadLocalNormImage=
      MonoidHom.ker (G := K.BinaryBadNormProduct) K.binaryNormProductCharacter := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact le_antisymm K.binaryBadLocalNormImage_le_normCharacter_ker
    K.binaryNormCharacter_ker_le_badLocalNormImage

/-- The actual original Picard image has index TWO, with no caller genus
or field certificate. -/
theorem binaryBadLocalNormImage_index_two (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryBadLocalNormImage.index=2 := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [K.binaryBadLocalNormImage_eq_normCharacter_ker,K.binaryNormProductCharacter_ker_index]

/-- Quantitative genus on the original Bad product and original class group. -/
theorem binaryLocalNormIndexProduct_eq_two_mul_twoTorsion (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryLocalNormIndexProduct=2 *
      Nat.card (powMonoidHom 2 : ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant) →*
        ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant)).ker := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [K.binaryLocalNormIndexProduct_eq_imageIndex_mul_twoTorsion,
    K.binaryBadLocalNormImage_index_two]

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormProductCharacter_scalar_eq_jacobi
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadLocalNormImage_le_normCharacter_ker
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadLocalNormImage_eq_normCharacter_ker
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryBadLocalNormImage_index_two
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalNormIndexProduct_eq_two_mul_twoTorsion
